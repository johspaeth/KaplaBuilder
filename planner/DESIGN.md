# KaplaPlanner: Design

Owner: C. Status: **draft for review**. System context: [docs/DESIGN.md](../docs/DESIGN.md),
[docs/WORKSPLIT.md](../docs/WORKSPLIT.md).

The planner answers one question: *which blocks go where, and in which order?* It is a
search. It is **not trusted**: the physics checker decides if a plan is safe. A planner bug
can give a worse plan. It cannot give a plan that falls down.

**The output is a list of build steps**, not just a finished figure. The finished figure
is only the last step. A person follows the steps one by one, so **the figure must stand
after every step**, not only at the end. Example: a skyscraper is built from the bottom
up, and each floor must stand before the next one goes on. The physics engine checks
every step (every prefix of the plan, see `Valid` in docs/DESIGN.md §3). The planner must
find an order that passes.

---

## 1. Inputs, outputs, and what we call

The planner imports only `KaplaCore`. It gets the other engines as values.

```lean
-- in KaplaCore (see §8 for the full list we need)
structure PhysicsEngine where
  check : HumanModel → Nat → BuildPlan → PhysicsReport     -- ok, or a list of Diagnostic

structure SemanticEngine where
  interpret : Request → IO TargetSpec                      -- the planner does not call this
  score     : TargetSpec → List Pose → ScoreReport
  bound     : TargetSpec → Nat → Bound

structure Planner where
  plan : PlanRequest → PhysicsEngine → SemanticEngine → IO (List Candidate)
```

- **In**: `PlanRequest` = target shape, block budget `N`, `HumanModel`, how many candidates
  to return, and a limit on physics calls.
- **Out**: a list of `Candidate`s, best first. Each holds the `BuildPlan`, the
  `PhysicsReport` and `ScoreReport` we got for it, and a difficulty rating.
- The orchestrator (D) sends the best candidate to the real `certify`. Only a certified
  plan reaches the user.

Inside, the planner is a **pure function**. `IO` is only a thin wrapper (for logging). So
every part can be tested with `#guard` and `#eval`.

During development we pass `PhysicsMock` and `SemanticMock` (§7). Later, `app/Main.lean`
passes the real engines. The planner code does not change.

---

## 2. Internal model: an integer grid

Kapla blocks are exactly 1 : 3 : 15 (7.8 × 23.4 × 117 mm). So we plan on a grid of cubes
with side **7.8 mm**, and a block fills a whole box of cells:

| Orientation | Size in cells (x × y × z) |
|---|---|
| flat, long side along x | 15 × 3 × 1 |
| flat, long side along y | 3 × 15 × 1 |
| on edge, along x / y | 15 × 1 × 3  /  1 × 15 × 3 |
| upright | 3 × 1 × 15  /  1 × 3 × 15 |

```lean
structure GridBlock where
  orient : Orient      -- one of the 6 rows above
  anchor : Int × Int × Int   -- the cell with the smallest x, y, z
```

Why a grid:
- Overlap, "rests on", and gap checks are plain integer arithmetic. They are fast and easy
  to test.
- Motifs (towers, walls) are naturally on this grid.
- We convert to the rational `Pose` of `KaplaCore` **once**, at the output:
  centre = (anchor + size / 2) × 7.8 mm.

Blocks that are not on the grid (round towers, which rotate about the vertical axis, and
leaning roof rafters) come later as a second kind of block that carries a `Pose`
directly. The grid stays the default.

Axes: z points up, the ground is z = 0, units are mm. This must match `KaplaCore`.

---

## 3. Pipeline

```
TargetSpec, N, HumanModel
   │
   ├─ 1. Decompose      parts of the target → regions (tower, wall, roof, trunk, …)
   ├─ 2. Scale search   try a few scales s; keep the best result
   │     for each s:
   │      ├─ 3. Motifs       fill each region with a motif (pure, cost known up front)
   │      ├─ 4. Budget       split N blocks over the regions (knapsack)
   │      ├─ 5. Assemble     place regions in world coordinates; stack roof on walls
   │      ├─ 6. Sequence     backward search: take the design apart, reverse it (§3.5)
   │      │                  → steps of 1..hands blocks, grip, approach, phase
   │      │                  → verified validator: steps rebuild exactly the design
   │      ├─ 7. Pre-check    cheap local checks (block count, one-block gaps)
   │      ├─ 8. Physics      physics.check; on unstable step k → back to 6 with a hint;
   │      │                  if sequencing fails → 9. Repair (change the design) → back to 5
   │      └─ 10. Score       semantics.score
   └─ 11. Rank          by score, then by difficulty; return the top k
```

### 3.1 Decompose
Read `TargetSpec.parts`: each part has a kind (tower, wall, roof:gable / cone / hip, trunk,
…) and a bounding box. One part becomes one region. The planner does **not** evaluate the
full shape DSL. The semantic engine scores the result against the real shape.

### 3.2 Scale search
A target has no fixed size. We try a short list of scales (for example the largest scale
where the cheapest motif still fits in N, then 3/4, 1/2 of that). Each scale gives one
candidate.

### 3.3 Motifs
A motif is a pure function from a few parameters to blocks, together with its block count:

```lean
structure Motif (P : Type) where
  name   : String
  blocks : P → List GridBlock     -- in the motif's own coordinates
  cost   : P → Nat                -- = (blocks p).length, proven per motif
```

Order of work:
1. **single**: one upright block ("tree trunk"). This handles N = 1.
2. **log-cabin tower**: pairs of flat blocks, each layer turned 90°.
3. **wall**: flat blocks in running bond (each row shifted by half a block).
4. **slab / floor**: flat blocks side by side.
5. **stepped roof**: flat rows, each stepping in by a safe overhang.
6. Later (needs tilted blocks from physics M3): leaning-rafter gable, A-frame pairs, tipi,
   hip. See docs/DESIGN.md §4.

### 3.4 Budget
Each region has a few motif variants (for example tower height 4, 8, 12 layers). Choosing
one variant per region so that the total cost is at most N, with the largest estimated
gain, is a small knapsack. Small dynamic programming over N is fast enough for N ≤ a few
hundred. The estimate is "volume of the region covered". The real score comes from the
semantic engine later.

### 3.5 Sequence: backward ("assembly by disassembly")
The sequencer gets the designed structure **D** (a list of blocks) and finds an order in
which a person can build it, so that every intermediate state stands. It finds it
**backward**: start with all of D, repeatedly take blocks away, then reverse the list.

**Why backward.**
- **Hand access becomes easy.** If a block can be taken out of the current state, it can be
  put in as the last step onto the rest. Taking blocks away only frees space, so a block that
  can come out now can still come out later. Searching forward, every placed block is a new
  obstacle, and a choice made early can trap a block many steps later (an inner block of a
  pocket, after the walls are up).
- **Counterweights come out right.** The counterweight cannot be taken away while the
  overhang still depends on it, so the search takes the overhang away first. Reversed, the
  counterweight goes in first (H3).
- **Pairs.** When no single block can come out, try two at once. That becomes one two-hand
  step (H7), never more than `HumanModel.hands`.

**The search.**
1. State = blocks still standing (starts as D).
2. Candidates to take away next, in this order: blocks with nothing resting on them; higher
   first; outer first. Then pairs.
3. A candidate is allowed if the rest still stands (planner's own cheap stability estimate on
   the grid, see below) and it can be lifted out (later: hand access, H5).
4. Depth-first with backtracking: if nothing is allowed, undo the last removal and try the
   next candidate. A fuel limit bounds the work.
5. Out of fuel → the sequencer reports failure. It **never drops blocks**; changing the
   design is the repair loop's job (§3.7).

**Two layers of stability checking.**
- *Inside the search*: a cheap, unverified estimate on the grid (load over support, like the
  physics mock). It is called many times.
- *After the search*: one real `physics.check` on the whole plan. If it reports
  `unstable k …`, the sequencer runs again, told that step k must not be the state it was.

**Verified validator.** The search is untrusted and may change often. Its output goes
through `validateSequence D steps : Bool`, which checks: every step has 1 to `hands`
blocks, and all steps together are a reordering of D. A sequence that fails is not used.
Theorem (§5): if the validator says yes, the build grows step by step from nothing to
exactly D. So the theorem holds for every search we write, without proving the search.

**Per step, also:**
- Grip: long sides for flat blocks, the top end for upright blocks.
- Approach: lower from above (the reverse of lifting out). Slide in sideways later.
- Phase: the region name ("left tower", "roof").

### 3.6 Pre-check (before we call physics)
- block count ≤ N
- no gap of exactly one block width between blocks (rule H6)

Whether blocks overlap and whether every block is held up (no block in mid-air) is decided
by the physics engine. The planner may keep cheap grid versions of these as shortcuts, to
save physics calls, but they are not verified and not part of any promise.

### 3.7 Repair
`physics.check` returns `Diagnostic`s. Each one maps to an edit:

| Diagnostic | Edit, in order of preference |
|---|---|
| `Unstable(step, block)` / `PressTips` | **sequence again first**, with step k marked bad (the backward search finds another order or a two-hand step); then change the design: shorten the overhang, add a counterweight block, drop the block |
| `Slides(step, contact)` | steeper pitch; add a stopper block (roofs, later) |
| `Unreachable(step)` | move the step earlier; change the approach |
| `TooManyHands(step)` | split the step |
| `Overlap` / `Clearance` | move by one cell; drop the block |
| `UnevenSupports(block)` | make both supports the same motif |

Two kinds of edits: a new **order** (sequencer only, D unchanged) and a new **design**
(D → D′, then sequence D′ from scratch). Only the repair loop changes the design; the
sequencer never adds or drops blocks. After each edit we check again. The loop has fixed
fuel (default 8 rounds) and a global limit on physics calls. If fuel runs out, we drop the
candidate.

### 3.8 Tiny N (N ≤ 4)
A fixed catalog of small layouts (upright trunk, two-block T, small arch, …). We check and
score all of them and keep the best. This gives the "1 block → stand it upright as a tree
trunk" case.

### 3.9 Rank and difficulty
Sort by score. If two scores are within 0.02, the easier plan wins. Difficulty comes from
the smallest slack in the physics report, the number of two-hand steps, and the number of
leaning blocks. It maps to easy, medium or expert.

---

## 4. Modules

```
planner/KaplaPlanner.lean          root, imports the rest
planner/KaplaPlanner/
  Grid.lean        GridBlock, Orient, occupancy, overlap / rests-on / gap, toPose
  Motif.lean       the Motif structure
  Motifs/Single.lean  Motifs/Tower.lean  Motifs/Wall.lean  Motifs/Slab.lean  Motifs/SteppedRoof.lean
  Decompose.lean   TargetSpec → regions
  Budget.lean      knapsack
  Sequencer.lean   backward search, steps, grip, approach, phase (untrusted)
  Validate.lean    validateSequence (verified, §5)
  Stability.lean   cheap grid stability estimate used inside the search (untrusted)
  PreCheck.lean    local checks of §3.6
  Repair.lean      Diagnostic → edit
  Search.lean      scale search, tiny-N catalog, rank, difficulty
  Planner.lean     `planner : KaplaCore.Planner`
  Tests.lean       runs on the fixture targets with the mocks
```

---

## 5. What we prove

Most safety rules belong to the physics engine: every step stands, no block is in mid-air,
no blocks overlap (`certify_sound`). The planner proves what only the planner knows: **how
the build steps relate to the structure it designed.**

Let D be the designed structure and **state k** the blocks standing after step k (the
blocks of the first k steps; core defines a plan this way).

1. **(a) The structure only grows.** Every step adds at least one block (at most `hands`)
   and removes none: state k is a strict prefix of state k+1. No empty steps.
2. **(b) Every state is part of the design.** State k contains only blocks of D, each at
   most as often as in D (a sub-multiset). Before the last step it is a proper part of D.
   After the last step it is exactly D: nothing lost, added or doubled.

Both are stated for `validateSequence` (§3.5): "if the validator accepts, (a) and (b)
hold". The planner only uses validated sequences, so they hold for every plan it returns,
whatever the search does. Together they say the build is a strictly growing chain from
nothing to exactly D. Physics then checks each state in that chain, and each one is a real
stage on the way to the figure the user is shown.

Also kept:
3. **Budget and physics** (`planPure_sound`, already in `specs/`): every returned plan
   passed the physics check and uses at most N blocks.
4. **Motif cost** (internal lemma): `(m.blocks p).length = m.cost p`.

Today `sequence_perm` (in `specs/`) proves the end of (b) for the simple bottom-up
sequencer. It will be replaced by the validator theorem.

Each statement gets a satisfiable `example` and rejected bad outputs, as `CLAUDE.md` §4
asks.

---

## 6. Tests

- `#guard` unit tests per module (motif counts, overlap, sequencer order).
- End-to-end: for every fixture target (`tree`, `duck`, `house`, `gable_roof`, `castle`) and
  a few N (1, 4, 20, 200), the planner returns at least one candidate that `PhysicsMock`
  accepts. This is our acceptance criterion from WORKSPLIT §5.
- Property tests with `plausible` (if we add it) on the sequencer and pre-check.

---

## 7. Mocks (in `KaplaCore.Mocks`)

The planner develops against these. They are *not* trusted and are deliberately simple.

- **PhysicsMock.check**: grid poses only. After **every step** (not only at the end), for
  every block, its centre of mass must lie over the bounding box of the blocks it rests on
  (or the ground). Also checks block count ≤ N and steps ≤ hands. It returns the matching
  `Diagnostic`s. Without the per-step check the planner would learn bad orders on mocks.
- **SemanticMock.score**: volume IoU between the blocks and the target part boxes, best of
  three scales (target as high, as wide or as deep as the blocks).
- **SemanticMock.bound**: `min(1, N · block volume / target volume)`.

---

## 8. What the planner needs from `KaplaCore` v0.1

This was the planner's request for the contract; it is now in `KaplaCore` v0.1. The names
follow WORKSPLIT §3.

| Type | Fields the planner uses |
|---|---|
| `Q` (= `Rat`), `Q3` | exists |
| `Upright` | `flat`, `onEdge`, `standing` |
| `Rot` | yaw as an exact rational (cos, sin) pair. Grid poses use 0° and 90° only |
| `Pose` | `up`, `rot`, `center` (block centre, mm) |
| `Grip`, `Approach` | `longSides` / `shortEnds` / `topEnd`; `fromAbove` / `slide axis sign` |
| `Step` | `blocks : List Pose`, `grip`, `approach`, `phase : String` |
| `BuildPlan` | `steps : List Step`, `blockCount` |
| `HumanModel` | all fields, plus `adult`, `child`, `expert` profiles |
| `PartTag` | `name`, `kind` (tower, wall, roof gable / cone / hip, trunk, other), `box` (axis-aligned min/max `Q3`) |
| `TargetSpec` | `shape`, `silhouette?`, `parts : List PartTag` |
| `Diagnostic` | the eight cases in WORKSPLIT §3. Step and block indices are `Nat` (block index = position in the flattened plan) |
| `PhysicsReport` | `ok`, `diagnostics`, `slackPerBlock?` |
| `ScoreReport` | `score`, `iou`, `silhouetteIoU?`, `perPart : List (String × Q)` |
| `Bound`, `Verdict` | `maxScore`, `verdict` |
| `PlanRequest` | `target`, `blocks : Nat`, `human`, `maxCandidates`, `maxChecks` |
| `Candidate` | `plan`, `physics`, `score`, `difficulty` |
| `Difficulty` | `easy`, `medium`, `expert` |
| engines | `PhysicsEngine`, `SemanticEngine`, `Planner` (§1) |
| mocks | `PhysicsMock`, `SemanticMock` (§7) |

The key point for the planner is that **every target part carries a bounding box and a
kind**. Then the planner never needs to evaluate the shape DSL itself.

---

## 9. Milestones

| # | Deliverable | Done when |
|---|---|---|
| P0 | `KaplaCore` v0.1 contract + mocks (team PR) | builds; all four review it |
| P1 ✅ | Grid, single + tower + column motifs, bottom-up sequencer, pre-check, planner on mocks | merged |
| P1.5 | Backward sequencer with backtracking and pairs; `validateSequence` + theorem (a)(b) in `specs/` | counterweight and "only stand as a pair" examples sequenced correctly on mocks; comparator green |
| P2 | Wall, slab, decompose, budget, scale search, repair loop, tiny-N catalog | a candidate for every fixture target at N = 1, 4, 20, 200 |
| P4 | Roof motifs (stepped first; leaning ones after physics M3), knapsack tuning | Neuschwanstein@200 on real engines (I3) |

## 10. Open questions for the team

1. Does `TargetSpec.parts` carry a bounding box per part (§8)? This is B's call.
2. Block index in `Diagnostic`: position in the flattened plan, or (step, index in step)?
   This is A's call.
3. Can `PhysicsEngine` also offer a cheap `checkState` (does this set of blocks stand)? The
   backward search asks this many times; today it uses its own rough estimate. Additive.
4. Should the mocks live in `KaplaCore.Mocks` (D needs them too for I1)? Proposed: yes.
