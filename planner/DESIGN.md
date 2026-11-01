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
  refine    : TargetSpec → String → IO TargetSpec            -- the planner does not call this
  score     : TargetSpec → Frame → List Pose → ScoreReport

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

Kapla blocks are exactly 15 × 3 × 1 block units. Block positions are whole numbers of
**grid units** (a quarter of a block unit), so a block is 60 × 12 × 4 grid units. For the
inside check a block is cut into cubes of side 1 block unit (4 grid units):

| Orientation | Size in cubes (x × y × z) |
|---|---|
| flat, long side along x | 15 × 3 × 1 |
| flat, long side along y | 3 × 15 × 1 |
| on edge, along x / y | 15 × 1 × 3  /  1 × 15 × 3 |
| upright | 3 × 1 × 15  /  1 × 3 × 15 |

```lean
structure GridBlock where
  orient : Orient      -- one of the 6 rows above
  x y z  : Int        -- the lowest corner, in grid units
```

Why a grid:
- Overlap, "rests on", and gap checks are plain integer arithmetic. They are fast and easy
  to test.
- Motifs (towers, walls) are naturally on this grid.
- We convert to the rational `Pose` of `KaplaCore` **once**, at the output:
  centre = (corner + size / 2) / 4.

Blocks that are not on the grid (round towers, which rotate about the vertical axis, and
leaning roof rafters) come later as a second kind of block that carries a `Pose`
directly. The grid stays the default.

Axes: z points up, the ground is z = 0. `KaplaCore` measures in block units (one block
thickness; a block is 15 × 3 × 1). The planner's grid is finer: one grid unit is a quarter of
a block unit, so the quarter points a person aims at (§3.4) are whole numbers. `toPose` and
`GridBlock.box` convert to block units.

---

## 3. Pipeline

```
TargetSpec (bubbles), N, HumanModel
   │
   ├─ 1. Bubbles        the target is a union of ellipsoids ("bubbles") (§3.1)
   ├─ 2. Scale search   try several scales s and grid offsets; keep the best (§3.2)
   │     for each (s, offset):
   │      ├─ 3. Allowed cells   grid cells that lie strictly inside the scaled bubbles (§3.3)
   │      ├─ 4. Design D        fill the surface with blocks, layer by layer, plus the
   │      │                     inner support it needs; at most N blocks (§3.4)
   │      │                     → verified check: every block strictly inside the bubbles
   │      ├─ 5. Sequence        backward search: take D apart, reverse it (§3.5)
   │      │                     → verified check: the steps rebuild exactly D
   │      ├─ 6. Pre-check       cheap local checks (block count, one-block gaps) (§3.6)
   │      ├─ 7. Physics         physics.check; on unstable step k → back to 5 with a hint;
   │      │                     if sequencing fails → 8. Repair: change D → back to 5 (§3.7)
   │      └─ 9. Score           semantics.score
   └─ 10. Rank          by score, then by difficulty; return the top k
```

The design problem in one sentence: **choose a scale and a set of at most N blocks that
lie strictly inside the target, cover its surface as well as possible, and can be built
step by step without falling.**

### 3.1 The target: bubbles

The semantic engine describes the target as a union of **bubbles** (`KaplaCore.Bubble`). A
bubble is a stretched ball (an ellipsoid) with its axes along x, y and z, given exactly in
rational numbers:

```lean
structure Bubble where
  label  : String       -- a name for people ("head", "tower 2", …)
  tags   : List String  -- hints for the planner ("tower", …)
  center : Q3
  semi   : Q3           -- the half-widths along x, y and z, each above 0
-- point p is inside  ⇔  ((p−c).x/semi.x)² + ((p−c).y/semi.y)² + ((p−c).z/semi.z)² ≤ 1
```

A bubble with a half-width of 0 or less contains nothing. A `Frame` (scale and a sideways
shift) says how big to build the model and where. Turned bubbles are not in the core format.
The planner's inside proof works for turned ellipsoids too (`Ellipsoid.lean`), so adding
them later only needs a new `bubble_contains_iff`.

The bubbles can overlap. The target is everything inside at least one bubble.

### 3.2 Scale search

The target has no fixed size; the planner chooses the scale s.
- **Too small**: thin parts (a tail, a spire) have no room for even one block, because blocks
  must be strictly inside. They vanish.
- **Too large**: N blocks cannot cover the surface. Covering a surface needs about s² blocks,
  so the useful scales are limited from above by N.

The likeness need not rise and fall smoothly with s, so we **sample** about 5–8 scales
between these two limits. At each scale we also try a few grid offsets (shifting the grid by
a fraction of a cell changes what fits). Each (scale, offset) gives one design.

### 3.3 Allowed cells (strictly inside)

A grid cell is **allowed** if its 8 corners lie inside one and the same bubble. A bubble is
convex, so the whole cell is then inside the target. A block is allowed if all its cells
are allowed. This may lose a little room where two bubbles meet, but it never lets a block
stick out.

Every test is exact arithmetic in `Rat`. The planner works with integer cells after this
step.

Kinds of allowed cells:
- **surface cell**: allowed, with at least one of its 6 neighbours not allowed;
- **inner cell**: allowed, all 6 neighbours allowed.

### 3.4 Design: cover the surface

Likeness is judged by the **outside shape** (surface focus). A hollow shell looks the same as
a solid build and costs far fewer blocks (about s² instead of s³). So the goal is: **cover
as many surface cells as possible, and use inner cells only where the shell needs support.**

Built **layer by layer, bottom up**, as Kapla is built:
1. **Ring**: in each layer, place blocks along the surface cells of that slice, like walls
   following the outline. Flat blocks for slices that change slowly; on-edge or upright
   blocks where a part is narrow and tall (trunk, spire).
2. **Bond**: blocks cross the joints of the layer below (the running bond of a wall, the
   crossing corners of a log cabin). This holds the ring together.
3. **Steps in and out**: where the outline grows from one layer to the next, the ring must
   overhang. Keep each overhang small enough that the load stays over its support (cheap
   grid estimate). Where the outline grows too fast, add inner support (a ledge or pillar,
   in inner cells) or leave the part out.
4. **Lids**: where the shape closes on top, span the opening with blocks resting on the
   ring below (a block spans up to 13 cells). Wide openings close in steps, each layer
   reaching in a little (like a stepped roof).
5. **Budget**: if this needs more than N blocks, decide what to keep. First every part keeps
   some blocks (the semantic engine's per-part score shows a missing part), then the blocks
   that define the outline seen from the side, then the rest.
6. **Improve**: try to move, swap or turn single blocks to cover more surface cells; repeat
   while it helps (with fuel).

The search is untrusted. Its output passes a **verified check**,
`insideBubbles bubbles s D : Bool`: every cell of every block has its 8 corners inside one
bubble (§5).

**Motifs** (tower, wall, slab, stepped roof; §3.4.1) are reused as ring and lid patterns, and
for tiny N.

#### 3.4.1 Motifs
A motif is a pure function from a few parameters to blocks, together with its block count:

```lean
structure Motif (P : Type) where
  name   : String
  blocks : P → List GridBlock     -- in the motif's own coordinates
  cost   : P → Nat                -- = (blocks p).length, proven per motif
```

Available: single upright block (N = 1, "tree trunk"), log-cabin tower, solid column. Planned:
wall in running bond, slab, stepped roof. Later (needs tilted blocks from physics M3):
leaning-rafter gable, A-frame pairs, tipi, hip (docs/DESIGN.md §4).

#### 3.4.2 Tiny N (N ≤ 4)
A fixed catalog of small layouts (upright trunk, two-block T, small arch, …), each placed
inside the bubbles at the best scale. The best scoring one wins.

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
| `Unstable(step, block)` / `PressTips` | **sequence again first**, with step k marked bad (the backward search finds another order or a two-hand step); then change the design: shorten the overhang, add a counterweight or inner support block (inside the bubbles), drop the block |
| `Slides(step, contact)` | steeper pitch; add a stopper block (roofs, later) |
| `Unreachable(step)` | move the step earlier; change the approach |
| `TooManyHands(step)` | split the step |
| `Overlap` / `Clearance` | move by one cell; drop the block |
| `UnevenSupports(block)` | build both supports the same way |

A design change may never add a block outside the bubbles: the `insideBubbles` check runs again.

Two kinds of edits: a new **order** (sequencer only, D unchanged) and a new **design**
(D → D′, then sequence D′ from scratch). Only the repair loop changes the design; the
sequencer never adds or drops blocks. After each edit we check again. The loop has fixed
fuel (default 8 rounds) and a global limit on physics calls. If fuel runs out, we drop the
candidate.

### 3.8 Rank and difficulty
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
  Bubble.lean      inside test, allowed / surface / inner cells (§3.1, §3.3)
  Inside.lean      insideBubbles check (verified, §5)
  Design.lean      scale search, rings, bonding, lids, budget, improvement (untrusted, §3.2, §3.4)
  Sequencer.lean   backward search, steps, grip, approach, phase (untrusted)
  Validate.lean    validateSequence (verified, §5)
  Stability.lean   cheap grid stability estimate used inside the search (untrusted)
  PreCheck.lean    local checks of §3.6
  Repair.lean      Diagnostic → edit
  Search.lean      tiny-N catalog, rank, difficulty
  Planner.lean     `planner : KaplaCore.Planner`
  Tests.lean       runs on the fixture targets with the mocks
```

---

## 5. What we prove

Most safety rules belong to the physics engine: every step stands, no block is in mid-air,
no blocks overlap (`certify_sound`). The planner proves what only the planner knows: **that
the design stays inside the target, and how the build steps relate to the design.**

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

3. **(c) Strictly inside the target.** Every point of every block of D lies inside the
   (scaled) bubbles. Stated for the check `insideBubbles` (§3.4): "if it accepts, every point
   of every block is inside some bubble". In words: **the plan never builds outside the
   shape**.
   Proof idea: a block is a union of cells; each cell's 8 corners lie inside one bubble.
   The bubble test is a sum of squares of straight-line (linear) functions, and such a
   square is never larger in the middle of a segment than at its ends. Every point of a cell
   is reached from its corners by three such in-between steps (along x, y, z), so it is
   inside too. This needs inequalities on `Rat` without Mathlib: the riskiest proof so far,
   so we try it early.

Also kept:
4. **Budget and physics** (`planPure_sound`, already in `specs/`): every returned plan
   passed the physics check and uses at most N blocks.
5. **Motif cost** (internal lemma): `(m.blocks p).length = m.cost p`.

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
- **SemanticMock.score**: IoU on a coarse voxel grid (cell = one block thickness) between
  the blocks and the union of the target part boxes. Per-part scores come from the same
  grid.
- **To change** for the bubble design: the mock score should become surface-based (share of
  surface cells covered by blocks) to match §3.4.

---

## 8. What the planner needs from `KaplaCore` v0.1

This was the planner's request for the contract; it is now in `KaplaCore` v0.1. The names
follow WORKSPLIT §3.

| Type | Fields the planner uses |
|---|---|
| `Q` (= `Rat`), `Q3` | exists |
| `Upright` | `flat`, `onEdge`, `standing` |
| `Rot` | yaw as an exact rational (cos, sin) pair. Grid poses use 0° and 90° only |
| `Pose` | `up`, `rot`, `center` (block centre) |
| `Grip`, `Approach` | `longSides` / `shortEnds` / `topEnd`; `fromAbove` / `slide axis sign` |
| `Step` | `blocks : List Pose`, `grip`, `approach`, `phase : String` |
| `BuildPlan` | `steps : List Step`, `blockCount` |
| `HumanModel` | all fields, plus `default` |
| `PartTag` | `name`, `kind` (tower, wall, roof gable / cone / hip, trunk, other), `box` (axis-aligned min/max `Q3`) |
| `TargetSpec` | `shape`, `silhouette?`, `parts : List PartTag` |
| `Diagnostic` | the eight cases in WORKSPLIT §3. Step and block indices are `Nat` (block index = position in the flattened plan) |
| `PhysicsReport` | `ok`, `diagnostics`, `slackPerBlock?` |
| `ScoreReport` | `score`, `iou`, `silhouetteIoU?`, `perPart : List (String × Q)`, `missing`, `extra`, `frame`, `blockCount`, `outside`, `uncovered`, `tooSmall` |
| `Verdict` | `good`, `coarse`, `abstract`, `symbolic` |
| `PlanRequest` | `target`, `blocks : Nat`, `human`, `maxCandidates`, `maxChecks` |
| `Candidate` | `plan`, `physics`, `score`, `difficulty` |
| `Difficulty` | `easy`, `medium`, `expert` |
| engines | `PhysicsEngine`, `SemanticEngine`, `Planner` (§1) |
| mocks | `PhysicsMock`, `SemanticMock` (§7) |

**Needed next** (core change, agree with B): `TargetSpec` gets `bubbles : List Bubble`
(§3.1). Each bubble names its part, so per-part scores still work. The planner then reads
only the bubbles, never the shape DSL.

---

## 9. Milestones

| # | Deliverable | Done when |
|---|---|---|
| P0 ✅ | `KaplaCore` v0.1 contract + mocks | merged |
| P1 ✅ | Grid, single + tower + column motifs, bottom-up sequencer, pre-check, planner on mocks | merged |
| P1.5 | Backward sequencer with backtracking and pairs; `validateSequence` + theorem (a)(b) in `specs/` | counterweight and "only stand as a pair" examples sequenced correctly on mocks; comparator green |
| P2 | Bubbles in core; allowed cells; `insideBubbles` + theorem (c) in `specs/` | comparator green; examples: a block that sticks out is rejected |
| P3 | Surface design: rings, bonding, lids, budget, improvement, scale search; repair loop | a candidate for every fixture target at N = 1, 4, 20, 200 on mocks |
| P4 | Roof motifs (stepped first; leaning ones after physics M3), knapsack tuning | Neuschwanstein@200 on real engines (I3) |

## 10. Open questions for the team

1. ~~B: the target as bubbles. Agreed format?~~ Settled: `KaplaCore.Bubble` (axes along x, y
   and z, §3.1).
2. B: a **surface-based** likeness score (the outside shape counts, not the inside volume).
   How exactly is it measured (surface coverage, silhouettes from several views, …)? The
   planner's internal goal (§3.4) should match it.
3. Block index in `Diagnostic`: position in the flattened plan, or (step, index in step)?
   This is A's call.
4. Can `PhysicsEngine` also offer a cheap `checkState` (does this set of blocks stand)? The
   backward search asks this many times; today it uses its own rough estimate. Additive.
