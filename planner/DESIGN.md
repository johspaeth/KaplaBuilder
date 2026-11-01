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

Kapla blocks are exactly 15 × 3 × 1. So we plan on a grid of cubes
with side **1**, and a block fills a whole box of cells:

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
  centre = anchor + size / 2.

Blocks that are not on the grid (round towers, which rotate about the vertical axis, and
leaning roof rafters) come later as a second kind of block that carries a `Pose`
directly. The grid stays the default.

Axes: z points up, the ground is z = 0, one unit is one block thickness. This must match `KaplaCore`.

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
   │      ├─ 6. Sequence     build order, steps of 1..hands blocks, grip, approach, phase
   │      ├─ 7. Pre-check    cheap local checks (overlap, one-block gaps, block count)
   │      ├─ 8. Physics      physics.check; on diagnostics → 9. Repair → back to 6
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

### 3.5 Sequence
The sequencer turns a set of blocks into build steps. Every step must stand, so this is a
**search, not just a sort**.

- Start order: sort blocks by bottom z, then by distance from the centre. A block's
  supports then always come before it. This is enough for simple cases such as a tower.
- Bottom-up is not always enough. Cases where the order must change:
  - **Counterweight first** (H3): an overhang stands only once the block that holds its
    back end down is in place. The two blocks can be at the same height.
  - **Press while placing** (H4): the hand presses on the new block. A block that stands
    can still tip the overhang below it while it is pressed.
  - **Hand access** (H5): if a higher block is placed first, a lower block next to it may
    no longer be reachable. Sometimes a lower block must wait.
  - **Pairs** (H7): two leaning blocks (A-frame) stand only together. They go into one
    two-hand step.
- When physics rejects step k, the repair loop (§3.7) first tries a new order.
- Steps: one block per step by default. Use a two-block step only where a motif says so
  (A-frame pairs) or repair needs it. Never more than `HumanModel.hands`.
- Grip: long sides for flat blocks, the top end for upright blocks.
- Approach: lower from above. Slide in sideways only when something blocks the path from
  above (later).
- Phase: the region name ("left tower", "roof").

### 3.6 Pre-check (before we call physics)
- block count ≤ N
- no two blocks overlap
- no gap of exactly one block width between blocks (rule H6)
- every block rests on the ground or on an earlier block

These checks are cheap and catch most planner bugs. The real physics check may be slow
(an exact LP in `Rat`), so we call it as rarely as we can.

### 3.7 Repair
`physics.check` returns `Diagnostic`s. Each one maps to an edit:

| Diagnostic | Edit, in order of preference |
|---|---|
| `Unstable(step, block)` / `PressTips` | **reorder first**: place the counterweight earlier, or join two blocks into one two-hand step; then shorten the overhang; add a counterweight block; drop the block |
| `Slides(step, contact)` | steeper pitch; add a stopper block (roofs, later) |
| `Unreachable(step)` | move the step earlier; change the approach |
| `TooManyHands(step)` | split the step |
| `Overlap` / `Clearance` | move by one cell; drop the block |
| `UnevenSupports(block)` | make both supports the same motif |

After each edit we sequence and check again. The loop has fixed fuel (default 8 rounds) and
a global limit on physics calls. If fuel runs out, we drop the candidate.

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
  Sequencer.lean   order, steps, grip, approach, phase
  PreCheck.lean    local checks of §3.6
  Repair.lean      Diagnostic → edit
  Search.lean      scale search, tiny-N catalog, rank, difficulty
  Planner.lean     `planner : KaplaCore.Planner`
  Tests.lean       runs on the fixture targets with the mocks
```

---

## 5. What we prove (optional, cheap, useful)

The planner does not need proofs for safety. But a few short theorems make it more
reliable and count for the "verification" judging axis. Each would go in
`specs/KaplaSpecs/Planner.lean` with a comparator config:

1. **Budget**: every candidate the planner returns uses at most N blocks.
2. **No lost blocks**: the sequencer's output, flattened, is a reordering of its input.
   No block is lost or duplicated.
3. **Hands**: every step has at least 1 and at most `hands` blocks.
4. **Motif cost**: `(m.blocks p).length = m.cost p` for every motif, so the budget step is
   correct by construction.
5. **Supports first** (grid blocks): in the sequenced order, each block rests on the ground
   or on a block placed earlier. This catches the "skyscraper built top-down" mistake
   before physics runs.

That every step *stands* is not a planner theorem. It is the physics guarantee
(`certify_sound`), because only the physics engine knows forces and balance.

Each gets a satisfiable `example` and a rejected bad output, as `CLAUDE.md` §4 asks.

---

## 6. Tests

- `#guard` unit tests per module (motif counts, overlap, sequencer order).
- End-to-end: for every fixture target (`tree`, `duck`, `house`, `gable_roof`, `castle`) and
  a few N (1, 4, 20, 200), the planner returns at least one candidate that `PhysicsMock`
  accepts. This is our acceptance criterion from WORKSPLIT §5.
- Property tests with `plausible` (if we add it) on the sequencer and pre-check.

---

## 7. Mocks (proposed for `KaplaCore.Mocks`)

The planner develops against these. They are *not* trusted and are deliberately simple.

- **PhysicsMock.check**: grid poses only. After **every step** (not only at the end), for
  every block, its centre of mass must lie over the bounding box of the blocks it rests on
  (or the ground). Also checks block count ≤ N and steps ≤ hands. It returns the matching
  `Diagnostic`s. Without the per-step check the planner would learn bad orders on mocks.
- **SemanticMock.score**: IoU on a coarse voxel grid (cell = one block thickness) between
  the blocks and the union of the target part boxes. Per-part scores come from the same
  grid.

---

## 8. What the planner needs from `KaplaCore` v0.1

`KaplaCore` is still empty, so this is the planner's request for the contract PR. The names
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

The key point for the planner is that **every target part carries a bounding box and a
kind**. Then the planner never needs to evaluate the shape DSL itself.

---

## 9. Milestones

| # | Deliverable | Done when |
|---|---|---|
| P0 | `KaplaCore` v0.1 contract + mocks (team PR) | builds; all four review it |
| P1 | Grid, single + tower motifs, sequencer, pre-check, planner on mocks | `kapla build` runs end to end on mocks (I1) |
| P2 | Wall, slab, decompose, budget, scale search, repair loop, tiny-N catalog | a candidate for every fixture target at N = 1, 4, 20, 200 |
| P3 | Theorems 1–4 of §5 in `specs/` and passing comparator | CI green |
| P4 | Roof motifs (stepped first; leaning ones after physics M3), knapsack tuning | Neuschwanstein@200 on real engines (I3) |

## 10. Open questions for the team

1. Does `TargetSpec.parts` carry a bounding box per part (§8)? This is B's call.
2. Block index in `Diagnostic`: position in the flattened plan, or (step, index in step)?
   This is A's call.
3. Can `PhysicsEngine` also offer a cheaper `checkPrefix` (only the newest step)? It would
   make the repair loop much faster. This is an additive change.
4. Should the mocks live in `KaplaCore.Mocks` (D needs them too for I1)? Proposed: yes.
