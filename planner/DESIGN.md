# KaplaPlanner: Design

Owner: C. Status: **v2 is implemented, except turns other than quarter turns (stalled).**
Sections 1–9 are the first plan. Section 10 says what v1 does. Section 11 is v2 (standing
blocks, branch-and-cut search under a time limit); §11.13 says what was built and measured.
Context: [docs/DESIGN.md](../docs/DESIGN.md), [docs/WORKSPLIT.md](../docs/WORKSPLIT.md),
[semantics/APPROACH.md](../semantics/APPROACH.md) §3–4 (the score).

## 1. The task

Input: a bubble model (the "sculpture", scale-free, height 1), a block budget `N`, the human
model, and the two engines.

Output: a few candidate build plans, best first. Each candidate:

- uses **at most** `N` blocks (fewer is allowed);
- is accepted by the physics engine (`PhysicsEngine.check … = ok`);
- has a likeness score as high as we can find (`SemanticEngine.score`).

We search over two things: **the height** `h` of the finished model (this fixes the size of
every bubble, by `Bubble.place (Frame.ofHeight h)`), and **the blocks** (which ones, where,
which face down, which turn, in which order).

The planner is not trusted. It does not need to find the best plan, only good ones. The
physics engine and the scorer check every plan we return.

## 2. Facts about the engines that shape the search

| Fact | Where | What it means for us |
|---|---|---|
| Score = covered cells / (target cells + cells that stick out) | `Score.lean` | Blocks outside the bubbles cost score. Blocks inside cost nothing but budget. |
| A cell counts as covered if it lies **between two built cells of the same bubble** on one x, y or z line | `Score.lean`, `coveredOfBubble` | A hollow shell scores as much as a solid fill. We only need to build the two ends of each line. |
| Target cells grow like `h³`. A shell needs blocks that grow like `h²` | geometry | For each `N` there is a best height. Too small: blocks stick out. Too large: the shell has holes. |
| Physics accepts only quarter turns (0°, 90°, 180°, 270°) | `CoreAdapter.lean`, `FromCore.lean` | v1 uses only the 6 axis-aligned poses. "Any rotation" waits until physics supports it. |
| Physics checks the build after **every block**, with an exact LP | `CoreAdapter.lean`, `Engine.lean` | One check is slow, and it gets slower with more blocks. `maxChecks` is 50. We call it only on finished candidates. |
| The score is a pure function and much cheaper than physics, but it recounts the whole target on every call | `Engine.lean` (semantics) | Fine for ranking a few hundred plans. Too slow to try each single-block move. |

## 3. How big the search space is, and how we cut it

With 6 poses and positions on a 1-unit grid in a 60 × 60 × 60 box there are about 10⁶
places for each block, and `N` of them to choose. A full search is not possible. We cut it in
five ways:

1. **Grid.** Every block corner is on the integer grid, and every turn is a quarter turn. Then
   a block fills exactly 45 whole cells, and every test (overlap, rests on, inside a bubble) is
   integer arithmetic.
2. **Height first.** The height is one number. We search it in an outer loop (§4.1). All
   other choices happen at a fixed height.
3. **Layer by layer.** We build in courses from the ground up. Each course is a small 2D
   problem: which blocks go into this slice of the sculpture. Supports come from the course
   below, so most stability questions are local.
4. **Only the ends of the lines.** Because of the fill rule we only try positions near the
   edge of each bubble's slice (§4.3). We never fill the inside. This leaves tens of
   candidate positions per course, not thousands.
5. **Our own fast score, checked against the real one.** The planner keeps its own copy of
   the score formula and updates it when one block is added or removed (§4.2). It uses the
   same core definitions (`Bubble.contains`, `Pose.contains`). Tests compare it with
   `SemanticEngine.score` on many plans. The real engine scores every candidate we return.

The physics engine stays expensive. We avoid most failed calls by building only what a simple
local rule (§4.4) thinks will stand, and we spend the 50 real checks on finished candidates.

## 4. Pipeline

```
bubble model, N, human model
 │
 ├─ 4.1 Height search     estimate a good height h*, then try a few heights near it
 │   for each height h:
 │    ├─ 4.2 Cell table    place the bubbles at h; mark for each grid cell which bubbles hold it
 │    ├─ 4.3 Build         courses from the ground up; per course choose blocks by gain per block
 │    ├─ 4.4 Local rule    keep only blocks that the cheap stability rule accepts
 │    ├─ 4.5 Budget        a cut-off on gain per block decides how many of the N blocks we use
 │    └─ 4.6 Improve       a few rounds of remove / move / swap blocks (optional)
 ├─ 4.7 Order + check     bottom-up order, real physics check, repair on diagnostics
 └─ 4.8 Choose            real score for each plan; return the best few, from different heights or styles
```

### 4.1 Height search

A cheap estimate first: for each bubble, the number of blocks to cover both ends of every line
along its cheapest axis is about `2 × (area of its shadow along that axis) / 45`, times a
waste factor (start with 1.5, tune it on fixtures). Add this up over the bubbles. It grows like
`h²`, so we can solve "estimate = N" for `h*`.

Then we run the build (4.2–4.6) at a few heights around `h*`, for example `0.7 h*`,
`0.85 h*`, `h*`, `1.15 h*`, `1.3 h*`. Score as a function of height is usually one hill, so we
add one or two heights near the best (a coarse golden-section search). That is 5–8 builds.

The build at each height is independent of the others, so they can run in parallel later.

### 4.2 Cell table and fast score

At height `h`, place the bubbles once. For every grid cell in their bounding box, store which
bubbles hold its centre (a small bit mask; at most 32 bubbles). Also store the number of target
cells `|T|`. This is the only place where we use the ellipsoid formula. After this, everything
is lookups.

Fast score state:

- for each bubble and each grid line along x, y, z: the first and the last built cell
  (`filledSpans` in the scorer);
- the number of covered cells, and the number of built cells inside no bubble (`extra`).

Adding a block updates at most 45 cells and the spans they touch. The **gain** of a block is the
change in score if we add it. Gain per block is what the build step compares.

Test: on every fixture and many random grid plans, our score equals `SemanticEngine.score`
exactly (`#guard`, plus a `plausible` property if we add it).

### 4.3 Build: courses from the ground up

The best shape for this score is a **log cabin**: in one course, blocks lie along y at the left
and right edges of the slice, so the fill covers every x-line between them. In the next course
they lie along x at the front and back edges, which covers the y-lines. Two to four blocks per
course cover the whole slice, and the crossings at the corners carry each other.

For each course `z = 0, 1, 2, …`:

1. **Candidates.** For each bubble that cuts this course, its slice is an ellipse (or a union of
   ellipses). For each slice edge, generate block positions that lie on the edge, just inside
   it, or just outside it, for the poses that make sense here: flat along x, flat along y, and
   on edge or standing where the slice is thin (ears, walls). This gives about 20–200 positions
   per course.
2. **Filter.** Remove positions that overlap built blocks, or that the local rule (4.4) rejects.
3. **Choose.** Repeatedly take the candidate with the highest gain per block, until no
   candidate gains more than the cut-off `λ` (4.5). Update the gains of the remaining
   candidates after each choice. The candidate list is short, so this is fast.

Tall flat-sided parts can also use **motifs**: ready-made patterns with known block counts,
such as a palisade of standing blocks (3 courses high per block, good for walls and ears) or a
solid slab for the foot. A bubble's tags (`tower`, `wall`, …) suggest which motif to try first.
A motif is one more candidate, with its gain divided by its block count.

**Beam.** A greedy choice in course `z` can block a good course `z + 1`. We keep the best `B`
partial builds after each course (beam width `B` = 4 to start), ranked by score so far plus an
estimate for the courses still to come.

### 4.4 Local stability rule (cheap, not trusted)

A block may be placed if:

- it lies on the ground, or rests on blocks of the course below;
- its centre of mass lies inside the region spanned by its supports, with a margin for the
  placement error (`epsRel`);
- for blocks that stick out (corbelling outward on a widening bubble), the part that sticks out
  is at most a set amount per course, and the weight above it is checked again when the next
  course goes on.

This is the rule of `PhysicsMock`, made stricter. It accepts less than the real engine. That is
on purpose: most plans that pass it also pass physics, so we waste few of the 50 real checks.

**Parts that float** (a tail on the side, a head over the body): if a bubble has no support
under it in the target, we build a short column of blocks under it, outside the bubbles. Those
blocks cost score as `extra`. The search decides if the part is worth it. Its gain is weighed
against the column's cost like any other block.

### 4.5 Budget: how many of the N blocks to use

We do not split `N` over the bubbles by hand. One number `λ` controls it: a block goes in only
if it gains at least `λ` per block. A high `λ` gives few, very useful blocks. A low `λ` uses
more blocks. We search `λ` (binary search) so that the build uses at most `N` blocks.

This also gives the user a **choice of sizes** almost for free. The builds for several `λ`
values are the best plans we found for 60 %, 80 % and 100 % of the budget. If 120 blocks score
0.61 and 200 blocks score 0.64, the user may prefer the smaller plan.

### 4.6 Improve (optional, after the first working version)

A few rounds of local search on the finished build: remove a block, move a block by one cell,
turn it a quarter turn, swap a block for a motif. Use the fast score and the local rule. Keep a
change if the score goes up and the block count stays at most `N` (simulated annealing if
plain hill climbing gets stuck). Every change is local, so each step costs about 45 cell
updates.

### 4.7 Order, real physics check, repair

- **Order.** Courses bottom-up. Inside a course: blocks that rest only on the course below
  first, then blocks that rest on them. One block per step. Two-block steps only where a motif
  needs them (physics today checks after every block anyway).
- **Check.** `physics.check human N plan`.
- **Repair** from the diagnostics, then check again, at most 3 rounds per candidate:

  | Diagnostic | Repair |
  |---|---|
  | `unstable (step, block)` | remove that block and everything resting on it, then build those courses again with a stricter local rule |
  | `overlap (i, j)`, `clearance (i, j)` | move block `j` by one cell, or remove it |
  | `tooManyHands`, `emptyStep` | fix the steps (a planner bug) |
  | `tooManyBlocks` | raise `λ` (a planner bug) |
  | `unreachable (step)` | a warning, not a failure. Note it in the difficulty |

- **Limit.** All candidates together use at most `maxChecks` real checks. Candidates that pass
  the local rule but still fail after repair are dropped.

### 4.8 Choose the candidates

For each plan that passed physics: get the real `ScoreReport` from the semantic engine. Throw
away plans the report does not accept (a block `outside`, or a bubble `uncovered`). Sort by
score. If two scores are within 0.02, the easier plan wins (fewer blocks that stick out, fewer
reach warnings). Return up to `maxCandidates`, from **different heights or block counts**,
so the user chooses between real alternatives, not three copies of one plan.

## 5. Cost estimate

Per height, with grid cells as integers:

- cell table: about 60³ = 216,000 cells × up to 32 bubble tests, once;
- build: about 60 courses × about 200 candidates × 45 cells per gain update, times beam width
  4, about 10⁸ simple operations at most, usually much less;
- 5–8 heights, and a few `λ` values per height (the `λ` search reuses the cell table).

Physics: at most 50 calls in total, only on finished plans. This is the slow part, and the
local rule is what keeps it small.

If this is too slow in practice: smaller beam, fewer heights, fewer candidates per edge, or
parallel heights. Measure first with `#eval` timings on the bunny and the egg.

## 6. Changes the planner needs from other components

None are needed to start. To ask for later (shared contract, so the whole team reviews):

1. **Height instead of frame.** Semantics moves `score` to a height (`core/score-height`).
   We already build only at `Frame.ofHeight h`, so this is a rename for us.
2. **Physics: arbitrary turns.** Needed before we can use non-quarter turns (round towers).
3. **Physics: a cheaper check of only the last course.** This would let us use the real engine
   during the build, not only at the end. It is optional.
4. **PlanRequest: a time budget** next to `maxChecks`.

## 7. What we prove (small and optional)

The planner is not trusted, so these are only for reliability:

1. Every returned candidate uses at most `N` blocks.
2. Every returned candidate has `physics.ok = true` and `score.accepted = true` (we filter for
   this, so the proof is short).
3. Every step has between 1 and `hands` blocks.
4. Our fast score equals the scorer's formula for grid plans. This is a theorem about our own
   copy of the formula, not about `KaplaSemantics`, because we may not import it. The
   differential tests in §4.2 compare the two.

Each one gets a statement in `specs/KaplaSpecs/Planner.lean`, an `example` with all hypotheses
true, and one bad output it rejects.

## 8. Steps

| # | Deliverable | Done when |
|---|---|---|
| P1 | Grid blocks, cell table, fast score | equals the semantic engine's score on all fixtures and random plans |
| P2 | Height estimate and log-cabin build for one bubble, local rule, bottom-up order | egg and ball at N = 10, 50, 200 pass `physicsMock` and the real physics engine |
| P3 | Many bubbles, floating parts, motifs, beam | bunny at N = 50 and 200 passes physics and is accepted by the scorer |
| P4 | `λ` budget, choosing candidates, repair loop, `Planner` value | `kapla build` returns 3 different candidates for each fixture |
| P5 | Improvement step, theorems of §7, timing work | CI green; bunny@200 in under a minute (target to be agreed) |

## 9. Questions for the team

1. **The fill rule can be gamed.** A floor and a lid with nothing between them fill every
   vertical line, and two blocks far apart on one line fill the whole gap (APPROACH.md §4
   calls this a known limit). The planner will find these tricks because they score well.
   Do we accept that, or should the planner prefer closed shells (for example, require
   that the walls are closed on every course)?
2. **Rotations.** Is "quarter turns only" fine for v1? Round towers would look better with
   other turns, but physics refuses them today.
3. **Is 50 physics checks enough?** It depends on how long one check takes for 200 blocks.
   Physics (A) should measure that.
4. **Candidates for the user.** Different heights, different block counts, or different
   styles (log cabin or palisade)? We can do all three. Which ones does the web page show?

## 10. v1 as built

### Files

| File | What it does |
|---|---|
| `Grid.lean` | grid blocks (flat, along x or y), their 45 cells, `toPose` |
| `Table.lean` | the cell table at one height (§4.2): bubble bit mask per cell, target count, per column the top cell and each bubble's lowest cell |
| `FastScore.lean` | the fast score (§4.2) and `refCounts`, the same definition computed directly, for tests |
| `Support.lean` | the local stability rule (§4.4) |
| `Build.lean` | one build: courses from the ground up, greedy by value (§4.3) |
| `Search.lean` | heights and settings, physics check and repair, choosing candidates; `planner` |
| `Blueprint.lean` | a candidate as a blueprint file for `kapla view` |
| `Proofs.lean`, `Tests.lean` | §7 and tests with the mock engines |

### Where v1 differs from the plan

| Plan | v1 | Why |
|---|---|---|
| Candidates near the slice edges only (§4.3) | every flat block of the course with a cell in a bubble | simpler, and fast enough; only one candidate per pick is checked for stability |
| Edge and standing blocks, motifs, beam (§4.3) | flat blocks only; no motifs, no beam | not needed for the first results; later work |
| Stability: centre of mass over the supports (§4.4) | a load model: loads go straight down where they can, else are shared between two contacts by the lever rule; every block's load must be 1 inside its contacts along it and 1/2 inside its sides; the whole stack is checked after every block | the simple rule let structures through that the physics engine rejects, and rejected log cabins that it accepts |
| Budget by a value cut-off `λ` (§4.5) | a limit on blocks per course (an even share of `N`, one more, or none), plus the hard limit `N` | a high `λ` also drops the low-value bottom blocks that everything rests on, and the build collapses |
| Value = score gain | covered cells − ½ × outside cells, plus: outside cells under a higher bubble cell cost 0 or are worth +¼ (foundation); +45 for the first block in a bubble; +45 for one block per course under a bubble with no block yet (a pillar) | without these, a ball (which touches the ground at one point) is never started, and small parts such as ears are never reached, so the scorer would not accept the plan |
| Golden-section search over heights (§4.1) | a coarse sweep (½ to 2 × a first guess, 6 settings), then a fine sweep near the two best heights (18 settings); builds run in parallel | which setting is best changes from model to model and height to height |
| Improve step (§4.6) | not done | |
| Repair: rebuild with a stricter rule | remove the blamed block and everything that no longer stands; give up when a quarter of the blocks are gone | simple; the local rule makes physics failures rare |
| Score differential test against `SemanticEngine.score` | `#guard`s against `refCounts` in the library; against the real scorer by hand (below) | the planner may not import the scorer |

The stored value of a candidate can go stale: placing a block fills cells along lines that
cross other candidates' lines. So the chosen candidate's change is always worked out again
before it is applied, and the fast score stays exact.

### Measured (real physics engine and real scorer, compiled, 8 cores)

Run by hand from a scratch executable that imports `KaplaPlanner`, `KaplaPhysics` and
`KaplaSemantics` (the planner itself may not import them). The fast score equalled the real
score on every plan compared.

| Model | N | Best candidate | Score | Accepted | Physics | Time |
|---|---|---|---|---|---|---|
| egg | 40 | height 24, 40 blocks | 0.711 | yes | ok | 4.5 s |
| bunny | 40 | height 21, 35 blocks | 0.471 | yes | ok | 2.8 s |
| ball | 40 | height 16, 40 blocks | 0.702 | yes | ok | 6.0 s |

All 3 candidates of each model were accepted by the scorer and the physics engine.

### Known limits

- Parts with nothing under them in the target (a tail sticking out sideways) are reached only
  by the pillar bonus or by corbelling; there is no separate support search.
- Only flat blocks with quarter turns.
- The physics engine is the slow part for large plans (see §9 question 3).

## 11. v2 design: standing blocks, turns, branch-and-cut search (not built)

### 11.1 Goals

1. **Standing and on-edge blocks**, and blocks that rest on them.
2. **Turns about the vertical axis** of 30°, 45° and 60° (and their multiples), as well as
   quarter turns.
3. **A search with guarantees about its effort:** branch-and-cut first, then a heuristic
   improvement phase, with backtracking. A **time limit of 30 seconds** (and a maximum number
   of tries as a safety limit). When the time runs out, the search stops and returns the best
   plans found so far, ranked by likeness score.

### 11.2 What the engines accept today (measured)

Five small plans, checked with the real physics engine:

| Plan | Physics |
|---|---|
| one standing block on the ground | ok |
| a flat block resting across two flat blocks (control) | ok |
| a flat block resting across the tops of two **standing** blocks | **not ok** (`unstable 2`) |
| a flat block resting across two **on-edge** blocks | **not ok** (`unstable 2`) |
| one flat block on the ground, turned 36.87° (3-4-5 turn) | **not ok** (`unstable 0`) |
| a standing block in the middle of a flat block (also: across it, at its end) | **not ok** (`unstable 1`) |
| an on-edge block along a flat block, or across two crossing flat blocks | **not ok** |

Why:

- **Thin faces cannot carry anything.** Physics rule R1 lets each block land up to
  ε = 10/39 off its planned spot. A load point must stay inside both blocks for every such
  error, so it must be about 2ε from each edge of the contact (`Load.InsideOf`, `Robust.lean`).
  Across the contact that is 4ε ≈ 1.03 in total. The top face of a standing block (3 × 1) and
  of an on-edge block (15 × 1) is only 1 wide. So under the current rules **nothing can rest on
  a standing or on-edge block**. The engine's solvers also keep load points that far inside
  the contact under the *upper* block, so **an upright block cannot stand on another block
  either**: upright blocks are possible only on the ground, carrying nothing.
- **Turns.** Physics has a pose only for quarter turns (`CoreAdapter.lean`). Any other turn
  is not ok, even a single block on the ground.
- **Exact 30°, 45°, 60° do not exist in core.** `Rot` stores cos and sin as rational
  numbers, and cos 30°, cos 45° and sin 60° are irrational. The nearest
  rational turns with small numbers come from Pythagorean triples:

  | Wanted | Triple (cos, sin) | Actual | Error |
  |---|---|---|---|
  | 30° | 56/65, 33/65 | 30.51° | 0.51° |
  | 45° | 119/169, 120/169 | 45.24° | 0.24° |
  | 60° | 33/65, 56/65 | 59.49° | 0.51° |
  | 30° (closer) | 209/241, 120/241 | 29.86° | 0.14° |
  | 45° (closer) | 697/985, 696/985 | 44.96° | 0.04° |

  The error is well below what a human can see or place (ε = 10/39 is 2 mm). Larger numbers
  make the physics LP slower, so the small triples are the default.
- The scorer already handles turned blocks: a block's cells are the cells whose centre is inside
  it (`poseCells`, by `Pose.contains`). A turned block has about 45 cells, not exactly 45. The
  fast score works for any list of cells, so it needs no change.

So the planner can add these features now, but plans that use them only pass physics after
physics changes (§11.9). The planner **finds out at run time** what physics accepts (§11.8), so
it does not need a new release when physics changes.

### 11.3 Poses

A pose is (upright, turn, position):

- **Upright:** flat (15 × 3 × 1), on edge (15 × 1 × 3), standing (3 × 1 × 15, or 1 × 3 × 15).
- **Turn:** 0°, 30°, 45°, 60°, 90°, 120°, 135°, 150° (a block turned by 180° is the same
  block). Quarter turns are exact; the others use the triples above.
- **Position:** block centres on a half-unit grid in x and y. Bottoms are on whole units
  (every course is 1 high).

The planner keeps blocks in **courses** as in v1. A flat block fills one course. An on-edge
block fills 3 courses. A standing block fills 15 courses and is placed in its lowest course.
Its cells in higher courses are reserved, so later courses build around it.

**Where each pose is useful** (this is how candidates are generated; we never try all poses
everywhere):

| Pose | Use |
|---|---|
| flat, quarter turn | the log cabin of v1: walls of large, round slices |
| flat, 30°/45°/60° | round slices: a block that follows the edge of an ellipse wastes fewer cells than an axis-aligned one. At each point on the slice edge, try the turn closest to the edge direction, and its two neighbours |
| on edge | thin walls and rims, 3 courses at once |
| standing | thin, tall parts (ears, a neck) and palisade walls, where nothing rests on top. One standing block covers 15 courses of one column, where v1 needs 15 flat blocks. Pillars under parts that would float must carry, so they stay flat blocks until standing blocks may carry (§11.8) |

### 11.4 Contacts and the load rule for all poses

v1's load rule works along one block at a time: each contact is an interval [lo, hi] along
the block, and loads go straight down or are shared between two contacts by the lever rule.
We keep that rule and make it work for any pose:

- **Contact shape.** Where block A rests on block B, the contact is the overlap of A's bottom
  face and B's top face. Both are rectangles, possibly turned, so the overlap is a convex
  polygon. We compute it exactly in rational numbers (cut one rectangle by the four sides of
  the other).
- **Along the block.** Express the contact polygon in the upper block's own axes. Its extent
  along the block's long axis is [lo, hi]. Its extent across the block must leave a margin on
  both sides.
- **Margin.** A contact is usable only if it is at least `minPatch` wide in both directions.
  `minPatch` comes from the probe in §11.8: about 4ε ≈ 1.03 under today's physics, so 1-wide
  faces never carry. If physics changes so that thin faces can carry, `minPatch` drops and
  standing and on-edge blocks become usable as supports with no other change.
- **Standing block as support.** Its whole load goes straight down through its foot. It
  carries a load only if its top contact and its foot both pass the margin test.

### 11.5 The search

#### What is searched

For each height (as in v1), we search over **builds made course by course**. A node in the
search tree is a partial build: courses 0 to z are fixed, and courses above z are empty. A
child of a node adds one more course, z + 1.

A child is one **course plan**: a set of blocks for course z + 1 (flat blocks in that course,
and on-edge and standing blocks whose lowest course is z + 1). Course plans come from a small
generator: v1's greedy step, run with different choices, for example:

- log-cabin direction (along x, along y, or both);
- how many blocks this course may use (the even share of what is left, one more, one less);
- with or without turned blocks;
- with or without a standing palisade or pillar.

Duplicate course plans are removed. Each node has at most `K` children (K = 4 to start), in
order of value. Unlike v1, the choice can change from course to course: v1 fixes one setting
for the whole build.

#### Branch and bound

The search goes depth first: it takes the best child first and goes up again (backtracks)
when a branch is finished or cut. It keeps the **incumbent**: the best complete build found
so far that physics accepted.

For each node it computes an **upper bound**: a score that no build below this node can beat.

```
bound = (covered now + cells that can still be covered) / (target cells + outside cells now)
```

"Cells that can still be covered" are the uncovered target cells that some later block can
still cover:

- every target cell above course z;
- a target cell at or below course z only if it is on a vertical line of a bubble that has a
  built cell below it (a later block above can close that line). No other line through it can
  change any more.

This number is also limited by the blocks left: one block can cover at most the target cells
on the lines through its own cells. We precompute the largest such number over all poses at
this height and multiply it by the blocks left.

Outside cells only ever go up, so the denominator is correct. If `bound ≤ incumbent score`,
the node is cut: no build below it can win.

The bound is loose (the fill rule lets one block cover a long line), so on real models it cuts
less than in textbook problems. That is why the tries limit and the heuristic phase matter.

#### Cuts

A cut removes a node or a child before it is explored. There are two kinds.

**Exact cuts** (they never remove a build that could be the best):

| Cut | Rule |
|---|---|
| bound | `bound ≤ incumbent score` (above) |
| budget | blocks used + blocks still needed > N. "Still needed": one block for each bubble with no block yet, plus a pillar under it if nothing can carry it (one flat block per course of gap; one standing block per 15 courses once standing blocks may carry) |
| dead bubble | a bubble with no block yet whose top is below course z can never get one, so the scorer would not accept the build |
| overlap | a block shares cells with a block already built |
| symmetry | if the model is its own mirror image (left-right), the first course that differs between a plan and its mirror image is explored on one side only |

**Learned cuts** (they may remove good builds; they keep the search away from builds that
physics refused):

| Cut | Rule |
|---|---|
| local rule | the load rule of §11.4 (cautious: it accepts less than physics does) |
| no-good | after physics fails at block b (§11.6): the pair (supports under b, pose of b) is stored and never tried again |
| same frontier | two nodes at the same course with the same top two courses and the same number of blocks: keep only the one with the higher score so far |

#### Physics in the loop and backtracking

Physics is called only on complete builds whose fast score beats the incumbent. Each call
costs one try of the physics budget (`maxChecks`, 50 by default).

Physics checks after every block, so a failure names the **first** block b that is
unstable; everything placed before b stands. The search then:

1. stores a no-good for b;
2. **jumps back** to the course of b (not just one level up). Everything above that course was
   built on a part that fails, so trying other choices up there is wasted effort;
3. tries the next child at that course.

This replaces v1's repair step ("remove blamed blocks and what rests on them").

#### Time limit, tries and stopping

The main limit is **time: 30 seconds** from the call to `planner.plan` until it returns
(decided). `Planner.plan` runs in `IO`, so the search reads the clock (`IO.monoMsNow`).

A **try** is one child built and evaluated (its blocks placed, the local rule checked, the
fast score and the bound worked out). One try is cheap: tens of blocks times about 45 cells.
The search works in rounds of a few hundred tries and looks at the clock between rounds.

| Limit | Default | When reached |
|---|---|---|
| time | 30 s (`timeLimitMs` = 30,000) | stop and return the incumbents |
| `maxTries` | a large safety limit (10⁷); not expected to be reached in 30 s | stop |
| `maxChecks` | from `PlanRequest` (50) | stop calling physics; finish without new incumbents |
| no open nodes | | stop: the incumbent is the best build that the course-plan generator can make |

At the stop, the search returns the incumbents (§11.7). Every result has passed physics and
uses at most N blocks, as in v1.

**The time is split** as follows:

| Share | Phase |
|---|---|
| first ~3 s | the probes (§11.8), and the v1 build at each height with its physics check, so there is a result early |
| up to ~60 % | tree search (§11.5) |
| the rest, up to 2 s before the limit | heuristic phase (§11.6) |
| last 2 s | real score of the incumbents, choose and return |

**Physics checks under a time limit.** One physics check cannot be stopped from outside: it
is a pure function, and failing checks of large plans took 130 s and 971 s (§10). So every
check runs in its own task (`Task.spawn`), and the search waits for it only until the time
is up. A check that is not finished by then counts as failed, and its plan is not returned. The
task may keep running in the background until the process ends; that is wasted CPU, but the
answer is on time. Two rules keep this from losing all results:

- the v1 build at each height is checked first, so a plan that passed is usually there after
  a few seconds;
- a new plan is sent to physics only if it beats the incumbent, and at most 8 checks run at
  the same time.

The tries are counted with a fuel number that goes down by one per try, so every search
function ends by structural recursion (no `partial def`), and "at most `maxTries` tries" can
be proved. The time limit is extra: it only makes the search stop earlier. The same input
can give different results on a faster or slower machine; with the time limit off (tests),
the search is deterministic.

#### Order inside the tree

Pure depth first spends all tries deep in the first branch. We use **limited discrepancy**
order instead: first the path that always takes the best child (this is the v1 build, and
gives the first incumbent quickly), then all paths that take a worse child once, then twice,
and so on. Bad early choices are corrected first, which matters most because everything above
depends on them.

### 11.6 Heuristic phase: improve the incumbents

The tree search gets about 60 % of the time. The rest goes to improving the best incumbents
with **large-neighbourhood search**:

1. Choose a course z (more often where the build covers its slice badly).
2. Remove every block at or above course z.
3. Search again from course z with the tree search of §11.5, with a small share of the tries,
   with the incumbent's score as the bar to beat.
4. Keep the new build if physics accepts it and it scores higher.

Then small moves on single blocks, kept if the fast score goes up and the local rule still
holds: remove a block that carries nothing, move a block by half a unit, change its turn to
the next one, change flat to on edge. Physics checks the result only when it beats the
incumbent.

A fixed random seed drives the choices, so the same input always gives the same output.

### 11.7 Heights and the result

Heights: as in v1, a coarse sweep and then a fine sweep. But the tries are shared by
**successive halving**: every height starts with a small share of the time; after each round
the worse half of the heights is dropped and the rest get twice as much time. Heights run in parallel.

Result: the best incumbents across all heights, ranked by the real score (accepted plans
first), at most one per height, as in v1 (`finalize`). If the tries run out before any build
passes physics, the result is empty, as in v1. With the v1 build checked first (§11.5), this
happens only if every v1 build fails physics or its check takes longer than the time limit.

### 11.8 Probing what physics accepts

At start, the planner sends three tiny plans to physics (3 of the 50 checks, each a few
milliseconds):

| Probe | If ok |
|---|---|
| a flat block on two standing blocks | standing and on-edge blocks may carry (`minPatch` 1) |
| one flat block on the ground with a 30° turn | turns of 30° and 60° are used |
| the same with a 45° turn | turns of 45° are used |

Otherwise those features stay off: standing and on-edge blocks are only placed where nothing
rests on them, and only quarter turns are used. The planner does not import physics, so this
is the only way to know.

### 11.9 What other components must change

| Owner | Change | Needed for |
|---|---|---|
| A (physics) | contacts between turned blocks (the contact is a convex polygon, not a rectangle) | any turn other than a quarter turn |
| A (physics) | a placement-error model where thin faces can carry. For example: a block lands within ε of the block it is placed on, not of its planned spot. Then a load point needs ε, not 2ε, from each edge, and a 1-wide face works. **Decided: not now.** So in v2 nothing rests on standing or on-edge blocks | anything resting on standing or on-edge blocks |
| A (physics) | a check with a time limit, or a check of only the new course | optional. The planner already waits at most until its own time limit (§11.5); a faster check means more checks fit in 30 s |
| team | 30°/45°/60° means the triples of §11.2. **Decided: yes** | turns |
| none (core) | `Rot.ofTriple` already exists | |

The planner needs no change in core. `timeLimitMs` and `maxTries` go into the planner's own
config with defaults; if the team wants them in `PlanRequest`, that is a later core change.

### 11.10 What we prove

As in v1 (§7): every result uses at most N blocks and passed physics. New:

- the search makes at most `maxTries` tries (fuel);
- the result is the best of the incumbents it found (sorted by score; the incumbent only ever
  gets better);
- the contact polygon of two blocks is inside both blocks' faces (a test with `#guard` on
  turned examples, a theorem if cheap).

We do not claim that the result is the best possible build. The cuts marked "learned" and the
limit of K children per node rule that out.

### 11.11 Steps

| # | Deliverable | Done when |
|---|---|---|
| B1 | poses with upright and turn; cells by `Pose.contains`; contact polygons | fast score equals the real scorer on turned and standing blocks |
| B2 | load rule for every pose; `minPatch`; the probes | the five plans of §11.2 get the same answer from the local rule as from physics |
| B3 | course-plan generator; tree search with bound, exact cuts, fuel, limited discrepancy order | at N = 40 the score is at least v1's on egg, ball and bunny |
| B4 | physics in the loop: no-goods, jump back | at N = 100 every model returns a plan that passes physics |
| B5 | heuristic phase; successive halving over heights; 30 s time limit | higher scores than B4 within 30 s; every call returns within 31 s |
| B6 | theorems of §11.10; README and §10 updated | CI green |

B1–B5 work with quarter turns and with standing blocks that carry nothing. They give better
plans today. Turned blocks start to pass physics as soon as physics supports them; blocks
resting on standing blocks only if physics later changes its error model (§11.9). The probes
switch both on with no change in the planner.

### 11.12 Decisions (2026-11-01)

1. The triples of §11.2 (errors of 0.24° to 0.51°) count as 30°, 45° and 60°.
2. Physics does not change its placement-error model for now. So in v2 standing and on-edge
   blocks carry nothing. The probe of §11.8 stays, so carrying switches on if this changes.
3. The search stops after **30 seconds** and returns the best plans found (§11.5).

4. Turns other than quarter turns are **stalled**. v2 uses only quarter turns; §11.3's turned
   poses and contact polygons are not built.

### 11.13 What was built (and where it differs from the design above)

| Design | Built |
|---|---|
| poses with turns, contact polygons (§11.3, §11.4) | quarter turns only (turns stalled). On-edge and standing blocks (`Grid.lean`), with `UprightRules` (`Support.lean`): by default upright blocks only on the ground, carrying nothing |
| three probes (§11.8) | two: an upright block on a flat one (`onFlat`), a flat block on two standing ones (`carry`). Both are not ok today |
| tree search, bound, cuts, no-goods, jump back, limited discrepancy order (§11.5) | as designed (`Tree.lean`). Children: the default setting, the other flat direction, both directions, one more block in the course, no limit, upright blocks (where allowed). The limit per course is the blocks left shared over the courses left. At most 3 children, 200 waiting nodes per height |
| exact symmetry cut | the model must be its own mirror image across `y = 0`, bubble by bubble |
| heuristic phase (§11.6) | restarts from the incumbent above a random course, and removing single blocks that carry nothing |
| heights (§11.7) | v1's coarse sweep first (36 builds), then tree searches at 8 heights (the two best, ±8 % and ±15 % around each, then the rest); halved at ⅓ and ⅔ of the time |
| time limit (§11.5) | `PlannerConfig.timeLimitMs` = 30,000, 2 s reserve; checks run in their own tasks, at most 4 at a time; a check not done at the end is not waited for |
| theorems (§11.10) | `candidatesOf_sound`, `candidatesOf_length` (every result within `N` blocks and passed physics; at most `maxCandidates`). The search runs in `IO`, so "at most `maxTries`" is a loop limit, not a theorem |

Measured, N = 40, real physics engine and scorer, 30 s, 8 cores. Every plan passed physics and
was accepted by the scorer:

| Model | v1 | v2 |
|---|---|---|
| egg | 0.711 (height 24, 40 blocks) | 0.735 (height 24, 39 blocks) |
| bunny | 0.471 (height 21, 35 blocks) | 0.546 (height 24, 32 blocks) |
| ball | 0.702 (height 16, 40 blocks) | 0.752 (height 17, 40 blocks) |

**Speed** (profiled with macOS `sample` and timed piece by piece). The first version spent
almost all its time building child courses, and kept only about 2 cores busy. Changes:

| Change | Effect |
|---|---|
| a node's candidates and their score changes are worked out once (`prepare`) and shared by its child settings, which build in parallel | one node: 23 ms → 2 ms |
| `deltaBlock`: the score change of a block by its positions in the table's arrays, no lists or hash map of groups (tested equal to `delta`) | 13 µs → 6 µs per block |
| values in whole numbers (`IntValue`), kept in an array and updated only when they change; bit count without a loop | the fraction arithmetic (GMP big numbers), ~38 % of the time before, is gone |
| support test before the bubble test when listing candidates; the pillar count only while a bubble has no block | `prepare` 2.2 ms → 1.4 ms |
| the halving keeps at least 4 searches | about 5 of 8 cores busy, was about 2 |

Tries in 30 s went up 7× to 13× (egg 7,635 → 99,694). Now about 70 % of the time is working out
score changes again after a block is placed (candidates on the same grid lines), and 14 % the
local rule.

**A check cannot be stopped.** The planner returns on time, but a physics check still running
at the end keeps the program alive until it is done (a failing check took up to 22 s more at
N = 40). The planner starts no check that the longest check so far says would end after the
limit, but the first slow check cannot be foreseen. Fixes outside the planner: the `kapla`
CLI ends the program once it has the answer (`IO.Process.exit`, owner D), or physics gets a
check with a time limit (owner A, §11.9).

No search used an upright block (on the ground they were never worth it), and no physics check
failed, so the no-good and jump-back path has run only in tests. Not yet measured: N = 100,
where failing checks are slow.
