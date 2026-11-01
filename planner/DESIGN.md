# KaplaPlanner: Design

Owner: C. Status: **draft for review**.
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
