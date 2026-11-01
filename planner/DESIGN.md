# KaplaPlanner: Design

Owner: C. Context: [docs/DESIGN.md](../docs/DESIGN.md), [docs/WORKSPLIT.md](../docs/WORKSPLIT.md),
[semantics/APPROACH.md](../semantics/APPROACH.md) §3–4 (the score).

## 1. The task

Input: a bubble model (height 1), a block budget `N`, the human model, the physics engine and
the scorer.

Output: up to `maxCandidates` build plans, best first. Each plan:

- uses at most `N` blocks;
- was accepted by the physics engine (`PhysicsEngine.check … = ok`);
- is ranked by the scorer's likeness score.

The planner chooses the height of the finished model and the blocks. It is not trusted: it does
not have to find the best plan, and physics and the scorer check every plan it returns.

## 2. Facts that shape the search

- **Score = covered cells / (target cells + cells outside the bubbles).** A cell counts as
  covered when it lies between two built cells of the same bubble on one x, y or z line. So a
  hollow shell scores as well as a solid fill: the planner only builds the two ends of each
  line. Blocks outside the bubbles lower the score.
- **Grid.** Every block corner is on the integer grid and every turn is a quarter turn. Then a
  block fills exactly 45 cells, and every test (overlap, rests on, inside a bubble) is integer
  arithmetic.
- **Upright blocks carry nothing.** Physics lets each block land up to ε = 10/39 off its spot,
  so a load point must stay about 0.51 inside every contact edge. The top face of a standing
  or on-edge block is only 1 wide. So nothing can rest on an upright block, and an upright
  block cannot stand on another block. The planner uses upright blocks only on the ground. At
  start it sends 2 tiny plans to physics; if physics ever accepts them, this switches on by
  itself (`UprightRules`).
- **Quarter turns only.** Physics rejects every other turn today.
- **Above 40 blocks, physics uses only its fast solver**, which settles one block at a time
  from the top. The planner then builds in *strict mode*: no load on an overhang.
- **A physics check is slow and cannot be stopped.** It runs in its own task; the planner does
  not wait for it past the time limit.

## 3. The algorithm

```
plan(model, N, timeLimit = 30 s):
  rules  ← 2 probe plans to physics          -- may upright blocks stand on / carry blocks?
  strict ← N > 40

  -- 1. Sweep (at most 25 % of the time, in parallel)
  h0 ← first guess of the height, from N and the model's width
  for h ∈ {½, ¾, 1, 1¼, 1½, 2}·h0, for each of 6 settings:  greedyBuild(h, setting)
  builds not done in time are left out

  -- 2. Tree searches at up to 8 heights
  heights: the 2 best of the sweep, ±8 % and ±15 % around each, then the other sweep heights
  each search starts from its height's best setting, and queues its best greedy build for physics
  until (time limit − reserve):
    collect finished physics checks; report each to its search
    start new checks: at most 4 at once, at most maxChecks in all, only plans that beat their
      search's best, and only if the longest check so far would still end in time
    at ⅓ and ⅔ of the time: stop the worse half of the searches (keep at least 4)
    after 60 % of the time: heuristic phase on
    run every live search for a few steps, in parallel

  -- 3. Result
  plans that passed physics: the best of each height first, then the others
  score the best maxCandidates with the scorer; return them, accepted plans first, by score

search step (one search, at one height):
  if heuristic phase (every 16 steps, or when no node waits):
    block removal: try the best plan without each block that carries nothing
    LNS: keep the best plan's blocks below a random course; queue that as a new node
  node ← newest node with the fewest discrepancies          -- limited discrepancy search
  if node is finished (top reached, or N blocks used):
    queue it for physics if it beats the search's best
  elif a pruning rule (§5) applies: drop it
  else:
    cands ← blocks starting in this course that rest on the course below (or the ground),
            touch a bubble, and are not a no-good
    children ← greedyCourse(cands, s) for each setting s:
      default, other direction, both directions, +1 block in the course, no limit,
      upright blocks (where allowed)
    drop equal children (and mirror images at course 0)
    keep the default child and the 2 best others; queue them

on a physics failure at block b:
  store "b on these supports" as a no-good
  drop the queued nodes that share blocks 0..b             -- backjumping
  queue blocks 0..b−1 as a smaller plan for physics

greedyCourse(cands, s):
  repeat until the course limit or N blocks:
    pick the candidate with the highest value (at least 1)
    work out its value again (blocks placed since may have changed it)
    place it if the local rule (§4) accepts it

value(block) = newly covered cells
             − ½ per new cell outside the bubbles (a share of that if a bubble cell is above it)
             + 45 per bubble that gets its first block
             + 45 for the first block in a course under a bubble with no block yet (a pillar)
```

The course limit: the blocks left shared evenly over the courses left, rounded up.

Values are kept in whole numbers, and each block's change to the score is worked out from the
cell table's arrays (`deltaBlock`). A node's candidates are worked out once (`prepare`) and
shared by all its child settings, which build in parallel.

## 4. The local stability rule

A cheap load model, stricter than physics, so few physics checks fail (`Support.lean`):

- A block rests on a block below only where the contact covers its full width and is at
  least 2 cells long.
- Every block weighs 1 at its middle. From the top down, each block passes its load to its
  contacts: straight down if the load point is over one contact, else shared between the two
  nearest contacts by the lever rule, 3/5 inside their edges.
- A block stands when its load point is at least 1 inside the span of its contacts along the
  block, and 3/5 inside its long sides.
- A block whose contacts span fewer than 6 cells carries loads only right above its contacts.
  In strict mode every block does.
- Loads are worked out on a fine grid (1/1024 for positions, 1/4096 for forces), so the
  numbers stay short.

## 5. Pruning rules

Safe (never drop a node that could lead to a better plan):

| Rule | Drops a node when |
|---|---|
| bound | `bound ≤` best score so far. `bound` = (covered now + cells that can still be covered) / (target + outside now). Cells that can still be covered: every target cell at or above this course, and below it only cells on a vertical line of a bubble above that bubble's highest built cell there |
| dead bubble | a bubble with no block yet ends below this course |

Heuristic (may drop good plans):

| Rule | Drops |
|---|---|
| budget | nodes with fewer blocks left than bubbles with no block (one block can reach two bubbles) |
| symmetry | a child at course 0 that is the mirror image of another, when the model is its own mirror image across `y = 0` |
| dominance | a node with the same course, block count, reached bubbles and top two courses as one with a higher score |
| no-good | a placement that physics refused before |
| local rule | blocks the rule of §4 rejects |
| limits | children beyond 3 per node; waiting nodes beyond 200 per search |

## 6. Settings (`PlannerConfig`)

| Setting | Default |
|---|---|
| `timeLimitMs` | 30,000 |
| `reserveMs` (for scoring at the end) | 2,000, at most a fifth of the limit |
| `sweepShare` | 25 % |
| `treeShare` (before the heuristic phase) | 60 % |
| `heights` (tree searches) | 8 |
| `parallelChecks` | 4 |
| `maxTries` (safety limit) | 10⁷ |

## 7. Proved, tested, trusted

- **Proved** (`Proofs.lean`): `candidatesOf_sound`: every returned plan uses at most `N` blocks
  and physics said ok. `candidatesOf_length`: at most `maxCandidates` plans. `toPlan_hands`:
  one block per step.
- **Tested:** the fast score equals `refCounts`, a direct recount, and `deltaBlock` equals the
  cell-list version; the local rule and the tree search with the mock engines. The fast score
  was compared by hand with the real scorer (the planner may not import it).
- **Assumed:** physics runs its global solver for at most 40 blocks (`physicsGlobalLimit`, a copy
  of `globalLimit` in `physics/KaplaPhysics/Engine.lean`). If that changes, update it here.

## 8. Limits and open questions

- **The fill rule can be gamed.** A floor and a lid with nothing between them fill every
  vertical line. The planner finds such plans because they score well. Should it prefer closed
  shells?
- **Quarter turns only**, until physics accepts other turns.
- **A running check keeps the program alive.** The planner returns on time, but a check that is
  still running keeps the process busy until it ends. Fix outside the planner: the `kapla` CLI
  exits once it has the answer, or physics gets a check with a time limit.
- The `kapla` CLI does not call the planner yet (`app/`, owner D).
- The theorems are not yet in `specs/` or `comparator/` (a shared change).

## 9. Files

| File | What it does |
|---|---|
| `Grid.lean` | grid blocks (flat, on edge, standing), their 45 cells, `toPose` |
| `Table.lean` | the cell table at one height: which bubbles hold each cell, target count, column tops |
| `FastScore.lean` | the fast score, updated one block at a time; `refCounts` for tests |
| `Support.lean` | the local stability rule |
| `Build.lean` | candidates of a course and the greedy course builder |
| `Tree.lean` | the tree search: bound, pruning, no-goods, backjumping, LNS, block removal |
| `Search.lean` | the sweep, the time-limited loop over the searches, physics checks, the result; `planner` |
| `Blueprint.lean` | a candidate as a blueprint file for `kapla view` |
| `Proofs.lean`, `Tests.lean` | §7 |
