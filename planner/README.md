# KaplaPlanner

Owner: C. Scope: see [docs/WORKSPLIT.md](../docs/WORKSPLIT.md).

- Build: `lake build KaplaPlanner`
- Files: `KaplaPlanner.lean` (root, imports the rest) and `KaplaPlanner/*.lean`.
- May import: `KaplaCore` only.
- Rules and CI: see the [README](../README.md).

## Demos

`KaplaPlanner/Demos.lean` holds the problems the planner is developed against: the ball,
bunny, egg and foot models, each with 10, 40 and 100 blocks (`demos`). Where PR #31's planner
was run on a problem, its result (blocks used, height) is kept as a bar to reach.

- `checkDemo req physics semantic candidates` lists what is wrong with an answer: no
  candidate, too many candidates, too many blocks, a plan physics does not accept, a plan the
  scorer does not accept, or a stored physics report that the engine does not confirm.
- `runDemos planner physics semantic` runs a planner on every demo and prints one line each.
