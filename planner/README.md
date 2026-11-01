# KaplaPlanner

Owner: C. Scope: see [docs/WORKSPLIT.md](../docs/WORKSPLIT.md).

- Build: `lake build KaplaPlanner`
- Files: `KaplaPlanner.lean` (root, imports the rest) and `KaplaPlanner/*.lean`.
- May import: `KaplaCore` only.
- Design: [DESIGN.md](DESIGN.md).
- Rules and CI: see the [README](../README.md).

## Status: P1 (on mocks)

Entry point: `KaplaPlanner.planner : KaplaCore.Planner` (pure core: `planPure`).

| File | What |
|---|---|
| `Grid.lean` | blocks on a unit grid; overlap, rests-on; `toPose` (checked equal to the grid box) |
| `Motif.lean`, `Motifs/` | motifs with a proven block count: single block, log-cabin tower, solid column |
| `Sequencer.lean` | bottom-up build order, one block per step, grip and approach |
| `PreCheck.lean` | block count, no overlap, supports first, before calling physics |
| `Search.lean` | proposals, physics check + repair (keep the stable prefix), score, rank |
| `Tests.lean` | end-to-end on `physicsMock` / `semanticMock` |
| `Ellipsoid.lean`, `Inside.lean`, `InsideProof.lean` | `insideBubbles`: the design is strictly inside the target's bubbles (proven) |
| `Bubble.lean` | scale/move bubbles, safe bounding box, allowed and surface cells |
| `Fixtures.lean` | bubble test targets: sphere, snowman, spire, duck, gate |
| `Eyeball.lean` | the eyeball rule: each block lines up (ends, centre, quarters) with a block it rests on |
| `Stability.lean` | cheap grid stability estimate used inside the search |
| `Design.lean` | P3 minimal filler: layer by layer, greedy surface coverage, scale and ground height search |
| `Export.lean` | blueprint JSON for the web viewer |
| `Demo.lean` | `kapla plan`: designs the bubble test targets, checks them with the physics engine the app passes in, writes blueprints |

## Demo

```sh
lake build kapla && .lake/build/bin/kapla plan 200 --no-clearance      # all bubble targets
lake exe kapla view out/planner-demo/duck.json --out out/planner-demo/duck --no-clearance
open out/planner-demo/duck/index.html
```
The demo lives in `Demo.lean`; the app runs it with the verified physics engine, both inside
the search (every block tried) and on the finished plan (every step). `--no-clearance` lets
blocks touch side by side; without it the engine asks for a gap of 2 × 2 mm between blocks
at the same height, and the search keeps only blocks that leave it.

Proven (standard axioms only):
- `planPure_sound` (main theorem, in `specs/` + `comparator/planner.json`): every returned candidate passed the physics check and uses at most N blocks.
- `sequence_perm` (main theorem, in `specs/` + `comparator/planner.json`): the steps contain exactly the input blocks, none lost or doubled.
- `sequence_step_size`: every step places exactly one block.
- `insideBubbles_sound` (main theorem, in `specs/` + `comparator/planner.json`): if the check accepts, every point of every block is inside some bubble.
- `towerLayers_length`, `columnLayers_length`: motif block counts are exact.

Not yet (P2+): several regions per target, walls, budget split, smarter repair (reorder, two-hand
steps), roofs.
