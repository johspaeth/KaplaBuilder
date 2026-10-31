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
| `Grid.lean` | blocks on a 7.8 mm grid; overlap, rests-on; `toPose` (checked equal to the grid box) |
| `Motif.lean`, `Motifs/` | motifs with a proven block count: single block, log-cabin tower, solid column |
| `Sequencer.lean` | bottom-up build order, one block per step, grip and approach |
| `PreCheck.lean` | block count, no overlap, supports first, before calling physics |
| `Search.lean` | proposals, physics check + repair (keep the stable prefix), score, rank |
| `Tests.lean` | end-to-end on `physicsMock` / `semanticMock` |

Proven (standard axioms only):
- `planPure_sound`: every returned candidate passed the physics check and uses at most N blocks.
- `sequence_perm`: the steps contain exactly the input blocks, none lost or doubled.
- `sequence_step_size`: every step places exactly one block.
- `towerLayers_length`, `columnLayers_length`: motif block counts are exact.

Not yet (P2+): several regions per target, walls, budget split, smarter repair (reorder, two-hand
steps), roofs.
