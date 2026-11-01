# KaplaCore

Owner: all (stewarded by D). Scope: see [docs/WORKSPLIT.md](../docs/WORKSPLIT.md).

- Build: `lake build KaplaCore`
- Files: `KaplaCore.lean` (root, imports the rest) and `KaplaCore/*.lean`.
- May import: Lean core and Batteries only.
- Rules and CI: see the [README](../README.md).

## Contents (v0.1 draft)

| File | What |
|---|---|
| `Basic.lean` | `Q` (= `Rat`), `Q3`, `Box` |
| `Block.lean` | block size, `Upright`, `Rot` (exact turn about the vertical axis), `Pose`, corners, bounding box |
| `Plan.lean` | `Grip`, `Approach`, `Step`, `BuildPlan`, `HumanModel` and its default |
| `Target.lean` | `Shape` (first version, owned by B), `PartTag` (kind + box), `TargetSpec`, `Request` |
| `Report.lean` | `Diagnostic`, `PhysicsReport`, `ScoreReport`, `Bound`, `Verdict`, `Difficulty` |
| `Engine.lean` | `PhysicsEngine`, `SemanticEngine`, `Planner`, `PlanRequest`, `Candidate` |
| `Mocks.lean` | `physicsMock` (load over support, every step), `semanticMock` (volume IoU): simple, unverified stand-ins for development |

Not yet: JSON codecs, tilted poses.
