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
| `Bubble.lean` | `Bubble`, `BubbleModel`, `contains`, `wellFormed`, `place` (takes a height), the egg example |
| `Block.lean` | block size, `Upright`, `Rot` (exact turn about the vertical axis), `Pose`, corners, bounding box |
| `Plan.lean` | `Grip`, `Approach`, `Step`, `BuildPlan`, `HumanModel` and its default |
| `Target.lean` | `PartTag` (kind + box), `TargetSpec`, `TargetSpec.ofBubbles`, `Request` |
| `Report.lean` | `Diagnostic`, `PhysicsReport`, `ScoreReport` with `accepted`, `Verdict`, `Difficulty` |
| `Engine.lean` | `PhysicsEngine`, `SemanticEngine`, `Planner`, `PlanRequest`, `Candidate` |
| `Mocks.lean` | `physicsMock` (load over support, every step), `semanticMock` (cell count): simple, unverified stand-ins for development |

Not yet: JSON codecs, tilted poses.
