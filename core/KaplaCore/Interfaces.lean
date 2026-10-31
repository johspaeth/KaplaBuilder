import KaplaCore.Types

/-!
# KaplaCore.Interfaces — engine interfaces

The planner never imports the physics or semantics packages; it receives them as values
of these structures. During development the mocks in `KaplaCore.Mocks` are plugged in.
-/

namespace Kapla

/-- A (possibly verified) physics checker. `check H N plan` must never report `ok` for a
plan that is not `Valid H N plan` when `verified = true` is claimed in the report. -/
structure PhysicsEngine where
  name : String
  check : HumanModel → Nat → BuildPlan → PhysicsReport

structure SemanticEngine where
  name : String
  interpret : Request → IO TargetSpec
  /-- Score the blocks against the target (the target's shape is in mm). -/
  score : TargetSpec → List Pose → ScoreReport
  /-- Proven ceiling for `N` blocks. -/
  bound : TargetSpec → Nat → Bound

structure Planner where
  name : String
  plan : PlanRequest → PhysicsEngine → SemanticEngine → IO (List Candidate)

structure Renderer where
  name : String
  render : RenderInput → String

end Kapla
