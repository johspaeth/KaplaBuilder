import KaplaCore.Report
import KaplaCore.Target

/-! # Engine interfaces

Each component implements one of these as a plain value. Components never import each
other: the planner receives the physics and semantic engines as arguments. During
development these are the mocks in `KaplaCore.Mocks`; `app/Main.lean` passes the real
ones. -/

namespace KaplaCore

/-- The physics engine: does the plan stand after every step, and can a person build it?
`check human maxBlocks plan` -/
structure PhysicsEngine where
  check : HumanModel → Nat → BuildPlan → PhysicsReport

/-- The semantic engine: what to build, and how close a set of blocks is to it. -/
structure SemanticEngine where
  /-- Prompt or picture → target. Calls Claude, so it is in `IO`. -/
  interpret : Request → IO TargetSpec
  /-- How much the blocks look like the target. -/
  score     : TargetSpec → List Pose → ScoreReport
  /-- The best score that this many blocks could reach. -/
  bound     : TargetSpec → Nat → Bound

/-- What the planner is asked to do. -/
structure PlanRequest where
  target        : TargetSpec
  /-- Use at most this many blocks. -/
  blocks        : Nat
  human         : HumanModel := .default
  /-- Return at most this many candidates. -/
  maxCandidates : Nat := 3
  /-- Call `PhysicsEngine.check` at most this many times. -/
  maxChecks     : Nat := 50
  deriving Inhabited

/-- One plan the planner proposes, with what the engines said about it. -/
structure Candidate where
  plan       : BuildPlan
  physics    : PhysicsReport
  score      : ScoreReport
  difficulty : Difficulty
  deriving Repr, Inhabited

/-- The planner: proposes plans, best first. -/
structure Planner where
  plan : PlanRequest → PhysicsEngine → SemanticEngine → IO (List Candidate)

end KaplaCore
