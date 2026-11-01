import KaplaCore.Block

/-! # Build plans and the human builder

A `BuildPlan` is a list of steps. In each step the builder places 1 or 2 blocks. The
structure must stand after every step, not only at the end. -/

namespace KaplaCore

/-- Where the fingers hold the block. -/
inductive Grip where
  /-- On the two long sides. -/
  | longSides
  /-- On the two short ends. -/
  | shortEnds
  /-- On the top end of a standing block. -/
  | topEnd
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A horizontal axis. -/
inductive Axis where
  | x
  | y
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How the block moves into place. -/
inductive Approach where
  /-- Lowered straight down from above. -/
  | fromAbove
  /-- Slid in sideways along `axis`; `positive` says in which direction it moves. -/
  | slide (axis : Axis) (positive : Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One build step: the blocks placed at the same time, and how. -/
structure Step where
  blocks   : List Pose
  grip     : Grip := .longSides
  approach : Approach := .fromAbove
  /-- A short label for the instructions, for example "left tower". -/
  phase    : String := ""
  deriving Repr, BEq, Inhabited

/-- A complete plan: the steps in build order. -/
structure BuildPlan where
  steps : List Step
  deriving Repr, BEq, Inhabited

/-- All blocks of the plan, in build order. Block number `i` in a `Diagnostic` is the
position in this list. -/
def BuildPlan.blocks (p : BuildPlan) : List Pose := p.steps.flatMap (·.blocks)

/-- The number of blocks the plan uses. -/
def BuildPlan.blockCount (p : BuildPlan) : Nat := p.blocks.length

/-- Example: a plan with one step that places one block. -/
def BuildPlan.example : BuildPlan := ⟨[{ blocks := [Pose.example] }]⟩

#guard BuildPlan.example.blockCount == 1

/-- What we assume about the person who builds. See docs/DESIGN.md §2.1.

The verified physics engine reads only `epsRel` and `hands`. -/
structure HumanModel where
  /-- How far a block may land from its own planned spot, along `x` and along `y` (rule R1
  of `spec/physics-rules.md`). Each block's error is separate, so two touching blocks can
  end up as much as `2 * epsRel` off from each other. Errors do not add up from level to
  level: a block high in a tower is still within `epsRel` of its planned spot. -/
  epsRel : Q
  /-- How far any block may drift from the plan in total. Not used by the verified physics
  engine: under R1 no block drifts more than `epsRel`. Kept for the mock and for later. -/
  eAbs   : Q
  /-- Downward press while placing a block, in block weights. -/
  press  : Q
  /-- The most blocks placed in one step. -/
  hands  : Nat
  /-- The smallest gap between two blocks that do not touch by design. -/
  clear  : Q
  /-- The friction coefficient we assume (lower than real wood, for safety). -/
  muSafe : Q
  deriving Repr, BEq, Inhabited

/-- The builder we assume. `epsRel = 10/39` is the 2 mm of the physics rules (R1). -/
def HumanModel.default : HumanModel :=
  { epsRel := 10 / 39, eAbs := 50 / 39, press := 1 / 2, hands := 2, clear := 25 / 39, muSafe := 3 / 10 }

#guard HumanModel.default.hands == 2

end KaplaCore
