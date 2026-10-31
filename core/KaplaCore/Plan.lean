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

/-- What we assume about the person who builds. See docs/DESIGN.md §2.1. -/
structure HumanModel where
  /-- mm: how far a block may be off, measured against the block(s) it rests on. -/
  epsRel : Q
  /-- mm: how far any block may drift from the plan in total. -/
  eAbs   : Q
  /-- Downward press while placing a block, in block weights. -/
  press  : Q
  /-- The most blocks placed in one step. -/
  hands  : Nat
  /-- mm: the smallest gap between two blocks that do not touch by design. -/
  clear  : Q
  /-- The friction coefficient we assume (lower than real wood, for safety). -/
  muSafe : Q
  deriving Repr, BEq, Inhabited

/-- A child: less precise, one hand. -/
def HumanModel.child : HumanModel :=
  { epsRel := 5, eAbs := 15, press := 1, hands := 1, clear := 5, muSafe := 1 / 4 }

/-- An adult (the default). -/
def HumanModel.adult : HumanModel :=
  { epsRel := 3, eAbs := 10, press := 1 / 2, hands := 2, clear := 5, muSafe := 3 / 10 }

/-- An expert builder. -/
def HumanModel.expert : HumanModel :=
  { epsRel := 3 / 2, eAbs := 5, press := 3 / 10, hands := 2, clear := 3, muSafe := 7 / 20 }

/-- Find a profile by name: "child", "adult" or "expert". -/
def HumanModel.ofName? : String → Option HumanModel
  | "child"  => some .child
  | "adult"  => some .adult
  | "expert" => some .expert
  | _        => none

#guard HumanModel.adult.hands == 2 && HumanModel.child.hands == 1

end KaplaCore
