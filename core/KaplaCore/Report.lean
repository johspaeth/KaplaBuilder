import KaplaCore.Plan

/-! # Reports from the engines

Only plain data crosses between components. The physics engine says "ok" or gives a list
of problems (`Diagnostic`). The semantic engine gives a score and an upper limit. -/

namespace KaplaCore

/-- One problem the physics engine found. `step` is a step number, `block` is a position in
`BuildPlan.blocks`. Both count from 0. -/
inductive Diagnostic where
  /-- After `step`, `block` falls or tips. -/
  | unstable (step block : Nat)
  /-- After `step`, a leaning block slides at contact number `contact`. -/
  | slides (step contact : Nat)
  /-- Pressing on corner `corner` of the new block(s) in `step` makes something tip. -/
  | pressTips (step corner : Nat)
  /-- The block(s) of `step` cannot be put in place by hand. -/
  | unreachable (step : Nat)
  /-- Blocks `i` and `j` overlap. -/
  | overlap (i j : Nat)
  /-- Blocks `i` and `j` do not touch, but the gap between them is too small. -/
  | clearance (i j : Nat)
  /-- `block` rests on support stacks that are built differently. -/
  | unevenSupports (block : Nat)
  /-- `step` places more blocks than the builder has hands. -/
  | tooManyHands (step : Nat)
  /-- `step` places no block. -/
  | emptyStep (step : Nat)
  /-- The plan uses `used` blocks, but only `limit` are allowed. -/
  | tooManyBlocks (used limit : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What the physics engine says about a plan. -/
structure PhysicsReport where
  ok          : Bool
  diagnostics : List Diagnostic := []
  /-- For each block, how much safety margin is left (mm), if the engine computes it. -/
  slackPerBlock : Option (List Q) := none
  deriving Repr, BEq, Inhabited

/-- How much the plan looks like the target, in words. -/
inductive Verdict where
  /-- Score at least 0.7. -/
  | good
  /-- Score from 0.4 to 0.7. -/
  | coarse
  /-- Score from 0.15 to 0.4. -/
  | abstract
  /-- Score below 0.15: only a symbol of the target. -/
  | symbolic
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The verdict for a score (docs/DESIGN.md §5). -/
def Verdict.ofScore (s : Q) : Verdict :=
  if s ≥ 7 / 10 then .good
  else if s ≥ 2 / 5 then .coarse
  else if s ≥ 3 / 20 then .abstract
  else .symbolic

#guard Verdict.ofScore 0.8 == .good && Verdict.ofScore 0.1 == .symbolic

/-- How much the plan looks like the target. All scores are between 0 and 1. -/
structure ScoreReport where
  score         : Q
  iou           : Q
  silhouetteIoU : Option Q := none
  /-- For each part name: how much of it the blocks cover. -/
  perPart       : List (String × Q) := []
  /-- Grid cells of the target that no block covers. -/
  missing       : Nat := 0
  /-- Grid cells covered by blocks that are not in the target. -/
  extra         : Nat := 0
  deriving Repr, BEq, Inhabited

/-- The best score that `N` blocks could reach, and its verdict. -/
structure Bound where
  maxScore : Q
  verdict  : Verdict
  deriving Repr, BEq, Inhabited

/-- How hard a plan is to build. -/
inductive Difficulty where
  | easy
  | medium
  | expert
  deriving Repr, BEq, DecidableEq, Inhabited

end KaplaCore
