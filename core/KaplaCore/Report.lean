import KaplaCore.Bubble
import KaplaCore.Plan

/-! # Reports from the engines

Only plain data crosses between components. The physics engine says "ok" or gives a list
of problems (`Diagnostic`). The semantic engine says which blocks are outside the target, which bubbles have no
block, and how similar the blocks are to the target. -/

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
  /-- For each block, how much safety margin is left, if the engine computes it. -/
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

/-- What the semantic engine says about a list of blocks, finished or partial, at one
`Frame`. All scores are between 0 and 1. -/
structure ScoreReport where
  /-- The similarity number. There is no minimum: a person decides if it is good enough. -/
  score         : Q
  iou           : Q := 0
  silhouetteIoU : Option Q := none
  /-- For each part name: how much of it the blocks cover. -/
  perPart       : List (String × Q) := []
  /-- Grid cells of the target that no block covers. -/
  missing       : Nat := 0
  /-- Grid cells covered by blocks that are not in the target. -/
  extra         : Nat := 0
  /-- The frame this report was computed at, so anyone can compute it again. -/
  frame         : Frame := Frame.ofHeight 1
  /-- How many blocks were scored. -/
  blockCount    : Nat := 0
  /-- Positions in the block list of blocks with none of their cells in any bubble. Any block
  here means reject, also for a partial plan. -/
  outside       : List Nat := []
  /-- Labels of bubbles with cells but no block yet. This is normal for a partial plan. -/
  uncovered     : List String := []
  /-- Labels of bubbles with no grid cell at this frame, so no block can ever count as being in
  them. They are ignored by `accepted`. A person can remove them before accepting the design. -/
  tooSmall      : List String := []
  deriving Repr, BEq, Inhabited

/-- The blocks may be shown to a person for approval: at least one block, no block outside, and
every bubble that has cells has a block. The score plays no part. -/
def ScoreReport.accepted (r : ScoreReport) : Bool :=
  r.blockCount > 0 && r.outside.isEmpty && r.uncovered.isEmpty

/-- The score in words. -/
def ScoreReport.verdict (r : ScoreReport) : Verdict := Verdict.ofScore r.score

#guard ScoreReport.accepted { score := 0, blockCount := 1 }
-- A low score is still accepted, and a report with no blocks is not.
#guard !ScoreReport.accepted { score := 1 }
#guard !ScoreReport.accepted { score := 1, blockCount := 1, outside := [0] }
#guard !ScoreReport.accepted { score := 1, blockCount := 1, uncovered := ["head"] }
-- A bubble that is too small does not stop acceptance.
#guard ScoreReport.accepted { score := 1, blockCount := 1, tooSmall := ["tail"] }

/-- How hard a plan is to build. -/
inductive Difficulty where
  | easy
  | medium
  | expert
  deriving Repr, BEq, DecidableEq, Inhabited

end KaplaCore
