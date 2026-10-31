import KaplaPlanner.Sequencer

/-! # Pre-check: cheap checks before we call the physics engine

The physics check is the judge, but it may be slow. These grid checks catch most planner
mistakes first:
- the plan uses at most `N` blocks;
- no two blocks overlap;
- **supports first**: every block stands on the ground or on a block placed in an
  earlier step. (A skyscraper built top-down fails here.) -/

namespace KaplaPlanner

/-- Every block stands on the ground or on a block that comes before it in the list. -/
def supportsFirst (bs : List GridBlock) : Bool :=
  (bs.zipIdx).all fun (b, i) => b.onGround || (bs.take i).any fun c => b.restsOn c

/-- No two blocks in the list overlap. -/
def noOverlap : List GridBlock → Bool
  | [] => true
  | b :: rest => rest.all (fun c => !b.overlaps c) && noOverlap rest

/-- What went wrong in the pre-check. -/
inductive PreProblem where
  | tooManyBlocks
  | overlap
  | unsupported
  deriving Repr, BEq, DecidableEq

/-- The pre-check. Returns the problems found (empty list = passed). -/
def preCheck (maxBlocks : Nat) (steps : List GridStep) : List PreProblem :=
  let bs := GridStep.allBlocks steps
  (if bs.length ≤ maxBlocks then [] else [.tooManyBlocks]) ++
  (if noOverlap bs then [] else [.overlap]) ++
  (if supportsFirst bs then [] else [.unsupported])

-- a two-block stack in the right order passes; in the wrong order it does not
#guard preCheck 2 (sequence "t" [⟨.flatX, 0, 0, 0⟩, ⟨.flatY, 0, 0, 1⟩]) == []
#guard preCheck 2 [⟨[⟨.flatY, 0, 0, 1⟩], ""⟩, ⟨[⟨.flatX, 0, 0, 0⟩], ""⟩] == [.unsupported]
#guard preCheck 1 (sequence "t" [⟨.flatX, 0, 0, 0⟩, ⟨.flatY, 0, 0, 1⟩]) == [.tooManyBlocks]
#guard preCheck 2 (sequence "t" [⟨.flatX, 0, 0, 0⟩, ⟨.flatY, 0, 0, 0⟩]) == [.overlap]

end KaplaPlanner
