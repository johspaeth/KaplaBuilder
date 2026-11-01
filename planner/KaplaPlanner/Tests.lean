import KaplaPlanner.Planner

/-! # End-to-end tests on the mock engines

For each test target and several block budgets, the planner must return at least one
candidate, every candidate must pass the mock physics check, and none may use more blocks
than allowed. -/

namespace KaplaPlanner.Tests
open KaplaCore

/-- A box target with one part. -/
def boxTarget (name : String) (kind : PartKind) (w d h : Q) : TargetSpec :=
  let b : Box := ⟨⟨0, 0, 0⟩, ⟨w, d, h⟩⟩
  { shape := .box b, parts := [⟨name, kind, b⟩] }

/-- Test targets. -/
def targets : List TargetSpec :=
  [ boxTarget "tree" .trunk 4 4 26,
    boxTarget "tower" .tower 15 15 38,
    boxTarget "house" .other 38 26 19,
    TargetSpec.example ]

/-- Block budgets to test. -/
def budgets : List Nat := [1, 2, 4, 20, 60]

/-- The planner on mocks, for one target and budget. -/
def run (t : TargetSpec) (n : Nat) (human : HumanModel := .adult) : List Candidate :=
  planPure { target := t, blocks := n, human } physicsMock semanticMock

/-- The planner's result for one target and budget is good:
- at least one candidate;
- every candidate passes the mock physics check (checked again here, independently of the
  planner's own filter) and uses at most `n` blocks;
- candidates come best first (up to the 1/50 rounding the ranking uses). -/
def resultOk (t : TargetSpec) (n : Nat) (human : HumanModel) : Bool :=
  let cs := run t n human
  let scores := cs.map (·.score.score)
  !cs.isEmpty &&
  cs.all (fun c => (physicsMock.check human n c.plan).ok && c.plan.blockCount ≤ n) &&
  (scores.zip scores.tail).all fun (a, b) => a + 1 / 50 ≥ b

#guard targets.all fun t => budgets.all fun n => resultOk t n .adult

-- also for a child, who has only one hand
#guard targets.all fun t => resultOk t 20 .child

-- with no blocks there is no plan
#guard (run TargetSpec.example 0).isEmpty

-- with one block, the plan is one upright block
#guard (run TargetSpec.example 1).map (·.plan.blockCount) == [1]

-- a tall tower with 60 blocks: a 30-layer log-cabin tower beats one block
#guard match run (boxTarget "tower" .tower 15 15 38) 60 with
  | best :: _ => best.plan.blockCount == 60 && best.score.score > 3 / 10
  | [] => false

-- a house with 60 blocks: a solid column, with a good likeness
#guard match run (boxTarget "house" .other 38 26 19) 60 with
  | best :: _ => best.score.score ≥ 3 / 5
  | [] => false

-- a thin tree with 20 blocks: one upright block is the best likeness ("tree trunk")
#guard match run (boxTarget "tree" .trunk 4 4 26) 20 with
  | best :: _ => best.plan.blockCount == 1
  | [] => false

end KaplaPlanner.Tests
