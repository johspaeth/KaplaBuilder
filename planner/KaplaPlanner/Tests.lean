import KaplaPlanner.Planner
import KaplaPlanner.Design
import KaplaPlanner.Stability
import KaplaPlanner.Fixtures

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
def run (t : TargetSpec) (n : Nat) (human : HumanModel := .default) : List Candidate :=
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

#guard targets.all fun t => budgets.all fun n => resultOk t n .default

-- also for a builder with only one hand
#guard targets.all fun t => resultOk t 20 { HumanModel.default with hands := 1 }

-- with no blocks there is no plan
#guard (run TargetSpec.example 0).isEmpty

-- with one block, the plan is one upright block
#guard (run TargetSpec.example 1).map (·.plan.blockCount) == [1]

-- a tall tower with 60 blocks: a 30-layer log-cabin tower beats one block
#guard match run (boxTarget "tower" .tower 15 15 38) 60 with
  | best :: _ => best.plan.blockCount == 60 && best.score.score > 3 / 20
  | [] => false

-- a house with 60 blocks: a solid column, with a good likeness
#guard match run (boxTarget "house" .other 38 26 19) 60 with
  | best :: _ => best.score.score ≥ 3 / 5
  | [] => false

-- a thin tree with 20 blocks: one upright block is the best likeness ("tree trunk")
#guard match run (boxTarget "tree" .trunk 4 4 26) 20 with
  | best :: _ => best.plan.blockCount == 1
  | [] => false

/-! ## Bubble designs (P3) -/

-- A small ball, at most 12 blocks: the design is strictly inside (proven check), every block
-- can be placed by eye, the plan stands after every step (mock physics), and the budget holds.
#guard
  let t := Fixtures.ofBubbles [ball "ball" ⟨0, 0, 10⟩ 10]
  match design standsNow t 12 [1] [1 / 5] with
  | none => false
  | some d =>
    let plan := toBuildPlan (sequence "ball" d.blocks)
    !d.blocks.isEmpty && d.blocks.length ≤ 12 && insideBubbles d.bubbles d.blocks &&
    eyeballable d.blocks && (physicsMock.check .default 12 plan).ok

-- The fast block check of the designer (`blockOk`, whole numbers) agrees with the proven
-- check (`insideBubbles`, exact fractions) on the snowman, for every pose, at odd offsets,
-- with blocks inside and outside.
#guard
  let bs := placeTarget Fixtures.snowman (3 / 2) (1 / 10)
  let fbs := prepareBubbles bs
  let blocks := Orient.all.flatMap fun o =>
    (List.range 13).flatMap fun (i : Nat) => (List.range 13).flatMap fun (k : Nat) =>
      [(⟨o, 7 * (i : Int) - 60, -6, 5 * (k : Int)⟩ : GridBlock),
       ⟨o, -30, 7 * (i : Int) - 45, 5 * (k : Int) + 2⟩]
  let agree := blocks.all fun b => blockOk fbs b == insideBubbles bs [b]
  let nIn := blocks.countP (blockOk fbs)
  agree && 0 < nIn && nIn < blocks.length

end KaplaPlanner.Tests
