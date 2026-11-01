import KaplaPlanner.Search

/-! # Tests with the mock engines

The full search runs hundreds of builds; that is fine compiled (a few seconds) but too slow to
run at build time. These tests run single builds and the checking step on small models, with
`physicsMock` and `semanticMock` from `KaplaCore.Mocks`. The real engines were tried by hand
(see `planner/README.md`). -/

namespace KaplaPlanner

open KaplaCore

/-- A small build: the ball at height 10, at most 12 blocks. -/
private def ballTrial : Trial := tryBuild ballModel 10 coarseSettings.head! 12

-- It uses the budget but no more, reaches the ball, and every block has a cell in the ball.
#guard
  let t := Table.make ballModel 10
  0 < ballTrial.blocks.length && ballTrial.blocks.length ≤ 12 && ballTrial.covers &&
    ballTrial.blocks.all (fun b => b.cells.any fun c => t.maskAt c != 0)
-- Its fast score equals the direct computation, and the local rule accepts the stack.
#guard
  let t := Table.make ballModel 10
  let (c, e) := refCounts t ballTrial.blocks
  ballTrial.fast == scoreOf t.target c e && (Stack.placeAll {} ballTrial.blocks 1).isSome
-- The mock physics engine accepts it after every step.
#guard (physicsMock.check .default 12 (toPlan ballTrial.blocks)).ok
-- Checking and scoring with the mocks gives one candidate, within the limits.
#guard
  let req : PlanRequest := { target := .ofBubbles ballModel, blocks := 12 }
  match checkTrials req physicsMock semanticMock [ballTrial] with
  | [c] => c.physics.ok && c.plan.blockCount ≤ 12 && c.score.accepted && c.score.frame == Frame.ofHeight 10
  | _ => false

-- The bunny at height 20 with 30 blocks reaches all six bubbles, with foundation cells worth a
-- little (they are what lets the head and ears be reached).
#guard (tryBuild bunnyModel 20 { cabin := none, underShare := -1 / 2, perCourse := 0 } 30).covers

-- A target that is not a bubble model gets no candidates.
#guard (planPure { target := TargetSpec.example, blocks := 10 } physicsMock semanticMock).isEmpty
-- No blocks, no candidates.
#guard (allTrials ballModel 0).isEmpty

-- In strict mode (for budgets above 40) the build is accepted by the strict local rule.
#guard
  let tr := tryBuild ballModel 10 { coarseSettings.head! with strict := true } 12
  !tr.blocks.isEmpty && (Stack.placeAll {} tr.blocks 1 true).isSome
#guard (forBudget 41 coarseSettings).all (·.strict) && !(forBudget 40 coarseSettings).any (·.strict)

-- The physics check blames the right block, and the repair removes it and what rested on it.
#guard
  let bs : List GBlock := [⟨.flatX, 0, 0, 0⟩, ⟨.flatY, 6, -6, 1⟩, ⟨.flatX, 0, 0, 2⟩]
  removeBlocks bs [1] 1 false == [⟨.flatX, 0, 0, 0⟩]
#guard blamed { ok := false, diagnostics := [.unstable 3 2, .tooManyHands 1] } == [2]

end KaplaPlanner
