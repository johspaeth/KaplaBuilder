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
  | [c] => c.physics.ok && c.plan.blockCount ≤ 12 && c.score.accepted && c.score.height == 10
  | _ => false

-- The bunny at height 20 with 30 blocks reaches all six bubbles, with foundation cells worth a
-- little (they are what lets the head and ears be reached).
#guard (tryBuild bunnyModel 20 { cabin := none, underShare := -1 / 2, perCourse := 0 } 30).covers

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

/-! ## The tree search, with the mock physics engine -/

/-- A tree search on the ball at height 10, 12 blocks, run to the end with checks right away. -/
private def ballTree : Tree :=
  let t := Table.make ballModel 10
  (Tree.make t 10 12 (paramsFor t default 12)).runWith physicsMock .default toPlan 400 20

-- It finds a plan that passed physics, within the block limit, that reaches the ball, and that
-- scores at least as well as the greedy build with the same setting.
#guard match ballTree.incumbent with
  | some lf => lf.covers && 0 < lf.blocks.size && lf.blocks.size ≤ 12 &&
      (physicsMock.check .default 12 (toPlan lf.blocks.toList)).ok &&
      lf.fast ≥ (tryBuild ballModel 10 default 12).fast
  | none => false
-- Its fast score is the direct one.
#guard match ballTree.incumbent with
  | some lf =>
    let t := Table.make ballModel 10
    let (c, e) := refCounts t lf.blocks.toList
    lf.fast == scoreOf t.target c e
  | none => false
-- The candidates from it are within the limits and accepted by the mock scorer.
#guard
  let req : PlanRequest := { target := .ofBubbles ballModel, blocks := 12 }
  match candidatesOf req semanticMock [ballTree] with
  | c :: _ => c.physics.ok && c.plan.blockCount ≤ 12 && c.score.accepted
  | [] => false

-- A refused block: the waiting nodes with the same blocks up to it are dropped, its placement
-- becomes a no-good, and the blocks before it are offered as a smaller plan.
#guard
  let t := Table.make ballModel 10
  let tr := Tree.make t 10 12 (paramsFor t default 12)
  let bs : Array GBlock := #[⟨.flatX, -7, -4, 0⟩, ⟨.flatX, -7, 1, 0⟩, ⟨.flatY, -4, -7, 1⟩]
  let lf := Leaf.ofBlocks t tr.info bs
  let tr' := tr.report lf { ok := false, diagnostics := [.unstable 2 2] }
  tr'.nogood.size == 1 && tr'.requests.size == 1 && tr'.requests[0]!.blocks.size == 2

-- The probes: the mock engine lets upright blocks stand on flat ones and carry (it has no
-- placement error); the rules follow what it says.
#guard probeRules physicsMock .default == { onFlat := true, carry := true }

-- Tree heights: at most `k`, no repeats.
#guard
  let trials := [{ height := 10, blocks := [], fast := 1 / 2, covers := true : Trial },
                 { height := 20, blocks := [], fast := 1 / 3, covers := true }]
  let hs := treeHeights trials 8
  hs.length ≤ 8 && (hs.map (·.1)).eraseDups.length == hs.length && hs.head?.map (·.1) == some 10

end KaplaPlanner
