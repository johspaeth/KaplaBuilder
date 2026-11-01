import KaplaCore

/-! # Demo problems for the planner

The planner is developed against a fixed set of problems: each demo model with 10, 40 and 100
blocks. This file holds the problems, the results of an earlier planner (PR #31) as a bar to
reach, and `checkDemo`, which says what is wrong with a planner's answer to a problem.

This file has no planner code. Any planner can be run on the demos with `runDemos`. -/

namespace KaplaPlanner

open KaplaCore

/-! ## Demo models -/

/-- A ball of height 1 with its bottom on the ground. The simplest round shape: it touches the
ground at one point. -/
def ballModel : BubbleModel :=
  { name := "ball"
    bubbles := [{ label := "ball", tags := [], center := ⟨0, 0, 1 / 2⟩
                  semi := ⟨1 / 2, 1 / 2, 1 / 2⟩ }] }

/-- The bunny, six bubbles. The same numbers as `web/examples/bubbles/bunny.json` and
`semantics/fixtures/targets/bunny.json`. -/
def bunnyModel : BubbleModel :=
  { name := "bunny"
    bubbles :=
      [ { label := "body", tags := ["tower"], center := ⟨0, 0, 28 / 100⟩
          semi := ⟨30 / 100, 22 / 100, 28 / 100⟩ }
      , { label := "head", tags := ["tower"], center := ⟨22 / 100, 0, 60 / 100⟩
          semi := ⟨17 / 100, 15 / 100, 16 / 100⟩ }
      , { label := "left ear", tags := ["wall"], center := ⟨20 / 100, -7 / 100, 86 / 100⟩
          semi := ⟨5 / 100, 3 / 100, 14 / 100⟩ }
      , { label := "right ear", tags := ["wall"], center := ⟨20 / 100, 7 / 100, 86 / 100⟩
          semi := ⟨5 / 100, 3 / 100, 14 / 100⟩ }
      , { label := "tail", tags := [], center := ⟨-32 / 100, 0, 30 / 100⟩
          semi := ⟨7 / 100, 7 / 100, 7 / 100⟩ }
      , { label := "paws", tags := ["slab"], center := ⟨30 / 100, 0, 5 / 100⟩
          semi := ⟨8 / 100, 14 / 100, 5 / 100⟩ } ] }

/-- The egg: `BubbleModel.egg` from Core, one tall bubble on the ground. -/
def eggModel : BubbleModel := BubbleModel.egg

/-- A half ball with its middle on the ground, such as a foot. The same numbers as
`web/examples/bubbles/foot.json`. Its widest part is on the ground. -/
def footModel : BubbleModel :=
  { name := "foot"
    bubbles := [{ label := "foot", tags := [], center := ⟨0, 0, 0⟩, semi := ⟨1, 1, 1⟩ }] }

/-- All demo models. -/
def demoModels : List BubbleModel := [ballModel, bunnyModel, eggModel, footModel]

/-- The block budgets every model is tried with. -/
def demoBudgets : List Nat := [10, 40, 100]

-- Every demo model is well formed, and the names are different.
#guard demoModels.all (·.wellFormed)
#guard (demoModels.map (·.name)).eraseDups.length == demoModels.length

/-! ## Demo problems -/

/-- What an earlier planner reached on a problem, with the real physics engine and scorer:
how many blocks it used, and at which height. -/
structure Reference where
  blocksUsed : Nat
  height     : Nat
  deriving Repr, BEq

/-- One problem: build `model` with at most `blocks` blocks. -/
structure Demo where
  model     : BubbleModel
  blocks    : Nat
  /-- The result of PR #31's planner, if there is one. -/
  reference : Option Reference := none

/-- The name of a problem, such as `bunny-40`. -/
def Demo.name (d : Demo) : String := s!"{d.model.name}-{d.blocks}"

/-- The request the planner gets for a problem. -/
def Demo.request (d : Demo) : PlanRequest :=
  { target := .ofBubbles d.model, blocks := d.blocks }

/-- The best plan of PR #31's planner for each problem (from the screenshots in that PR). -/
def referenceOf : String → Option Reference
  | "bunny-10"  => some ⟨6, 10⟩
  | "bunny-40"  => some ⟨32, 24⟩
  | "bunny-100" => some ⟨59, 31⟩
  | "egg-10"    => some ⟨1, 4⟩
  | "egg-40"    => some ⟨39, 24⟩
  | "egg-100"   => some ⟨63, 27⟩
  | "ball-10"   => some ⟨10, 9⟩
  | "ball-40"   => some ⟨40, 17⟩
  | "ball-100"  => some ⟨43, 17⟩
  | _ => none

/-- Every demo model with every budget. -/
def demos : List Demo :=
  demoModels.flatMap fun m => demoBudgets.map fun n =>
    let d : Demo := { model := m, blocks := n }
    { d with reference := referenceOf d.name }

#guard demos.length == 12
#guard (demos.map (·.name)).eraseDups.length == demos.length
-- The earlier planner stayed within the budget on every problem it was tried on.
#guard demos.all fun d => d.reference.all (·.blocksUsed ≤ d.blocks)
-- Every reference belongs to a demo.
#guard (demos.filter (·.reference.isSome)).length == 9

/-! ## Checking a planner's answer -/

/-- What can be wrong with the candidates a planner returns for a request. -/
inductive Problem where
  /-- The planner returned nothing. -/
  | noCandidate
  /-- More candidates than `maxCandidates`. -/
  | tooManyCandidates (count : Nat)
  /-- Candidate `i` uses more blocks than allowed. -/
  | tooManyBlocks (i used : Nat)
  /-- The physics engine does not accept candidate `i`. -/
  | fallsDown (i : Nat)
  /-- The scorer does not accept candidate `i` (a block outside, or a bubble with no block). -/
  | notAccepted (i : Nat)
  /-- The physics report stored in candidate `i` is not what the engine says. -/
  | wrongPhysicsReport (i : Nat)
  deriving Repr, BEq

/-- Everything wrong with `cs` as an answer to `req`. The engines are asked again; the
reports inside the candidates are not trusted. An empty list means the answer is good. -/
def checkDemo (req : PlanRequest) (physics : PhysicsEngine) (semantic : SemanticEngine)
    (cs : List Candidate) : List Problem :=
  let count := if cs.isEmpty then [.noCandidate]
    else if cs.length > req.maxCandidates then [.tooManyCandidates cs.length] else []
  let each := (cs.zipIdx).flatMap fun (c, i) =>
    let report := physics.check req.human req.blocks c.plan
    let score := semantic.score req.target c.score.height c.plan.blocks
    (if c.plan.blockCount > req.blocks then [.tooManyBlocks i c.plan.blockCount] else []) ++
    (if !report.ok then [.fallsDown i] else []) ++
    (if report.ok != c.physics.ok then [.wrongPhysicsReport i] else []) ++
    (if !score.accepted then [.notAccepted i] else [])
  count ++ each

/-- The result of one demo run. -/
structure DemoResult where
  demo     : Demo
  problems : List Problem
  /-- Block count, height and score of each candidate, best first. -/
  found    : List (Nat × Q × Q)

/-- One line per demo: what the planner found, the reference, and any problems. -/
def DemoResult.line (r : DemoResult) : String :=
  let found := r.found.map fun (n, h, s) => s!"{n} blocks @ h={h}, score {s}"
  let ref := match r.demo.reference with
    | some x => s!"{x.blocksUsed} blocks @ h={x.height}"
    | none => "-"
  let status := if r.problems.isEmpty then "OK" else s!"PROBLEMS {repr r.problems}"
  s!"{r.demo.name}: {status}; found {found}; PR #31: {ref}"

/-- Run a planner on one demo and check its answer. -/
def runDemo (planner : Planner) (physics : PhysicsEngine) (semantic : SemanticEngine)
    (d : Demo) : IO DemoResult := do
  let cs ← planner.plan d.request physics semantic
  return { demo := d, problems := checkDemo d.request physics semantic cs
           found := cs.map fun c => (c.plan.blockCount, c.score.height, c.score.score) }

/-- Run a planner on every demo, print one line per demo, and return the results. -/
def runDemos (planner : Planner) (physics : PhysicsEngine) (semantic : SemanticEngine)
    (ds : List Demo := demos) : IO (List DemoResult) := do
  let mut out := []
  for d in ds do
    let r ← runDemo planner physics semantic d
    IO.println r.line
    out := out ++ [r]
  return out

/-! ## The checker accepts good answers and rejects bad ones -/

/-- A flat block in the middle of the ground, lengthwise along x. -/
private def middleFlat : Pose := ⟨.flat, .id, ⟨1 / 2, 3 / 2, 1 / 2⟩⟩

/-- A candidate with these blocks, scored at this height by the mock engines. -/
private def mockCandidate (d : Demo) (height : Q) (bs : List Pose) : Candidate :=
  let plan := BuildPlan.ofBlocks bs
  { plan, physics := physicsMock.check .default d.blocks plan
    score := semanticMock.score d.request.target height bs, difficulty := default }

private def ball10 : Demo := { model := ballModel, blocks := 10 }

-- One flat block in the middle of the ball at height 20 is a good answer.
#guard checkDemo ball10.request physicsMock semanticMock [mockCandidate ball10 20 [middleFlat]]
  == []
-- No answer is a problem.
#guard checkDemo ball10.request physicsMock semanticMock [] == [.noCandidate]
-- Too many blocks: eleven blocks stacked, with a budget of ten.
#guard
  let stack := (List.range 11).map fun k => { middleFlat with center.z := k + 1 / 2 }
  (checkDemo ball10.request physicsMock semanticMock [mockCandidate ball10 20 stack]).contains
    (.tooManyBlocks 0 11)
-- A block in the air falls down; a report that says it stands is caught.
#guard
  let floating := { middleFlat with center.z := 5 + 1 / 2 }
  let c := { mockCandidate ball10 20 [floating] with physics := { ok := true } }
  let ps := checkDemo ball10.request physicsMock semanticMock [c]
  ps.contains (.fallsDown 0) && ps.contains (.wrongPhysicsReport 0)
-- A block far from the ball is not accepted by the scorer.
#guard
  let far := { middleFlat with center.x := 100 }
  (checkDemo ball10.request physicsMock semanticMock [mockCandidate ball10 20 [far]]).contains
    (.notAccepted 0)
-- Four answers when at most three are asked for.
#guard
  let c := mockCandidate ball10 20 [middleFlat]
  (checkDemo ball10.request physicsMock semanticMock [c, c, c, c]).contains
    (.tooManyCandidates 4)

end KaplaPlanner
