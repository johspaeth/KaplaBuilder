import KaplaPlanner.Design
import KaplaPlanner.Export
import KaplaPlanner.Sequencer
import KaplaPlanner.Fixtures

/-! # Planner demo: fill the bubble test targets and write blueprint files

`app/Main.lean` runs this as `kapla plan [N] [target ...]`, with the verified physics engine.
The planner may not import the physics engine, so the app passes it in twice:

* `stands`: the engine's answer for the blocks placed so far, used by the search for every
  block it tries;
* `phys`: the engine behind core's interface, which checks the finished plan step by step.

Then view a result: `lake exe kapla view out/planner-demo/duck.json --out out/planner-demo/duck`. -/

namespace KaplaPlanner
open KaplaCore

/-- The physics result in words, for the page notes and the terminal. -/
def physicsNote (r : PhysicsReport) : String :=
  if r.ok then "physics (verified engine): stands after every step"
  else s!"physics (verified engine): NOT shown to stand ({r.diagnostics.length} problems)"

/-- Design one target, check the plan with `phys`, and write `out/planner-demo/NAME.json`. -/
def demoOne (stands : List GridBlock → Bool) (phys : PhysicsEngine) (name : String)
    (t : TargetSpec) (n : Nat) (scales : List Q) : IO Unit := do
  match design stands t n scales with
  | none => IO.println s!"{name}: no design"
  | some d =>
    let steps := sequence name d.blocks
    let plan := toBuildPlan steps
    let report := phys.check .default n plan
    let notes := [s!"{d.blocks.length} blocks (budget {n}), scale {d.scale}",
      s!"covers {d.covered} of {d.total} surface cubes ({(d.coverage * 100).floor} %)",
      s!"strictly inside the target (proven check): {insideBubbles d.bubbles d.blocks}",
      s!"every block placed by eye: {eyeballable (GridStep.allBlocks steps)}",
      physicsNote report]
    let dir : System.FilePath := "out/planner-demo"
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir / s!"{name}.json")
      (blueprintJson s!"{name} (planner demo)" s!"{d.blocks.length} blocks" notes plan d.bubbles)
    IO.println s!"{name}: {String.intercalate "; " notes}"
    for dg in report.diagnostics.take 5 do IO.println s!"  {repr dg}"

/-- `kapla plan [N] [target ...]`: design every fixture target (or the ones named) with at
most `N` blocks (default 60). -/
def demoMain (stands : List GridBlock → Bool) (phys : PhysicsEngine) (args : List String) :
    IO UInt32 := do
  let n := (args.head?.bind String.toNat?).getD 60
  let wanted := args.drop 1
  -- larger budgets allow larger scales
  let scales : List Q := if n ≤ 60 then [3/4, 1, 3/2] else [1, 3/2, 2, 5/2]
  for (name, t) in Fixtures.all do
    if wanted.isEmpty || wanted.contains name then demoOne stands phys name t n scales
  return 0

end KaplaPlanner
