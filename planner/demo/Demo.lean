import KaplaPlanner
import KaplaPlanner.Stability

/-! Planner demo: fill bubble test targets with blocks and write blueprint files.

    lake env lean --run planner/demo/Demo.lean [N] [target ...]
    lake exe kapla view out/planner-demo/sphere.json --out out/planner-demo/sphere

Uses the mock physics engine (not the verified one). -/

open KaplaCore KaplaPlanner

def runOne (name : String) (t : TargetSpec) (n : Nat) (scales : List Q) : IO Unit := do
  -- inside the search: the planner's cheap estimate; at the end: the physics engine (mock)
  match design standsNow t n scales with
  | none => IO.println s!"{name}: no design"
  | some d =>
    let steps := sequence name d.blocks
    let plan := toBuildPlan steps
    let phys := physicsMock.check .adult n plan
    let inside := insideBubbles d.bubbles d.blocks
    let byEye := eyeballable (GridStep.allBlocks steps)
    let pct := (d.coverage * 100).floor
    let notes := [s!"{d.blocks.length} blocks (budget {n}), scale {d.scale}",
      s!"covers {d.covered} of {d.total} surface cubes ({pct} %)",
      s!"strictly inside the target (proven check): {inside}",
      s!"every block placed by eye: {byEye}",
      s!"mock physics, every step: {if phys.ok then "stands" else s!"fails {repr phys.diagnostics}"}"]
    let dir : System.FilePath := "out/planner-demo"
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir / s!"{name}.json")
      (blueprintJson s!"{name} (planner demo)" s!"{d.blocks.length} blocks" notes plan)
    IO.println s!"{name}: {String.intercalate "; " notes}"

def main (args : List String) : IO Unit := do
  let n := (args.head?.bind String.toNat?).getD 60
  let wanted := args.drop 1
  -- larger budgets allow larger scales
  let scales : List Q := if n ≤ 60 then [3/4, 1, 3/2] else [1, 3/2, 2, 5/2]
  for (name, t) in Fixtures.all do
    if wanted.isEmpty || wanted.contains name then runOne name t n scales
