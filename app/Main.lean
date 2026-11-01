import KaplaCore
import KaplaPhysics
import KaplaSemantics
import KaplaPlanner
import KaplaWeb

/-! The `kapla` CLI. The only place where the real engines meet.

* `kapla` lists the components.
* `kapla view BLUEPRINT.json [--out DIR]` writes `DIR/index.html` (default `out/`): a 3D view
  and step-by-step cards for the blueprint. Format: `web/README.md`.
-/

/-- Write the page for a blueprint file. -/
def view (file : String) (out : String) : IO UInt32 := do
  let txt ← IO.FS.readFile file
  match KaplaWeb.parsePlan txt with
  | .error e =>
    IO.eprintln s!"{file}: {e}"
    return 1
  | .ok p =>
    IO.FS.createDirAll out
    let path := System.FilePath.mk out / "index.html"
    IO.FS.writeFile path (KaplaWeb.render p)
    IO.println s!"wrote {path} ({p.steps.length} steps)"
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["view", file] => view file "out"
  | ["view", file, "--out", out] => view file out
  | [] =>
    IO.println "KaplaBuilder scaffold. Components:"
    for name in [KaplaPhysics.componentName, KaplaSemantics.componentName,
                 KaplaPlanner.componentName, KaplaWeb.componentName] do
      IO.println s!"  - {name}"
    IO.println "Show a blueprint: kapla view BLUEPRINT.json [--out DIR]"
    return 0
  | _ =>
    IO.eprintln "usage: kapla view BLUEPRINT.json [--out DIR]"
    return 64
