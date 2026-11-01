import KaplaCore
import KaplaPhysics
import KaplaSemantics
import KaplaPlanner
import KaplaWeb

/-! The `kapla` CLI. The only place where the real engines meet.

* `kapla` lists the components.
* `kapla check BLUEPRINT.json [--max N] [--no-clearance]` runs the verified physics engine
  on the blueprint (default builder, at most `N` blocks, default 200) and lists the problems
  it finds. Exit code 0 when the plan is `ok`, 1 when it is not.
* `kapla view BLUEPRINT.json [--out DIR] [--no-clearance]` writes `DIR/index.html` (default
  `out/`): a 3D view and step-by-step cards for the blueprint, with the physics engine's
  result in the notes. Format: `web/README.md`.
* `kapla plan [N] [target ...] [--no-clearance]` runs the planner demo: it fills the bubble
  test targets with at most `N` blocks (default 60), with the verified physics engine, and
  writes blueprint files to `out/planner-demo/`.

`--no-clearance` allows blocks placed side by side and touching: the engine then does not ask
that a 2 mm error can never push two blocks into each other.
-/

open Lean (Json JsonNumber)
open KaplaCore (Q Q3 Rot Upright BuildPlan HumanModel PhysicsReport Diagnostic)

/-! ## Reading a blueprint exactly

The viewer reads numbers as `Float`, for drawing. The physics engine needs the exact
numbers, so we read the same file again here, into a `KaplaCore.BuildPlan`. -/

/-- A JSON number as an exact fraction: `mantissa / 10^exponent`. -/
def ratOfJsonNumber (n : JsonNumber) : Q := (n.mantissa : Q) / ((10 ^ n.exponent : Nat) : Q)

#guard ratOfJsonNumber ⟨25, 1⟩ == 5 / 2

/-- Read a number written as a JSON number (`3`, `2.5`) or as an exact fraction in a string
(`"-169/10"`, `"7"`), without rounding. -/
def readQ (j : Json) : Except String Q :=
  match j with
  | .num n => .ok (ratOfJsonNumber n)
  | .str s =>
    let int (t : String) : Except String Int :=
      match t.trimAscii.toString.toInt? with
      | some i => .ok i
      | none => .error s!"not a number: \"{s}\""
    match s.splitOn "/" with
    | [a] => return (← int a : Q)
    | [a, b] => do
      let d ← int b
      if d == 0 then throw s!"zero denominator: \"{s}\""
      return (← int a : Q) / d
    | _ => .error s!"not a number: \"{s}\""
  | _ => .error s!"expected a number, got {j.compress}"

#guard (readQ (.str "-169/10")).toOption == some (-169 / 10)
#guard (readQ (.num ⟨25, 1⟩)).toOption == some (5 / 2)

/-- Read one block: `up` (`"flat"`, `"edge"` or `"upright"`), `rot` (`c`, `s`) and
`center`. -/
def readPose (j : Json) : Except String KaplaCore.Pose := do
  let up ← match (j.getObjValAs? String "up").toOption.getD "flat" with
    | "flat" => pure Upright.flat
    | "edge" => pure .onEdge
    | "upright" => pure .standing
    | u => throw s!"unknown \"up\": \"{u}\""
  let center ← j.getObjValAs? (Array Json) "center"
  unless center.size == 3 do throw "\"center\" needs three numbers"
  let rot := (j.getObjVal? "rot").toOption
  let c ← match rot.bind (·.getObjVal? "c" |>.toOption) with
    | some v => readQ v
    | none => pure 1
  let s ← match rot.bind (·.getObjVal? "s" |>.toOption) with
    | some v => readQ v
    | none => pure 0
  return ⟨up, ⟨c, s⟩, ⟨← readQ center[0]!, ← readQ center[1]!, ← readQ center[2]!⟩⟩

/-- Read the steps of a blueprint (`{"steps": ...}` or `{"plan": {"steps": ...}}`). Only the
blocks and the phase are kept: grip and approach do not change the physics check. -/
def readBuildPlan (txt : String) : Except String BuildPlan := do
  let j ← Json.parse txt
  let planJ := (j.getObjVal? "plan").toOption.getD j
  let steps ← planJ.getObjValAs? (Array Json) "steps"
  let steps ← steps.toList.mapM fun st => do
    let bs ← st.getObjValAs? (Array Json) "blocks"
    return { blocks := ← bs.toList.mapM readPose,
             phase := (st.getObjValAs? String "phase").toOption.getD "" : KaplaCore.Step }
  return ⟨steps⟩

/-! ## Running the physics engine -/

/-- Default block budget: one Kapla box (K5). -/
def defaultMaxBlocks : Nat := 200

/-- One problem from the physics engine, in words. Steps and blocks count from 1 here. -/
def describe : Diagnostic → String
  | .unstable s b => s!"step {s + 1}: not shown to stand after block {b + 1} (falls, risky, or a turn the engine cannot check)"
  | .slides s c => s!"step {s + 1}: slides at contact {c + 1}"
  | .pressTips s c => s!"step {s + 1}: pressing on corner {c + 1} tips something"
  | .unreachable s => s!"step {s + 1}: may be hard to reach (warning only)"
  | .overlap i j => s!"blocks {i + 1} and {j + 1} overlap"
  | .clearance i j => s!"blocks {i + 1} and {j + 1} are too close: a 2 mm error could push them together"
  | .unevenSupports b => s!"block {b + 1} rests on supports built differently"
  | .tooManyHands s => s!"step {s + 1}: more blocks than the builder has hands"
  | .emptyStep s => s!"step {s + 1}: places no block"
  | .tooManyBlocks used limit => s!"uses {used} blocks, at most {limit} allowed"

/-- Short lines for the page notes and the terminal. -/
def physicsLines (opts : KaplaPhysics.PlanOptions) (r : PhysicsReport) : List String :=
  let clearance := if opts.clearance then "" else " (clearance not checked)"
  (if r.ok then s!"Physics (verified): well-formed and solid after every block, for 2 mm placement errors{clearance}"
   else s!"Physics (verified): not shown to be safe to build{clearance}") :: r.diagnostics.map describe

/-- Run the verified physics engine (`physicsEngine` when clearance is on). -/
def runPhysics (opts : KaplaPhysics.PlanOptions) (maxBlocks : Nat) (plan : BuildPlan) :
    PhysicsReport :=
  KaplaPhysics.coreCheck opts HumanModel.default maxBlocks plan

/-- Check a blueprint file with the verified physics engine. -/
def check (opts : KaplaPhysics.PlanOptions) (file : String) (maxBlocks : Nat) : IO UInt32 := do
  match readBuildPlan (← IO.FS.readFile file) with
  | .error e =>
    IO.eprintln s!"{file}: {e}"
    return 1
  | .ok plan =>
    let r := runPhysics opts maxBlocks plan
    IO.println s!"{file}: {plan.steps.length} steps, {plan.blockCount} blocks"
    for line in physicsLines opts r do IO.println s!"  {line}"
    return if r.ok then 0 else 1

/-- Write the page for a blueprint file, with the physics result in the notes. -/
def view (opts : KaplaPhysics.PlanOptions) (file : String) (out : String) : IO UInt32 := do
  let txt ← IO.FS.readFile file
  match KaplaWeb.parsePlan txt, readBuildPlan txt with
  | .error e, _ | _, .error e =>
    IO.eprintln s!"{file}: {e}"
    return 1
  | .ok p, .ok plan =>
    let r := runPhysics opts defaultMaxBlocks plan
    let p := { p with notes := p.notes ++ physicsLines opts r }
    IO.FS.createDirAll out
    let path := System.FilePath.mk out / "index.html"
    IO.FS.writeFile path (KaplaWeb.render p)
    IO.println s!"wrote {path} ({p.steps.length} steps, physics {if r.ok then "ok" else "not ok"})"
    return 0

/-! ## Planning with the verified physics engine -/

/-- The physics engine's answer for the blocks placed so far, in this order, for the
planner's search: they are well-formed, clear of each other (only if `opts.clearance` is on),
and solid for 2 mm placement errors. Only the whole build is checked, not every step: the
search adds one block at a time and checked the earlier builds then. The finished plan is
checked again step by step. -/
def physicsStands (opts : KaplaPhysics.PlanOptions) (bs : List KaplaPlanner.GridBlock) : Bool :=
  match KaplaPhysics.buildOf (bs.map KaplaPlanner.GridBlock.toPose) with
  | none => false
  | some b =>
    let ε := HumanModel.default.epsRel
    decide (KaplaPhysics.WellFormed b) &&
      (!opts.clearance || decide (KaplaPhysics.Clear ε b)) &&
      -- only the fast solver: the slow one runs many times on blocks that are refused anyway
      match KaplaPhysics.RobustSolver.proposeLoadsLocal ε b with
      | some ls => decide (KaplaPhysics.SolidCertificate ε b ls)
      | none => false

/-- The verified physics engine behind core's interface, with these options. -/
def physicsWith (opts : KaplaPhysics.PlanOptions) : KaplaCore.PhysicsEngine :=
  ⟨KaplaPhysics.coreCheck opts⟩

def usage : String :=
  "usage: kapla check BLUEPRINT.json [--max N] [--no-clearance]\n" ++
  "       kapla view BLUEPRINT.json [--out DIR] [--no-clearance]\n" ++
  "       kapla plan [N] [target ...] [--no-clearance]"

def main (args : List String) : IO UInt32 := do
  let opts : KaplaPhysics.PlanOptions := { clearance := !args.contains "--no-clearance" }
  match args.filter (· != "--no-clearance") with
  | ["check", file] => check opts file defaultMaxBlocks
  | ["check", file, "--max", n] =>
    match n.toNat? with
    | some n => check opts file n
    | none => IO.eprintln usage; return 64
  | ["view", file] => view opts file "out"
  | ["view", file, "--out", out] => view opts file out
  | "plan" :: rest => KaplaPlanner.demoMain (physicsStands opts) (physicsWith opts) rest
  | [] =>
    IO.println "KaplaBuilder scaffold. Components:"
    for name in [KaplaPhysics.componentName, KaplaSemantics.componentName,
                 KaplaPlanner.componentName, KaplaWeb.componentName] do
      IO.println s!"  - {name}"
    IO.println "Check a blueprint: kapla check BLUEPRINT.json [--max N] [--no-clearance]"
    IO.println "Show a blueprint:  kapla view BLUEPRINT.json [--out DIR] [--no-clearance]"
    IO.println "Planner demo:      kapla plan [N] [target ...] [--no-clearance]"
    return 0
  | _ =>
    IO.eprintln usage
    return 64
