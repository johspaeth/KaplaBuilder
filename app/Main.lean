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

* `kapla plan [--blocks N] [--strategy NAME] [--target MODEL.json] [--out BLUEPRINT.json]`
  runs a planner strategy (default `empty`) on a bubble model (default: the egg), with the
  verified physics engine and the verified scorer, and lists the candidates. `--out` writes the
  best candidate as a blueprint for `kapla view`. The strategies `ai` and `ai-unchecked` call
  Claude and need `ANTHROPIC_API_KEY`.

By default the engine also asks that a 3.9 mm error can never close a gap between two
blocks, and that no block goes into a slot exactly its own width. `--no-clearance` turns
these two checks off. Blocks that touch in the plan (side by side, end to end, one on
another) are fine either way.
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

/-- Read one block: `up` (`"flat"`, `"edge"` or `"upright"`), `rot` and `center`. The turn
is either `{"deg": d}` with `d` a multiple of 15 (B6), or the exact cosine and sine
`{"c": c, "s": s}`. -/
def readPose (j : Json) : Except String KaplaCore.Pose := do
  let up ← match (j.getObjValAs? String "up").toOption.getD "flat" with
    | "flat" => pure Upright.flat
    | "edge" => pure .onEdge
    | "upright" => pure .standing
    | u => throw s!"unknown \"up\": \"{u}\""
  let center ← j.getObjValAs? (Array Json) "center"
  unless center.size == 3 do throw "\"center\" needs three numbers"
  let rot := (j.getObjVal? "rot").toOption
  let r ← match rot.bind (·.getObjVal? "deg" |>.toOption) with
    | some d => do
      let k := (← readQ d) / 15
      unless k.den == 1 do throw s!"\"deg\" must be a multiple of 15, got {d.compress}"
      pure (Rot.step15 (k.num % 24).toNat)
    | none => do
      let c ← match rot.bind (·.getObjVal? "c" |>.toOption) with
        | some v => readQ v
        | none => pure 1
      let s ← match rot.bind (·.getObjVal? "s" |>.toOption) with
        | some v => readQ v
        | none => pure 0
      pure ⟨c, s⟩
  return ⟨up, r, ⟨← readQ center[0]!, ← readQ center[1]!, ← readQ center[2]!⟩⟩

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
  | .unreachable s => s!"step {s + 1}: may be hard to reach (warning only)"
  | .overlap i j => s!"blocks {i + 1} and {j + 1} overlap"
  | .clearance i j => s!"blocks {i + 1} and {j + 1} have a small gap: a 3.9 mm error could close it"
  | .tightSlot s => s!"step {s + 1}: the block goes into a slot exactly its own width; a 3.9 mm error could close it"
  | .unevenSupports b => s!"block {b + 1} rests on supports built differently"
  | .tooManyHands s => s!"step {s + 1}: more blocks than the builder has hands"
  | .emptyStep s => s!"step {s + 1}: places no block"
  | .tooManyBlocks used limit => s!"uses {used} blocks, at most {limit} allowed"

/-- The plan has a block turned by a 15° step that is not a quarter turn (B6). Such plans
are checked at the planned positions only. -/
def hasTurnedBlocks (plan : BuildPlan) : Bool :=
  (KaplaPhysics.buildOf plan.blocks).isNone && (KaplaPhysics.turnedBuildOf plan.blocks).isSome

/-- Short lines for the page notes and the terminal. -/
def physicsLines (opts : KaplaPhysics.PlanOptions) (plan : BuildPlan) (r : PhysicsReport) :
    List String :=
  let first :=
    if hasTurnedBlocks plan then
      if r.ok then "Physics (verified): well-formed and stands after every block, at the planned positions (turned blocks: placement errors, gaps and reach not checked)"
      else "Physics (verified): not shown to stand at the planned positions (turned blocks)"
    else
      let clearance := if opts.clearance then "" else " (small gaps and tight slots not checked)"
      if r.ok then s!"Physics (verified): well-formed and solid after every block, for 3.9 mm placement errors{clearance}"
      else s!"Physics (verified): not shown to be safe to build{clearance}"
  first :: r.diagnostics.map describe

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
    for line in physicsLines opts plan r do IO.println s!"  {line}"
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
    let p := { p with notes := p.notes ++ physicsLines opts plan r }
    IO.FS.createDirAll out
    let path := System.FilePath.mk out / "index.html"
    IO.FS.writeFile path (KaplaWeb.render p)
    IO.println s!"wrote {path} ({p.steps.length} steps, physics {if r.ok then "ok" else "not ok"})"
    return 0

/-! ## Running the planner -/

/-- A plan as a blueprint file (`web/README.md`), with the target's bubbles at the plan's
height. Numbers are exact fractions in strings. -/
def blueprintJson (title : String) (target : KaplaCore.TargetSpec) (c : KaplaCore.Candidate) :
    Json :=
  let q (x : Q) : Json := Json.str (KaplaPlanner.showQ x)
  let upName : Upright → String
    | .flat => "flat"
    | .onEdge => "edge"
    | .standing => "upright"
  let pose (p : KaplaCore.Pose) : Json := Json.mkObj
    [ ("up", upName p.up)
    , ("rot", Json.mkObj [("c", q p.rot.cos), ("s", q p.rot.sin)])
    , ("center", Json.arr #[q p.center.x, q p.center.y, q p.center.z]) ]
  let bubble (b : KaplaCore.Bubble) : Json :=
    let b := b.place c.score.height
    Json.mkObj
      [ ("label", b.label)
      , ("center", Json.arr #[q b.center.x, q b.center.y, q b.center.z])
      , ("semi", Json.arr #[q b.semi.x, q b.semi.y, q b.semi.z]) ]
  Json.mkObj
    [ ("title", title)
    , ("subtitle", s!"{c.plan.blockCount} blocks, height {KaplaPlanner.showQ c.score.height}")
    , ("bubbles", Json.arr (target.model.bubbles.map bubble).toArray)
    , ("plan", Json.mkObj [("steps", Json.arr (c.plan.steps.map fun st =>
        Json.mkObj [("blocks", Json.arr (st.blocks.map pose).toArray)]).toArray)]) ]

/-- Run a planner strategy on a target and list its candidates. -/
def plan (name : String) (blocks : Nat) (targetFile out : Option String) : IO UInt32 := do
  match KaplaPlanner.strategyByName? name with
  | none =>
    IO.eprintln s!"unknown strategy \"{name}\"; known: {KaplaPlanner.strategies.map (·.name)}"
    return 64
  | some s =>
    let target ← match targetFile with
      | none => pure (some KaplaCore.TargetSpec.egg)
      | some file => do
        match KaplaSemantics.decode (← IO.FS.readFile file) with
        | .ok m => pure (some (KaplaCore.TargetSpec.ofBubbles m))
        | .error e => IO.eprintln s!"{file}: {e}"; pure none
    let some target := target | return 1
    let req : KaplaCore.PlanRequest := { target, blocks }
    let cands ← s.toPlanner.plan req KaplaPhysics.physicsEngine KaplaSemantics.semanticEngine
    IO.println s!"strategy {s.name}: {cands.length} candidates"
    for c in cands do
      let physics := if c.physics.ok then "physics ok (verified)"
        else if c.physics.diagnostics.isEmpty then "physics not checked"
        else "physics not ok"
      IO.println s!"  {c.plan.blockCount} blocks, height {KaplaPlanner.showQ c.score.height}, score {KaplaPlanner.showScore c.score.score}, {physics}"
    match out, cands with
    | some path, c :: _ =>
      if let some dir := (System.FilePath.mk path).parent then IO.FS.createDirAll dir
      IO.FS.writeFile path (blueprintJson s!"{target.model.name} ({s.name})" target c).pretty
      IO.println s!"wrote {path}"
    | _, _ => pure ()
    return 0

def usage : String :=
  "usage: kapla check BLUEPRINT.json [--max N] [--no-clearance]\n" ++
  "       kapla view BLUEPRINT.json [--out DIR] [--no-clearance]\n" ++
  "       kapla plan [--blocks N] [--strategy NAME] [--target MODEL.json] [--out BLUEPRINT.json]"

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
  | "plan" :: rest =>
    let rec go (name : String) (blocks : Nat) (target out : Option String) :
        List String → IO UInt32
      | [] => plan name blocks target out
      | "--strategy" :: n :: r => go n blocks target out r
      | "--target" :: f :: r => go name blocks (some f) out r
      | "--out" :: f :: r => go name blocks target (some f) r
      | "--blocks" :: n :: r => match n.toNat? with
        | some n => go name n target out r
        | none => do IO.eprintln usage; return 64
      | _ => do IO.eprintln usage; return 64
    go "empty" defaultMaxBlocks none none rest
  | [] =>
    IO.println "KaplaBuilder scaffold. Components:"
    for name in [KaplaPhysics.componentName, KaplaSemantics.componentName,
                 KaplaPlanner.componentName, KaplaWeb.componentName] do
      IO.println s!"  - {name}"
    IO.println "Check a blueprint: kapla check BLUEPRINT.json [--max N] [--no-clearance]"
    IO.println "Show a blueprint:  kapla view BLUEPRINT.json [--out DIR] [--no-clearance]"
    return 0
  | _ =>
    IO.eprintln usage
    return 64
