import Std.Http
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
  verified physics engine and the verified scorer, and shows its plan. `--out` writes the
  plan as a blueprint for `kapla view`. The strategies `ai` and `ai-unchecked` call
  Claude and need `ANTHROPIC_API_KEY`.

* `kapla serve [--port N]` starts the website on this computer only (default port 8000). Run it
  from the top folder of the repo: saved models are in `models/`. Requests: `web/README.md`.

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

/-- A block turned by `deg` degrees, as blueprint JSON. -/
def degBlockJson (deg : Int) : Json :=
  Json.mkObj [("up", "flat"), ("rot", Json.mkObj [("deg", deg)]),
    ("center", Json.arr #[0, 0, "1/2"])]

/-- The physics engine and the viewer read a `{"deg": d}` turn as the same turn: the viewer
draws the exact turn that is checked. Tested for all 24 steps of 15°, and for negative
angles. -/
def turnsAgree (deg : Int) : Bool :=
  match readPose (degBlockJson deg), KaplaWeb.readBlock (degBlockJson deg) with
  | .ok p, .ok b => KaplaWeb.ratToFloat p.rot.cos == b.c && KaplaWeb.ratToFloat p.rot.sin == b.s
  | _, _ => false

#guard (List.range 24).all fun k => turnsAgree (15 * k)
#guard [-15, -45, -90, 360, 405].all turnsAgree

/-- The point `(x, y)` is strictly inside the rectangle the viewer draws for `b`. -/
def drawnInside (b : KaplaWeb.ViewBlock) (x y : Float) : Bool :=
  let u := b.c * (x - b.x) + b.s * (y - b.y)
  let v := -b.s * (x - b.x) + b.c * (y - b.y)
  u.abs < KaplaWeb.blockL / 2 && v.abs < KaplaWeb.blockW / 2

/-- Found in review: a flat block and one at 45°, close but not touching in the checked
geometry. With literal 45° the viewer drew them overlapping at `(7.49, -4.24)`. -/
def nearContact : String :=
  "{\"steps\":[{\"blocks\":[{\"up\":\"flat\",\"center\":[0,-4,\"1/2\"]}]}," ++
  "{\"blocks\":[{\"up\":\"flat\",\"rot\":{\"deg\":45},\"center\":[\"180/13\",0,\"1/2\"]}]}]}"

#guard match KaplaWeb.parsePlan nearContact with
  | .ok p => match p.steps with
    | [s0, s1] => match s0.blocks, s1.blocks with
      | [a], [b] => !(drawnInside a 7.49 (-4.24) && drawnInside b 7.49 (-4.24))
      | _, _ => false
    | _ => false
  | .error _ => false

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
    let req : KaplaCore.PlanRequest := { target, blocks, maxCandidates := 1 }
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

/-! ## The website

`kapla serve` answers the page's requests. Only `Site.lean` in `web/` knows what the page looks
like, and only `decode` decides what a good model is. -/

/-- The folder for saved models, from the top folder of the repo. -/
def modelsDir : System.FilePath := "models"

/-- Make a name safe to use as a file name, so a save stays inside `models/`. It keeps small letters,
digits, `-` and `_`. Capital letters become small. Anything else becomes one `-`. At most 64 letters.
With nothing left, the result is empty. -/
def cleanName (name : String) : String :=
  let mapped := name.toList.map fun c =>
    if c.isDigit || c == '_' then c
    else if c.isAlpha then c.toLower
    else '-'
  let single := mapped.foldr (init := ([] : List Char)) fun c acc =>
    match acc with
    | '-' :: _ => if c == '-' then acc else c :: acc
    | _ => c :: acc
  let edge (c : Char) := c == '-' || c == '_'
  let trim (l : List Char) := ((l.dropWhile edge).reverse.dropWhile edge).reverse
  String.ofList (trim ((trim single).take 64))

#guard cleanName "My Bunny!" == "my-bunny"
#guard cleanName "../../etc/passwd" == "etc-passwd"
#guard cleanName "a.json" == "a-json"
#guard cleanName "egg_2" == "egg_2"
#guard cleanName "..." == ""
#guard (cleanName (String.ofList (List.replicate 100 'x'))).length == 64

/-- Where a saved model with this clean name lives. -/
def modelPath (name : String) : System.FilePath := modelsDir / (name ++ ".json")

/-- The names of the saved models, in order. A file whose name is not clean is left out. -/
def listModels : IO (List String) := do
  let entries ← modelsDir.readDir
  let names := entries.toList.filterMap fun e =>
    let p := e.path
    match p.extension, p.fileStem with
    | some "json", some stem => if cleanName stem == stem then some stem else none
    | _, _ => none
  return names.toArray.qsort (· < ·) |>.toList

/-- A reply: its status and JSON text. -/
structure Reply where
  status : Std.Http.Status := .ok
  json : String

/-- A reply with one message for the person. -/
def errorReply (status : Std.Http.Status) (message : String) : Reply :=
  { status, json := (Json.mkObj [("error", Json.str message)]).compress }

/-- `GET /models` -/
def getModels : IO Reply := do
  let names ← listModels
  return { json := (Json.mkObj [("models", Json.arr (names.map Json.str).toArray)]).compress }

/-- `GET /models/NAME`: the model, after `decode` has checked the file. -/
def getModel (name : String) : IO Reply := do
  if cleanName name != name || name.isEmpty then
    return errorReply .notFound "there is no model with this name"
  let path := modelPath name
  unless ← path.pathExists do
    return errorReply .notFound "there is no model with this name"
  match KaplaSemantics.decode (← IO.FS.readFile path) with
  | .ok m => return { json := KaplaSemantics.encode m }
  | .error e => return errorReply .unprocessableEntity s!"the file is not a good model: {e}"

/-- `POST /models` with `name`, `model` and `overwrite`. The saved model takes the clean name. An
existing name is replaced only with `overwrite` true; otherwise the reply is 409. -/
def postModel (body : String) : IO Reply := do
  let parsed : Except String (String × Bool × KaplaCore.BubbleModel) := do
    let j ← KaplaSemantics.parseJson body
    let name ← (← j.getObjVal? "name").getStr?
    let overwrite := (j.getObjValAs? Bool "overwrite").toOption.getD false
    let m ← KaplaSemantics.decode (← j.getObjVal? "model").compress
    return (name, overwrite, m)
  match parsed with
  | .error e => return errorReply .badRequest s!"The model was not saved: {e}"
  | .ok (typed, overwrite, m) =>
    let name := cleanName typed
    if name.isEmpty then
      return errorReply .badRequest "Give a name with at least one letter or digit."
    let path := modelPath name
    if !overwrite && (← path.pathExists) then
      return { status := .conflict, json := (Json.mkObj [("name", Json.str name)]).compress }
    let saved := { m with name }
    -- Write a new file first, so a failed write cannot damage a saved model.
    let temp := modelsDir / s!".{name}.tmp"
    IO.FS.writeFile temp (KaplaSemantics.encodePretty saved ++ "\n")
    IO.FS.rename temp path
    return { json := (Json.mkObj [("name", Json.str name),
                                  ("model", KaplaSemantics.modelToJson saved)]).compress }

/-- Is this request from our own page? Another website open in the browser can also send requests to
this computer. The address it used (`Host`) and the page it came from (`Origin`) show that. -/
def fromOurPage (port : Nat) (host origin : Option String) : Bool :=
  let ours := [s!"localhost:{port}", s!"127.0.0.1:{port}"]
  (host.any ours.contains) && (origin.all fun o => ours.any (fun h => o == s!"http://{h}"))

#guard fromOurPage 8000 (some "localhost:8000") none
#guard fromOurPage 8000 (some "127.0.0.1:8000") (some "http://127.0.0.1:8000")
#guard !fromOurPage 8000 (some "localhost:8000") (some "https://example.com")
#guard !fromOurPage 8000 (some "example.com") none
#guard !fromOurPage 8000 none none

/-- The file that holds the API key, from the top folder of the repo. -/
def keyFile : System.FilePath := "semantics" / "dev" / ".env"

/-- `GET /status`: does the server have a key? The key itself never leaves the server. -/
def getStatus (key : Option String) : Reply :=
  { json := (Json.mkObj [("key", Json.bool key.isSome)]).compress }

/-- `POST /chat` with `text`, `messages` (the earlier conversation) and `model` (the model on screen, or
null). The answer is `reply` and `model`; `model` is null when Claude only answered. -/
def postChat (key : Option String) (body : String) : IO Reply := do
  let some key := key
    | return errorReply .serviceUnavailable
        "The API key is missing. Put it in semantics/dev/.env and start kapla serve again."
  let parsed : Except String (String × List KaplaSemantics.ChatMessage × Option KaplaCore.BubbleModel) := do
    let j ← KaplaSemantics.parseJson body
    let text ← (← j.getObjVal? "text").getStr?
    let messages ← (← (← j.getObjVal? "messages").getArr?).toList.mapM fun m => do
      let role ← (← m.getObjVal? "role").getStr?
      unless role == "user" || role == "assistant" do throw s!"unknown role {role}"
      return (⟨role, ← (← m.getObjVal? "text").getStr?⟩ : KaplaSemantics.ChatMessage)
    let model ← match j.getObjVal? "model" with
      | .ok .null | .error _ => pure none
      | .ok m => some <$> KaplaSemantics.decode m.compress
    return (text, messages, model)
  match parsed with
  | .error e => return errorReply .badRequest s!"The message was not sent: {e}"
  | .ok (text, messages, model) =>
    if text.trimAscii.isEmpty then
      return errorReply .badRequest "The message is empty."
    match ← KaplaSemantics.chat key messages model text with
    | .error e => return errorReply .badGateway e
    | .ok a =>
      return { json := (Json.mkObj
        [ ("reply", Json.str a.reply)
        , ("model", match a.model with
            | some m => KaplaSemantics.modelToJson m
            | none => .null) ]).compress }

/-! ### The proposal -/

/-- A free and fast planner for testing the page: a pile of flat blocks at the middle. It makes no
calls to Claude. -/
def standInTower : KaplaPlanner.Strategy :=
  ⟨"stand-in tower (test only)", fun req ph sem =>
    let n := min req.blocks 30
    let pose (k : Nat) : KaplaCore.Pose := ⟨.flat, .id, ⟨0, 0, (k : Q) + 1 / 2⟩⟩
    let plan : BuildPlan := ⟨(List.range n).map fun k => { blocks := [pose k] }⟩
    pure [{ plan, physics := ph.check req.human req.blocks plan
            score := sem.score req.target n plan.blocks, difficulty := default }]⟩

/-- The planners the website offers. -/
def sitePlanners : List KaplaPlanner.Strategy := standInTower :: KaplaPlanner.strategies

/-- `GET /planners` -/
def getPlanners : Reply :=
  { json := (Json.mkObj [("planners", Json.arr (sitePlanners.map (Json.str ·.name)).toArray)]).compress }

/-- How long the page waits for a planner, in seconds. -/
def plannerSeconds : Nat := 900

/-- A plan in the blueprint format of `web/README.md`, for drawing. -/
def planToViewJson (plan : BuildPlan) : Json :=
  let up : Upright → String
    | .flat => "flat" | .onEdge => "edge" | .standing => "upright"
  let num := KaplaSemantics.ratToJson
  let pose (b : KaplaCore.Pose) := Json.mkObj
    [ ("up", Json.str (up b.up))
    , ("rot", Json.mkObj [("c", num b.rot.cos), ("s", num b.rot.sin)])
    , ("center", KaplaSemantics.q3ToJson b.center) ]
  Json.mkObj [("steps", Json.arr (plan.steps.map fun st => Json.mkObj
    [ ("blocks", Json.arr (st.blocks.map pose).toArray), ("phase", Json.str st.phase) ]).toArray)]

/-- Run a planner and ask for one plan. Physics and the scorer are run here again, so the badges do not
depend on what a planner reports about itself. The height is the one the planner chose. -/
def makeProposal (s : KaplaPlanner.Strategy) (m : KaplaCore.BubbleModel) (blocks : Nat) :
    IO Json := do
  let target := KaplaCore.TargetSpec.ofBubbles m
  let candidates ← s.toPlanner.plan { target, blocks, maxCandidates := 1 }
    KaplaPhysics.physicsEngine KaplaSemantics.semanticEngine
  match candidates.head? with
  | none => return Json.mkObj [("proposal", .null)]
  | some c =>
    let opts : KaplaPhysics.PlanOptions := {}
    let physics := runPhysics opts blocks c.plan
    let score := KaplaSemantics.semanticEngine.score target c.score.height c.plan.blocks
    let view ← IO.ofExcept ((KaplaWeb.readPlan (planToViewJson c.plan)).map KaplaWeb.pageData)
    return Json.mkObj [("proposal", Json.mkObj
      [ ("view", view)
      , ("score", KaplaSemantics.reportToJson score)
      , ("stands", Json.bool physics.ok)
      , ("physics", Json.arr ((physicsLines opts c.plan physics).map Json.str).toArray) ])]

/-- `POST /plan` with `planner`, `blocks` and `model`. The answer is `proposal`, or null if the
planner made none. The page gets an answer even if a planner does not end. -/
def postPlan (body : String) : IO Reply := do
  let parsed : Except String (String × Nat × KaplaCore.BubbleModel) := do
    let j ← KaplaSemantics.parseJson body
    let planner ← (← j.getObjVal? "planner").getStr?
    let blocks ← j.getObjValAs? Nat "blocks"
    let m ← KaplaSemantics.decode (← j.getObjVal? "model").compress
    return (planner, blocks, m)
  match parsed with
  | .error e => return errorReply .badRequest s!"No proposal: {e}"
  | .ok (name, blocks, m) =>
    if blocks == 0 || blocks > defaultMaxBlocks then
      return errorReply .badRequest s!"The block limit must be a whole number from 1 to {defaultMaxBlocks}."
    let some s := sitePlanners.find? (·.name == name)
      | return errorReply .badRequest s!"There is no planner named {name}."
    let task ← IO.asTask (makeProposal s m blocks) .dedicated
    let rec wait : Nat → IO Bool
      | 0 => return false
      | n + 1 => do
        if ← IO.hasFinished task then return true
        IO.sleep 100
        wait n
    unless ← wait (plannerSeconds * 10) do
      IO.cancel task
      return errorReply .gatewayTimeout s!"The planner did not finish in {plannerSeconds / 60} minutes."
    match task.get with
    | .ok j => return { json := j.compress }
    | .error e => return errorReply .internalServerError s!"The planner stopped with an error: {e}"

/-- The biggest request we read. A model has at most 32 bubbles, so this is plenty. -/
def maxBodyBytes : UInt64 := 1024 * 1024

section Server
open Std Async
open Std Http Server

/-- The website: its port, and the API key if there is one. -/
structure Site where
  port : Nat
  key : Option String

/-- Send a reply as JSON. A browser must not keep an old list of models. -/
def sendJson (r : Reply) : ContextAsync (Response Body.Any) :=
  Response.withStatus r.status |>.header! "Cache-Control" "no-store" |>.json r.json

instance : Handler Site where
  onRequest site req := do
    let host := (req.line.headers.get? (.mk "host")).map toString
    let origin := (req.line.headers.get? (.mk "origin")).map toString
    unless fromOurPage site.port host origin do
      return ← sendJson (errorReply .forbidden "this request did not come from the Defy Gravity page")
    let path := (toString req.line.uri).takeWhile (· != '?') |>.toString
    let method := req.line.method
    let guarded (action : IO Reply) : ContextAsync (Response Body.Any) := do
      let r ← (action.toBaseIO : BaseIO _)
      match r with
      | .ok reply => sendJson reply
      | .error e =>
        IO.eprintln s!"{path}: {e}"
        sendJson (errorReply .internalServerError s!"The server could not do this: {e}")
    if method == .get && path == "/" then
      Response.ok |>.header! "Cache-Control" "no-store" |>.html KaplaWeb.sitePage
    else if method == .get && path == "/status" then
      sendJson (getStatus site.key)
    else if method == .post && path == "/chat" then
      try
        let body : String ← req.body.readAll (maximumSize := some maxBodyBytes)
        guarded (postChat site.key body)
      catch e =>
        sendJson (errorReply .badRequest s!"The message was not sent: could not read it: {e}")
    else if method == .get && path == "/planners" then
      sendJson getPlanners
    else if method == .post && path == "/plan" then
      try
        let body : String ← req.body.readAll (maximumSize := some maxBodyBytes)
        guarded (postPlan body)
      catch e =>
        sendJson (errorReply .badRequest s!"No proposal: could not read the request: {e}")
    else if method == .get && path == "/models" then
      guarded getModels
    else if method == .get && path.startsWith "/models/" then
      guarded (getModel (path.drop "/models/".length).toString)
    else if method == .post && path == "/models" then
      try
        let body : String ← req.body.readAll (maximumSize := some maxBodyBytes)
        guarded (postModel body)
      catch e =>
        sendJson (errorReply .badRequest s!"The model was not saved: could not read it: {e}")
    else
      sendJson (errorReply .notFound "no such page")

/-- Start the website and keep it running. -/
def serve (port : Nat) : IO UInt32 := do
  unless ← modelsDir.isDir do
    IO.eprintln "No models/ folder here. Run this from the top folder of the repo."
    return 1
  let key ← KaplaSemantics.loadApiKey keyFile
  -- The AI planners read the key from the environment, and Lean cannot change the environment of a
  -- running program. So start this program again once, with the key set.
  if let some k := key then
    if (← IO.getEnv "ANTHROPIC_API_KEY") != some k then
      let child ← IO.Process.spawn
        { cmd := ← IO.appPath |>.map toString, args := #["serve", "--port", toString port]
          env := #[("ANTHROPIC_API_KEY", some k)] }
      return ← child.wait
  if key.isNone then
    IO.println "No API key in semantics/dev/.env, so the chat will not work. The rest of the site does."
  try
    Async.block do
      let addr : Net.SocketAddress := .v4 ⟨.ofParts 127 0 0 1, port.toUInt16⟩
      let server ← Server.serve addr (Site.mk port key)
      IO.println s!"Defy Gravity is running. Open http://localhost:{port}"
      (← IO.getStdout).flush
      server.waitShutdown
    return 0
  catch e =>
    IO.eprintln s!"Could not start on port {port}: {e}"
    IO.eprintln "If another program uses this port, try: lake exe kapla serve --port 8001"
    return 1

end Server

def usage : String :=
  "usage: kapla check BLUEPRINT.json [--max N] [--no-clearance]\n" ++
  "       kapla view BLUEPRINT.json [--out DIR] [--no-clearance]\n" ++
  "       kapla plan [--blocks N] [--strategy NAME] [--target MODEL.json] [--out BLUEPRINT.json]\n" ++
  "       kapla serve [--port N]"

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
  | ["serve"] => serve 8000
  | ["serve", "--port", n] =>
    match n.toNat? with
    | some n =>
      if n == 0 || n > 65535 then
        IO.eprintln usage
        return 64
      serve n
    | none => IO.eprintln usage; return 64
  | [] =>
    IO.println "KaplaBuilder scaffold. Components:"
    for name in [KaplaPhysics.componentName, KaplaSemantics.componentName,
                 KaplaPlanner.componentName, KaplaWeb.componentName] do
      IO.println s!"  - {name}"
    IO.println "Check a blueprint: kapla check BLUEPRINT.json [--max N] [--no-clearance]"
    IO.println "Show a blueprint:  kapla view BLUEPRINT.json [--out DIR] [--no-clearance]"
    IO.println "Start the website: kapla serve [--port N]"
    return 0
  | _ =>
    IO.eprintln usage
    return 64
