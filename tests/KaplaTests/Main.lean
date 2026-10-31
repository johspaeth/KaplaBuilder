import KaplaPhysics
import KaplaSemantics
import KaplaPlanner
import KaplaWeb

/-!
# Contract tests (`lake test`)

* JSON round trips of the fixture plans and targets;
* the verified checker reproduces `fixtures/physics_expected/` exactly;
* semantics, planner and renderer smoke tests (real engines and mocks).
-/

open Kapla Lean

structure Ctx where
  failures : IO.Ref Nat
  total : IO.Ref Nat

def expect (c : Ctx) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  c.total.modify (· + 1)
  if ok then IO.println s!"  ok    {name}"
  else
    c.failures.modify (· + 1)
    IO.println s!"  FAIL  {name} {detail}"

def readJson (p : System.FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile p))

def jsonFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let es ← dir.readDir
  return (es.toList.map (·.path) |>.filter (·.extension == some "json")).mergeSort
    (fun a b => a.toString ≤ b.toString)

def testRationals (c : Ctx) : IO Unit := do
  IO.println "rationals"
  expect c "\"117/5\" parses exactly" (parseQ "117/5" == .ok (117/5))
  expect c "23.4 (JSON number) parses exactly" ((fromJson? (Json.parse "23.4" |>.toOption.get!) : Except String Q) == .ok (117/5))
  expect c "rational JSON round trip" ((fromJson? (toJson (-39/10 : Q)) : Except String Q) == .ok (-39/10))
  let r := Rot.approxDeg 30
  expect c "approxDeg 30 is within 0.1°" ((r.toDeg - 30).abs < 0.1)
  expect c "non-orthogonal rotation is rejected"
    ((fromJson? (Json.parse "{\"c\": 1, \"s\": 1}" |>.toOption.get!) : Except String Rot) matches .error _)

def testPhysics (c : Ctx) : IO Unit := do
  IO.println "physics (verified checker vs fixtures/physics_expected)"
  for f in ← jsonFiles "fixtures/physics_expected" do
    let j ← readJson f
    let name ← IO.ofExcept (j.getObjValAs? String "plan")
    let prof ← IO.ofExcept (j.getObjValAs? String "profile")
    let n ← IO.ofExcept (j.getObjValAs? Nat "blocks")
    let ok ← IO.ofExcept (j.getObjValAs? Bool "ok")
    let ds ← IO.ofExcept (j.getObjValAs? (List Diagnostic) "diagnostics")
    let robust := (j.getObjValAs? Bool "robust").toOption.getD false
    let plan : BuildPlan ← IO.ofExcept (fromJson? (← readJson s!"fixtures/plans/{name}.json"))
    let H := (HumanModel.profile? prof).get!
    let rep := Physics.report H n plan
    expect c s!"{f.fileStem.getD ""}" (rep.ok == ok && rep.diagnostics == ds)
      s!"got ok={rep.ok} {repr rep.diagnostics}"
    expect c s!"{f.fileStem.getD ""} robust = {robust}" (rep.guarantees.robust == robust)
      s!"got robust={rep.guarantees.robust}"
    if robust then
      expect c s!"{f.fileStem.getD ""} proves Robust" (Physics.certifyRobustPlan H plan).isSome
    -- an accepted plan must also come with a proof-carrying value
    if ok then
      expect c s!"{f.fileStem.getD ""} certifies" ((Physics.certifyPlan H n plan).1 matches .ok _)

def testRoundTrips (c : Ctx) : IO Unit := do
  IO.println "JSON round trips"
  for f in ← jsonFiles "fixtures/plans" do
    let p : BuildPlan ← IO.ofExcept (fromJson? (← readJson f))
    expect c s!"plan {f.fileStem.getD ""}" ((fromJson? (toJson p) : Except String BuildPlan) == .ok p)
  for f in ← jsonFiles "fixtures/targets" do
    let t : Except String TargetSpec := fromJson? (← readJson f)
    expect c s!"target {f.fileStem.getD ""}" (t matches .ok _)

def testSemantics (c : Ctx) : IO Unit := do
  IO.println "semantics"
  let tree := (Semantics.lookupTarget "tree").get!
  let trunkOnly := Semantics.scoreBlocks tree [Planning.uprightAt 0 0]
  expect c "one upright block scores > 0 against the tree" (trunkOnly.score > 0)
  expect c "score ≤ ceiling (tree, N = 1)" (trunkOnly.score ≤ (Semantics.boundFor tree 1).maxScore)
  let box : TargetSpec := { name := "slab", shape := .box 117 (117/5) (39/5) }
  let exact := Semantics.scoreBlocks box [{ up := .flat, rot := Rot.id, center := ⟨0, 0, 39/10⟩ }]
  expect c "a block matching its own box has IoU 1" (exact.iou == 1) s!"{exact.iou}"
  expect c "verdict bands" (Verdict.ofScore (7/10) == .good && Verdict.ofScore (1/10) == .symbolic)

def testPlanner (c : Ctx) : IO Unit := do
  IO.println "planner (real engines)"
  for (prompt, n) in [("tower", 12), ("tree", 1), ("wall", 20)] do
    let t := (Semantics.lookupTarget prompt).get!
    let req : PlanRequest :=
      { target := t, blocks := n, human := HumanModel.adult, bound := Semantics.boundFor t n }
    let cands ← Planning.planner.plan req Physics.engine Semantics.engine
    match cands.head? with
    | none => expect c s!"{prompt}@{n}: a candidate" false
    | some best =>
      expect c s!"{prompt}@{n}: best candidate certified, ≤ {n} blocks"
        (best.physics.ok && best.plan.blockCount ≤ n &&
          (Physics.certifyPlan .adult n best.plan).1 matches .ok _)

def testMocksAndWeb (c : Ctx) : IO Unit := do
  IO.println "mocks + web"
  let req : Request := { prompt := "mock tower", blocks := 6 }
  let t ← Mocks.semantics.interpret req
  let preq : PlanRequest :=
    { target := t, blocks := 6, human := HumanModel.adult, bound := Mocks.semantics.bound t 6 }
  let cands ← Mocks.planner.plan preq Mocks.physics Mocks.semantics
  expect c "mock planner returns a candidate" (!cands.isEmpty)
  let some cand := cands.head? | return
  expect c "mock physics accepts the mock stack" cand.physics.ok
  let html := Web.render { request := req, human := .adult, bound := Mocks.semantics.bound t 6,
                           candidate := cand }
  expect c "page renders with data and three.js" ((html.splitOn "const DATA").length == 2 &&
    (html.splitOn "three@0.128.0").length > 1)
  expect c "mock page never claims verified" ((html.splitOn "verified: stands").length == 1)
  let evil : Request := { req with prompt := "<b>x</b>" }
  let evilPage := Web.render
    { request := evil, human := HumanModel.adult, bound := Mocks.semantics.bound t 6, candidate := cand }
  expect c "page escapes the prompt" ((evilPage.splitOn "<b>x</b>").length == 1)

def main : IO UInt32 := do
  let c : Ctx := { failures := ← IO.mkRef 0, total := ← IO.mkRef 0 }
  testRationals c
  testRoundTrips c
  testPhysics c
  testSemantics c
  testMocksAndWeb c
  testPlanner c
  let f ← c.failures.get
  IO.println s!"\n{(← c.total.get) - f} passed, {f} failed"
  return if f = 0 then 0 else 1
