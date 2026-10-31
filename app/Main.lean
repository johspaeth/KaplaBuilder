import KaplaPhysics
import KaplaSemantics
import KaplaPlanner
import KaplaWeb

/-!
# `kapla` — the only place where the real engines meet

```
kapla build --blocks 200 --prompt "castle" [--profile adult] [--eps-mm 3] [--out out/] [--mock]
kapla check blueprint.json [--profile child] [--blocks N]
kapla view blueprint.json [--out DIR]        # page for any blueprint (web/README.md)
```
-/

open Kapla Lean

/-- The final output of a successful build: a plan *proven* `Valid`, plus its score and
the score ceiling. -/
structure VerifiedBlueprint (H : HumanModel) (N : Nat) where
  plan : { p : BuildPlan // Physics.Valid H N p }
  cert : Physics.Certificate
  /-- A proof of the stronger `Robust` (H1/H2, translations), when one was found. -/
  robust : Option (PLift (Physics.Robust H plan.val) × Physics.RobustCertificate)
  score : ScoreReport
  bound : Bound

structure Args where
  cmd : String := "help"
  file : Option String := none
  blocks : Option Nat := none
  prompt : String := ""
  image : Option String := none
  profile : String := "adult"
  epsMM : Option Q := none
  out : String := "out"
  mock : Bool := false

partial def parseArgs (xs : List String) (a : Args := {}) : Except String Args :=
  match xs with
  | [] => .ok a
  | "--blocks" :: n :: r => match n.toNat? with
    | some n => parseArgs r { a with blocks := some n }
    | none => .error s!"--blocks expects a number, got '{n}'"
  | "--prompt" :: p :: r => parseArgs r { a with prompt := p }
  | "--image" :: p :: r => parseArgs r { a with image := some p }
  | "--profile" :: p :: r => parseArgs r { a with profile := p }
  | "--eps-mm" :: e :: r => match parseQ e with
    | .ok q => parseArgs r { a with epsMM := some q }
    | .error err => .error err
  | "--out" :: o :: r => parseArgs r { a with out := o }
  | "--mock" :: r => parseArgs r { a with mock := true }
  | x :: r =>
    if x.startsWith "--" then .error s!"unknown option {x}"
    else if a.cmd == "help" then parseArgs r { a with cmd := x }
    else parseArgs r { a with file := some x }

def usage : String := "usage:
  kapla build --blocks N --prompt TEXT [--image FILE] [--profile child|adult|expert]
              [--eps-mm E] [--out DIR] [--mock]
  kapla check BLUEPRINT.json [--profile P] [--blocks N]
  kapla serve            (planned: M7)"

def humanModel (a : Args) : Except String HumanModel := do
  let some h := HumanModel.profile? a.profile
    | throw s!"unknown profile '{a.profile}' (child, adult, expert)"
  return match a.epsMM with | some e => { h with epsRel := e } | none => h

def writeFile (dir : System.FilePath) (name : String) (content : String) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / name) content
  IO.println s!"  wrote {dir / name}"

def build (a : Args) : IO UInt32 := do
  let H ← IO.ofExcept (humanModel a)
  let some N := a.blocks | throw (IO.userError "build needs --blocks N")
  if a.prompt.isEmpty then throw (IO.userError "build needs --prompt TEXT")
  let (ph, se, pl) : PhysicsEngine × SemanticEngine × Kapla.Planner :=
    if a.mock then (Mocks.physics, Mocks.semantics, Mocks.planner)
    else (Physics.engine, Semantics.engine, Planning.planner)
  let req : Request := { prompt := a.prompt, image := a.image, blocks := N, profile := a.profile }
  IO.println s!"kapla build: '{a.prompt}', {N} blocks, profile {a.profile} \
    (physics: {ph.name}, semantics: {se.name}, planner: {pl.name})"
  let target ← se.interpret req
  let bound := se.bound target N
  IO.println s!"  target: {target.name}; score ceiling with {N} blocks at nominal size: \
    {Web.pct bound.maxScore} ({bound.verdict.describe})"
  let cands ← pl.plan { target, blocks := N, human := H, bound } ph se
  let some best := cands.head? | do IO.eprintln "  the planner found no candidate"; return 1
  IO.println s!"  {cands.length} candidates; best: {best.motif}, {best.plan.blockCount} blocks, \
    scale {Web.fmt1 best.target.unitMM.toFloat}, likeness {Web.pct best.score.score} \
    (ceiling at this scale {Web.pct (se.bound best.target N).maxScore}), \
    physics ok = {best.physics.ok}"
  let out : System.FilePath := a.out
  -- the ceiling depends on the scale the planner chose, so recompute it for that scale
  let page (c : Candidate) :=
    Web.render { request := req, human := H, bound := se.bound c.target N, candidate := c }
  if a.mock then
    writeFile out "index.html" (page best)
    writeFile out "blueprint.json" (toJson best.plan).pretty
    IO.println "  (mock engines: nothing here is verified)"
    return 0
  -- the trusted step: re-certify the chosen plan with the verified checker
  match Physics.certifyPlan H N best.plan with
  | (.ok p, cert) =>
    let vb : VerifiedBlueprint H N :=
      { plan := p, cert, robust := Physics.certifyRobustPlan H p.val,
        score := se.score best.target p.val.blocks,
        bound := se.bound best.target N }
    let cand := { best with plan := vb.plan.val, score := vb.score,
                            physics := Physics.report H N vb.plan.val }
    writeFile out "index.html" (page cand)
    writeFile out "blueprint.json" (toJson vb.plan.val).pretty
    writeFile out "certificate.json" (toJson vb.cert).compress
    if let some (_, rc) := vb.robust then
      writeFile out "robust-certificate.json" (toJson rc).compress
    writeFile out "report.json" (toJson cand).pretty
    IO.println s!"  ✓ certified: Valid {a.profile} {N} (stands after every step and under the press, no overlaps or tight gaps, \
      ≤ {H.hands} blocks per step)"
    if vb.robust.isSome then
      IO.println s!"  ✓ certified: Robust {a.profile} (every misplacement within {Web.fmt1 H.epsRel.toFloat} mm relative, \
        {Web.fmt1 H.eAbs.toFloat} mm absolute — translations)"
    else
      IO.println "  · not certified robust to placement error (only the nominal plan is guaranteed)"
    return 0
  | (.error ds, _) =>
    IO.eprintln "  ✗ no candidate passed the verified checker; writing the best attempt for debugging"
    for d in ds.take 10 do IO.eprintln s!"    - {d.describe}"
    writeFile out "index.html" (page best)
    return 2

def checkCmd (a : Args) : IO UInt32 := do
  let H ← IO.ofExcept (humanModel a)
  let some f := a.file | throw (IO.userError "check needs a blueprint file")
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile f))
  let plan : BuildPlan ← match fromJson? j with
    | .ok p => pure p
    | .error _ => IO.ofExcept (j.getObjValAs? BuildPlan "plan")
  let N := a.blocks.getD plan.blockCount
  let rep := Physics.report H N plan
  IO.println (toJson rep).pretty
  if rep.ok then
    IO.println s!"✓ Valid ({a.profile}, N = {N}) — certified by the verified checker"
    if rep.guarantees.robust then
      IO.println s!"✓ Robust ({a.profile}) — every admissible misplacement (translations) stands"
    else
      IO.println "· not certified robust to placement error"
    return 0
  else
    for d in rep.diagnostics do IO.println s!"✗ {d.describe}"
    return 1

/-- `kapla view`: the page for any blueprint file, without checking it. -/
def viewCmd (file : String) (out : String) : IO UInt32 := do
  match KaplaWeb.parsePlan (← IO.FS.readFile file) with
  | .error e => IO.eprintln s!"{file}: {e}"; return 1
  | .ok p =>
    IO.FS.createDirAll out
    let path := System.FilePath.mk out / "index.html"
    IO.FS.writeFile path (KaplaWeb.render p)
    IO.println s!"wrote {path} ({p.steps.length} steps)"
    return 0

def main (argv : List String) : IO UInt32 := do
  match argv with
  | ["view", file] => return ← viewCmd file "out"
  | ["view", file, "--out", out] => return ← viewCmd file out
  | _ => pure ()
  match parseArgs argv with
  | .error e => IO.eprintln e; IO.eprintln usage; return 64
  | .ok a =>
    try
      match a.cmd with
      | "build" => build a
      | "check" => checkCmd a
      | "serve" => IO.eprintln "kapla serve is planned for M7"; return 64
      | _ => IO.println usage; return 0
    catch e =>
      IO.eprintln s!"error: {e}"
      return 1
