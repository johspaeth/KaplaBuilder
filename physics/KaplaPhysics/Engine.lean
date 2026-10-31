import KaplaPhysics.Checker
import KaplaPhysics.Solver
import KaplaPhysics.RobustSolver

/-!
# KaplaPhysics.Engine — `PhysicsEngine` implementation

`check` = untrusted solver → verified `certify`. The report says `ok` **only** when
`certify` produced a proof of `Valid`; the solver can only make it say `ok` less often.
-/

namespace Kapla.Physics

open Kapla

/-- Common points of touching blocks (untrusted search): corners of either block and the
corners of their horizontal contact patch. Only pairs not already cleared by the grown-box
separating-axis test need one. -/
def touchWitnesses (H : HumanModel) (arr : Array Pose) (sup : Array (List Solver.Support)) :
    TouchWitnesses := Id.run do
  let mut out : TouchWitnesses := Array.replicate arr.size []
  for j in [0:arr.size] do
    let b := arr[j]!
    for i in [0:j] do
      let a := arr[i]!
      if decide (SeparatedG (H.clear / 2) a b) then continue
      let patch (lowerOf upper : Nat) : List Q3 :=
        (sup.getD upper []).flatMap fun s =>
          if s.lower = some lowerOf then s.poly.map fun q => ⟨q.x, q.y, arr[upper]!.bottomZ⟩ else []
      let cands := a.corners ++ b.corners ++ patch i j ++ patch j i
      match cands.find? fun p => decide (a.Mem p) && decide (b.Mem p) with
      | some p => out := out.modify j ((i, p) :: ·)
      | none => pure ()
  return out

/-- Run the solver on every prefix, with and without the builder's press. A prefix it cannot
solve gets an empty force list (so `certify` rejects it), and the failing block is
remembered as a diagnostic hint. -/
def buildCertificate (H : HumanModel) (plan : BuildPlan) : Certificate × List Diagnostic := Id.run do
  let arr := plan.blocks.toArray
  let sup := Solver.contacts arr
  let mut forces : Array (List PointForce) := #[]
  let mut press : Array (List (List (List PointForce))) := #[]
  let mut hints : List Diagnostic := []
  let mut start := 0
  for k in [0:plan.steps.length] do
    let n := (plan.steps.getD k default).blocks.length
    let m := start + n
    -- after the first failure the certificate is rejected anyway: skip the remaining work
    unless hints.isEmpty do
      forces := forces.push []
      press := press.push []
      start := m
      continue
    match Solver.solvePrefix arr sup m with
    | .ok fs => forces := forces.push fs
    | .error b =>
      forces := forces.push []
      hints := hints ++ [.unstable k b]
    let mut perBlock : Array (List (List PointForce)) := #[]
    for t in [0:n] do
      let i := start + t
      let mut perCorner : Array (List PointForce) := #[]
      for j in [0:4] do
        if hj : j < 4 then
          let c := topCorner arr[i]! ⟨j, hj⟩
          match Solver.solvePrefix arr sup m [pressLoad H i c] with
          | .ok fs => perCorner := perCorner.push fs
          | .error _ =>
            perCorner := perCorner.push []
            if hints.isEmpty then hints := hints ++ [.pressTips k (4 * t + j)]
      perBlock := perBlock.push perCorner.toList
    press := press.push perBlock.toList
    start := m
  return ({ forces := forces.toList, press := press.toList, touch := touchWitnesses H arr sup },
    hints)

/-- Robust certificates for every step and pressed corner, or the first `(step, block)` the
robust solver cannot carry with the margins that placement error demands. -/
def buildRobustCertificate (H : HumanModel) (plan : BuildPlan) :
    Except (Nat × Nat) RobustCertificate := Id.run do
  let arr := plan.blocks.toArray
  let sup := Solver.contacts arr
  let refs := plan.refs.toArray
  let mut steps : Array RCert := #[]
  let mut press : Array (List (List RCert)) := #[]
  let mut start := 0
  for k in [0:plan.steps.length] do
    let n := (plan.steps.getD k default).blocks.length
    let m := start + n
    match Solver.solveRobust H refs arr sup m with
    | .ok c => steps := steps.push c
    | .error b => return .error (k, b)
    let mut perBlock : Array (List RCert) := #[]
    for t in [0:n] do
      let i := start + t
      let mut perCorner : Array RCert := #[]
      for j in [0:4] do
        if hj : j < 4 then
          match Solver.solveRobust H refs arr sup m [pressLoad H i (topCorner arr[i]! ⟨j, hj⟩)] with
          | .ok c => perCorner := perCorner.push c
          | .error b => return .error (k, b)
      perBlock := perBlock.push perCorner.toList
    press := press.push perBlock.toList
    start := m
  return .ok { steps := steps.toList, press := press.toList }

/-- Try to prove `Robust H plan` (H1/H2, translations). `none` = only the nominal guarantees
hold (or could not be certified). -/
def certifyRobustPlan (H : HumanModel) (plan : BuildPlan) :
    Option (PLift (Robust H plan) × RobustCertificate) :=
  match buildRobustCertificate H plan with
  | .error _ => none
  | .ok rc => (certifyRobust H plan rc).map (·, rc)

/-- Unsupported features are rejected up front so a report never overclaims. -/
def unsupportedFeatures (_plan : BuildPlan) : List Diagnostic := []

/-- The guarantees established so far (see `Valid`). -/
def engineGuarantees : Guarantees :=
  { equilibriumEveryStep := true, nonOverlap := true, handsPerStep := true, press := true,
    clearance := true }

/-- Certify a plan, returning the proof-carrying plan or diagnostics. -/
def certifyPlan (H : HumanModel) (N : Nat) (plan : BuildPlan) :
    Except (List Diagnostic) { p : BuildPlan // Valid H N p } × Certificate :=
  let (cert, hints) := buildCertificate H plan
  match certify H N plan cert with
  | .ok p => (.ok p, cert)
  | .error ds =>
    -- prefer the solver's precise "which block fails first" hint for instability
    let isStab : Diagnostic → Bool := fun | .unstable _ _ | .pressTips _ _ => true | _ => false
    let structural := ds.filter (!isStab ·)
    let unstable := if hints.isEmpty then ds.filter isStab else hints.take 1
    (.error (structural ++ unstable), cert)

def report (H : HumanModel) (N : Nat) (plan : BuildPlan) : PhysicsReport :=
  match (certifyPlan H N plan).1 with
  | .ok _ =>
    let robust := (certifyRobustPlan H plan).isSome
    { ok := true, engine := "verified-m2a", verified := true,
      guarantees := { engineGuarantees with robust } }
  | .error ds => { ok := false, diagnostics := ds, engine := "verified-m2a", verified := true,
                   guarantees := engineGuarantees }

/-- The real physics engine (M1). -/
def engine : PhysicsEngine where
  name := "verified-m2a"
  check := report

end Kapla.Physics
