import KaplaPhysics.RobustCheck
import KaplaPhysics.Solver

/-!
# KaplaPhysics.RobustSolver — **untrusted** robust certificates

Like `Solver.solvePrefix`, top down, but every contact patch is first shrunk by the margins
the robust check demands: by `κ·σ_j` on the face of the block `j` above and by `κ·(r + σ_j)`
on the face of the block below, where `σ_j` is `j`'s shift budget (fixed by then: it only
depends on the forces from the blocks resting on `j`) and `r` the misalignment bound of the
two blocks (shortest alignment path, else the drift cap `2·eAbs`).
-/

namespace Kapla.Physics.Solver

open Kapla

/-- The footprint of `b` shrunk by `κ·m` on every side (counter-clockwise), if non-empty. -/
def shrunkFoot (b : Pose) (m : Q) : Option (List Q2) :=
  let hx := b.half.x - kappa b * m
  let hy := b.half.y - kappa b * m
  if hx ≤ 0 || hy ≤ 0 then none else
    some <| [(-1, -1), (1, -1), (1, 1), (-1, 1)].map fun ((sx, sy) : Q × Q) =>
      let p := b.toWorld ⟨sx * hx, sy * hy, 0⟩
      ⟨p.x, p.y⟩

/-- Undirected alignment graph on the blocks `< n`. -/
def refAdj (refs : Array (Option Nat)) (n : Nat) : Array (List Nat) := Id.run do
  let mut adj : Array (List Nat) := Array.replicate n []
  for j in [0:n] do
    if let some i := refs.getD j none then
      if i < n then
        adj := adj.modify j (i :: ·)
        adj := adj.modify i (j :: ·)
  return adj

/-- Shortest alignment path `j → … → i` with at most `maxLen` vertices (breadth first). -/
def shortestPath (adj : Array (List Nat)) (j i maxLen : Nat) : Option (List Nat) := Id.run do
  if j = i then return some [j]
  let mut prev : Std.HashMap Nat Nat := {}
  let mut frontier : List Nat := [j]
  let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert j
  for _ in [1:maxLen] do
    let mut next : List Nat := []
    for v in frontier do
      for w in adj.getD v [] do
        unless seen.contains w do
          seen := seen.insert w
          prev := prev.insert w v
          next := w :: next
    if seen.contains i then
      let mut path := [i]
      let mut cur := i
      for _ in [0:maxLen] do
        match prev.get? cur with
        | some p => path := p :: path; cur := p
        | none => break
      return some path
    frontier := next
  return none

/-- Robust contact forces for the first `m` blocks of `arr`, or the index of a block whose
load cannot be carried with the required margins. -/
def solveRobust (H : HumanModel) (refs : Array (Option Nat)) (arr : Array Pose)
    (sup : Array (List Support)) (m : Nat) (loads : List Load := []) : Except Nat RCert := Id.run do
  let n := min m arr.size
  let adj := refAdj refs n
  let cap := 2 * H.eAbs
  -- longest path still cheaper than the drift cap
  let maxLen : Nat := if H.epsRel ≤ 0 then n else min n ((cap / H.epsRel).floor.toNat + 1)
  let rOf (j i : Nat) : Q × List Nat :=
    match shortestPath adj j i maxLen with
    | some p =>
      let r := ((p.length : Q) - 1) * H.epsRel
      if r < cap then (r, p) else (cap, [])
    | none => (cap, [])
  let mut W : Array Q := Array.replicate n Block.weight
  let mut Mx : Array Q := (arr.extract 0 n).map (·.center.x)
  let mut My : Array Q := (arr.extract 0 n).map (·.center.y)
  let mut D : Array Q := Array.replicate n 0
  for l in loads do
    if l.block < n then
      W := W.modify l.block (· + l.mag)
      Mx := Mx.modify l.block (· + l.mag * l.pt.x)
      My := My.modify l.block (· + l.mag * l.pt.y)
  let order := (List.range n).mergeSort fun i j => arr[i]!.bottomZ ≥ arr[j]!.bottomZ
  let mut rank : Array Nat := Array.replicate n 0
  let mut idx := 0
  for j in order do
    rank := rank.set! j idx
    idx := idx + 1
  let mut sigma : Array Q := Array.replicate n 0
  let mut out : Array RForce := #[]
  for j in order do
    let b := arr[j]!
    let w := W[j]!
    let σ := D[j]! / w
    sigma := sigma.set! j σ
    let P : Q2 := ⟨Mx[j]! / w, My[j]! / w⟩
    let some own := shrunkFoot b σ | return .error j
    -- shrunk patches: (lower, r, path, polygon)
    let patches : List (Option Nat × Q × List Nat × List Q2) :=
      (sup[j]!).filterMap fun s =>
        match s.lower with
        | none => some (none, 0, [], own)
        | some i =>
          if i < n then
            let (r, p) := rOf j i
            match shrunkFoot arr[i]! (r + σ) with
            | none => none
            | some lowF =>
              let poly := clipPoly own lowF
              if poly.isEmpty then none else some (some i, r, p, poly)
          else none
    let centroids : Array (Option Nat × Q × List Nat × Q2) := (patches.map fun (lo, r, p, poly) =>
      let k : Q := poly.length
      (lo, r, p, (⟨(poly.map (·.x)).sum / k, (poly.map (·.y)).sum / k⟩ : Q2))).toArray
    let corners : Array (Option Nat × Q × List Nat × Q2) :=
      (patches.flatMap fun (lo, r, p, poly) => poly.map ((lo, r, p, ·))).toArray
    let pt4 (e : Option Nat × Q × List Nat × Q2) : Q2 := e.2.2.2
    let attempt : Option (Array (Option Nat × Q × List Nat × Q2) × List (Nat × Q)) :=
      match decompose (centroids.map pt4) P with
      | some parts => some (centroids, parts)
      | none => (decompose (corners.map pt4) P).map (corners, ·)
    match attempt with
    | none => return .error j
    | some (pts, parts) =>
      let z := b.bottomZ
      for (k, frac) in parts do
        if frac > 0 then
          let (lower, r, path, v) := pts[k]!
          let mag := frac * w
          out := out.push { f := { lower, upper := j, pt := ⟨v.x, v.y, z⟩, mag }, r, path }
          if let some i := lower then
            W := W.modify i (· + mag)
            Mx := Mx.modify i (· + mag * v.x)
            My := My.modify i (· + mag * v.y)
            D := D.modify i (· + mag * (r + σ))
  return .ok { rfs := out.toList, sigma, rank }

end Kapla.Physics.Solver
