import KaplaPhysics.Spec

/-!
# KaplaPhysics.Solver — **untrusted** certificate generation

Finds contact forces for a structure. Nothing here is trusted: every force it proposes is
re-checked exactly by `certify`. A bug can only cause a rejection, never a false accept.

Method (exact, ℚ):
1. contacts: for every block, the ground or each block whose top face is at the height of
   its bottom face; the contact patch is the intersection of the two footprints
   (Sutherland–Hodgman clipping of convex polygons);
2. load paths, top down: a block carries its own weight plus the forces from the blocks on
   it. Their resultant `W` at point `P` is split onto the corners of its contact patches —
   by Carathéodory, `P` lies in the convex hull of the corners iff it lies in some triangle
   (or segment, or point) of them. We first try the centres of the patches (keeps loads
   central), then all corners, using a fan triangulation of their convex hull.

The top-down split is a heuristic: it can miss a solution that a full LP would find (when
an upper block must lean its load onto a particular support). The LP of DESIGN §6 replaces
it in M2; the checker stays the same.
-/

namespace Kapla.Physics.Solver

open Kapla

def cross (o a b : Q2) : Q := (a.x - o.x) * (b.y - o.y) - (a.y - o.y) * (b.x - o.x)

private def dedupe (ps : List Q2) : List Q2 := ps.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) []

/-- Intersection of a convex polygon with a convex counter-clockwise polygon. -/
def clipPoly (subj clip : List Q2) : List Q2 := Id.run do
  let clipA := clip.toArray
  let mut out := subj.toArray
  for i in [0:clipA.size] do
    let a := clipA[i]!
    let b := clipA[(i + 1) % clipA.size]!
    let inp := out
    out := #[]
    for j in [0:inp.size] do
      let p := inp[j]!
      let q := inp[(j + 1) % inp.size]!
      let dp := cross a b p
      let dq := cross a b q
      if dp ≥ 0 then out := out.push p
      if (dp ≥ 0) != (dq ≥ 0) then
        let t := dp / (dp - dq)
        out := out.push ⟨p.x + t * (q.x - p.x), p.y + t * (q.y - p.y)⟩
  return dedupe out.toList

/-- Convex hull (Andrew's monotone chain), counter-clockwise, without collinear points.
Returns indices into `V`. -/
def hull (V : Array Q2) : Array Nat := Id.run do
  let idx := (List.range V.size).toArray.qsort fun i j =>
    V[i]!.x < V[j]!.x || (V[i]!.x = V[j]!.x && V[i]!.y < V[j]!.y)
  -- drop duplicate points
  let idx := idx.toList.foldl (fun (acc : Array Nat) i =>
    if acc.size > 0 && V[acc.back!]! = V[i]! then acc else acc.push i) #[]
  if idx.size ≤ 2 then return idx
  let half (ord : Array Nat) : Array Nat := Id.run do
    let mut h : Array Nat := #[]
    for i in ord do
      while h.size ≥ 2 && cross V[h[h.size-2]!]! V[h[h.size-1]!]! V[i]! ≤ 0 do
        h := h.pop
      h := h.push i
    return h
  let lower := half idx
  let upper := half idx.reverse
  return lower.pop ++ upper.pop

/-- Write `P` as a non-negative combination (weights summing to 1) of points of `V`.
Returns `(index, weight)` pairs. By Carathéodory it suffices to search the triangles of a
fan triangulation of the convex hull (or a segment / point when the hull is degenerate). -/
def decompose (V : Array Q2) (P : Q2) : Option (List (Nat × Q)) := Id.run do
  let H := hull V
  if H.size = 0 then return none
  if H.size = 1 then return if V[H[0]!]! = P then some [(H[0]!, 1)] else none
  if H.size = 2 then
    let a := V[H[0]!]!; let b := V[H[1]!]!
    let len2 := (b.x - a.x) ^ 2 + (b.y - a.y) ^ 2
    if cross a b P ≠ 0 then return none
    let t := ((P.x - a.x) * (b.x - a.x) + (P.y - a.y) * (b.y - a.y)) / len2
    return if 0 ≤ t && t ≤ 1 then some [(H[0]!, 1 - t), (H[1]!, t)] else none
  let a := V[H[0]!]!
  for k in [1:H.size - 1] do
    let b := V[H[k]!]!; let c := V[H[k+1]!]!
    let d := cross a b c
    let lb := cross a P c / d
    let lc := cross a b P / d
    let la := 1 - lb - lc
    if la ≥ 0 && lb ≥ 0 && lc ≥ 0 then
      return some [(H[0]!, la), (H[k]!, lb), (H[k+1]!, lc)]
  return none

structure Support where
  lower : Option Nat
  poly : List Q2

/-- Contact patches under block `j`. -/
def supportsOf (bs : Array Pose) (byTop : Std.HashMap Q (List Nat)) (j : Nat) : List Support :=
  let b := bs[j]!
  let ground := if b.bottomZ = 0 then [{ lower := none, poly := b.footprint : Support }] else []
  let others := (byTop.getD b.bottomZ []).filterMap fun i =>
    if i = j then none else
      let poly := clipPoly b.footprint bs[i]!.footprint
      if poly.isEmpty then none else some { lower := some i, poly }
  ground ++ others


/-- Contact patches under every block of `arr` (independent of the build prefix). -/
def contacts (arr : Array Pose) : Array (List Support) := Id.run do
  let mut byTop : Std.HashMap Q (List Nat) := {}
  for h : i in [0:arr.size] do
    byTop := byTop.insert arr[i].topZ (i :: byTop.getD arr[i].topZ [])
  return (Array.range arr.size).map (supportsOf arr byTop)

/-- Contact forces for the first `m` blocks of `arr` under gravity plus `loads`, or the
index of a block whose load cannot be carried. `sup` comes from `contacts arr`. -/
def solvePrefix (arr : Array Pose) (sup : Array (List Support)) (m : Nat)
    (loads : List Load := []) : Except Nat (List PointForce) := Id.run do
  let n := min m arr.size
  -- accumulated load (weight) and first moment (Σ F·p) per block
  let mut W : Array Q := Array.replicate n Block.weight
  let mut Mx : Array Q := (arr.extract 0 n).map (·.center.x)
  let mut My : Array Q := (arr.extract 0 n).map (·.center.y)
  for l in loads do
    if l.block < n then
      W := W.modify l.block (· + l.mag)
      Mx := Mx.modify l.block (· + l.mag * l.pt.x)
      My := My.modify l.block (· + l.mag * l.pt.y)
  let order := (List.range n).mergeSort fun i j => arr[i]!.bottomZ ≥ arr[j]!.bottomZ
  let mut forces : Array PointForce := #[]
  for j in order do
    let sup := sup[j]!.filter fun s => match s.lower with | some i => i < n | none => true
    let w := W[j]!
    let P : Q2 := ⟨Mx[j]! / w, My[j]! / w⟩
    -- prefer the centres of the contact patches (keeps loads central), then their corners
    let centroids : Array (Option Nat × Q2) := (sup.map fun s =>
      let k : Q := s.poly.length
      (s.lower, (⟨(s.poly.map (·.x)).sum / k, (s.poly.map (·.y)).sum / k⟩ : Q2))).toArray
    let corners : Array (Option Nat × Q2) := (sup.flatMap fun s => s.poly.map (s.lower, ·)).toArray
    let attempt : Option (Array (Option Nat × Q2) × List (Nat × Q)) :=
      match decompose (centroids.map (·.2)) P with
      | some parts => some (centroids, parts)
      | none => (decompose (corners.map (·.2)) P).map (corners, ·)
    match attempt with
    | none => return .error j
    | some (pts, parts) =>
      let z := arr[j]!.bottomZ
      for (idx, frac) in parts do
        if frac > 0 then
          let (lower, v) := pts[idx]!
          let mag := frac * w
          forces := forces.push { lower, upper := j, pt := ⟨v.x, v.y, z⟩, mag }
          if let some i := lower then
            W := W.modify i (· + mag)
            Mx := Mx.modify i (· + mag * v.x)
            My := My.modify i (· + mag * v.y)
  return .ok forces.toList

/-- Contact forces for the whole structure `bs`. -/
def solve (bs : List Pose) (loads : List Load := []) : Except Nat (List PointForce) :=
  let arr := bs.toArray
  solvePrefix arr (contacts arr) arr.size loads

end Kapla.Physics.Solver
