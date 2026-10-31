import KaplaCore.Engine

/-! # Mock engines

Simple stand-ins so that each component can be developed alone. They are **not**
verified and **not** the real rules. They are deliberately simple and more forgiving than
the real engines.

- `physicsMock`: blocks must not overlap, and after **every step** each block must be held
  up: the load on it must act over its support. Loads are split equally between supports.
  It ignores hand error, the press of placing, hand access and friction.
- `semanticMock`: volume IoU of the blocks against the target's part boxes. It tries three scales (target as high, as wide or as deep as the blocks) and keeps
  the best. -/

namespace KaplaCore

/-! ## Physics mock -/

namespace PhysicsMock

/-- The overlap of two closed intervals has positive length. -/
def overlaps (a1 a2 b1 b2 : Q) : Bool := max a1 b1 < min a2 b2

/-- The two boxes share some volume. -/
def boxesOverlap (a b : Box) : Bool :=
  overlaps a.lo.x a.hi.x b.lo.x b.hi.x && overlaps a.lo.y a.hi.y b.lo.y b.hi.y &&
  overlaps a.lo.z a.hi.z b.lo.z b.hi.z

/-- `upper` rests on `lower`: the bottom of one is the top of the other, and their
footprints share some area. -/
def restsOn (upper lower : Box) : Bool :=
  upper.lo.z == lower.hi.z && overlaps upper.lo.x upper.hi.x lower.lo.x lower.hi.x &&
  overlaps upper.lo.y upper.hi.y lower.lo.y lower.hi.y

/-- The area where `upper` touches `lower`, as a flat box at the contact height. -/
def contact (upper lower : Box) : Box :=
  ⟨⟨max upper.lo.x lower.lo.x, max upper.lo.y lower.lo.y, upper.lo.z⟩,
   ⟨min upper.hi.x lower.hi.x, min upper.hi.y lower.hi.y, upper.lo.z⟩⟩

/-- How load flows down when only the first `n` blocks are built. For each block: its total
load (its own weight 1 plus what rests on it) and the point (x, y) where that load acts.
A block with one support passes its load point on unchanged. A block with several supports
splits its load equally, acting at the centre of each contact. (This is a rough rule; the
real engine solves for the forces.) `above[j]` and `below[j]` list the blocks that rest on
`j` and that `j` rests on. -/
def loads (boxes : Array Box) (centers : Array Q3) (above below : Array (List Nat)) (n : Nat) :
    Array (Q × Q × Q) := Id.run do
  let mut res : Array (Q × Q × Q) := centers.map fun c => (1, c.x, c.y)
  -- top-down: a block's bottom is higher than the bottom of everything it rests on
  let order := (List.range n).mergeSort fun i j => boxes[i]!.lo.z ≥ boxes[j]!.lo.z
  for i in order do
    let mut w : Q := 1
    let mut mx : Q := centers[i]!.x
    let mut my : Q := centers[i]!.y
    for u in above[i]!.filter (· < n) do
      let (wu, ux, uy) := res[u]!
      let k := (below[u]!.filter (· < n)).length
      if k == 1 then
        w := w + wu; mx := mx + wu * ux; my := my + wu * uy
      else
        let c := contact boxes[u]! boxes[i]!
        let share := wu / (k : Q)
        w := w + share
        mx := mx + share * (c.lo.x + c.hi.x) / 2
        my := my + share * (c.lo.y + c.hi.y) / 2
    res := res.set! i (w, mx / w, my / w)
  return res

/-- Is block `i` held up when only the first `n` blocks are built? Its load point must lie
over the box around the places where it touches its supports (or the ground). -/
def heldUp (boxes : Array Box) (below : Array (List Nat)) (load : Array (Q × Q × Q))
    (n i : Nat) : Bool :=
  let b := boxes[i]!
  let support : Option Box :=
    if b.lo.z == 0 then some b
    else Box.joinAll ((below[i]!.filter (· < n)).map fun j => contact b boxes[j]!)
  match support with
  | none => false
  | some s =>
    let (_, cx, cy) := load[i]!
    s.lo.x ≤ cx && cx ≤ s.hi.x && s.lo.y ≤ cy && cy ≤ s.hi.y

/-- The mock check. -/
def check (h : HumanModel) (maxBlocks : Nat) (plan : BuildPlan) : PhysicsReport := Id.run do
  let poses := plan.blocks.toArray
  let boxes := poses.map Pose.box
  let centers := poses.map (·.center)
  let n := poses.size
  let mut diags : Array Diagnostic := #[]
  if n > maxBlocks then diags := diags.push (.tooManyBlocks n maxBlocks)
  for (st, k) in plan.steps.zipIdx do
    if st.blocks.isEmpty then diags := diags.push (.emptyStep k)
    if st.blocks.length > h.hands then diags := diags.push (.tooManyHands k)
  for i in [0:n] do
    for j in [i + 1:n] do
      if boxesOverlap boxes[i]! boxes[j]! then diags := diags.push (.overlap i j)
  -- who rests on whom (the same for every step; a step sees only the blocks built so far)
  let mut above : Array (List Nat) := Array.replicate n []
  let mut below : Array (List Nat) := Array.replicate n []
  for i in [0:n] do
    for j in [0:n] do
      if i != j && restsOn boxes[i]! boxes[j]! then
        above := above.modify j (i :: ·)
        below := below.modify i (j :: ·)
  -- after each step, check every block built so far. Stop at the first step that fails.
  let mut built := 0
  for (st, k) in plan.steps.zipIdx do
    built := built + st.blocks.length
    let load := loads boxes centers above below built
    let bad := (List.range built).filter fun i => !heldUp boxes below load built i
    if !bad.isEmpty then
      for i in bad do diags := diags.push (.unstable k i)
      break
  return { ok := diags.isEmpty, diagnostics := diags.toList }

end PhysicsMock

/-- The mock physics engine. Not verified; see the top of this file. -/
def physicsMock : PhysicsEngine := ⟨PhysicsMock.check⟩

/-- Helper for examples: a flat block whose lowest corner is at `(x, y, z)`. -/
def flatAt (x y z : Q) (turned : Bool := false) : Pose :=
  if turned then ⟨.flat, .quarter, ⟨x + blockWidth / 2, y + blockLength / 2, z + blockThickness / 2⟩⟩
  else ⟨.flat, .id, ⟨x + blockLength / 2, y + blockWidth / 2, z + blockThickness / 2⟩⟩

/-- One block per step. -/
def BuildPlan.ofBlocks (bs : List Pose) : BuildPlan := ⟨bs.map fun b => { blocks := [b] }⟩

private def t : Q := blockThickness

-- a stack of three blocks stands
#guard (physicsMock.check .adult 10 (.ofBlocks [flatAt 0 0 0, flatAt 0 0 t, flatAt 0 0 (2*t)])).ok
-- a block floating in the air falls
#guard (physicsMock.check .adult 10 (.ofBlocks [flatAt 0 0 t])).diagnostics == [.unstable 0 0]
-- an overhang of 3/4 of a block tips
#guard (physicsMock.check .adult 10 (.ofBlocks [flatAt 0 0 0, flatAt 90 0 t])).diagnostics
  == [.unstable 1 1]
-- an overhang that tips alone stands when a counterweight on its back end is placed in
-- the same (two-hand) step ...
private def overhang : Pose := flatAt 60 0 t
private def counterweight : Pose := flatAt 30 0 (2*t)
#guard (physicsMock.check .adult 10
  ⟨[{ blocks := [flatAt 0 0 0] }, { blocks := [overhang, counterweight] }]⟩).ok
-- ... but placed one at a time, the overhang tips at step 1, before the counterweight is
-- on: the mock checks every step, not only the finished structure
#guard (physicsMock.check .adult 10
  (.ofBlocks [flatAt 0 0 0, overhang, counterweight])).diagnostics == [.unstable 1 1]
-- a log-cabin tower (each layer turned 90°) stands
private def cabin (layers : Nat) : List Pose := (List.range layers).flatMap fun (k : Nat) =>
  let z := (k : Q) * t
  if k % 2 == 0 then [flatAt 0 0 z, flatAt 0 (blockLength - blockWidth) z]
  else [flatAt 0 0 z true, flatAt (blockLength - blockWidth) 0 z true]
#guard (physicsMock.check .adult 20 (.ofBlocks (cabin 6))).ok
-- too many blocks, too many hands, overlap
#guard (physicsMock.check .adult 1 (.ofBlocks [flatAt 0 0 0, flatAt 200 0 0])).diagnostics
  == [.tooManyBlocks 2 1]
#guard (physicsMock.check .child 10 ⟨[{ blocks := [flatAt 0 0 0, flatAt 200 0 0] }]⟩).diagnostics
  == [.tooManyHands 0]
#guard (physicsMock.check .adult 10 (.ofBlocks [flatAt 0 0 0, flatAt 50 0 0])).diagnostics
  == [.overlap 0 1]

/-! ## Semantic mock -/

namespace SemanticMock

/-- The volume two boxes share (mm³). -/
def sharedVolume (a b : Box) : Q :=
  let len (a1 a2 b1 b2 : Q) : Q := max 0 (min a2 b2 - max a1 b1)
  len a.lo.x a.hi.x b.lo.x b.hi.x * len a.lo.y a.hi.y b.lo.y b.hi.y *
  len a.lo.z a.hi.z b.lo.z b.hi.z

/-- Volume of one block (mm³). -/
def blockVolume : Q := blockLength * blockWidth * blockThickness

/-- Move and scale a box: first scale about `o`, then add `d`. -/
def Box.place (o d : Q3) (k : Q) (b : Box) : Box :=
  ⟨((b.lo.sub o).scale k).add d, ((b.hi.sub o).scale k).add d⟩

/-- The target's parts, scaled by `k` and moved so that they stand on the ground, centred
under the blocks in x and y. -/
def fitParts (t : TargetSpec) (blocks : List Pose) (k : Q) : List PartTag :=
  let parts := t.partsOrWhole
  match Box.joinAll (parts.map (·.box)), Box.joinAll (blocks.map Pose.box) with
  | some tb, some pb =>
    let o : Q3 := ⟨(tb.lo.x + tb.hi.x) / 2, (tb.lo.y + tb.hi.y) / 2, tb.lo.z⟩
    let d : Q3 := ⟨(pb.lo.x + pb.hi.x) / 2, (pb.lo.y + pb.hi.y) / 2, 0⟩
    parts.map fun p => { p with box := Box.place o d k p.box }
  | _, _ => parts

/-- The scales the mock tries: make the target as high, as wide (x) or as deep (y) as the
blocks. The real semantic engine may search more scales. -/
def scales (t : TargetSpec) (blocks : List Pose) : List Q :=
  match Box.joinAll (t.partsOrWhole.map (·.box)), Box.joinAll (blocks.map Pose.box) with
  | some tb, some pb =>
    let ratio (a b : Q) : List Q := if b == 0 then [] else [a / b]
    let ks := ratio pb.size.z tb.size.z ++ ratio pb.size.x tb.size.x ++ ratio pb.size.y tb.size.y
    if ks.isEmpty then [1] else ks
  | _, _ => [1]

/-- Volume IoU of the blocks against the target scaled by `k`. Blocks are boxes (exact
for turns of 0° and 90°). Target parts are assumed not to overlap, and blocks are assumed
not to overlap (the physics check rejects that). `missing` and `extra` are given in units
of one block thickness cubed (7.8³ mm³), rounded down. -/
def scoreAt (t : TargetSpec) (blocks : List Pose) (k : Q) : ScoreReport :=
  let parts := fitParts t blocks k
  let bboxes := blocks.map Pose.box
  let tVol := parts.foldl (fun v p => v + p.box.volume) 0
  let bVol := bboxes.foldl (fun v b => v + b.volume) 0
  let shared (p : Box) : Q := bboxes.foldl (fun v b => v + sharedVolume p b) 0
  let both := parts.foldl (fun v p => v + shared p.box) 0
  let union := tVol + bVol - both
  let iou : Q := if union ≤ 0 then 0 else both / union
  let cells (v : Q) : Nat := (v / (blockThickness ^ 3)).floor.toNat
  { score := iou, iou := iou
    perPart := parts.map fun p => (p.name, if p.box.volume ≤ 0 then 0 else shared p.box / p.box.volume)
    missing := cells (tVol - both), extra := cells (bVol - both) }

/-- The mock score: the best grid IoU over the scales in `scales`. -/
def score (t : TargetSpec) (blocks : List Pose) : ScoreReport :=
  (scales t blocks).foldl (fun best k =>
    let r := scoreAt t blocks k
    if r.score > best.score then r else best) (scoreAt t blocks 1)

/-- The mock limit: `N` blocks share at most `N` block volumes with the target, measured at
the target's own size. (Rough: the score may pick another scale.) -/
def bound (t : TargetSpec) (n : Nat) : Bound :=
  let tVol := t.partsOrWhole.foldl (fun v p => v + p.box.volume) 0
  let m : Q := if tVol ≤ 0 then 0 else min 1 ((n : Q) * blockVolume / tVol)
  ⟨m, Verdict.ofScore m⟩

end SemanticMock

/-- The mock semantic engine. Not verified; see the top of this file.
`interpret` ignores the prompt and returns the example tower. -/
def semanticMock : SemanticEngine :=
  { interpret := fun _ => pure TargetSpec.example
    score := SemanticMock.score
    bound := SemanticMock.bound }

-- two boxes that share half of one block
#guard SemanticMock.sharedVolume (flatAt 0 0 0).box (flatAt (blockLength / 2) 0 0).box
  == SemanticMock.blockVolume / 2
-- blocks that fill a target box exactly score 1
#guard
  let b : Box := ⟨⟨0, 0, 0⟩, ⟨blockLength, blockWidth, 2 * blockThickness⟩⟩
  (semanticMock.score { shape := .box b } [flatAt 0 0 0, flatAt 0 0 t]).iou == 1
-- one block against a tower 3 blocks wide scores less than 1
#guard (semanticMock.score
  { shape := .box ⟨⟨0, 0, 0⟩, ⟨blockLength, blockLength, blockThickness⟩⟩ } [flatAt 0 0 0]).iou
  < 1

end KaplaCore
