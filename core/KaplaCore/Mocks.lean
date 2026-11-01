import KaplaCore.Engine

/-! # Mock engines

Simple stand-ins so that each component can be developed alone. They are **not**
verified and **not** the real rules. They are deliberately simple and more forgiving than
the real engines.

- `physicsMock`: blocks must not overlap, and after **every step** each block must be held
  up: the load on it must act over its support. Loads are split equally between supports.
  It ignores hand error, the press of placing, hand access and friction.
- `semanticMock`: for bubble targets, counts grid cells inside blocks and bubbles, without the
  real engine's credit for hollow insides. For other targets, volume IoU against the part
  boxes; those targets never report a block as outside. -/

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
#guard (physicsMock.check .default 10 (.ofBlocks [flatAt 0 0 0, flatAt 0 0 t, flatAt 0 0 (2*t)])).ok
-- a block floating in the air falls
#guard (physicsMock.check .default 10 (.ofBlocks [flatAt 0 0 t])).diagnostics == [.unstable 0 0]
-- an overhang of 3/4 of a block tips
#guard (physicsMock.check .default 10 (.ofBlocks [flatAt 0 0 0, flatAt 12 0 t])).diagnostics
  == [.unstable 1 1]
-- an overhang that tips alone stands when a counterweight on its back end is placed in
-- the same (two-hand) step ...
private def overhang : Pose := flatAt 8 0 t
private def counterweight : Pose := flatAt 4 0 (2*t)
#guard (physicsMock.check .default 10
  ⟨[{ blocks := [flatAt 0 0 0] }, { blocks := [overhang, counterweight] }]⟩).ok
-- ... but placed one at a time, the overhang tips at step 1, before the counterweight is
-- on: the mock checks every step, not only the finished structure
#guard (physicsMock.check .default 10
  (.ofBlocks [flatAt 0 0 0, overhang, counterweight])).diagnostics == [.unstable 1 1]
-- a log-cabin tower (each layer turned 90°) stands
private def cabin (layers : Nat) : List Pose := (List.range layers).flatMap fun (k : Nat) =>
  let z := (k : Q) * t
  if k % 2 == 0 then [flatAt 0 0 z, flatAt 0 (blockLength - blockWidth) z]
  else [flatAt 0 0 z true, flatAt (blockLength - blockWidth) 0 z true]
#guard (physicsMock.check .default 20 (.ofBlocks (cabin 6))).ok
-- too many blocks, too many hands, overlap
#guard (physicsMock.check .default 1 (.ofBlocks [flatAt 0 0 0, flatAt 26 0 0])).diagnostics
  == [.tooManyBlocks 2 1]
#guard (physicsMock.check { HumanModel.default with hands := 1 } 10 ⟨[{ blocks := [flatAt 0 0 0, flatAt 26 0 0] }]⟩).diagnostics
  == [.tooManyHands 0]
#guard (physicsMock.check .default 10 (.ofBlocks [flatAt 0 0 0, flatAt 6 0 0])).diagnostics
  == [.overlap 0 1]

/-! ## Semantic mock -/

namespace SemanticMock

/-- The volume two boxes share (cubic block units). -/
def sharedVolume (a b : Box) : Q :=
  let len (a1 a2 b1 b2 : Q) : Q := max 0 (min a2 b2 - max a1 b1)
  len a.lo.x a.hi.x b.lo.x b.hi.x * len a.lo.y a.hi.y b.lo.y b.hi.y *
  len a.lo.z a.hi.z b.lo.z b.hi.z

/-- Volume of one block (cubic block units). -/
def blockVolume : Q := blockLength * blockWidth * blockThickness

/-- Move and scale a box: first scale about `o`, then add `d`. -/
def Box.place (o d : Q3) (k : Q) (b : Box) : Box :=
  ⟨((b.lo.sub o).scale k).add d, ((b.hi.sub o).scale k).add d⟩

/-- Volume IoU of the blocks against the target's part boxes at this frame. Blocks are boxes
(exact for turns of 0° and 90°). Target parts are assumed not to overlap, and blocks are
assumed not to overlap (the physics check rejects that). `missing` and `extra` are given in
units of one block thickness cubed, rounded down. -/
def scoreBoxes (t : TargetSpec) (f : Frame) (blocks : List Pose) : ScoreReport :=
  let parts : List PartTag := t.partsOrWhole.map fun p =>
    { p with box := Box.place ⟨0, 0, 0⟩ ⟨f.shiftX, f.shiftY, 0⟩ f.scale p.box }
  let bboxes := blocks.map Pose.box
  let tVol : Q := parts.foldl (fun (v : Q) p => v + p.box.volume) 0
  let bVol : Q := bboxes.foldl (fun v b => v + b.volume) 0
  let shared (p : Box) : Q := bboxes.foldl (fun v b => v + sharedVolume p b) 0
  let both : Q := parts.foldl (fun (v : Q) p => v + shared p.box) 0
  let union := tVol + bVol - both
  let iou : Q := if union ≤ 0 then 0 else both / union
  let cells (v : Q) : Nat := (v / (blockThickness ^ 3)).floor.toNat
  { score := iou, iou := iou
    perPart := parts.map fun p => (p.name, if p.box.volume ≤ (0 : Q) then (0 : Q) else shared p.box / p.box.volume)
    missing := cells (tVol - both), extra := cells (bVol - both)
    frame := f, blockCount := blocks.length }

/-- The centres of the unit grid cells in a box, faces included. -/
def cellCentres (b : Box) : List Q3 :=
  let line (lo hi : Q) : List Q :=
    let first := (lo - 1 / 2).ceil
    (List.range ((hi - 1 / 2).floor + 1 - first).toNat).map fun (n : Nat) =>
      ((first + (n : Int) : Int) : Q) + 1 / 2
  (line b.lo.x b.hi.x).flatMap fun x => (line b.lo.y b.hi.y).flatMap fun y =>
    (line b.lo.z b.hi.z).map fun z => ⟨x, y, z⟩

/-- The grid cells of one block, as their centres. -/
def blockCells (p : Pose) : List Q3 := (cellCentres p.box).filter p.contains

/-- The grid cells of one placed bubble, as their centres. -/
def bubbleCells (b : Bubble) : List Q3 := (cellCentres b.box).filter b.contains

/-- Compare blocks with a bubble model at this frame, by counting grid cells. A bubble's cell is
covered only if a block fills it: hollow insides get no credit here. Blocks are assumed not to
overlap. -/
def scoreBubbles (m : BubbleModel) (f : Frame) (blocks : List Pose) : ScoreReport :=
  let placed := m.bubbles.map (Bubble.place f)
  let inAny (c : Q3) : Bool := placed.any (·.contains c)
  let cellsOf := blocks.map blockCells
  let built := cellsOf.flatten
  -- count a cell shared by two bubbles once: only for the first bubble that has it
  let rec countTarget : List Bubble → Nat
    | [] => 0
    | b :: rest =>
      (bubbleCells b).countP (fun c => !rest.any (·.contains c)) + countTarget rest
  let target := countTarget placed
  let inside := built.countP inAny
  let extra := built.length - inside
  let denominator := target + extra
  let covered (b : Bubble) : Nat := built.countP b.contains
  let hasCells (b : Bubble) : Bool := !(bubbleCells b).isEmpty
  { score := if denominator == 0 then 0 else (inside : Q) / (denominator : Q)
    perPart := (placed.filter hasCells).map fun b =>
      (b.label, (covered b : Q) / ((bubbleCells b).length : Q))
    missing := target - inside
    extra
    frame := f
    blockCount := blocks.length
    outside := (List.range blocks.length).filter fun i =>
      !((cellsOf.getD i []).any inAny)
    uncovered := (placed.filter fun b => hasCells b && covered b == 0).map (·.label)
    tooSmall := (placed.filter fun b => !hasCells b).map (·.label) }

/-- The mock score. -/
def score (t : TargetSpec) (f : Frame) (blocks : List Pose) : ScoreReport :=
  match t.shape with
  | .bubbles m => scoreBubbles m f blocks
  | _ => scoreBoxes t f blocks

end SemanticMock

/-- The mock semantic engine. Not verified; see the top of this file.
`interpret` ignores the prompt and returns the example tower. `refine` ignores the remark. -/
def semanticMock : SemanticEngine :=
  { interpret := fun _ => pure TargetSpec.example
    refine := fun t _ => pure t
    score := SemanticMock.score }

-- two boxes that share half of one block
#guard SemanticMock.sharedVolume (flatAt 0 0 0).box (flatAt (blockLength / 2) 0 0).box
  == SemanticMock.blockVolume / 2
-- blocks that fill a target box exactly score 1
#guard
  let b : Box := ⟨⟨0, 0, 0⟩, ⟨blockLength, blockWidth, 2 * blockThickness⟩⟩
  (semanticMock.score { shape := .box b } (Frame.ofHeight 1) [flatAt 0 0 0, flatAt 0 0 t]).iou == 1
-- one block against a target 5 blocks wide scores less than 1
#guard (semanticMock.score
  { shape := .box ⟨⟨0, 0, 0⟩, ⟨blockLength, blockLength, blockThickness⟩⟩ } (Frame.ofHeight 1)
  [flatAt 0 0 0]).iou < 1

private def ball : TargetSpec := .ofBubbles
  { name := "ball"
    bubbles := [{ label := "ball", tags := [], center := ⟨0, 0, 1 / 2⟩, semi := ⟨1 / 2, 1 / 2, 1 / 2⟩ }] }
/-- A flat block filling cells 0-14 along x, 0-2 along y and level 0. -/
private def flat : Pose := ⟨.flat, .id, ⟨15 / 2, 3 / 2, 1 / 2⟩⟩
/-- The same block, far away. -/
private def farFlat : Pose := ⟨.flat, .id, ⟨100, 3 / 2, 1 / 2⟩⟩

-- the egg at height 30 has exactly the 5152 cells `egg.json` promises the planner
#guard (SemanticMock.bubbleCells
  ((BubbleModel.egg.bubbles.head!).place (Frame.ofHeight 30))).length == 5152
-- only cells above the ground count: a half sphere of radius 2 has 16 cells, none below ground
#guard
  let foot : Bubble := { label := "foot", tags := [], center := ⟨0, 0, 0⟩, semi := ⟨2, 2, 2⟩ }
  let cells := SemanticMock.bubbleCells foot
  cells.length == 16 && cells.all (·.z > 0)
-- a block touching the ball: 1 of its 45 cells is inside, of 8 cells in the ball
#guard
  let r := semanticMock.score ball (Frame.ofHeight 2) [flat]
  r.score == 1 / 52 && r.missing == 7 && r.extra == 44 && r.accepted &&
    r.verdict == .symbolic && r.frame == Frame.ofHeight 2
-- a block far away is outside, and the ball has no block
#guard
  let r := semanticMock.score ball (Frame.ofHeight 2) [flat, farFlat]
  r.outside == [1] && !r.accepted
#guard
  let r := semanticMock.score ball (Frame.ofHeight 2) [farFlat]
  r.outside == [0] && r.uncovered == ["ball"] && !r.accepted
-- a partial plan with no block outside is not rejected for what it has not built yet
#guard
  let two : TargetSpec := .ofBubbles
    { name := "two"
      bubbles := [{ label := "a", tags := [], center := ⟨0, 0, 1 / 2⟩, semi := ⟨1 / 2, 1 / 2, 1 / 2⟩ },
                  { label := "b", tags := [], center := ⟨20, 0, 1 / 2⟩, semi := ⟨1 / 2, 1 / 2, 1 / 2⟩ }] }
  let r := semanticMock.score two (Frame.ofHeight 2) [flat]
  r.outside == [] && r.uncovered == ["b"] && !r.accepted
-- a bubble too small to hold a cell is listed and ignored ...
#guard
  let r := semanticMock.score ball (Frame.ofHeight (1 / 2)) []
  r.tooSmall == ["ball"] && r.uncovered == [] && !r.accepted
-- ... an empty plan is still not accepted, and any block is then outside
#guard
  let r := semanticMock.score ball (Frame.ofHeight (1 / 2)) [flat]
  r.outside == [0] && !r.accepted

end KaplaCore
