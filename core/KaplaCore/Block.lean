import KaplaCore.Basic

/-! # One Kapla block and where it is

A Kapla block is 15 × 3 × 1 block units. A `Pose` says where one block is:
which face is down, how it is turned about the vertical axis, and where its centre is.
Tilted blocks (for roofs) come later as an extension. -/

namespace KaplaCore

/-- Block length. -/
def blockLength : Q := 15
/-- Block width. -/
def blockWidth : Q := 3
/-- Block thickness. -/
def blockThickness : Q := 1

/-- Which face of the block is down. -/
inductive Upright where
  /-- Lying flat: the big face is down. Height 1. -/
  | flat
  /-- On its long edge. Height 3. -/
  | onEdge
  /-- Standing on its small end. Height 15. -/
  | standing
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The block's size along its own x, y and z axes before it is turned.
The long side is along x when it is not standing. -/
def Upright.dims : Upright → Q3
  | .flat     => ⟨blockLength, blockWidth, blockThickness⟩
  | .onEdge   => ⟨blockLength, blockThickness, blockWidth⟩
  | .standing => ⟨blockWidth, blockThickness, blockLength⟩

/-- A turn about the vertical axis, given exactly by its cosine and sine.
Only turns with `cos² + sin² = 1` are meant (see `Rot.valid`). We get exact rational
turns from Pythagorean triples, for example 3-4-5. -/
structure Rot where
  cos : Q
  sin : Q
  deriving Repr, BEq, DecidableEq, Inhabited

/-- No turn. -/
def Rot.id : Rot := ⟨1, 0⟩
/-- A quarter turn (90°, counter-clockwise seen from above). -/
def Rot.quarter : Rot := ⟨0, 1⟩

/-- The turn given by a Pythagorean triple `a² + b² = c²`: cos = a/c, sin = b/c. -/
def Rot.ofTriple (a b c : Int) : Rot := ⟨(a : Q) / c, (b : Q) / c⟩

/-- True if the turn is a real rotation (`cos² + sin² = 1`). -/
def Rot.valid (r : Rot) : Bool := r.cos * r.cos + r.sin * r.sin == 1

#guard Rot.id.valid && Rot.quarter.valid && (Rot.ofTriple 3 4 5).valid
#guard !(Rot.mk 1 1).valid

/-- First turn by `b`, then by `a`: the angles add up. -/
def Rot.comp (a b : Rot) : Rot :=
  ⟨a.cos * b.cos - a.sin * b.sin, a.sin * b.cos + a.cos * b.sin⟩

/-- About 30° (29.86°): the triple 209-120-241. Exact turns by 30° need `√3`, which is not
a fraction; at the end of a block this one is off by 0.14 mm. -/
def Rot.deg30 : Rot := Rot.ofTriple 209 120 241
/-- About 45° (45.24°): the triple 119-120-169. Off by 0.24 mm at the end of a block. -/
def Rot.deg45 : Rot := Rot.ofTriple 119 120 169
/-- About 60° (60.14°): the triple 120-209-241. Off by 0.14 mm at the end of a block. -/
def Rot.deg60 : Rot := Rot.ofTriple 120 209 241

#guard Rot.deg30.valid && Rot.deg45.valid && Rot.deg60.valid
#guard Rot.deg30 == ⟨209 / 241, 120 / 241⟩
-- two quarter turns are a half turn; 30° and 60° come from the same triple, so together
-- they are exactly a quarter turn
#guard Rot.quarter.comp Rot.quarter == ⟨-1, 0⟩
#guard Rot.deg30.comp Rot.deg60 == Rot.quarter

/-- Turn the horizontal part of a vector by `r`. -/
def Rot.apply (r : Rot) (v : Q3) : Q3 :=
  ⟨r.cos * v.x - r.sin * v.y, r.sin * v.x + r.cos * v.y, v.z⟩

#guard Rot.quarter.apply ⟨1, 0, 5⟩ == ⟨0, 1, 5⟩

/-- Where one block is: which face is down, how it is turned, and its centre. -/
structure Pose where
  up     : Upright
  rot    : Rot
  center : Q3
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The 8 corners of the block. -/
def Pose.corners (p : Pose) : List Q3 :=
  let d := p.up.dims
  let h : Q3 := ⟨d.x / 2, d.y / 2, d.z / 2⟩
  let signs : List Q := [-1, 1]
  signs.flatMap fun sx => signs.flatMap fun sy => signs.map fun sz =>
    p.center.add (p.rot.apply ⟨sx * h.x, sy * h.y, sz * h.z⟩)

/-- The smallest box with sides parallel to the axes that contains the block.
For turns of 0° or 90° this is exactly the block. -/
def Pose.box (p : Pose) : Box :=
  let d := p.up.dims
  let c := p.rot.cos.abs
  let s := p.rot.sin.abs
  let h : Q3 := ⟨(c * d.x + s * d.y) / 2, (s * d.x + c * d.y) / 2, d.z / 2⟩
  ⟨p.center.sub h, p.center.add h⟩

/-- True if the point is inside the block. Of each pair of opposite faces, the one on the higher
side in x, y or z is not part of the block, however the block is turned (for a slanted face,
x decides first, then y). So two touching blocks never share a point on their shared face, and
a block that is not turned, or turned by a quarter turn, contains exactly 45 cell centres of a
unit grid wherever it is. -/
def Pose.contains (p : Pose) (q : Q3) : Bool :=
  let d := p.up.dims
  let v := q.sub p.center
  -- turn `v` back into the block's own axes
  let lx := p.rot.cos * v.x + p.rot.sin * v.y
  let ly := -p.rot.sin * v.x + p.rot.cos * v.y
  -- true if the block axis with direction (ax, ay) points to the higher side
  let pointsHigh (ax ay : Q) : Bool := ax > 0 || (ax == 0 && ay > 0)
  let within (t size : Q) (high : Bool) : Bool :=
    if high then -size ≤ 2 * t && 2 * t < size else -size < 2 * t && 2 * t ≤ size
  within lx d.x (pointsHigh p.rot.cos p.rot.sin) &&
    within ly d.y (pointsHigh (-p.rot.sin) p.rot.cos) && within v.z d.z true

/-- Example: a flat block lying on the ground at the origin. -/
def Pose.example : Pose := ⟨.flat, .id, ⟨0, 0, blockThickness / 2⟩⟩

#guard Pose.example.box == ⟨⟨-15/2, -3/2, 0⟩, ⟨15/2, 3/2, 1⟩⟩
#guard Pose.example.corners.length == 8
#guard Pose.example.contains ⟨7, 0, 1/2⟩ && !Pose.example.contains ⟨8, 0, 1/2⟩
-- the low face is inside, the high face is not
#guard Pose.example.contains ⟨-15/2, 0, 1/2⟩ && !Pose.example.contains ⟨15/2, 0, 1/2⟩
-- turned by 90°, the long side is along y
#guard (Pose.mk .flat .quarter ⟨0, 0, 0⟩).contains ⟨0, 7, 0⟩
#guard (Pose.mk .flat .quarter ⟨0, 0, 0⟩).box.size == ⟨blockWidth, blockLength, blockThickness⟩

/-- The centres of the unit grid cells in `-20 ≤ x, y < 20`, `0 ≤ z < 20`. -/
private def cellCentres : List Q3 :=
  let line (n : Nat) (lo : Int) : List Q := (List.range n).map fun i => ((lo + Int.ofNat i : Int) : Q) + 1 / 2
  (line 40 (-20)).flatMap fun x => (line 40 (-20)).flatMap fun y => (line 20 0).map fun z => ⟨x, y, z⟩

-- a turned and an unturned block touch on a cell centre: exactly one of them has the point,
-- whichever is on the left
#guard !(Pose.mk .flat .id ⟨-7, 0, 1 / 2⟩).contains ⟨1 / 2, 1 / 2, 1 / 2⟩
#guard (Pose.mk .flat .quarter ⟨2, 0, 1 / 2⟩).contains ⟨1 / 2, 1 / 2, 1 / 2⟩
#guard !(Pose.mk .flat .quarter ⟨-1, 0, 1 / 2⟩).contains ⟨1 / 2, 1 / 2, 1 / 2⟩
#guard (Pose.mk .flat .id ⟨8, 0, 1 / 2⟩).contains ⟨1 / 2, 1 / 2, 1 / 2⟩
-- a half turn does not move the missing face
#guard !(Pose.mk .flat ⟨-1, 0⟩ ⟨0, 0, 1 / 2⟩).contains ⟨15 / 2, 0, 1 / 2⟩
#guard (Pose.mk .flat ⟨-1, 0⟩ ⟨0, 0, 1 / 2⟩).contains ⟨-15 / 2, 0, 1 / 2⟩

-- 45 cells when the faces lie on cell centres, between them, or anywhere else
#guard cellCentres.countP Pose.example.contains == 45
#guard cellCentres.countP (Pose.mk .flat .id ⟨15 / 2, 3 / 2, 1 / 2⟩).contains == 45
#guard cellCentres.countP (Pose.mk .flat .quarter ⟨1 / 3, 1 / 3, 1 / 2⟩).contains == 45
#guard cellCentres.countP (Pose.mk .standing .id ⟨0, 0, 15 / 2⟩).contains == 45

end KaplaCore
