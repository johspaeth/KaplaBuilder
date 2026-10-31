import KaplaCore.Basic

/-! # One Kapla block and where it is

A Kapla block is 117 × 23.4 × 7.8 mm (ratio 15 : 3 : 1). A `Pose` says where one block is:
which face is down, how it is turned about the vertical axis, and where its centre is.
Tilted blocks (for roofs) come later as an extension. -/

namespace KaplaCore

/-- Block length (mm). -/
def blockLength : Q := 117
/-- Block width (mm). -/
def blockWidth : Q := 117 / 5
/-- Block thickness (mm). -/
def blockThickness : Q := 39 / 5

#guard blockWidth == 23.4 && blockThickness == 7.8
#guard blockLength == 15 * blockThickness && blockWidth == 3 * blockThickness

/-- Which face of the block is down. -/
inductive Upright where
  /-- Lying flat: the big face is down. Height 7.8 mm. -/
  | flat
  /-- On its long edge. Height 23.4 mm. -/
  | onEdge
  /-- Standing on its small end. Height 117 mm. -/
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

/-- Turn the horizontal part of a vector by `r`. -/
def Rot.apply (r : Rot) (v : Q3) : Q3 :=
  ⟨r.cos * v.x - r.sin * v.y, r.sin * v.x + r.cos * v.y, v.z⟩

#guard Rot.quarter.apply ⟨1, 0, 5⟩ == ⟨0, 1, 5⟩

/-- Where one block is: which face is down, how it is turned, and its centre (mm). -/
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

/-- True if the point is inside the block (or on its surface). -/
def Pose.contains (p : Pose) (q : Q3) : Bool :=
  let d := p.up.dims
  let v := q.sub p.center
  -- turn `v` back into the block's own axes
  let lx := p.rot.cos * v.x + p.rot.sin * v.y
  let ly := -p.rot.sin * v.x + p.rot.cos * v.y
  2 * lx.abs ≤ d.x && 2 * ly.abs ≤ d.y && 2 * v.z.abs ≤ d.z

/-- Example: a flat block lying on the ground at the origin. -/
def Pose.example : Pose := ⟨.flat, .id, ⟨0, 0, blockThickness / 2⟩⟩

#guard Pose.example.box == ⟨⟨-117/2, -117/10, 0⟩, ⟨117/2, 117/10, 39/5⟩⟩
#guard Pose.example.corners.length == 8
#guard Pose.example.contains ⟨50, 0, 1⟩ && !Pose.example.contains ⟨60, 0, 1⟩
-- turned by 90°, the long side is along y
#guard (Pose.mk .flat .quarter ⟨0, 0, 0⟩).contains ⟨0, 50, 0⟩
#guard (Pose.mk .flat .quarter ⟨0, 0, 0⟩).box.size == ⟨blockWidth, blockLength, blockThickness⟩

end KaplaCore
