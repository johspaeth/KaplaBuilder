import KaplaCore.Basic

/-! # What to build: the target

The semantic engine turns a prompt or a picture into a `TargetSpec`. The shape language
here is a first version; the semantic engine (B) owns its meaning and may extend it.

Every target also has a list of parts. Each part has a kind and a bounding box. The
planner uses only the parts, so it never has to evaluate the shape itself. -/

namespace KaplaCore

/-- A 3D shape. -/
inductive Shape where
  /-- A box with sides parallel to the axes. -/
  | box (b : Box)
  /-- An upright cylinder: centre of the bottom face, radius, height. -/
  | cylinder (base : Q3) (radius height : Q)
  /-- An upright cone: centre of the bottom face, radius at the bottom, height. -/
  | cone (base : Q3) (radius height : Q)
  /-- Everything that is in either shape. -/
  | union (a b : Shape)
  /-- Everything in `a` that is not in `b`. -/
  | diff (a b : Shape)
  deriving Repr, BEq, Inhabited

/-- A box that contains the shape. -/
def Shape.bbox : Shape → Box
  | .box b => b
  | .cylinder c r h | .cone c r h => ⟨⟨c.x - r, c.y - r, c.z⟩, ⟨c.x + r, c.y + r, c.z + h⟩⟩
  | .union a b => a.bbox.join b.bbox
  | .diff a _ => a.bbox

/-- What a part of the target is. The planner chooses how to build it from this. -/
inductive PartKind where
  | tower
  | wall
  | roofGable
  | roofCone
  | roofHip
  | trunk
  | other
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One named part of the target, with a box that contains it. -/
structure PartTag where
  name : String
  kind : PartKind
  box  : Box
  deriving Repr, BEq, Inhabited

/-- A black-and-white picture of the target's outline (row by row, `true` = inside). -/
structure Mask where
  width  : Nat
  height : Nat
  pixels : Array Bool
  deriving Repr, BEq, Inhabited

/-- A bubble: a sphere that may be stretched and turned (an ellipsoid). The target is the
union of its bubbles.

A point `x` is inside when
`(u₁·(x − c))² + (u₂·(x − c))² + (u₃·(x − c))² ≤ 1`, where `c` is the centre.
Each `uᵢ` is an axis direction divided by the radius along that axis. Any turn and stretch
can be written this way with rational numbers. -/
structure Bubble where
  /-- The part of the target this bubble belongs to ("head", "left tower", …). -/
  part   : String
  center : Q3
  u1     : Q3
  u2     : Q3
  u3     : Q3
  deriving Repr, BEq, Inhabited

/-- The bubble formula at point `p`: at most 1 inside, more than 1 outside. -/
def Bubble.value (b : Bubble) (p : Q3) : Q :=
  let d := p.sub b.center
  (b.u1.dot d) ^ 2 + (b.u2.dot d) ^ 2 + (b.u3.dot d) ^ 2

/-- The point `p` is inside the bubble (on its surface counts too). -/
def Bubble.contains (b : Bubble) (p : Q3) : Prop := b.value p ≤ 1

instance (b : Bubble) (p : Q3) : Decidable (b.contains p) := by
  unfold Bubble.contains; infer_instance

/-- A ball with centre `c` and radius `r`. -/
def Bubble.ball (part : String) (c : Q3) (r : Q) : Bubble :=
  ⟨part, c, ⟨1 / r, 0, 0⟩, ⟨0, 1 / r, 0⟩, ⟨0, 0, 1 / r⟩⟩

/-- An upright ellipsoid with radii `rx`, `ry`, `rz` along the axes. -/
def Bubble.ellipsoid (part : String) (c : Q3) (rx ry rz : Q) : Bubble :=
  ⟨part, c, ⟨1 / rx, 0, 0⟩, ⟨0, 1 / ry, 0⟩, ⟨0, 0, 1 / rz⟩⟩

-- a ball of radius 10 at the origin
#guard decide ((Bubble.ball "b" ⟨0, 0, 0⟩ 10).contains ⟨6, 8, 0⟩)
#guard !decide ((Bubble.ball "b" ⟨0, 0, 0⟩ 10).contains ⟨6, 8, 1⟩)
-- an ellipsoid stretched along z
#guard decide ((Bubble.ellipsoid "e" ⟨0, 0, 0⟩ 1 1 5).contains ⟨0, 0, 5⟩)
-- the same ellipsoid turned 90° about the x axis is stretched along y
#guard decide ((Bubble.mk "t" ⟨0, 0, 0⟩ ⟨1, 0, 0⟩ ⟨0, 0, 1⟩ ⟨0, 1/5, 0⟩).contains ⟨0, 5, 0⟩)

/-- What to build. -/
structure TargetSpec where
  shape      : Shape
  silhouette : Option Mask := none
  parts      : List PartTag := []
  /-- The target as a union of bubbles. The planner builds strictly inside them. -/
  bubbles    : List Bubble := []
  deriving Repr, BEq, Inhabited

/-- The parts of the target. If it has none, the whole shape is one part of kind `other`. -/
def TargetSpec.partsOrWhole (t : TargetSpec) : List PartTag :=
  if t.parts.isEmpty then [⟨"whole", .other, t.shape.bbox⟩] else t.parts

/-- Example: a tower 13 wide and 38 high. -/
def TargetSpec.example : TargetSpec :=
  let b : Box := ⟨⟨0, 0, 0⟩, ⟨13, 13, 38⟩⟩
  { shape := .box b, parts := [⟨"tower", .tower, b⟩] }

#guard TargetSpec.example.partsOrWhole.length == 1
#guard (Shape.cylinder ⟨0, 0, 0⟩ 10 50).bbox == ⟨⟨-10, -10, 0⟩, ⟨10, 10, 50⟩⟩

/-- What the user asks for. -/
structure Request where
  prompt : String
  /-- Path to a picture, if the user gave one. -/
  image  : Option String := none
  blocks : Nat
  deriving Repr, BEq, Inhabited

end KaplaCore
