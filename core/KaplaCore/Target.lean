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

/-- What to build. -/
structure TargetSpec where
  shape      : Shape
  silhouette : Option Mask := none
  parts      : List PartTag := []
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
