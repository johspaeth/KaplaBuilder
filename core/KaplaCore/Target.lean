import KaplaCore.Bubble

/-! # What to build: the target

The semantic engine turns a prompt or a picture into a `TargetSpec`: a bubble model, with
extra data for the planner.

Every target also has a list of parts. Each part has a kind and a bounding box. The
planner uses only the parts, so it never has to evaluate the shape itself. -/

namespace KaplaCore

/-- A box that contains the part of the model above the ground. -/
def BubbleModel.bbox (m : BubbleModel) : Box :=
  (Box.joinAll (m.bubbles.map Bubble.box)).getD ⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩

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

/-- The kind for a bubble: from its first tag that names a kind, else `other`. -/
def PartKind.ofTags (tags : List String) : PartKind :=
  let known : String → Option PartKind
    | "tower" => some .tower
    | "wall" => some .wall
    | "roof:gable" => some .roofGable
    | "roof:cone" => some .roofCone
    | "roof:hip" => some .roofHip
    | "trunk" => some .trunk
    | _ => none
  (tags.findSome? known).getD .other

#guard PartKind.ofTags ["slab", "wall", "tower"] == .wall
#guard PartKind.ofTags ["slab"] == .other

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
  model      : BubbleModel
  silhouette : Option Mask := none
  parts      : List PartTag := []
  deriving Repr, BEq, Inhabited

/-- The parts of the target. If it has none, the whole shape is one part of kind `other`. -/
def TargetSpec.partsOrWhole (t : TargetSpec) : List PartTag :=
  if t.parts.isEmpty then [⟨"whole", .other, t.model.bbox⟩] else t.parts

/-- The target for a bubble model, with one part for each bubble. The part's box is at the
model's own size, before any height. -/
def TargetSpec.ofBubbles (m : BubbleModel) : TargetSpec :=
  { model := m
    parts := m.bubbles.map fun b => ⟨b.label, PartKind.ofTags b.tags, b.box⟩ }

/-- Example: the egg as a target. -/
def TargetSpec.egg : TargetSpec := .ofBubbles .egg

#guard TargetSpec.egg.parts == [⟨"egg", .tower, ⟨⟨-3 / 10, -3 / 10, 0⟩, ⟨3 / 10, 3 / 10, 1⟩⟩⟩]
#guard TargetSpec.egg.model.bbox == ⟨⟨-3 / 10, -3 / 10, 0⟩, ⟨3 / 10, 3 / 10, 1⟩⟩

-- A target with no parts counts as one part.
#guard (TargetSpec.mk .egg none []).partsOrWhole.map (·.name) == ["whole"]

/-- What the user asks for. -/
structure Request where
  prompt : String
  /-- Path to a picture, if the user gave one. -/
  image  : Option String := none
  blocks : Nat
  deriving Repr, BEq, Inhabited

end KaplaCore
