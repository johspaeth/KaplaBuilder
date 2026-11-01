/-! # Numbers, points and boxes

All lengths are exact fractions (`Rat`) in millimetres. Axes: `z` points up, the ground is
at `z = 0`. -/

namespace KaplaCore

/-- Exact rational numbers. We never use floats. -/
abbrev Q := Rat

/-- A point in space with exact rational coordinates (millimetres). -/
structure Q3 where
  x : Rat
  y : Rat
  z : Rat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Add two points coordinate by coordinate. -/
def Q3.add (p q : Q3) : Q3 := ⟨p.x + q.x, p.y + q.y, p.z + q.z⟩

/-- Example: moving the origin by (1, 2, 3) gives (1, 2, 3). -/
example : Q3.add ⟨0, 0, 0⟩ ⟨1, 2, 3⟩ = ⟨1, 2, 3⟩ := by simp [Q3.add, Rat.zero_add]

#guard Q3.add ⟨1, 1, 1⟩ ⟨1, 2, 3⟩ == ⟨2, 3, 4⟩

/-- Subtract `q` from `p`, coordinate by coordinate. -/
def Q3.sub (p q : Q3) : Q3 := ⟨p.x - q.x, p.y - q.y, p.z - q.z⟩

/-- Multiply every coordinate by `k`. -/
def Q3.scale (k : Q) (p : Q3) : Q3 := ⟨k * p.x, k * p.y, k * p.z⟩

#guard Q3.sub ⟨2, 3, 4⟩ ⟨1, 1, 1⟩ == ⟨1, 2, 3⟩
#guard Q3.scale 2 ⟨1, 2, 3⟩ == ⟨2, 4, 6⟩

/-- A box with sides parallel to the axes, given by its lowest and highest corner.
A box is meant to have `lo ≤ hi` in every coordinate. -/
structure Box where
  lo : Q3
  hi : Q3
  deriving Repr, BEq, Inhabited

/-- The size of the box along x, y and z. -/
def Box.size (b : Box) : Q3 := b.hi.sub b.lo

/-- The volume of the box (cubic millimetres). -/
def Box.volume (b : Box) : Q := let s := b.size; s.x * s.y * s.z

/-- The smallest box that contains both boxes. -/
def Box.join (a b : Box) : Box :=
  ⟨⟨min a.lo.x b.lo.x, min a.lo.y b.lo.y, min a.lo.z b.lo.z⟩,
   ⟨max a.hi.x b.hi.x, max a.hi.y b.hi.y, max a.hi.z b.hi.z⟩⟩

/-- The smallest box that contains every box in the list (`none` for an empty list). -/
def Box.joinAll : List Box → Option Box
  | [] => none
  | b :: bs => some (bs.foldl Box.join b)

/-- The point `p` is in the box (on its surface counts too). -/
def Box.contains (b : Box) (p : Q3) : Prop :=
  b.lo.x ≤ p.x ∧ p.x ≤ b.hi.x ∧ b.lo.y ≤ p.y ∧ p.y ≤ b.hi.y ∧ b.lo.z ≤ p.z ∧ p.z ≤ b.hi.z

instance (b : Box) (p : Q3) : Decidable (b.contains p) := by
  unfold Box.contains; infer_instance

/-- The 8 corners of the box. -/
def Box.corners (b : Box) : List Q3 :=
  [b.lo.x, b.hi.x].flatMap fun x => [b.lo.y, b.hi.y].flatMap fun y =>
    [b.lo.z, b.hi.z].map fun z => ⟨x, y, z⟩

/-- The dot product: `u.x·v.x + u.y·v.y + u.z·v.z`. -/
def Q3.dot (u v : Q3) : Q := u.x * v.x + u.y * v.y + u.z * v.z

#guard (Box.mk ⟨0, 0, 0⟩ ⟨1, 2, 3⟩).volume == 6
#guard decide ((Box.mk ⟨0, 0, 0⟩ ⟨1, 2, 3⟩).contains ⟨1, 1, 3⟩)
#guard !decide ((Box.mk ⟨0, 0, 0⟩ ⟨1, 2, 3⟩).contains ⟨1, 1, 4⟩)
#guard (Box.mk ⟨0, 0, 0⟩ ⟨1, 2, 3⟩).corners.length == 8
#guard Box.join ⟨⟨0, 0, 0⟩, ⟨1, 1, 1⟩⟩ ⟨⟨2, 0, 0⟩, ⟨3, 1, 1⟩⟩ == ⟨⟨0, 0, 0⟩, ⟨3, 1, 1⟩⟩

end KaplaCore
