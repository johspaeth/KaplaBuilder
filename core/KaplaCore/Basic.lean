/-! Placeholder for the shared data types. Replace with the real contract (v0.1). -/

namespace KaplaCore

/-- A point in space with exact rational coordinates (millimetres). -/
structure Q3 where
  x : Rat
  y : Rat
  z : Rat
  deriving Repr, BEq, DecidableEq

/-- Add two points coordinate by coordinate. -/
def Q3.add (p q : Q3) : Q3 := ⟨p.x + q.x, p.y + q.y, p.z + q.z⟩

/-- Example: moving the origin by (1, 2, 3) gives (1, 2, 3). -/
example : Q3.add ⟨0, 0, 0⟩ ⟨1, 2, 3⟩ = ⟨1, 2, 3⟩ := by simp [Q3.add, Rat.zero_add]

#guard Q3.add ⟨1, 1, 1⟩ ⟨1, 2, 3⟩ == ⟨2, 3, 4⟩

end KaplaCore
