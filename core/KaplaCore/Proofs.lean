import KaplaCore.Basic

/-! Proofs of the statements in `specs/KaplaSpecs/Core.lean`.
The names and statements must match the spec exactly; `lake comparator` checks this. -/

namespace KaplaCore

/-- The order in which two points are added does not matter. -/
theorem Q3.add_comm (p q : Q3) : Q3.add p q = Q3.add q p := by
  simp [Q3.add, Rat.add_comm]

end KaplaCore
