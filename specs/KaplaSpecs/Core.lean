import KaplaCore.Basic

/-! # Spec for KaplaCore (human-owned)

The statements here are the promise. Proofs live in `core/KaplaCore/Proofs.lean`.
`sorry` is expected in this file only. `lake comparator --config comparator/core.json`
checks that the proof proves exactly these statements, with only standard axioms. -/

namespace KaplaCore

/-- The order in which two points are added does not matter. -/
theorem Q3.add_comm (p q : Q3) : Q3.add p q = Q3.add q p := by
  sorry

end KaplaCore
