import KaplaPlanner.Grid

/-! # Motifs

A motif is a known building pattern (a tower, a wall, …). It turns a few parameters into
blocks, and it knows in advance how many blocks that takes. The count is proven, so the
budget step can trust it. -/

namespace KaplaPlanner

/-- A building pattern with parameters `P`. -/
structure Motif (P : Type) where
  name     : String
  /-- The blocks, in the motif's own coordinates (lowest corner near the origin, on the
  ground). Listed bottom to top. -/
  blocks   : P → List GridBlock
  /-- How many blocks the motif uses. -/
  cost     : P → Nat
  /-- The cost is exact. -/
  cost_eq  : ∀ p, (blocks p).length = cost p

end KaplaPlanner
