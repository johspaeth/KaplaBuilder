import KaplaPlanner.Motif

/-! # Single block

One block standing upright, like a tree trunk. This is the plan for N = 1, and the
fallback when nothing else fits. -/

namespace KaplaPlanner.Motifs

/-- One upright block on the ground. -/
def single : Motif Unit where
  name := "single upright block"
  blocks := fun _ => [⟨.uprightX, 0, 0, 0⟩]
  cost := fun _ => 1
  cost_eq := fun _ => rfl

#guard single.blocks () == [⟨.uprightX, 0, 0, 0⟩]

end KaplaPlanner.Motifs
