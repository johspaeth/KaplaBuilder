import KaplaPhysics

/-! Run with `lake env lean scripts/AxiomAudit.lean`. CI fails unless every theorem on the
soundness path depends only on `propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`,
no `native_decide` / `Lean.ofReduceBool`). -/

#print axioms Kapla.Physics.certify_sound
#print axioms Kapla.Physics.checkAll_sound
#print axioms Kapla.Physics.separated_sound
#print axioms Kapla.Physics.forcesOKFast_sound
#print axioms Kapla.Pose.dot_expand
#print axioms Kapla.Physics.press_from_corners
#print axioms Kapla.Physics.pressCheck_sound
#print axioms Kapla.Physics.clearanceCheck_sound
#print axioms Kapla.Physics.shift_bound
#print axioms Kapla.Physics.robustL_sound
#print axioms Kapla.Physics.robust_press
#print axioms Kapla.Physics.robustA_sound
#print axioms Kapla.Physics.checkRobust_sound
