import KaplaPhysics.Engine

/-! # Spec for KaplaPhysics (human-owned)

Rules: `spec/physics-rules.md`. What "well-formed", "stable", "solid" and "safe plan"
mean is in `physics/KaplaPhysics/Rules.lean`; the engine is in
`physics/KaplaPhysics/Engine.lean`. Proofs live in `physics/KaplaPhysics/Proofs.lean`.
`sorry` is expected in this file only. -/

namespace KaplaPhysics

/-- Property 1 ("stands" is right): when the engine answers "stable", there are allowed
pushes that balance every plank (S2). -/
theorem stabilityAnswer_stable_sound (b : Build) (h : stabilityAnswer b = .stable) :
    Stable b := by
  sorry

/-- Property 2 ("falls" is right): when the engine answers "falls", no allowed pushes
balance every plank (S3). -/
theorem stabilityAnswer_falls_sound (b : Build) (h : stabilityAnswer b = .falls) :
    ¬ Stable b := by
  sorry

/-- Property 3 ("solid" is right): when the verdict is "solid", the build is stable for
every combination of placement errors up to `ε` (R3). -/
theorem verdict_solid_sound (ε : Rat) (b : Build) (h : verdict ε b = .solid) :
    SolidWithin ε b := by
  sorry

/-- When the verdict is "risky", the build is stable at the exact positions (R4). -/
theorem verdict_risky_sound (ε : Rat) (b : Build) (h : verdict ε b = .risky) : Stable b := by
  sorry

/-- When the verdict is "falls", the build is not stable (R4). -/
theorem verdict_falls_sound (ε : Rat) (b : Build) (h : verdict ε b = .falls) : ¬ Stable b := by
  sorry

/-- Property 4 ("the plan is safe"): when the engine accepts a plan, it uses at most
`maxPlanks` planks, and after every step the build so far is well-formed and solid for
placement errors up to `ε` (K4, K5). -/
theorem checkPlan_sound (ε : Rat) (maxPlanks : Nat) (steps : Build)
    (h : checkPlan ε maxPlanks steps = true) : SafePlan ε maxPlanks steps := by
  sorry

end KaplaPhysics
