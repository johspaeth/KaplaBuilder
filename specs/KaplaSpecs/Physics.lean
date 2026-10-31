import KaplaPhysics.Engine

/-! # Spec for KaplaPhysics (human-owned)

Rules: `spec/physics-rules.md`. What "well-formed", "stable" and "stands at every step"
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

/-- Property 4, at the exact positions: when the engine accepts a plan, it uses at most
`maxPlanks` planks, and after every step the build so far is well-formed and stable. -/
theorem checkPlan_sound (maxPlanks : Nat) (steps : Build)
    (h : checkPlan maxPlanks steps = true) : StandsAtEveryStep maxPlanks steps := by
  sorry

end KaplaPhysics
