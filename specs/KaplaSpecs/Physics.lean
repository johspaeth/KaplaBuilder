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

/-- Property 5 ("reachable" is right): when the checker finds a direction, the plank can
come in along it in a straight line from far away and drop into place without sharing
inside space with any plank already placed (K3). -/
theorem reachDir_sound (placed : Build) (p : Plank) (h : Rat) (d : Dir)
    (hd : reachDir? placed p h = some d) : StraightPath placed p h d.vec := by
  sorry

/-- Property 5 for a plan: when no step is listed as hard to reach, every step can be put
in place by a straight path and a drop. -/
theorem hardToReach_nil_sound (h : Rat) (steps : Build) (hn : hardToReach h steps = []) :
    EveryStepReachable h steps := by
  sorry

/-- Property 7 (contacts are right): the overlap of two rectangles holds exactly the points
that lie in both. -/
theorem Rect.inter_contains (r s : Rect) (x y : Rat) :
    (r.inter s).Contains x y ↔ r.Contains x y ∧ s.Contains x y := by
  sorry

/-- Property 7: a rectangle has an area bigger than zero exactly when some point lies
strictly inside it (C3). -/
theorem Rect.hasArea_iff (r : Rect) :
    r.HasArea ↔ ∃ x y, r.x0 < x ∧ x < r.x1 ∧ r.y0 < y ∧ y < r.y1 := by
  sorry

/-- Property 7: plank `i` rests on plank `j` over `r` exactly when `i`'s bottom is at the
height of `j`'s top, `r` is the overlap of their footprints, and `r` has an area (C1, C2). -/
theorem restPatch_plank_iff (b : Build) (i j : Nat) (r : Rect) :
    restPatch b i (.plank j) = some r ↔
      (b.get i).z = (b.get j).top ∧ r = (b.get i).footprint.inter (b.get j).footprint ∧
        r.HasArea := by
  sorry

/-- Property 7: plank `i` rests on the ground over `r` exactly when its bottom is at `z = 0`
and `r` is its whole footprint (C1, C2). -/
theorem restPatch_ground_iff (b : Build) (i : Nat) (r : Rect) :
    restPatch b i .ground = some r ↔ (b.get i).z = 0 ∧ r = (b.get i).footprint := by
  sorry

end KaplaPhysics
