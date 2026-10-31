import KaplaPhysics.Engine
import KaplaPhysics.Sums
import KaplaPhysics.RobustProofs

/-! # Proofs of the physics theorems

The statements are in `specs/KaplaSpecs/Physics.lean`; `lake comparator` checks that the
names and statements here match them exactly. -/

namespace KaplaPhysics

open Solver (Motion allSupports)

/-! ## "Stable" answers are right -/

/-- If the push check passes, the build is stable (S2). -/
theorem checkPushes_sound (b : Build) (ps : List Push) (h : checkPushes b ps = true) :
    Stable b := by
  simp only [checkPushes, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨ps, h.1, h.2⟩

/-- Property 1: when the engine answers "stable", the build is stable (S2). -/
theorem globalAnswer_stable_sound (b : Build) (h : globalAnswer b = .stable) :
    Stable b := by
  unfold globalAnswer at h
  split at h
  · split at h
    · exact checkPushes_sound b _ (by assumption)
    · cases h
  · split at h <;> cases h
  · cases h

theorem fallbackAnswer_stable_sound (b : Build) (h : fallbackAnswer b = .stable) :
    Stable b := by
  unfold fallbackAnswer at h
  split at h
  · exact globalAnswer_stable_sound b h
  · cases h

theorem stabilityAnswer_stable_sound (b : Build) (h : stabilityAnswer b = .stable) :
    Stable b := by
  unfold stabilityAnswer at h
  split at h
  · split at h
    · exact checkPushes_sound b _ (by assumption)
    · exact fallbackAnswer_stable_sound b h
  · exact fallbackAnswer_stable_sound b h

/-! ## "Falls" answers are right -/

/-- The weighted rise of plank `i` at the push points equals the lift of its centre, when
the pushes balance plank `i`. -/
theorem balanced_rise (b : Build) (ms : List Motion) (ps : List Push) (i : Nat)
    (hb : Balanced b ps i) :
    (ps.map fun p => p.upOn i * rise b ms (.plank i) p.x p.y).sum = (ms.getD i default).lift := by
  obtain ⟨h1, h2, h3⟩ := hb
  let m := ms.getD i default
  have : ∀ p ∈ ps, p.upOn i * rise b ms (.plank i) p.x p.y
      = (m.lift * p.upOn i + m.tiltX * (p.upOn i * (p.x - (b.get i).centerX)))
        + m.tiltY * (p.upOn i * (p.y - (b.get i).centerY)) := by
    intro p _; simp only [rise, m]; grind
  rw [sum_map_congr _ _ _ this, sum_map_add, sum_map_add, sum_map_mul_left, sum_map_mul_left,
    sum_map_mul_left, h1, h2, h3]
  grind

/-- What one allowed push contributes to the sum over all planks. -/
theorem push_sum_over_planks (b : Build) (ms : List Motion) (p : Push)
    (hp : p.Allowed b) :
    ((List.range b.length).map fun i => p.upOn i * rise b ms (.plank i) p.x p.y).sum
      = p.force * (rise b ms (.plank p.upper) p.x p.y - rise b ms p.lower p.x p.y) := by
  obtain ⟨_, hup, hlow, _⟩ := hp
  have split : ∀ i ∈ List.range b.length, p.upOn i * rise b ms (.plank i) p.x p.y
      = (if p.upper = i then p.force * rise b ms (.plank i) p.x p.y else 0)
        - (if p.lower = .plank i then p.force * rise b ms (.plank i) p.x p.y else 0) := by
    intro i _; simp only [Push.upOn]; split <;> split <;> grind
  rw [sum_map_congr _ _ _ split, sum_map_sub,
    sum_range_single _ _ hup (fun i => p.force * rise b ms (.plank i) p.x p.y)]
  cases hl : p.lower with
  | ground => simp [sum_map_zero, rise] <;> grind
  | plank j =>
    rw [hl] at hlow
    have := sum_range_single b.length j hlow (fun i => p.force * rise b ms (.plank i) p.x p.y)
    simp only [Support.plank.injEq] at this ⊢
    rw [this]; grind

/-- Under a fall certificate, every allowed push does work at least zero. -/
theorem push_work_nonneg (b : Build) (ms : List Motion) (hc : FallCertificate b ms)
    (p : Push) (hp : p.Allowed b) :
    0 ≤ p.force * (rise b ms (.plank p.upper) p.x p.y - rise b ms p.lower p.x p.y) := by
  obtain ⟨hf, hup, hlow, hcorner⟩ := hp
  have hs : p.lower ∈ allSupports b.length := by
    cases hl : p.lower with
    | ground => simp [allSupports]
    | plank j => rw [hl] at hlow; simp [allSupports, Support.InBuild] at hlow ⊢; exact hlow
  have hno := hc.1 p.upper hup p.lower hs
  unfold NoPushInto at hno
  revert hcorner hno
  cases restPatch b p.upper p.lower with
  | none => intro h; exact h.elim
  | some r =>
    intro hcorner hno
    have := hno (p.x, p.y) hcorner
    exact Rat.mul_nonneg hf (by grind)

/-- A fall certificate shows that the build is not stable. -/
theorem fallCertificate_sound (b : Build) (ms : List Motion) (hc : FallCertificate b ms) :
    ¬ Stable b := by
  rintro ⟨ps, hallowed, hbal⟩
  -- The total lift equals the work all pushes do on the motion ...
  have total : ((List.range b.length).map fun i => (ms.getD i default).lift).sum
      = (ps.map fun p => p.force *
          (rise b ms (.plank p.upper) p.x p.y - rise b ms p.lower p.x p.y)).sum := by
    calc ((List.range b.length).map fun i => (ms.getD i default).lift).sum
        = ((List.range b.length).map fun i =>
            (ps.map fun p => p.upOn i * rise b ms (.plank i) p.x p.y).sum).sum := by
          apply sum_map_congr
          intro i hi
          rw [balanced_rise b ms ps i (hbal i (List.mem_range.mp hi))]
      _ = (ps.map fun p => ((List.range b.length).map fun i =>
            p.upOn i * rise b ms (.plank i) p.x p.y).sum).sum := sum_map_sum_comm _ _ _
      _ = _ := sum_map_congr _ _ _ fun p hp => push_sum_over_planks b ms p (hallowed p hp)
  -- ... which is at least zero, but the certificate says it is below zero.
  have := sum_map_nonneg ps _ fun p hp => push_work_nonneg b ms hc p (hallowed p hp)
  have := hc.2
  grind

/-- Property 2: when the engine answers "falls", the build is not stable (S3). -/
theorem globalAnswer_falls_sound (b : Build) (h : globalAnswer b = .falls) :
    ¬ Stable b := by
  unfold globalAnswer at h
  split at h
  · split at h <;> cases h
  · split at h
    · exact fallCertificate_sound b _ (of_decide_eq_true (by assumption))
    · cases h
  · cases h

theorem fallbackAnswer_falls_sound (b : Build) (h : fallbackAnswer b = .falls) :
    ¬ Stable b := by
  unfold fallbackAnswer at h
  split at h
  · exact globalAnswer_falls_sound b h
  · cases h

theorem stabilityAnswer_falls_sound (b : Build) (h : stabilityAnswer b = .falls) :
    ¬ Stable b := by
  unfold stabilityAnswer at h
  split at h
  · split at h
    · cases h
    · exact fallbackAnswer_falls_sound b h
  · exact fallbackAnswer_falls_sound b h

/-! ## "Solid" answers are right -/

/-- If the solidity check passes, the build is solid. -/
theorem passes_sound (ε : Rat) (b : Build) (o : Option (List Load))
    (h : solidAnswer.passes ε b o = true) : SolidWithin ε b := by
  unfold solidAnswer.passes at h
  split at h
  · exact solidCertificate_sound ε b _ (of_decide_eq_true h)
  · cases h

theorem solidAnswer_sound (ε : Rat) (b : Build) (h : solidAnswer ε b = true) :
    SolidWithin ε b := by
  simp only [solidAnswer, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨_, h⟩ <;> exact passes_sound ε b _ h

/-- Property 3: when the engine's verdict is "solid", the build is stable for every
combination of placement errors up to `ε` (R3). -/
theorem verdict_solid_sound (ε : Rat) (b : Build) (h : verdict ε b = .solid) :
    SolidWithin ε b := by
  unfold verdict at h
  split at h
  · exact solidAnswer_sound ε b (by assumption)
  · split at h <;> cases h

/-- When the verdict is "risky", the build is stable at the exact positions (S2). -/
theorem verdict_risky_sound (ε : Rat) (b : Build) (h : verdict ε b = .risky) : Stable b := by
  unfold verdict at h
  split at h
  · cases h
  · split at h
    · exact stabilityAnswer_stable_sound b (by assumption)
    all_goals cases h

/-- When the verdict is "falls", the build is not stable (S3). -/
theorem verdict_falls_sound (ε : Rat) (b : Build) (h : verdict ε b = .falls) : ¬ Stable b := by
  unfold verdict at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact stabilityAnswer_falls_sound b (by assumption)
    · cases h

/-! ## Accepted plans are safe at every step -/

/-- Property 4: an accepted plan uses at most `maxPlanks` planks, and after every step the
build so far is well-formed and solid for placement errors up to `ε` (K4, K5). -/
theorem checkPlan_sound (ε : Rat) (maxPlanks : Nat) (steps : Build)
    (h : checkPlan ε maxPlanks steps = true) : SafePlan ε maxPlanks steps := by
  simp only [checkPlan, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  refine ⟨h.1, fun k hk1 hk2 => ?_⟩
  obtain ⟨hw, hs⟩ := h.2 (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at hw hs
  exact ⟨hw, solidAnswer_sound ε _ hs⟩

end KaplaPhysics
