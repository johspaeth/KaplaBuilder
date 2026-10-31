import KaplaPhysics.Engine
import KaplaPhysics.Sums
import KaplaPhysics.RobustProofs

/-! # Proofs of the physics theorems

The statements are in `specs/KaplaSpecs/Physics.lean`; `lake comparator` checks that the
names and statements here match them exactly. -/

namespace KaplaPhysics

open Solver (Motion allSupports)

/-! ## Contacts are right (property 7, C1–C3) -/

/-- The overlap of two rectangles holds exactly the points that lie in both. -/
theorem Rect.inter_contains (r s : Rect) (x y : Rat) :
    (r.inter s).Contains x y ↔ r.Contains x y ∧ s.Contains x y := by
  simp only [Rect.inter, Rect.Contains]
  grind

/-- A rectangle has an area bigger than zero exactly when some point lies strictly inside
it (C3: a line or a point is not enough). -/
theorem Rect.hasArea_iff (r : Rect) :
    r.HasArea ↔ ∃ x y, r.x0 < x ∧ x < r.x1 ∧ r.y0 < y ∧ y < r.y1 := by
  constructor
  · intro ⟨hx, hy⟩
    exact ⟨(r.x0 + r.x1) / 2, (r.y0 + r.y1) / 2, by grind, by grind, by grind, by grind⟩
  · rintro ⟨x, y, h1, h2, h3, h4⟩
    exact ⟨by grind, by grind⟩

/-- C1, C2: plank `i` rests on plank `j` over the patch `r` exactly when `i`'s bottom is at
the height of `j`'s top, `r` is the overlap of their footprints, and `r` has an area. -/
theorem restPatch_plank_iff (b : Build) (i j : Nat) (r : Rect) :
    restPatch b i (.plank j) = some r ↔
      (b.get i).z = (b.get j).top ∧ r = (b.get i).footprint.inter (b.get j).footprint ∧
        r.HasArea := by
  simp only [restPatch]
  split
  · rename_i h
    constructor
    · intro e; cases e; exact ⟨h.1, rfl, h.2⟩
    · rintro ⟨_, rfl, _⟩; rfl
  · rename_i h
    constructor
    · intro e; cases e
    · rintro ⟨hz, rfl, ha⟩; exact absurd ⟨hz, ha⟩ h

/-- C1, C2: plank `i` rests on the ground over the patch `r` exactly when its bottom is at
`z = 0` and `r` is its whole footprint. -/
theorem restPatch_ground_iff (b : Build) (i : Nat) (r : Rect) :
    restPatch b i .ground = some r ↔ (b.get i).z = 0 ∧ r = (b.get i).footprint := by
  simp only [restPatch]
  split
  · rename_i h
    constructor
    · intro e; cases e; exact ⟨h, rfl⟩
    · rintro ⟨_, rfl⟩; rfl
  · rename_i h
    constructor
    · intro e; cases e
    · rintro ⟨hz, _⟩; exact absurd hz h

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

/-! ## Reaching the spot (property 5, K3) -/

theorem dropMisses_sound (p q : Plank) (h : Rat) (hm : DropMisses p h q) (s : Rat)
    (hs0 : 0 ≤ s) (hsh : s ≤ h) : ¬ Overlap (p.moveBy 0 0 s) q := by
  simp only [DropMisses, OverlapXY] at hm
  simp only [Overlap, Plank.moveBy, Plank.x1, Plank.y1, Plank.top]
  simp only [Plank.x1, Plank.y1, Plank.top] at hm
  grind

theorem rayMisses_sound (d : Dir) (p q : Plank) (h : Rat) (hm : RayMisses d p h q) (t : Rat)
    (ht : 0 ≤ t) :
    ¬ Overlap (p.moveBy (t * d.vec.1) (t * d.vec.2.1) (h + t * d.vec.2.2)) q := by
  cases d <;> simp only [RayMisses, OverlapXY, OverlapZ] at hm <;>
    simp only [Dir.vec, Overlap, Plank.moveBy, Plank.x1, Plank.y1, Plank.top] <;>
    simp only [Plank.x1, Plank.y1, Plank.top] at hm <;> grind

/-- Property 5 ("reachable" is right): a direction the checker accepts gives a straight
path and a drop that touch no placed plank (K3). -/
theorem reachDir_sound (placed : Build) (p : Plank) (h : Rat) (d : Dir)
    (hd : reachDir? placed p h = some d) : StraightPath placed p h d.vec := by
  have hm := List.find?_some hd
  simp only [decide_eq_true_eq] at hm
  refine ⟨by cases d <;> decide, by cases d <;> decide +kernel, ?_, ?_⟩
  · intro t ht q hq; exact rayMisses_sound d p q h (hm q hq).2 t ht
  · intro s hs0 hsh q hq; exact dropMisses_sound p q h (hm q hq).1 s hs0 hsh

/-- Every step that `hardToReach` does not list can be put in place by a straight path. -/
theorem hardToReach_sound (h : Rat) (steps : Build) (k : Nat) (hk : k < steps.length)
    (hn : k ∉ hardToReach h steps) : Reachable (steps.take k) (steps.get k) h := by
  simp only [hardToReach, List.mem_filter, List.mem_range, Option.isNone_iff_eq_none,
    not_and] at hn
  cases hr : reachDir? (steps.take k) (steps.get k) h with
  | none => exact absurd hr (hn hk)
  | some d => exact ⟨d.vec, reachDir_sound _ _ _ d hr⟩

/-- When no step is hard to reach, every step can be put in place (K3 for a plan). -/
theorem hardToReach_nil_sound (h : Rat) (steps : Build) (hn : hardToReach h steps = []) :
    EveryStepReachable h steps := fun k hk =>
  hardToReach_sound h steps k hk (by simp [hn])

end KaplaPhysics
