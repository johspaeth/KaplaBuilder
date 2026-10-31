import KaplaPhysics.Engine

/-! # Proofs of the physics theorems

The statements are in `specs/KaplaSpecs/Physics.lean`; `lake comparator` checks that the
names and statements here match them exactly. -/

namespace KaplaPhysics

open Solver (Motion allSupports)

/-! ## Sums of lists of fractions -/

section Sums

variable {α β : Type}

theorem sum_map_add (l : List α) (f g : α → Rat) :
    (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp <;> grind
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; grind

theorem sum_map_sub (l : List α) (f g : α → Rat) :
    (l.map fun a => f a - g a).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp <;> grind
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; grind

theorem sum_map_mul_left (l : List α) (c : Rat) (f : α → Rat) :
    (l.map fun a => c * f a).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp <;> grind
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; grind

theorem sum_map_zero (l : List α) : (l.map fun _ => (0 : Rat)).sum = 0 := by
  induction l with
  | nil => simp <;> grind
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; grind

theorem sum_map_congr (l : List α) (f g : α → Rat) (h : ∀ a ∈ l, f a = g a) :
    (l.map f).sum = (l.map g).sum := by
  rw [List.map_congr_left h]

theorem sum_map_nonneg (l : List α) (f : α → Rat) (h : ∀ a ∈ l, 0 ≤ f a) :
    0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp <;> grind
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (by simp)
    have h2 := ih fun x hx => h x (by simp [hx])
    grind

/-- Two sums can be done in either order. -/
theorem sum_map_sum_comm (l₁ : List α) (l₂ : List β) (F : α → β → Rat) :
    (l₁.map fun a => (l₂.map fun b => F a b).sum).sum
      = (l₂.map fun b => (l₁.map fun a => F a b).sum).sum := by
  induction l₂ with
  | nil => simp [sum_map_zero]
  | cons b l₂ ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [sum_map_add, ih]

/-- Summing over `0, ..., n-1` a term that is zero except at `a < n` gives the term at `a`. -/
theorem sum_range_single (n a : Nat) (ha : a < n) (f : Nat → Rat) :
    ((List.range n).map fun i => if a = i then f i else 0).sum = f a := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases h : a = n
    · subst h
      have : ((List.range a).map fun i => if a = i then f i else 0).sum = 0 := by
        rw [sum_map_congr _ _ (fun _ => 0)]
        · exact sum_map_zero _
        · intro i hi; simp at hi; simp; omega
      simp [this] <;> grind
    · rw [ih (by omega)]; simp [h] <;> grind

end Sums

/-! ## "Stable" answers are right -/

/-- If the push check passes, the build is stable (S2). -/
theorem checkPushes_sound (b : Build) (ps : List Push) (h : checkPushes b ps = true) :
    Stable b := by
  simp only [checkPushes, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨ps, h.1, h.2⟩

/-- Property 1: when the engine answers "stable", the build is stable (S2). -/
theorem stabilityAnswer_stable_sound (b : Build) (h : stabilityAnswer b = .stable) :
    Stable b := by
  unfold stabilityAnswer at h
  split at h
  · split at h
    · exact checkPushes_sound b _ (by assumption)
    · cases h
  · split at h <;> cases h
  · cases h

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
theorem stabilityAnswer_falls_sound (b : Build) (h : stabilityAnswer b = .falls) :
    ¬ Stable b := by
  unfold stabilityAnswer at h
  split at h
  · split at h <;> cases h
  · split at h
    · exact fallCertificate_sound b _ (of_decide_eq_true (by assumption))
    · cases h
  · cases h

/-! ## Accepted plans stand at every step -/

/-- Property 4 (at the exact positions): an accepted plan uses at most `maxPlanks` planks,
and after every step the build so far is well-formed and stable. -/
theorem checkPlan_sound (maxPlanks : Nat) (steps : Build)
    (h : checkPlan maxPlanks steps = true) : StandsAtEveryStep maxPlanks steps := by
  simp only [checkPlan, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at h
  refine ⟨h.1, fun k hk1 hk2 => ?_⟩
  obtain ⟨hw, hs⟩ := h.2 (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at hw hs
  exact ⟨hw, stabilityAnswer_stable_sound _ hs⟩

end KaplaPhysics
