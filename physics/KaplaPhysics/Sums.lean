/-! # Sums of lists of fractions

Small facts about `List.sum` over `Rat`, used by the physics proofs. -/

namespace KaplaPhysics

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

theorem sum_map_mul_right (l : List α) (c : Rat) (f : α → Rat) :
    (l.map fun a => f a * c).sum = (l.map f).sum * c := by
  rw [sum_map_congr _ _ (fun a => c * f a) (fun _ _ => by grind), sum_map_mul_left]; grind

theorem sum_flatMap (l : List α) (f : α → List β) (g : β → Rat) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- The weighted sum `Σ c m * e m` is at most `ε * Σ size (c m)` in size, when every
`e m` is at most `ε` in size. -/
theorem sum_mul_le (L : List Nat) (c e : Nat → Rat) (ε : Rat)
    (he : ∀ m ∈ L, -ε ≤ e m ∧ e m ≤ ε) :
    (L.map fun m => c m * e m).sum ≤ ε * (L.map fun m => max (c m) (-(c m))).sum ∧
    -(ε * (L.map fun m => max (c m) (-(c m))).sum) ≤ (L.map fun m => c m * e m).sum := by
  induction L with
  | nil => simp
  | cons m L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hm := he m (by simp)
    have ih := ih fun k hk => he k (by simp [hk])
    by_cases hc : 0 ≤ c m
    · have h1 := Rat.mul_nonneg hc (show 0 ≤ ε - e m by grind)
      have h2 := Rat.mul_nonneg hc (show 0 ≤ ε + e m by grind)
      have hmax : max (c m) (-(c m)) = c m := by grind
      rw [hmax]; grind
    · have h1 := Rat.mul_nonneg (show 0 ≤ -(c m) by grind) (show 0 ≤ ε - e m by grind)
      have h2 := Rat.mul_nonneg (show 0 ≤ -(c m) by grind) (show 0 ≤ ε + e m by grind)
      have hmax : max (c m) (-(c m)) = -(c m) := by grind
      rw [hmax]; grind

end Sums

end KaplaPhysics
