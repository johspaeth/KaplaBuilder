import KaplaPhysics.Robust
import KaplaPhysics.Sums
import KaplaSpecs.PhysicsRules.Examples

/-! # A solidity certificate makes the build solid

Plan of the proof, for one combination of errors `d`:
1. Each load acts at a point inside the real contact patch, and the patch still has an area
   (`load_allowed`).
2. The certificate's equations give balance for this `d` (`solid_balanced`). -/

namespace KaplaPhysics

open KaplaCore (Pose)

/-! ## Moving the build -/

@[simp] theorem shift_length (b : Build) (d : Nat → Rat × Rat) :
    (b.shift d).length = b.length := by
  simp [Build.shift]

theorem shift_get (b : Build) (d : Nat → Rat × Rat) (i : Nat) (h : i < b.length) :
    (b.shift d).get i = (b.get i).moveBy (d i).1 (d i).2 0 := by
  simp [Build.shift, Build.get, List.getD_eq_getElem?_getD, h]

/-- Which way a push acts on plank `i`: `+1` up, `-1` down, `0` not at all. -/
def Push.sign (i : Nat) (p : Push) : Rat :=
  (if p.upper = i then 1 else 0) - (if p.lower = .plank i then 1 else 0)

theorem upOn_eq (i : Nat) (p : Push) : p.upOn i = p.force * p.sign i := by
  simp only [Push.upOn, Push.sign]; split <;> split <;> grind

theorem div_nonneg' {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  rw [Rat.div_def]; exact Rat.mul_nonneg ha (Rat.le_of_lt (Rat.inv_pos.mpr hb))

/-- A side of a moved plank, at a moved point, has its old value at the point moved back. -/
theorem moved_side (p : Plank) (dx dy x y : Rat) (g : Aff) (hg : g ∈ (p.moveBy dx dy 0).sides) :
    ∃ g0 ∈ p.sides, g.eval x y = g0.eval (x - dx) (y - dy) ∧ g0.slope = g.slope := by
  rw [sides_moveBy] at hg
  obtain ⟨g0, h0, rfl⟩ := List.mem_map.mp hg
  exact ⟨g0, h0, Aff.shift_eval _ _ _ _ _, by simp [Aff.slope, Aff.shift]⟩

/-- A side's value changes by at most `e * slope` when the point moves by at most `e`. -/
theorem eval_move (g : Aff) (x y u v e : Rat) (hu : -e ≤ u ∧ u ≤ e) (hv : -e ≤ v ∧ v ≤ e) :
    g.eval x y - e * g.slope ≤ g.eval (x + u) (y + v) := by
  have := (Aff.lin_le g e u v hu hv).2
  simp only [Aff.eval]; grind

/-! ## Loads under errors -/

/-- The weighted sum of the planks' errors along one axis. -/
def mixSum (n : Nat) (mix : Array Rat) (e : Nat → Rat) : Rat :=
  ((List.range n).map fun m => mix.getD m 0 * e m).sum

/-- The push a load gives when the planks land with errors `d`. -/
def Load.at (l : Load) (n : Nat) (d : Nat → Rat × Rat) : Push :=
  { upper := l.upper, lower := l.lower, force := l.force,
    x := l.x + mixSum n l.mix (fun m => (d m).1),
    y := l.y + mixSum n l.mix (fun m => (d m).2) }

theorem at_upOn (l : Load) (n : Nat) (d : Nat → Rat × Rat) (i : Nat) :
    (l.at n d).upOn i = l.upOn i := rfl

/-- The load point, relative to plank `o`, moves by the weighted sum of `relMix`. -/
theorem sum_relMix (l : Load) (n o : Nat) (ho : o < n) (e : Nat → Rat) :
    ((List.range n).map fun m => l.relMix o m * e m).sum = mixSum n l.mix e - e o := by
  rw [sum_map_congr _ _ (fun m => l.mix.getD m 0 * e m - if o = m then e m else 0),
    sum_map_sub, sum_range_single n o ho e]
  · rfl
  · intro m _; simp only [Load.relMix]; split <;> split <;> grind

/-- For errors of at most `ε`, the load point stays within `ε * drift` of where it moves
with plank `o`. -/
theorem relMix_bound (ε : Rat) (l : Load) (n o : Nat) (ho : o < n) (e : Nat → Rat)
    (he : ∀ m < n, -ε ≤ e m ∧ e m ≤ ε) :
    mixSum n l.mix e - e o ≤ ε * l.drift n o ∧ -(ε * l.drift n o) ≤ mixSum n l.mix e - e o := by
  rw [← sum_relMix l n o ho e]
  exact sum_mul_le _ _ _ ε fun m hm => he m (List.mem_range.mp hm)

/-- The load point stays inside plank `o`'s moved footprint. -/
theorem inside_moved (ε : Rat) (b : Build) (l : Load) (o : Nat) (d : Nat → Rat × Rat)
    (ho : o < b.length) (hd : SmallShift ε b.length d) (hin : l.InsideOf ε b o) :
    ((b.shift d).get o).Covers (l.at b.length d).x (l.at b.length d).y := by
  have bx := relMix_bound ε l b.length o ho (fun m => (d m).1) fun m hm => ⟨(hd m hm).1, (hd m hm).2.1⟩
  have by' := relMix_bound ε l b.length o ho (fun m => (d m).2)
    fun m hm => ⟨(hd m hm).2.2.1, (hd m hm).2.2.2⟩
  rw [covers_iff_sides, shift_get b d o ho]
  intro g hg
  obtain ⟨g0, h0, he, -⟩ := moved_side _ _ _ _ _ g hg
  rw [he]
  have hm := eval_move g0 l.x l.y (mixSum b.length l.mix (fun m => (d m).1) - (d o).1)
    (mixSum b.length l.mix (fun m => (d m).2) - (d o).2) (ε * l.drift b.length o)
    ⟨by grind, by grind⟩ ⟨by grind, by grind⟩
  have := hin g0 h0
  simp only [Load.at]
  rw [show l.x + mixSum b.length l.mix (fun m => (d m).1) - (d o).1
      = l.x + (mixSum b.length l.mix (fun m => (d m).1) - (d o).1) by grind,
    show l.y + mixSum b.length l.mix (fun m => (d m).2) - (d o).2
      = l.y + (mixSum b.length l.mix (fun m => (d m).2) - (d o).2) by grind]
  grind

/-- Under errors of at most `ε`, a valid load gives an allowed push in the moved build. -/
theorem load_allowed (ε : Rat) (b : Build) (l : Load) (d : Nat → Rat × Rat)
    (hl : l.Valid ε b) (hd : SmallShift ε b.length d) :
    (l.at b.length d).Allowed (b.shift d) := by
  obtain ⟨hf, hu, hin, hinU, hlow⟩ := hl
  have pu := inside_moved ε b l l.upper d hu hd hinU
  have du := hd l.upper hu
  refine ⟨hf, by simpa [Load.at] using hu, ?_, ?_, ?_⟩
  · cases h : l.lower with
    | ground => simp [Load.at, h, Support.InBuild]
    | plank j => rw [h] at hin; simpa [Load.at, h, Support.InBuild] using hin
  · cases hs : l.lower with
    | ground =>
      rw [hs] at hlow
      simp only [Load.at, hs, RestsOn, shift_get b d _ hu, moveBy_bottom]; grind
    | plank j =>
      rw [hs] at hlow hin
      obtain ⟨hz, -, hwU, hwJ⟩ := hlow
      have hj : j < b.length := hin
      have dj := hd j hj
      simp only [Load.at, hs, RestsOn, shift_get b d _ hu, shift_get b d _ hj, moveBy_bottom,
        moveBy_top]
      refine ⟨by grind, l.wx + (d l.upper).1, l.wy + (d l.upper).2, ?_, ?_⟩
      · rw [coversInside_iff_sides]
        intro g hg
        obtain ⟨g0, h0, he, -⟩ := moved_side _ _ _ _ _ g hg
        rw [he]
        have := hwU g0 h0
        rw [show l.wx + (d l.upper).1 - (d l.upper).1 = l.wx by grind,
          show l.wy + (d l.upper).2 - (d l.upper).2 = l.wy by grind]
        exact this
      · rw [coversInside_iff_sides]
        intro g hg
        obtain ⟨g0, h0, he, -⟩ := moved_side _ _ _ _ _ g hg
        rw [he]
        have hm := eval_move g0 l.wx l.wy ((d l.upper).1 - (d j).1) ((d l.upper).2 - (d j).2)
          (2 * ε) ⟨by grind, by grind⟩ ⟨by grind, by grind⟩
        have := hwJ g0 h0
        rw [show l.wx + (d l.upper).1 - (d j).1 = l.wx + ((d l.upper).1 - (d j).1) by grind,
          show l.wy + (d l.upper).2 - (d j).2 = l.wy + ((d l.upper).2 - (d j).2) by grind]
        grind
  · cases hs : l.lower with
    | ground => exact ⟨by simpa [Load.at] using pu, by simp [Load.at, hs]⟩
    | plank j =>
      rw [hs] at hlow hin
      have hj : j < b.length := hin
      refine ⟨by simpa [Load.at] using pu, ?_⟩
      simp only [Load.at, hs]
      exact inside_moved ε b l j d hj hd hlow.2.1

/-! ## The certificate gives balance for every error -/

/-- The pushes for errors `d`: every load, at its moved point. -/
def solidPushes (b : Build) (ls : List Load) (d : Nat → Rat × Rat) : List Push :=
  ls.map fun l => l.at b.length d

theorem solid_allowed (ε : Rat) (b : Build) (ls : List Load) (d : Nat → Rat × Rat)
    (hc : SolidCertificate ε b ls) (hd : SmallShift ε b.length d) :
    ∀ p ∈ solidPushes b ls d, p.Allowed (b.shift d) := by
  intro p hp
  simp only [solidPushes, List.mem_map] at hp
  obtain ⟨l, hl, rfl⟩ := hp
  exact load_allowed ε b l d (hc.2.1 l hl) hd

/-- Loads that do not touch plank `i` do not lift it. -/
theorem upOn_of_not_touches (i : Nat) (l : Load) (h : l.Touches i = false) : l.upOn i = 0 := by
  simp only [Load.Touches, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  simp [Load.upOn, h.1, h.2]; grind

/-- Summing over the loads that touch plank `i` is the same as summing over all loads. -/
theorem sum_near (ls : List Load) (i : Nat) (f : Load → Rat) :
    ((ls.filter (Load.Touches i)).map fun l => l.upOn i * f l).sum
      = (ls.map fun l => l.upOn i * f l).sum := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    by_cases h : l.Touches i = true
    · simp [h, ih]
    · simp only [Bool.not_eq_true] at h
      simp [h, ih, upOn_of_not_touches i l h]; grind

/-- `BalancedLoads`, with the sums taken over all loads. -/
theorem balancedLoads_full (b : Build) (ls : List Load) (i : Nat) (hb : BalancedLoads b ls i) :
    (ls.map fun l => l.upOn i).sum = 1 ∧
    (ls.map fun l => l.upOn i * l.x).sum = (b.get i).centerX ∧
    (ls.map fun l => l.upOn i * l.y).sum = (b.get i).centerY ∧
    ∀ m < b.length, (ls.map fun l => l.upOn i * l.mix.getD m 0).sum = if m = i then 1 else 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  refine ⟨?_, ?_, ?_, fun m hm => ?_⟩
  · have := sum_near ls i (fun _ => 1); simp only [Rat.mul_one] at this; rw [← this]; exact h1
  · rw [← sum_near]; exact h2
  · rw [← sum_near]; exact h3
  · rw [← sum_near]; exact h4 m hm

/-- The planks' errors, weighted by how the loads on plank `i` move with them, add up to
plank `i`'s own error. -/
theorem mix_total (b : Build) (ls : List Load) (i : Nat) (hi : i < b.length) (e : Nat → Rat)
    (hb : BalancedLoads b ls i) :
    (ls.map fun l => l.upOn i * mixSum b.length l.mix e).sum = e i := by
  obtain ⟨_, _, _, hm⟩ := balancedLoads_full b ls i hb
  calc (ls.map fun l => l.upOn i * mixSum b.length l.mix e).sum
      = (ls.map fun l => ((List.range b.length).map fun m =>
          l.upOn i * l.mix.getD m 0 * e m).sum).sum := by
        apply sum_map_congr; intro l _
        simp only [mixSum]; rw [← sum_map_mul_left]
        apply sum_map_congr; intro m _; grind
    _ = ((List.range b.length).map fun m =>
          (ls.map fun l => l.upOn i * l.mix.getD m 0).sum * e m).sum := by
        rw [← sum_map_sum_comm]
        apply sum_map_congr; intro m _
        rw [← sum_map_mul_right]
    _ = ((List.range b.length).map fun m => if i = m then e m else 0).sum := by
        apply sum_map_congr; intro m hmr
        rw [hm m (List.mem_range.mp hmr)]
        split <;> split <;> grind
    _ = e i := sum_range_single _ _ hi e

theorem solid_balanced (ε : Rat) (b : Build) (ls : List Load) (d : Nat → Rat × Rat)
    (hc : SolidCertificate ε b ls) (i : Nat)
    (hi : i < b.length) : Balanced (b.shift d) (solidPushes b ls d) i := by
  have hb := hc.2.2 i hi
  have mx := mix_total b ls i hi (fun m => (d m).1) hb
  have my := mix_total b ls i hi (fun m => (d m).2) hb
  obtain ⟨h1, h2, h3, _⟩ := balancedLoads_full b ls i hb
  have cx : ((b.shift d).get i).centerX = (b.get i).centerX + (d i).1 := by
    rw [shift_get b d i hi]; simp only [Pose.centerX, Pose.moveBy]
  have cy : ((b.shift d).get i).centerY = (b.get i).centerY + (d i).2 := by
    rw [shift_get b d i hi]; simp only [Pose.centerY, Pose.moveBy]
  unfold Balanced
  simp only [solidPushes, List.map_map, Function.comp_def, at_upOn]
  refine ⟨h1, ?_, ?_⟩
  · rw [sum_map_congr _ _ (fun l => l.upOn i * l.x + l.upOn i * mixSum b.length l.mix
        (fun m => (d m).1) - l.upOn i * ((b.shift d).get i).centerX)
        (fun _ _ => by simp only [Load.at]; grind),
      sum_map_sub, sum_map_add, sum_map_mul_right, h1, h2, mx, cx]
    grind
  · rw [sum_map_congr _ _ (fun l => l.upOn i * l.y + l.upOn i * mixSum b.length l.mix
        (fun m => (d m).2) - l.upOn i * ((b.shift d).get i).centerY)
        (fun _ _ => by simp only [Load.at]; grind),
      sum_map_sub, sum_map_add, sum_map_mul_right, h1, h3, my, cy]
    grind

/-- A passing solidity certificate makes the build solid (R3). -/
theorem solidCertificate_sound (ε : Rat) (b : Build) (ls : List Load)
    (hc : SolidCertificate ε b ls) : SolidWithin ε b := by
  refine ⟨hc.1, fun d hd => ?_⟩
  refine ⟨solidPushes b ls d, solid_allowed ε b ls d hc hd, ?_⟩
  intro i hi
  rw [shift_length] at hi
  exact solid_balanced ε b ls d hc i hi

/-- With no errors, the build is the planned one. -/
theorem shift_zero (b : Build) : b.shift (fun _ => (0, 0)) = b := Examples.shift_zero b

/-- A solid build is stable at the exact positions. -/
theorem solid_stable (ε : Rat) (b : Build) (h : SolidWithin ε b) : Stable b := by
  have hε := h.1
  have := h.2 (fun _ => (0, 0)) (fun _ _ => by simp only; grind)
  rwa [shift_zero] at this

end KaplaPhysics
