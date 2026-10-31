import KaplaPhysics.Robust
import KaplaPhysics.Sums

/-! # A solidity certificate makes the build solid

Plan of the proof, for one combination of errors `d`:
1. Each load acts at a point inside the real contact patch (`load_patch`).
2. A push at a point inside a rectangle has the same effect as four pushes at its corners
   (`spread_*`, rule F4).
3. The certificate's equations give balance for this `d` (`solid_balanced`). -/

namespace KaplaPhysics

/-! ## Moving the build -/

@[simp] theorem shift_length (b : Build) (d : Nat → Rat × Rat) :
    (b.shift d).length = b.length := by
  simp [Build.shift]

theorem shift_get (b : Build) (d : Nat → Rat × Rat) (i : Nat) (h : i < b.length) :
    (b.shift d).get i = { b.get i with x := (b.get i).x + (d i).1, y := (b.get i).y + (d i).2 } := by
  simp [Build.shift, Build.get, List.getD_eq_getElem?_getD, h]

/-- Every pose has a length and a width bigger than zero. -/
theorem pose_size_pos (p : Pose) : 0 < p.size.dx ∧ 0 < p.size.dy := by
  cases p <;> decide +kernel

/-! ## Spreading a push over the corners of a rectangle (F4) -/

/-- Replace a push at a point inside `r` by four pushes at the corners of `r`. The weights
split the push in proportion to how close the point is to each corner. -/
def spreadOver (r : Rect) (p : Push) : List Push :=
  let a := (p.x - r.x0) / (r.x1 - r.x0)
  let c := (p.y - r.y0) / (r.y1 - r.y0)
  [{ p with x := r.x0, y := r.y0, force := p.force * (1 - a) * (1 - c) },
   { p with x := r.x1, y := r.y0, force := p.force * a * (1 - c) },
   { p with x := r.x0, y := r.y1, force := p.force * (1 - a) * c },
   { p with x := r.x1, y := r.y1, force := p.force * a * c }]

/-- Which way a push acts on plank `i`: `+1` up, `-1` down, `0` not at all. -/
def Push.sign (i : Nat) (p : Push) : Rat :=
  (if p.upper = i then 1 else 0) - (if p.lower = .plank i then 1 else 0)

theorem upOn_eq (i : Nat) (p : Push) : p.upOn i = p.force * p.sign i := by
  simp only [Push.upOn, Push.sign]; split <;> split <;> grind

theorem div_nonneg' {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  rw [Rat.div_def]; exact Rat.mul_nonneg ha (Rat.le_of_lt (Rat.inv_pos.mpr hb))

/-- The fraction of the way from `x0` to `x1` at which `t` lies, and its complement, are
both at least zero. -/
theorem frac_bounds (x0 x1 t : Rat) (h : x0 < x1) (h0 : x0 ≤ t) (h1 : t ≤ x1) :
    0 ≤ (t - x0) / (x1 - x0) ∧ 0 ≤ 1 - (t - x0) / (x1 - x0) := by
  refine ⟨div_nonneg' (by grind) (by grind), ?_⟩
  have : 1 - (t - x0) / (x1 - x0) = (x1 - t) / (x1 - x0) := by grind
  rw [this]; exact div_nonneg' (by grind) (by grind)

/-- Spreading keeps the net push on every plank. -/
theorem spread_force (r : Rect) (p : Push) (i : Nat) :
    ((spreadOver r p).map fun q => q.upOn i).sum = p.upOn i := by
  simp only [spreadOver, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, upOn_eq,
    Push.sign]
  grind

/-- Spreading keeps the turning effect along `x` on every plank. -/
theorem spread_turnX (r : Rect) (p : Push) (i : Nat) (c : Rat) (h : r.x0 < r.x1) :
    ((spreadOver r p).map fun q => q.upOn i * (q.x - c)).sum = p.upOn i * (p.x - c) := by
  simp only [spreadOver, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, upOn_eq,
    Push.sign]
  have : r.x1 - r.x0 ≠ 0 := by grind
  grind

/-- Spreading keeps the turning effect along `y` on every plank. -/
theorem spread_turnY (r : Rect) (p : Push) (i : Nat) (c : Rat) (h : r.y0 < r.y1) :
    ((spreadOver r p).map fun q => q.upOn i * (q.y - c)).sum = p.upOn i * (p.y - c) := by
  simp only [spreadOver, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, upOn_eq,
    Push.sign]
  have : r.y1 - r.y0 ≠ 0 := by grind
  grind

/-- Spreading a push from inside a contact patch gives four allowed corner pushes. -/
theorem spread_allowed (b : Build) (r : Rect) (p : Push)
    (hf : 0 ≤ p.force) (hu : p.upper < b.length) (hl : p.lower.InBuild b.length)
    (hr : restPatch b p.upper p.lower = some r) (hx : r.x0 < r.x1) (hy : r.y0 < r.y1)
    (hx0 : r.x0 ≤ p.x) (hx1 : p.x ≤ r.x1) (hy0 : r.y0 ≤ p.y) (hy1 : p.y ≤ r.y1) :
    ∀ q ∈ spreadOver r p, q.Allowed b := by
  obtain ⟨a0, a1⟩ := frac_bounds _ _ _ hx hx0 hx1
  obtain ⟨c0, c1⟩ := frac_bounds _ _ _ hy hy0 hy1
  intro q hq
  simp only [spreadOver, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;>
    refine ⟨?_, hu, hl, ?_⟩ <;> simp only [hr, Rect.corners, List.mem_cons] <;>
    first
    | simp
    | exact Rat.mul_nonneg (Rat.mul_nonneg hf (by assumption)) (by assumption)

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
    (b.get o).x + (d o).1 ≤ (l.at b.length d).x ∧
    (l.at b.length d).x ≤ (b.get o).x1 + (d o).1 ∧
    (b.get o).y + (d o).2 ≤ (l.at b.length d).y ∧
    (l.at b.length d).y ≤ (b.get o).y1 + (d o).2 := by
  have bx := relMix_bound ε l b.length o ho (fun m => (d m).1) fun m hm => ⟨(hd m hm).1, (hd m hm).2.1⟩
  have by' := relMix_bound ε l b.length o ho (fun m => (d m).2)
    fun m hm => ⟨(hd m hm).2.2.1, (hd m hm).2.2.2⟩
  simp only [Load.InsideOf] at hin
  simp only [Load.at]
  grind

/-- Under errors of at most `ε`, a valid load sits inside a real contact patch with an
area bigger than zero. -/
theorem load_patch (ε : Rat) (b : Build) (l : Load) (d : Nat → Rat × Rat)
    (hl : l.Valid ε b) (hd : SmallShift ε b.length d) :
    ∃ r, restPatch (b.shift d) l.upper l.lower = some r ∧ r.x0 < r.x1 ∧ r.y0 < r.y1 ∧
      r.x0 ≤ (l.at b.length d).x ∧ (l.at b.length d).x ≤ r.x1 ∧
      r.y0 ≤ (l.at b.length d).y ∧ (l.at b.length d).y ≤ r.y1 := by
  obtain ⟨_, hu, hin, hinU, hlow⟩ := hl
  have pu := inside_moved ε b l l.upper d hu hd hinU
  have du := hd l.upper hu
  cases hs : l.lower with
  | ground =>
    rw [hs] at hlow
    have := pose_size_pos (b.get l.upper).pose
    refine ⟨((b.shift d).get l.upper).footprint, ?_, ?_⟩
    · simp [restPatch, shift_get b d _ hu, hlow]
    · simp only [shift_get b d _ hu, Plank.footprint, Plank.x1, Plank.y1] at pu ⊢
      grind
  | plank j =>
    rw [hs] at hlow hin
    obtain ⟨hz, harea, hinJ⟩ := hlow
    have hj : j < b.length := hin
    have pj := inside_moved ε b l j d hj hd hinJ
    have dj := hd j hj
    simp only [Rect.HasArea, Rect.shrink, Rect.inter, Plank.footprint] at harea
    refine ⟨((b.shift d).get l.upper).footprint.inter ((b.shift d).get j).footprint, ?_, ?_⟩
    · simp only [restPatch, shift_get b d _ hu, shift_get b d _ hj]
      rw [ite_eq_left_iff]
      intro hn; apply absurd _ hn
      refine ⟨by simpa [Plank.top] using hz, ?_⟩
      simp only [Rect.HasArea, Rect.inter, Plank.footprint, Plank.x1, Plank.y1] at harea ⊢
      grind
    · simp only [shift_get b d _ hu, shift_get b d _ hj, Rect.inter, Plank.footprint,
        Plank.x1, Plank.y1] at pu pj harea ⊢
      grind

/-! ## The certificate gives balance for every error -/

/-- The pushes for errors `d`: every load, spread over the corners of its real patch. -/
def solidPushes (b : Build) (ls : List Load) (d : Nat → Rat × Rat) : List Push :=
  ls.flatMap fun l =>
    spreadOver ((restPatch (b.shift d) l.upper l.lower).getD default) (l.at b.length d)

theorem solid_allowed (ε : Rat) (b : Build) (ls : List Load) (d : Nat → Rat × Rat)
    (hc : SolidCertificate ε b ls) (hd : SmallShift ε b.length d) :
    ∀ p ∈ solidPushes b ls d, p.Allowed (b.shift d) := by
  intro p hp
  simp only [solidPushes, List.mem_flatMap] at hp
  obtain ⟨l, hl, hp⟩ := hp
  have hv := hc.1 l hl
  obtain ⟨r, hr, hx, hy, hx0, hx1, hy0, hy1⟩ := load_patch ε b l d hv hd
  rw [hr] at hp
  exact spread_allowed (b.shift d) r (l.at b.length d) hv.1 (by simpa [Load.at] using hv.2.1)
    (by have := hv.2.2.1; cases h : l.lower <;> simp_all [Support.InBuild, Load.at])
    hr hx hy hx0 hx1 hy0 hy1 p hp

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
    (hc : SolidCertificate ε b ls) (hd : SmallShift ε b.length d) (i : Nat)
    (hi : i < b.length) : Balanced (b.shift d) (solidPushes b ls d) i := by
  have hb := hc.2 i hi
  have patch : ∀ l ∈ ls, ∃ r, restPatch (b.shift d) l.upper l.lower = some r ∧
      r.x0 < r.x1 ∧ r.y0 < r.y1 := fun l hl => by
    obtain ⟨r, hr, hx, hy, _⟩ := load_patch ε b l d (hc.1 l hl) hd
    exact ⟨r, hr, hx, hy⟩
  have mx := mix_total b ls i hi (fun m => (d m).1) hb
  have my := mix_total b ls i hi (fun m => (d m).2) hb
  obtain ⟨h1, h2, h3, _⟩ := balancedLoads_full b ls i hb
  have cx : ((b.shift d).get i).centerX = (b.get i).centerX + (d i).1 := by
    rw [shift_get b d i hi]; simp only [Plank.centerX]; grind
  have cy : ((b.shift d).get i).centerY = (b.get i).centerY + (d i).2 := by
    rw [shift_get b d i hi]; simp only [Plank.centerY]; grind
  refine ⟨?_, ?_, ?_⟩
  · rw [solidPushes, sum_flatMap,
      sum_map_congr _ _ _ fun l _ => spread_force _ (l.at b.length d) i]
    simpa only [at_upOn] using h1
  · rw [solidPushes, sum_flatMap, sum_map_congr _ _ (fun l => l.upOn i *
        (l.x + mixSum b.length l.mix (fun m => (d m).1) - ((b.shift d).get i).centerX))]
    · rw [sum_map_congr _ _ (fun l => l.upOn i * l.x + l.upOn i * mixSum b.length l.mix
          (fun m => (d m).1) - l.upOn i * ((b.shift d).get i).centerX) (fun _ _ => by grind),
        sum_map_sub, sum_map_add, sum_map_mul_right, h1, h2, mx, cx]
      grind
    · intro l hl
      obtain ⟨r, hr, hx, _⟩ := patch l hl
      rw [hr]; exact spread_turnX r _ i _ hx
  · rw [solidPushes, sum_flatMap, sum_map_congr _ _ (fun l => l.upOn i *
        (l.y + mixSum b.length l.mix (fun m => (d m).2) - ((b.shift d).get i).centerY))]
    · rw [sum_map_congr _ _ (fun l => l.upOn i * l.y + l.upOn i * mixSum b.length l.mix
          (fun m => (d m).2) - l.upOn i * ((b.shift d).get i).centerY) (fun _ _ => by grind),
        sum_map_sub, sum_map_add, sum_map_mul_right, h1, h3, my, cy]
      grind
    · intro l hl
      obtain ⟨r, hr, _, hy⟩ := patch l hl
      rw [hr]; exact spread_turnY r _ i _ hy

/-- A passing solidity certificate makes the build solid (R3). -/
theorem solidCertificate_sound (ε : Rat) (b : Build) (ls : List Load)
    (hc : SolidCertificate ε b ls) : SolidWithin ε b := by
  intro d hd
  refine ⟨solidPushes b ls d, solid_allowed ε b ls d hc hd, ?_⟩
  intro i hi
  rw [shift_length] at hi
  exact solid_balanced ε b ls d hc hd i hi

/-- With no errors, the build is the planned one. -/
theorem shift_zero (b : Build) : b.shift (fun _ => (0, 0)) = b := by
  apply List.ext_getElem
  · simp [Build.shift]
  · intro i _ _; simp only [Build.shift, List.getElem_mapIdx]
    rw [Rat.add_zero, Rat.add_zero]

/-- A solid build is stable at the exact positions. -/
theorem solid_stable (ε : Rat) (b : Build) (hε : 0 ≤ ε) (h : SolidWithin ε b) : Stable b := by
  have := h (fun _ => (0, 0)) (fun _ _ => by simp only; grind)
  rwa [shift_zero] at this

end KaplaPhysics
