import KaplaSpecs.PhysicsRules.Rules
import KaplaPhysics.Sums

/-! # Footprints as sides, and certificates about them

Seen from above, a plank covers a rectangle that may be turned. We write it as four
*sides*: four expressions `a * x + b * y + c` that are all at least zero exactly on the
footprint (`covers_iff_sides`).

Many questions are then about a few such expressions:

* "two planks share no area": some weights `≥ 0` on their sides add up to a number that
  does not depend on the point and is not above zero (`no_common_inside`);
* "the motion lifts the upper plank at every point of the patch": the rise is a weighted
  sum of the patch's sides plus a number `≥ 0` (`nonneg_on`).

The engine proposes the weights (untrusted); checking them is a few multiplications. The
polygon clipping at the end only proposes points; nothing depends on it being right. -/

namespace KaplaPhysics

open KaplaCore (Pose Rot)

/-- The expression `a * x + b * y + c` in the point `(x, y)`. -/
structure Aff where
  a : Rat
  b : Rat
  c : Rat
  deriving Repr, DecidableEq, Inhabited

namespace Aff

/-- The value at the point `(x, y)`. -/
def eval (f : Aff) (x y : Rat) : Rat := f.a * x + f.b * y + f.c

/-- The same expression for a plank moved by `(dx, dy)`: its value at a moved point is the
old value at the old point. -/
def shift (f : Aff) (dx dy : Rat) : Aff := ⟨f.a, f.b, f.c - f.a * dx - f.b * dy⟩

/-- How fast the value can change when the point moves at most 1 along `x` and at most 1
along `y`: `|a| + |b|`. -/
def slope (f : Aff) : Rat := max f.a (-f.a) + max f.b (-f.b)

theorem shift_eval (f : Aff) (dx dy x y : Rat) :
    (f.shift dx dy).eval x y = f.eval (x - dx) (y - dy) := by
  simp only [eval, shift]; grind

theorem slope_nonneg (f : Aff) : 0 ≤ f.slope := by
  simp only [slope]; grind

/-- `|a * dx + b * dy| ≤ e * (|a| + |b|)` when `dx` and `dy` are at most `e` in size. -/
theorem lin_le (f : Aff) (e dx dy : Rat) (hx : -e ≤ dx ∧ dx ≤ e) (hy : -e ≤ dy ∧ dy ≤ e) :
    f.a * dx + f.b * dy ≤ e * f.slope ∧ -(e * f.slope) ≤ f.a * dx + f.b * dy := by
  simp only [slope]
  have ha : f.a * dx ≤ e * max f.a (-f.a) ∧ -(e * max f.a (-f.a)) ≤ f.a * dx := by
    by_cases h : 0 ≤ f.a
    · have h1 := Rat.mul_nonneg h (show 0 ≤ e - dx by grind)
      have h2 := Rat.mul_nonneg h (show 0 ≤ e + dx by grind)
      rw [show max f.a (-f.a) = f.a by grind]; constructor <;> grind
    · have h1 := Rat.mul_nonneg (show 0 ≤ -f.a by grind) (show 0 ≤ e - dx by grind)
      have h2 := Rat.mul_nonneg (show 0 ≤ -f.a by grind) (show 0 ≤ e + dx by grind)
      rw [show max f.a (-f.a) = -f.a by grind]; constructor <;> grind
  have hb : f.b * dy ≤ e * max f.b (-f.b) ∧ -(e * max f.b (-f.b)) ≤ f.b * dy := by
    by_cases h : 0 ≤ f.b
    · have h1 := Rat.mul_nonneg h (show 0 ≤ e - dy by grind)
      have h2 := Rat.mul_nonneg h (show 0 ≤ e + dy by grind)
      rw [show max f.b (-f.b) = f.b by grind]; constructor <;> grind
    · have h1 := Rat.mul_nonneg (show 0 ≤ -f.b by grind) (show 0 ≤ e - dy by grind)
      have h2 := Rat.mul_nonneg (show 0 ≤ -f.b by grind) (show 0 ≤ e + dy by grind)
      rw [show max f.b (-f.b) = -f.b by grind]; constructor <;> grind
  constructor <;> grind

end Aff

/-! ## The four sides of a footprint -/

/-- The four sides of the plank's footprint: half the length minus and plus the distance
along the length, and half the width minus and plus the distance along the width. All four
are at least zero exactly on the footprint. -/
def _root_.KaplaCore.Pose.sides (p : Plank) : List Aff :=
  let c := p.rot.cos
  let s := p.rot.sin
  let cx := p.center.x
  let cy := p.center.y
  [⟨-c, -s, p.size.x / 2 + (c * cx + s * cy)⟩, ⟨c, s, p.size.x / 2 - (c * cx + s * cy)⟩,
   ⟨s, -c, p.size.y / 2 + (-s * cx + c * cy)⟩, ⟨-s, c, p.size.y / 2 - (-s * cx + c * cy)⟩]

theorem sides_eval (p : Plank) (x y : Rat) :
    p.sides.map (·.eval x y) =
      [p.size.x / 2 - p.alongLength x y, p.size.x / 2 + p.alongLength x y,
       p.size.y / 2 - p.alongWidth x y, p.size.y / 2 + p.alongWidth x y] := by
  simp only [Pose.sides, List.map_cons, List.map_nil, Aff.eval, Pose.alongLength,
    Pose.alongWidth, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- Seen from above, a point is under the plank exactly when all four sides are at least
zero there. -/
theorem covers_iff_sides (p : Plank) (x y : Rat) :
    p.Covers x y ↔ ∀ g ∈ p.sides, 0 ≤ g.eval x y := by
  have e := sides_eval p x y
  simp only [Pose.sides, List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  simp only [Pose.Covers, Pose.sides, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq]
  rw [e1, e2, e3, e4]
  constructor
  · intro h; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind
  · intro h; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- A point is strictly inside the footprint exactly when all four sides are above zero. -/
theorem coversInside_iff_sides (p : Plank) (x y : Rat) :
    p.CoversInside x y ↔ ∀ g ∈ p.sides, 0 < g.eval x y := by
  have e := sides_eval p x y
  simp only [Pose.sides, List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  simp only [Pose.CoversInside, Pose.sides, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq]
  rw [e1, e2, e3, e4]
  constructor
  · intro h; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind
  · intro h; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- Moving a plank moves its sides. -/
theorem sides_moveBy (p : Plank) (dx dy dz : Rat) :
    (p.moveBy dx dy dz).sides = p.sides.map (·.shift dx dy) := by
  simp only [Pose.sides, Pose.moveBy, Pose.size, Aff.shift, List.map_cons, List.map_nil,
    List.cons.injEq, Aff.mk.injEq, and_true, true_and]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem moveBy_zero (p : Plank) : p.moveBy 0 0 0 = p := by
  simp [Pose.moveBy, Rat.add_zero]

theorem moveBy_bottom (p : Plank) (dx dy dz : Rat) :
    (p.moveBy dx dy dz).bottom = p.bottom + dz := by
  simp only [Pose.moveBy, Pose.bottom, Pose.size]; grind

theorem moveBy_top (p : Plank) (dx dy dz : Rat) :
    (p.moveBy dx dy dz).top = p.top + dz := by
  simp only [Pose.moveBy, Pose.top, Pose.size]; grind

/-! ## Weighted sums of sides -/

/-- Some expressions, each with a weight. -/
abbrev Cert := List (Rat × Aff)

namespace Cert

/-- The sum of the weights. -/
def weight (C : Cert) : Rat := (C.map (·.1)).sum

/-- The weighted sum of the expressions, as one expression. -/
def combo (C : Cert) : Aff :=
  ⟨(C.map fun e => e.1 * e.2.a).sum, (C.map fun e => e.1 * e.2.b).sum,
   (C.map fun e => e.1 * e.2.c).sum⟩

/-- Every weight is at least zero and every expression is one of `gs`. -/
def Uses (C : Cert) (gs : List Aff) : Prop := ∀ e ∈ C, 0 ≤ e.1 ∧ e.2 ∈ gs

instance (C : Cert) (gs : List Aff) : Decidable (C.Uses gs) := by unfold Uses; infer_instance

/-- The same weights on the moved expressions. -/
def shift (C : Cert) (dx dy : Rat) : Cert := C.map fun e => (e.1, e.2.shift dx dy)

theorem combo_eval (C : Cert) (x y : Rat) :
    C.combo.eval x y = (C.map fun e => e.1 * e.2.eval x y).sum := by
  simp only [combo, Aff.eval]
  rw [← sum_map_mul_right, ← sum_map_mul_right, ← sum_map_add, ← sum_map_add]
  apply sum_map_congr; intro e _; grind

theorem combo_shift (C : Cert) (dx dy : Rat) : (C.shift dx dy).combo = C.combo.shift dx dy := by
  simp only [shift, combo, Aff.shift, List.map_map, Function.comp_def, Aff.mk.injEq, true_and]
  rw [← sum_map_mul_right, ← sum_map_mul_right, ← sum_map_sub, ← sum_map_sub]
  apply sum_map_congr; intro e _; grind

theorem combo_append (C D : Cert) :
    (C ++ D).combo = ⟨C.combo.a + D.combo.a, C.combo.b + D.combo.b, C.combo.c + D.combo.c⟩ := by
  simp [combo, List.sum_append]

theorem weight_shift (C : Cert) (dx dy : Rat) : (C.shift dx dy).weight = C.weight := by
  simp [weight, shift, Function.comp_def]

theorem weight_append (C D : Cert) : (C ++ D).weight = C.weight + D.weight := by
  simp [weight, List.sum_append]

theorem uses_shift (C : Cert) (gs : List Aff) (h : C.Uses gs) (dx dy : Rat) :
    (C.shift dx dy).Uses (gs.map (·.shift dx dy)) := by
  intro e he
  simp only [shift, List.mem_map] at he
  obtain ⟨e', he', rfl⟩ := he
  exact ⟨(h e' he').1, List.mem_map.mpr ⟨_, (h e' he').2, rfl⟩⟩

theorem uses_append (C D : Cert) (gs hs : List Aff) (hC : C.Uses gs) (hD : D.Uses hs) :
    (C ++ D).Uses (gs ++ hs) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact ⟨(hC e h).1, List.mem_append_left _ (hC e h).2⟩
  · exact ⟨(hD e h).1, List.mem_append_right _ (hD e h).2⟩

/-- A weighted sum with weights `≥ 0` (not all zero) of numbers above zero is above zero. -/
theorem sum_pos (C : Cert) (f : Aff → Rat) (h0 : ∀ e ∈ C, 0 ≤ e.1 ∧ 0 < f e.2)
    (hw : 0 < C.weight) : 0 < (C.map fun e => e.1 * f e.2).sum := by
  induction C with
  | nil => simp [weight] at hw
  | cons e C ih =>
    simp only [weight, List.map_cons, List.sum_cons] at hw ⊢
    have he := h0 e (by simp)
    have hrest : 0 ≤ (C.map fun e => e.1 * f e.2).sum :=
      sum_map_nonneg _ _ fun e' h' => Rat.mul_nonneg (h0 e' (by simp [h'])).1
        (Rat.le_of_lt (h0 e' (by simp [h'])).2)
    by_cases hpos : 0 < e.1
    · have := Rat.mul_pos hpos he.2; grind
    · have he1 : e.1 = 0 := by grind
      have := ih (fun e' h' => h0 e' (by simp [h'])) (by simp only [weight]; grind)
      rw [he1, Rat.zero_mul]; grind

/-- If weights `≥ 0` (not all zero) on some expressions add up to a number that does not
depend on the point and is not above zero, no point makes all of them above zero. -/
theorem no_common_inside (C : Cert) (gs : List Aff) (hU : C.Uses gs) (hw : 0 < C.weight)
    (ha : C.combo.a = 0) (hb : C.combo.b = 0) (hc : C.combo.c ≤ 0) (x y : Rat)
    (hpos : ∀ g ∈ gs, 0 < g.eval x y) : False := by
  have h1 := combo_eval C x y
  have h2 := sum_pos C (fun g => g.eval x y) (fun e he => ⟨(hU e he).1, hpos _ (hU e he).2⟩) hw
  rw [show C.combo.eval x y = C.combo.c by simp [Aff.eval, ha, hb]; grind] at h1
  grind

/-- If `f` minus weights `≥ 0` on some expressions is a number `≥ 0`, then `f` is at least
zero wherever all the expressions are. -/
theorem nonneg_on (C : Cert) (gs : List Aff) (f : Aff) (hU : C.Uses gs)
    (ha : f.a = C.combo.a) (hb : f.b = C.combo.b) (hc : C.combo.c ≤ f.c) (x y : Rat)
    (hnn : ∀ g ∈ gs, 0 ≤ g.eval x y) : 0 ≤ f.eval x y := by
  have h1 := combo_eval C x y
  have h2 : 0 ≤ (C.map fun e => e.1 * e.2.eval x y).sum :=
    sum_map_nonneg _ _ fun e he => Rat.mul_nonneg (hU e he).1 (hnn _ (hU e he).2)
  have : f.eval x y = C.combo.eval x y + (f.c - C.combo.c) := by
    simp only [Aff.eval, ha, hb]; grind
  grind

end Cert

/-! ## Two planks share no area -/

/-- Weights on the sides of two planks `p` (part `P`) and `q` (part `Q`). -/
structure Sep where
  P : Cert
  Q : Cert
  deriving Repr, Inhabited

/-- The weights fit: they are on the right sides, at least zero, not all zero, and their sum
does not depend on the point. -/
def Sep.Fits (s : Sep) (p q : Plank) : Prop :=
  s.P.Uses p.sides ∧ s.Q.Uses q.sides ∧ 0 < s.P.weight + s.Q.weight ∧
    s.P.combo.a + s.Q.combo.a = 0 ∧ s.P.combo.b + s.Q.combo.b = 0

instance (s : Sep) (p q : Plank) : Decidable (s.Fits p q) := by unfold Sep.Fits; infer_instance

/-- The number the weighted sum adds up to. Not above zero means: the planks share no area. -/
def Sep.value (s : Sep) : Rat := s.P.combo.c + s.Q.combo.c

/-- With weights that fit, the planks moved by `(dx, dy)` and `(ex, ey)` share no area, as
long as the weighted sum for the moved planks is not above zero. -/
theorem Sep.no_share_moved (s : Sep) (p q : Plank) (hs : s.Fits p q) (dx dy dz ex ey ez : Rat)
    (hv : s.value - (s.P.combo.a * dx + s.P.combo.b * dy) - (s.Q.combo.a * ex + s.Q.combo.b * ey)
      ≤ 0) :
    ¬ SharesArea (p.moveBy dx dy dz) (q.moveBy ex ey ez) := by
  obtain ⟨hP, hQ, hw, ha, hb⟩ := hs
  rintro ⟨x, y, h1, h2⟩
  rw [coversInside_iff_sides, sides_moveBy] at h1 h2
  have hU := Cert.uses_append _ _ _ _ (Cert.uses_shift _ _ hP dx dy) (Cert.uses_shift _ _ hQ ex ey)
  refine Cert.no_common_inside _ _ hU ?_ ?_ ?_ ?_ x y ?_
  · rw [Cert.weight_append, Cert.weight_shift, Cert.weight_shift]; exact hw
  · rw [Cert.combo_append, Cert.combo_shift, Cert.combo_shift]; simp only [Aff.shift]; exact ha
  · rw [Cert.combo_append, Cert.combo_shift, Cert.combo_shift]; simp only [Aff.shift]; exact hb
  · rw [Cert.combo_append, Cert.combo_shift, Cert.combo_shift]
    simp only [Aff.shift]; simp only [Sep.value] at hv; grind
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact h1 g h
    · exact h2 g h

/-- With weights that fit and a value not above zero, the planks share no area. -/
theorem Sep.no_share (s : Sep) (p q : Plank) (hs : s.Fits p q) (hv : s.value ≤ 0) :
    ¬ SharesArea p q := by
  have := s.no_share_moved p q hs 0 0 0 0 0 0 (by grind)
  rwa [moveBy_zero, moveBy_zero] at this

/-- With weights that fit and a value of at most `-ε * (slopes)`, the planks share no area
after each moves by at most `ε` along `x` and along `y`. -/
theorem Sep.no_share_within (s : Sep) (p q : Plank) (hs : s.Fits p q) (ε : Rat)
    (hv : s.value + ε * (s.P.combo.slope + s.Q.combo.slope) ≤ 0) (dx dy ex ey : Rat)
    (hdx : -ε ≤ dx ∧ dx ≤ ε) (hdy : -ε ≤ dy ∧ dy ≤ ε) (hex : -ε ≤ ex ∧ ex ≤ ε)
    (hey : -ε ≤ ey ∧ ey ≤ ε) :
    ¬ SharesArea (p.moveBy dx dy 0) (q.moveBy ex ey 0) := by
  apply s.no_share_moved p q hs
  have h1 := Aff.lin_le s.P.combo ε dx dy hdx hdy
  have h2 := Aff.lin_le s.Q.combo ε ex ey hex hey
  grind

/-! ## Untrusted helpers: candidate weights and points

Nothing below needs to be right: the checks above decide. -/

/-- Weights on the sides of `p` whose sum is `(largest value of n · point over p) - n · point`
when `p`'s turn is a real turn. -/
def sideWeights (p : Plank) (nx ny : Rat) : Cert :=
  let c := p.rot.cos
  let s := p.rot.sin
  let α := nx * c + ny * s
  let β := -nx * s + ny * c
  let sd := p.sides
  [if 0 ≤ α then (α, sd.getD 0 default) else (-α, sd.getD 1 default),
   if 0 ≤ β then (β, sd.getD 2 default) else (-β, sd.getD 3 default)]

/-- Candidate weights: separate `p` and `q` along the direction `(nx, ny)` (`p` on the low
side). -/
def sepAlong (p q : Plank) (nx ny : Rat) : Sep := ⟨sideWeights p nx ny, sideWeights q (-nx) (-ny)⟩

/-- The directions worth trying: along the length and the width of each plank, both ways. -/
def sepDirections (p q : Plank) : List (Rat × Rat) :=
  let d := fun (r : Rot) => [(r.cos, r.sin), (-r.sin, r.cos)]
  let ds := d p.rot ++ d q.rot
  ds ++ ds.map fun (a, b) => (-a, -b)

/-- The candidate separations of `p` and `q`. -/
def sepCandidates (p q : Plank) : List Sep :=
  (sepDirections p q).map fun (nx, ny) => sepAlong p q nx ny

/-- Some candidate shows that `p` and `q` share no area, even when each moves by up to `ε`
along `x` and along `y`. -/
def sepCheck (ε : Rat) (p q : Plank) : Bool :=
  (sepCandidates p q).any fun s =>
    decide (s.Fits p q) && decide (s.value + ε * (s.P.combo.slope + s.Q.combo.slope) ≤ 0)

theorem sepCheck_sound (ε : Rat) (p q : Plank) (h : sepCheck ε p q = true) :
    ∃ s : Sep, s.Fits p q ∧ s.value + ε * (s.P.combo.slope + s.Q.combo.slope) ≤ 0 := by
  simp only [sepCheck, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨s, -, h1, h2⟩ := h
  exact ⟨s, h1, h2⟩

/-- The corners of the plank's footprint, in turning order. -/
def _root_.KaplaCore.Pose.corners2 (p : Plank) : List (Rat × Rat) :=
  let c := p.rot.cos
  let s := p.rot.sin
  let h := p.size.x / 2
  let k := p.size.y / 2
  let pt := fun (u v : Rat) => (p.center.x + u * c - v * s, p.center.y + u * s + v * c)
  [pt (-h) (-k), pt h (-k), pt h k, pt (-h) k]

/-- Cut a polygon (corners in order) by the half-plane where `g ≥ 0`. -/
def clipBy (poly : List (Rat × Rat)) (g : Aff) : List (Rat × Rat) :=
  match poly with
  | [] => []
  | first :: _ =>
    let edges := poly.zip (poly.drop 1 ++ [first])
    edges.flatMap fun ((x0, y0), (x1, y1)) =>
      let v0 := g.eval x0 y0
      let v1 := g.eval x1 y1
      let keep := if 0 ≤ v0 then [(x0, y0)] else []
      let cross :=
        if (0 < v0 && v1 < 0) || (v0 < 0 && 0 < v1) then
          let t := v0 / (v0 - v1)
          [(x0 + t * (x1 - x0), y0 + t * (y1 - y0))]
        else []
      keep ++ cross

/-- The corners of the patch where `p` meets `q` seen from above: `p`'s footprint cut by
`q`'s sides. -/
def patchPoly (p q : Plank) : List (Rat × Rat) := q.sides.foldl clipBy p.corners2

/-- The average of the corners, if there are any. Inside the patch when it has an area. -/
def average (poly : List (Rat × Rat)) : Option (Rat × Rat) :=
  if poly.isEmpty then none
  else
    let n : Rat := poly.length
    some ((poly.map (·.1)).sum / n, (poly.map (·.2)).sum / n)

#guard average (patchPoly (Plank.at .flatX 0 0 0) (Plank.at .flatY 0 0 0)) == some (3 / 2, 3 / 2)
#guard (patchPoly (Plank.at .flatX 0 0 0) (Plank.at .flatX 15 0 0)).all fun (x, _) => x == 15
#guard patchPoly (Plank.at .flatX 0 0 0) (Plank.at .flatX 16 0 0) == []

end KaplaPhysics
