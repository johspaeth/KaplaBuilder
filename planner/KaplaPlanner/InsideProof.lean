import KaplaPlanner.Inside
import KaplaPlanner.Ellipsoid

/-! # Lemmas for the proof that `insideBubbles` is correct

The idea: the bubble formula is a sum of squares of straight-line (linear) functions. On a
segment along one axis, such a sum is never larger in the middle than at both ends. So if
both ends are inside a bubble, the whole segment is. Going along x, then y, then z, every
point of a cell is reached from its 8 corners. -/

namespace KaplaPlanner
open KaplaCore

/-- If `(c − a)·v ≤ (c − x)·va + (x − a)·vc` with `va, vc ≤ 1` and `a ≤ x ≤ c`, then
`v ≤ 1`. (`hac` covers the case `a = c`, where the segment is one point.) -/
theorem le_one_of_interp (a x c v va vc : Rat) (hax : a ≤ x) (hxc : x ≤ c)
    (ha : va ≤ 1) (hc : vc ≤ 1) (hac : a = c → v = va)
    (h : (c - a) * v ≤ (c - x) * va + (x - a) * vc) : v ≤ 1 := by
  by_cases e : a = c
  · rw [hac e]; exact ha
  · have hpos : 0 < c - a := by grind
    have h1 : (c - x) * va ≤ (c - x) * 1 := Rat.mul_le_mul_of_nonneg_left ha (by grind)
    have h2 : (x - a) * vc ≤ (x - a) * 1 := Rat.mul_le_mul_of_nonneg_left hc (by grind)
    have h3 : (c - a) * v ≤ (c - a) * 1 := by grind
    exact Rat.le_of_mul_le_mul_left h3 hpos

/-- A sum of three squares is not negative. -/
theorem sum_sq_nonneg (a b c : Rat) : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have h1 : 0 ≤ a ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
  have h2 : 0 ≤ b ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
  have h3 : 0 ≤ c ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
  grind

/-- `(c − a)(x − a)(c − x) ≥ 0` when `a ≤ x ≤ c`. -/
theorem seg_nonneg (a x c : Rat) (hax : a ≤ x) (hxc : x ≤ c) :
    0 ≤ (c - a) * (x - a) * (c - x) :=
  Rat.mul_nonneg (Rat.mul_nonneg (by grind) (by grind)) (by grind)

/-- Along x: if both ends of a segment are inside the bubble, so is every point between. -/
theorem line_x (b : Ellipsoid) (y z a x c : Rat) (hax : a ≤ x) (hxc : x ≤ c)
    (ha : b.contains ⟨a, y, z⟩) (hc : b.contains ⟨c, y, z⟩) : b.contains ⟨x, y, z⟩ := by
  unfold Ellipsoid.contains at *
  apply le_one_of_interp a x c _ _ _ hax hxc ha hc (fun e => by subst e; rw [show x = a by grind])
  have key : (c - x) * b.value ⟨a, y, z⟩ + (x - a) * b.value ⟨c, y, z⟩ - (c - a) * b.value ⟨x, y, z⟩
      = (b.u1.x ^ 2 + b.u2.x ^ 2 + b.u3.x ^ 2) * ((c - a) * (x - a) * (c - x)) := by
    simp only [Ellipsoid.value, Q3.dot, Q3.sub]; grind
  have := Rat.mul_nonneg (sum_sq_nonneg b.u1.x b.u2.x b.u3.x) (seg_nonneg a x c hax hxc)
  grind

/-- Along y: same as `line_x`. -/
theorem line_y (b : Ellipsoid) (x z a y c : Rat) (hay : a ≤ y) (hyc : y ≤ c)
    (ha : b.contains ⟨x, a, z⟩) (hc : b.contains ⟨x, c, z⟩) : b.contains ⟨x, y, z⟩ := by
  unfold Ellipsoid.contains at *
  apply le_one_of_interp a y c _ _ _ hay hyc ha hc (fun e => by subst e; rw [show y = a by grind])
  have key : (c - y) * b.value ⟨x, a, z⟩ + (y - a) * b.value ⟨x, c, z⟩ - (c - a) * b.value ⟨x, y, z⟩
      = (b.u1.y ^ 2 + b.u2.y ^ 2 + b.u3.y ^ 2) * ((c - a) * (y - a) * (c - y)) := by
    simp only [Ellipsoid.value, Q3.dot, Q3.sub]; grind
  have := Rat.mul_nonneg (sum_sq_nonneg b.u1.y b.u2.y b.u3.y) (seg_nonneg a y c hay hyc)
  grind

/-- Along z: same as `line_x`. -/
theorem line_z (b : Ellipsoid) (x y a z c : Rat) (haz : a ≤ z) (hzc : z ≤ c)
    (ha : b.contains ⟨x, y, a⟩) (hc : b.contains ⟨x, y, c⟩) : b.contains ⟨x, y, z⟩ := by
  unfold Ellipsoid.contains at *
  apply le_one_of_interp a z c _ _ _ haz hzc ha hc (fun e => by subst e; rw [show z = a by grind])
  have key : (c - z) * b.value ⟨x, y, a⟩ + (z - a) * b.value ⟨x, y, c⟩ - (c - a) * b.value ⟨x, y, z⟩
      = (b.u1.z ^ 2 + b.u2.z ^ 2 + b.u3.z ^ 2) * ((c - a) * (z - a) * (c - z)) := by
    simp only [Ellipsoid.value, Q3.dot, Q3.sub]; grind
  have := Rat.mul_nonneg (sum_sq_nonneg b.u1.z b.u2.z b.u3.z) (seg_nonneg a z c haz hzc)
  grind

/-- If the 8 corners of a box are inside an ellipsoid, every point of the box is. -/
theorem contains_of_corners (b : Ellipsoid) (bx : Box) (hc : ∀ q ∈ bx.corners, b.contains q)
    (p : Q3) (hp : bx.contains p) : b.contains p := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2⟩ := hp
  have corner : ∀ x y z, (x = bx.lo.x ∨ x = bx.hi.x) → (y = bx.lo.y ∨ y = bx.hi.y) →
      (z = bx.lo.z ∨ z = bx.hi.z) → b.contains ⟨x, y, z⟩ := by
    intro x y z hx hy hz
    apply hc
    simp only [Box.corners, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false]
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> simp
  -- along x: the 4 edges of the box that run along x
  have ex : ∀ y z, (y = bx.lo.y ∨ y = bx.hi.y) → (z = bx.lo.z ∨ z = bx.hi.z) →
      b.contains ⟨p.x, y, z⟩ := fun y z hy hz =>
    line_x b y z _ _ _ hx1 hx2 (corner _ _ _ (.inl rfl) hy hz) (corner _ _ _ (.inr rfl) hy hz)
  -- along y: the 2 faces of the box at the bottom and the top
  have ey : ∀ z, (z = bx.lo.z ∨ z = bx.hi.z) → b.contains ⟨p.x, p.y, z⟩ := fun z hz =>
    line_y b p.x z _ _ _ hy1 hy2 (ex _ _ (.inl rfl) hz) (ex _ _ (.inr rfl) hz)
  -- along z: the point itself
  have := line_z b p.x p.y _ _ _ hz1 hz2 (ey _ (.inl rfl)) (ey _ (.inr rfl))
  exact this

/-- If the 8 corners of a box are inside a bubble, every point of the box is. (A bubble
with a half-width of 0 or less contains no corner, so this case cannot happen.) -/
theorem bubble_contains_of_corners (b : Bubble) (bx : Box)
    (hc : ∀ q ∈ bx.corners, b.contains q = true) (p : Q3) (hp : bx.contains p) :
    b.contains p = true := by
  have hlo : (⟨bx.lo.x, bx.lo.y, bx.lo.z⟩ : Q3) ∈ bx.corners := by simp [Box.corners]
  have hlo' := (bubble_contains_iff b _).mp (hc _ hlo)
  rw [bubble_contains_iff]
  -- the lowest corner is not below the ground, so `p`, which is above it, is not either
  have hz : 0 ≤ p.z := Rat.le_trans hlo'.1 hp.2.2.2.2.1
  exact ⟨hz, hlo'.2.1, contains_of_corners (bubbleEllipsoid b) bx
    (fun q hq => ((bubble_contains_iff b q).mp (hc q hq)).2.2) p hp⟩

/-- A box whose corners lie in one bubble lies inside the bubbles. -/
theorem boxInOne_sound (bs : List Bubble) (bx : Box) (h : boxInOne bs bx = true) (p : Q3)
    (hp : bx.contains p) : ∃ b ∈ bs, b.contains p = true := by
  simp only [boxInOne, List.any_eq_true, List.all_eq_true] at h
  obtain ⟨b, hb, hc⟩ := h
  exact ⟨b, hb, bubble_contains_of_corners b bx hc p hp⟩

/-- A point between `lo` and `hi` lies in one of the two halves. -/
theorem mem_halves (lo hi x : Q) (h1 : lo ≤ x) (h2 : x ≤ hi) :
    ∃ h ∈ halves lo hi, h.1 ≤ x ∧ x ≤ h.2 := by
  by_cases hx : x ≤ (lo + hi) / 2
  · exact ⟨(lo, (lo + hi) / 2), by simp [halves], h1, hx⟩
  · exact ⟨((lo + hi) / 2, hi), by simp [halves], by grind, h2⟩

/-- A point of a box lies in one of its 8 halves. -/
theorem mem_boxOctants (bx : Box) (p : Q3) (hp : bx.contains p) :
    ∃ o ∈ boxOctants bx, o.contains p := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2⟩ := hp
  obtain ⟨⟨x0, x1⟩, hxm, hxa, hxb⟩ := mem_halves _ _ _ hx1 hx2
  obtain ⟨⟨y0, y1⟩, hym, hya, hyb⟩ := mem_halves _ _ _ hy1 hy2
  obtain ⟨⟨z0, z1⟩, hzm, hza, hzb⟩ := mem_halves _ _ _ hz1 hz2
  refine ⟨⟨⟨x0, y0, z0⟩, ⟨x1, y1, z1⟩⟩, ?_, ⟨hxa, hxb, hya, hyb, hza, hzb⟩⟩
  simp only [boxOctants, List.mem_flatMap, List.mem_map]
  exact ⟨(x0, x1), hxm, (y0, y1), hym, (z0, z1), hzm, rfl⟩

/-- If `boxInside` accepts a box, every point of the box lies inside some bubble. -/
theorem boxInside_sound (bs : List Bubble) : ∀ (depth : Nat) (bx : Box),
    boxInside bs bx depth = true → ∀ p : Q3, bx.contains p → ∃ b ∈ bs, b.contains p = true := by
  intro depth
  induction depth with
  | zero => exact fun bx h => boxInOne_sound bs bx h
  | succ d ih =>
    intro bx h p hp
    simp only [boxInside, Bool.or_eq_true, List.all_eq_true] at h
    rcases h with h | h
    · exact boxInOne_sound bs bx h p hp
    · obtain ⟨o, ho, hpo⟩ := mem_boxOctants bx p hp
      exact ih o (h o ho) p hpo

/-- A run of `n ≥ 1` pieces of length `h`, starting at `a`, covers every point between its
ends: each such point is in one of the pieces `[a + m·h, a + (m+1)·h]`, `m < n`. -/
theorem split_run (h : Rat) : ∀ (n : Nat) (a x : Rat), 0 < n →
    a ≤ x → x ≤ a + n * h → ∃ m < n, a + m * h ≤ x ∧ x ≤ a + (m + 1) * h := by
  intro n
  induction n with
  | zero => intro _ _ h0; exact absurd h0 (Nat.lt_irrefl 0)
  | succ n ih =>
    intro a x _ h1 h2
    by_cases hx : x ≤ a + h
    · exact ⟨0, Nat.succ_pos n, by push_cast; grind, by push_cast; grind⟩
    · have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simp at h2; exact absurd h2 hx
        · exact hpos
      have h2' : x ≤ (a + h) + n * h := by push_cast at h2; grind
      obtain ⟨m, hm, a1, a2⟩ := ih (a + h) x hn (by grind) h2'
      refine ⟨m + 1, by omega, ?_, ?_⟩ <;> push_cast <;> grind

theorem mem_intRange (a : Int) (n m d : Nat) (hm : m < n) :
    a + ((d * m : Nat) : Int) ∈ intRange a n d := by
  simp only [intRange, List.mem_map, List.mem_range]
  exact ⟨m, hm, rfl⟩

/-- Every block is at least one cube long in each direction. -/
theorem Orient.cubes_pos (o : Orient) :
    0 < o.cubes.1 ∧ 0 < o.cubes.2.1 ∧ 0 < o.cubes.2.2 := by
  cases o <;> decide

/-- One axis of `cell_of_point`: a point between the block's two faces lies in one of the
block's cubes along that axis. -/
theorem axis_cube (lo : Int) (n : Nat) (hn : 0 < n) (x : Rat)
    (h1 : (lo : Rat) * unit ≤ x) (h2 : x ≤ ((lo + ((cubeSide * n : Nat) : Int) : Int) : Rat) * unit) :
    ∃ m < n, ((lo + ((cubeSide * m : Nat) : Int) : Int) : Rat) * unit ≤ x ∧
      x ≤ ((lo + ((cubeSide * m : Nat) : Int) + (cubeSide : Int) : Int) : Rat) * unit := by
  have h2' : x ≤ (lo : Rat) * unit + n * (4 * unit) := by
    simp only [cubeSide] at h2; push_cast at h2; grind
  obtain ⟨m, hm, a1, a2⟩ := split_run (4 * unit) n ((lo : Rat) * unit) x hn h1 h2'
  refine ⟨m, hm, ?_, ?_⟩ <;> simp only [cubeSide] <;> push_cast <;> grind

/-- Every point of a block lies in one of its cubes. -/
theorem cell_of_point (blk : GridBlock) (p : Q3) (hp : blk.box.contains p) :
    ∃ c ∈ blk.cells, (cellBox c.1 c.2.1 c.2.2).contains p := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2⟩ := hp
  obtain ⟨cx, cy, cz⟩ := Orient.cubes_pos blk.orient
  obtain ⟨i, hi, ix1, ix2⟩ := axis_cube blk.x _ cx p.x hx1 hx2
  obtain ⟨j, hj, jy1, jy2⟩ := axis_cube blk.y _ cy p.y hy1 hy2
  obtain ⟨k, hk, kz1, kz2⟩ := axis_cube blk.z _ cz p.z hz1 hz2
  refine ⟨(_, _, _), ?_, ix1, ix2, jy1, jy2, kz1, kz2⟩
  simp only [GridBlock.cells, List.mem_flatMap, List.mem_map]
  exact ⟨_, mem_intRange _ _ _ _ hi, _, mem_intRange _ _ _ _ hj, _, mem_intRange _ _ _ _ hk, rfl⟩

end KaplaPlanner
