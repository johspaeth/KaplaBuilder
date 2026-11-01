import KaplaSemantics.Check
import Std.Data.HashSet.Lemmas

/-! # Proofs of the five semantics theorems

The statements are in `specs/KaplaSpecs/Semantics.lean`. What each one says, and why it matters,
is in `semantics/APPROACH.md` §6. -/

namespace KaplaSemantics

open KaplaCore

/-! ## `dedupe` -/

/-- The loop inside `dedupe`. While the set and the list hold the same cubes and the list has no
repeats, the result holds the cubes seen so far plus the new ones, with no repeats. -/
private theorem dedupe_loop (cells : List GridPt) (s : Std.HashSet GridPt) (out : List GridPt)
    (hs : ∀ x, s.contains x = true ↔ x ∈ out) (hn : out.Nodup) :
    let r := cells.foldl (fun (acc : Std.HashSet GridPt × List GridPt) c =>
      if acc.1.contains c then acc else (acc.1.insert c, c :: acc.2)) (s, out)
    (∀ x, x ∈ r.2 ↔ x ∈ out ∨ x ∈ cells) ∧ r.2.Nodup := by
  induction cells generalizing s out with
  | nil => simpa using hn
  | cons c rest ih =>
    simp only [List.foldl_cons]
    by_cases hc : s.contains c = true
    · simp only [hc, ↓reduceIte]
      refine ⟨fun x => ?_, (ih s out hs hn).2⟩
      rw [(ih s out hs hn).1 x, List.mem_cons]
      have hco : c ∈ out := (hs c).1 hc
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hco
        · exact Or.inr h
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have hs' : ∀ x, (s.insert c).contains x = true ↔ x ∈ c :: out := by
        intro x
        rw [Std.HashSet.contains_insert, List.mem_cons, Bool.or_eq_true, hs x, beq_iff_eq,
          @eq_comm _ c x]
      have hn' : (c :: out).Nodup :=
        List.nodup_cons.2 ⟨fun h => hc ((hs c).2 h), hn⟩
      refine ⟨fun x => ?_, (ih _ _ hs' hn').2⟩
      rw [(ih _ _ hs' hn').1 x]
      simp only [List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h

/-- `dedupe` keeps the same cubes. -/
theorem mem_dedupe (cells : List GridPt) (g : GridPt) : g ∈ dedupe cells ↔ g ∈ cells := by
  have h := (dedupe_loop cells {} [] (by simp) List.nodup_nil).1 g
  simpa [dedupe] using h

/-- `dedupe` leaves no cube twice. -/
theorem nodup_dedupe (cells : List GridPt) : (dedupe cells).Nodup := by
  exact (List.reverse_perm _).nodup_iff.2 (dedupe_loop cells {} [] (by simp) List.nodup_nil).2

/-! ## Counting -/

/-- A list with no repeats, all of whose items are in `b`, is no longer than `b`. -/
private theorem length_le_of_subset {α : Type} [DecidableEq α] (a b : List α)
    (hn : a.Nodup) (hs : ∀ x ∈ a, x ∈ b) : a.length ≤ b.length := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    have hx : x ∈ b := hs x (by simp)
    have hn' := List.nodup_cons.1 hn
    have hsub : ∀ y ∈ xs, y ∈ b.erase x := by
      intro y hy
      have hne : y ≠ x := fun e => hn'.1 (e ▸ hy)
      exact (List.mem_erase_of_ne hne).2 (hs y (List.mem_cons_of_mem _ hy))
    have := ih _ hn'.2 hsub
    rw [List.length_erase_of_mem hx] at this
    have hpos : 0 < b.length := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

/-! ## Numbers -/

private theorem sq_nonneg (d : Q) : 0 ≤ d * d := by
  by_cases h : 0 ≤ d
  · exact Rat.mul_nonneg h h
  · have h' : 0 ≤ -d := by grind
    have := Rat.mul_nonneg h' h'
    grind

/-- If a number's square is at most 1, the number is from -1 to 1. -/
private theorem between_of_sq_le_one (d : Q) (h : d * d ≤ 1) : -1 ≤ d ∧ d ≤ 1 := by
  constructor
  · apply Classical.byContradiction
    intro hc
    have hd : d < -1 := by grind
    have h1 : 0 < -d - 1 := by grind
    have h2 : 0 < -d := by grind
    have := Rat.mul_pos h1 h2
    grind
  · apply Classical.byContradiction
    intro hc
    have hd : 1 < d := by grind
    have h1 : 0 < d - 1 := by grind
    have h2 : 0 < d := by grind
    have := Rat.mul_pos h1 h2
    grind

/-- If `((t - c) / a)²` is at most 1 and `a` is above 0, then `t` is within `a` of `c`. -/
private theorem within_of_sq_le_one (t c a : Q) (ha : 0 < a)
    (h : (t - c) / a * ((t - c) / a) ≤ 1) : c - a ≤ t ∧ t ≤ c + a := by
  have ⟨h1, h2⟩ := between_of_sq_le_one _ h
  have hne : a ≠ 0 := by grind
  have he : (t - c) / a * a = t - c := Rat.div_mul_cancel hne
  have ha' : 0 ≤ a := by grind
  have l := Rat.mul_le_mul_of_nonneg_right h1 ha'
  have r := Rat.mul_le_mul_of_nonneg_right h2 ha'
  grind

/-! ## Listing the cubes of a box -/

/-- The whole numbers listed are exactly those from `lo` to `hi`. -/
theorem mem_intsBetween (lo hi x : Int) : x ∈ intsBetween lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  simp only [intsBetween, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · intro h
    exact ⟨(x - lo).toNat, by omega, by omega⟩

/-- A cube whose middle is from `lo` to `hi` along one axis is on the list for that axis. -/
private theorem mem_line (lo hi : Q) (t : Int) (hl : lo ≤ (t : Q) + 1 / 2)
    (hh : (t : Q) + 1 / 2 ≤ hi) :
    t ∈ intsBetween (lo - 1 / 2).ceil (hi - 1 / 2).floor := by
  rw [mem_intsBetween]
  constructor
  · apply Rat.ceil_le_iff.2
    grind
  · apply Rat.le_floor_iff.2
    grind

/-- A cube whose middle is in the box, faces included, is listed by `boxCells`. -/
theorem mem_boxCells (b : Box) (g : GridPt)
    (hx : b.lo.x ≤ g.centre.x ∧ g.centre.x ≤ b.hi.x)
    (hy : b.lo.y ≤ g.centre.y ∧ g.centre.y ≤ b.hi.y)
    (hz : b.lo.z ≤ g.centre.z ∧ g.centre.z ≤ b.hi.z) :
    g ∈ boxCells b := by
  obtain ⟨i, j, k⟩ := g
  simp only [boxCells, List.mem_flatMap, List.mem_map]
  exact ⟨i, mem_line _ _ _ hx.1 hx.2, j, mem_line _ _ _ hy.1 hy.2, k, mem_line _ _ _ hz.1 hz.2, rfl⟩

/-- What passing a bubble's test means, one fact per part of the test. -/
private theorem contains_parts (b : Bubble) (p : Q3) (h : b.contains p = true) :
    0 ≤ p.z ∧ b.center.x - b.semi.x ≤ p.x ∧ p.x ≤ b.center.x + b.semi.x ∧
      b.center.y - b.semi.y ≤ p.y ∧ p.y ≤ b.center.y + b.semi.y ∧
      b.center.z - b.semi.z ≤ p.z ∧ p.z ≤ b.center.z + b.semi.z := by
  simp only [Bubble.contains, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hz, ha⟩, hb⟩, hc⟩, hs⟩ := h
  have sx := sq_nonneg ((p.x - b.center.x) / b.semi.x)
  have sy := sq_nonneg ((p.y - b.center.y) / b.semi.y)
  have sz := sq_nonneg ((p.z - b.center.z) / b.semi.z)
  have x := within_of_sq_le_one p.x b.center.x b.semi.x ha (by grind)
  have y := within_of_sq_le_one p.y b.center.y b.semi.y hb (by grind)
  have z := within_of_sq_le_one p.z b.center.z b.semi.z hc (by grind)
  exact ⟨hz, x.1, x.2, y.1, y.2, z.1, z.2⟩

/-- A cube passes the test of a bubble only if it is in the bubble's box. -/
theorem mem_boxCells_of_contains (b : Bubble) (g : GridPt) (h : b.contains g.centre = true) :
    g ∈ boxCells b.box := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := contains_parts b g.centre h
  apply mem_boxCells
  · exact ⟨h1, h2⟩
  · exact ⟨h3, h4⟩
  · refine ⟨?_, h6⟩
    simp only [Bubble.box, Q3.sub]
    rw [Rat.max_def]
    split <;> assumption

/-- A bubble's listed cubes are exactly the cubes passing its test. -/
theorem mem_bubbleCells (b : Bubble) (g : GridPt) :
    g ∈ bubbleCells b ↔ b.contains g.centre = true := by
  simp only [bubbleCells, List.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_boxCells_of_contains b g h, h⟩⟩

/-! ## The two checks -/

theorem checkWithin_correct (m : BubbleModel) (height : Q) (plan : List Pose) :
    checkWithin m height plan = true ↔ WithinTarget m height plan := by
  simp [checkWithin, WithinTarget, blockOutside]

theorem checkCovers_correct (m : BubbleModel) (height : Q) (plan : List Pose) :
    checkCovers m height plan = true ↔ CoversTarget m height plan := by
  simp [checkCovers, CoversTarget, bubbleUncovered, List.isEmpty_eq_false_iff]

/-! ## The score -/

/-- Every covered cube is a target cube. -/
theorem covered_subset_target (m : BubbleModel) (height : Q) (built : List GridPt) (g : GridPt)
    (h : g ∈ coveredCells (m.bubbles.map (placeAt height)) built) : g ∈ targetCells m height := by
  simp only [coveredCells, targetCells, mem_dedupe, List.mem_flatMap] at h ⊢
  obtain ⟨b, hb, hg⟩ := h
  exact ⟨b, hb, (List.mem_filter.1 hg).1⟩

/-- A part divided by a whole above 0 is from 0 to 1. -/
private theorem ratio_in_unit_interval (a n : Nat) (h : a ≤ n) (hn : 0 < n) :
    0 ≤ (a : Q) / (n : Q) ∧ (a : Q) / (n : Q) ≤ 1 := by
  have hn' : (0 : Q) < (n : Q) := by
    have := (Rat.natCast_lt_natCast (a := 0) (b := n)).2 hn
    simpa using this
  have ha : (0 : Q) ≤ (a : Q) := Rat.natCast_nonneg
  have hle : (a : Q) ≤ (n : Q) := Rat.natCast_le_natCast.2 h
  have he : (a : Q) / (n : Q) * (n : Q) = (a : Q) := Rat.div_mul_cancel (by grind)
  constructor
  · apply Classical.byContradiction
    intro hc
    have := Rat.mul_pos (a := -((a : Q) / (n : Q))) (by grind) hn'
    grind
  · apply Classical.byContradiction
    intro hc
    have := Rat.mul_pos (a := (a : Q) / (n : Q) - 1) (by grind) hn'
    grind

/-- `scoreOf` is from 0 to 1 when no more cubes are covered than there are in the target. -/
theorem scoreOf_in_unit_interval (target covered extra : Nat) (h : covered ≤ target) :
    0 ≤ scoreOf target covered extra ∧ scoreOf target covered extra ≤ 1 := by
  unfold scoreOf
  split
  · decide
  · rename_i hz
    exact ratio_in_unit_interval _ _ (by omega) (by
      have : target + extra ≠ 0 := by simpa using hz
      omega)

/-- The share of a bubble that is covered is from 0 to 1. -/
theorem perBubble_in_unit_interval (built : List GridPt) (b : Bubble) :
    0 ≤ perBubble built b ∧ perBubble built b ≤ 1 := by
  unfold perBubble
  simp only
  split
  · decide
  · rename_i hz
    exact ratio_in_unit_interval _ _ (List.length_filter_le _ _) (by
      have : (bubbleCells b).length ≠ 0 := by simpa using hz
      omega)

theorem score_in_unit_interval (m : BubbleModel) (height : Q) (plan : List Pose) :
    0 ≤ score m height plan ∧ score m height plan ≤ 1 := by
  apply scoreOf_in_unit_interval
  exact length_le_of_subset _ _ (nodup_dedupe _) (covered_subset_target m height _)

/-! ## The two lists of cubes -/

theorem targetCells_correct (m : BubbleModel) (height : Q) (g : GridPt) :
    g ∈ targetCells m height ↔ ∃ b ∈ m.bubbles, (placeAt height b).contains g.centre = true := by
  simp only [targetCells, mem_dedupe, List.mem_flatMap, List.mem_map, mem_bubbleCells]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, h⟩
    exact ⟨b, hb, h⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨_, ⟨b, hb, rfl⟩, h⟩

/-- The inside test of a block, along one axis: the position is within the size, whichever face
is left out. -/
private theorem within_bounds (t size : Q) (high : Bool)
    (h : (if high = true then (decide (-size ≤ 2 * t) && decide (2 * t < size))
      else (decide (-size < 2 * t) && decide (2 * t ≤ size))) = true) :
    -size ≤ 2 * t ∧ 2 * t ≤ size := by
  cases high <;> simp at h <;> grind

/-- If `2 * l` is within `d` of 0, then `2 * (c * l)` is within `|c| * d` of 0. -/
private theorem scaled_bounds (c l d : Q) (h1 : -d ≤ 2 * l) (h2 : 2 * l ≤ d) :
    -(c.abs * d) ≤ 2 * (c * l) ∧ 2 * (c * l) ≤ c.abs * d := by
  by_cases hc : 0 ≤ c
  · rw [Rat.abs_of_nonneg hc]
    have a := Rat.mul_le_mul_of_nonneg_left h1 hc
    have b := Rat.mul_le_mul_of_nonneg_left h2 hc
    grind
  · have hc' : c ≤ 0 := by grind
    have hn : 0 ≤ -c := by grind
    rw [Rat.abs_of_nonpos hc']
    have a := Rat.mul_le_mul_of_nonneg_left h1 hn
    have b := Rat.mul_le_mul_of_nonneg_left h2 hn
    grind

/-- For a real turn: a point within a block, measured along the block's own axes, is within the
block's box, measured along x and y. -/
private theorem turned_bounds (c s dx dy vx vy : Q) (hv : c * c + s * s = 1)
    (x1 : -dx ≤ 2 * (c * vx + s * vy)) (x2 : 2 * (c * vx + s * vy) ≤ dx)
    (y1 : -dy ≤ 2 * (-s * vx + c * vy)) (y2 : 2 * (-s * vx + c * vy) ≤ dy) :
    -(c.abs * dx + s.abs * dy) ≤ 2 * vx ∧ 2 * vx ≤ c.abs * dx + s.abs * dy ∧
      -(s.abs * dx + c.abs * dy) ≤ 2 * vy ∧ 2 * vy ≤ s.abs * dx + c.abs * dy := by
  have ex : c * (c * vx + s * vy) - s * (-s * vx + c * vy) = vx := by grind
  have ey : s * (c * vx + s * vy) + c * (-s * vx + c * vy) = vy := by grind
  have a1 := scaled_bounds c _ _ x1 x2
  have a2 := scaled_bounds s _ _ y1 y2
  have a3 := scaled_bounds s _ _ x1 x2
  have a4 := scaled_bounds c _ _ y1 y2
  grind

/-- For a real turn, every cube that passes a block's test is in the block's box. -/
theorem mem_boxCells_of_pose_contains (p : Pose) (hrot : p.rot.valid = true) (g : GridPt)
    (h : p.contains g.centre = true) : g ∈ boxCells p.box := by
  have hv : p.rot.cos * p.rot.cos + p.rot.sin * p.rot.sin = 1 := by
    simpa [Rot.valid] using hrot
  simp only [Pose.contains, Bool.and_eq_true] at h
  obtain ⟨⟨hx, hy⟩, hz⟩ := h
  have ⟨x1, x2⟩ := within_bounds _ _ _ hx
  have ⟨y1, y2⟩ := within_bounds _ _ _ hy
  have ⟨z1, z2⟩ := within_bounds (g.centre.sub p.center).z p.up.dims.z true hz
  simp only [Q3.sub] at x1 x2 y1 y2 z1 z2
  have ⟨b1, b2, b3, b4⟩ := turned_bounds _ _ _ _ _ _ hv x1 x2 y1 y2
  apply mem_boxCells <;> simp only [Pose.box, Q3.sub, Q3.add]
  · constructor <;> grind
  · constructor <;> grind
  · constructor <;> grind

/-- For a real turn, a block's listed cubes are exactly the cubes passing its test. -/
theorem mem_poseCells (p : Pose) (hrot : p.rot.valid = true) (g : GridPt) :
    g ∈ poseCells p ↔ p.contains g.centre = true := by
  simp only [poseCells, List.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_boxCells_of_pose_contains p hrot g h, h⟩⟩

theorem blockCells_correct (plan : List Pose) (hrot : ∀ blk ∈ plan, blk.rot.valid = true)
    (g : GridPt) :
    g ∈ blockCells plan ↔ ∃ blk ∈ plan, blk.contains g.centre = true := by
  simp only [blockCells, mem_dedupe, List.mem_flatMap]
  constructor
  · rintro ⟨blk, hb, hg⟩
    exact ⟨blk, hb, (mem_poseCells blk (hrot blk hb) g).1 hg⟩
  · rintro ⟨blk, hb, hg⟩
    exact ⟨blk, hb, (mem_poseCells blk (hrot blk hb) g).2 hg⟩

/-! ## Examples

Each theorem on a concrete input, and outputs it rejects. The ball is `ballModel` at height 2: the
ball of radius 1 around (0, 0, 1). `flatBlock` fills cubes 0-14 along x, 0-2 along y and level 0.

What a reviewer must read for each theorem:
- `targetCells_correct`: `GridPt.centre`, `Bubble.contains`, `placeAt`, `Bubble.place`, `targetCells`.
- `blockCells_correct`: `GridPt.centre`, `Pose.contains`, `Rot.valid`, `blockCells`, `poseCells`,
  `Pose.box`, `boxCells`, `dedupe`.
- `checkWithin_correct`: `WithinTarget`, `poseCells`, `Pose.contains`, `Pose.box`, `boxCells`,
  `Bubble.contains`, `placeAt`, `checkWithin`.
- `checkCovers_correct`: `CoversTarget`, `bubbleCells`, `Bubble.box`, `boxCells`, `blockCells`,
  `Bubble.contains`, `placeAt`, `checkCovers`.
- `score_in_unit_interval`: `score`, `scoreOf`, `targetCells`, `coveredCells`, `extraCells`,
  `blockCells`. -/

/-- A block whose end is in the ball but whose middle is not. -/
private def endBlock : Pose := ⟨.flat, .id, ⟨7, 0, 1 / 2⟩⟩

/-- A block far from the ball. -/
private def farBlock : Pose := ⟨.flat, .id, ⟨100, 3 / 2, 1 / 2⟩⟩

-- targetCells_correct: a cube in the ball is listed.
example : (-1, -1, 0) ∈ targetCells ballModel 2 :=
  (targetCells_correct _ _ _).2 ⟨_, .head _, by decide +kernel⟩

-- It rejects the empty list as the answer.
example : ¬ ∀ g : GridPt, g ∈ ([] : List GridPt) ↔
    ∃ b ∈ ballModel.bubbles, (placeAt 2 b).contains g.centre = true := by
  intro h
  exact List.not_mem_nil ((h (-1, -1, 0)).2 ⟨_, .head _, by decide +kernel⟩)

-- It rejects a list holding a cube outside the ball.
example : ¬ ∀ g : GridPt, g ∈ ([(5, 5, 5)] : List GridPt) ↔
    ∃ b ∈ ballModel.bubbles, (placeAt 2 b).contains g.centre = true := by
  intro h
  obtain ⟨b, hb, hc⟩ := (h (5, 5, 5)).1 (.head _)
  simp only [ballModel, List.mem_singleton] at hb
  subst hb
  exact absurd hc (by decide +kernel)

-- checkWithin_correct: a block with one cube in the ball passes.
example : WithinTarget ballModel 2 [flatBlock] :=
  (checkWithin_correct _ _ _).1 (by decide +kernel)

-- A block far away fails.
example : ¬ WithinTarget ballModel 2 [farBlock] := fun h =>
  absurd ((checkWithin_correct _ _ _).2 h) (by decide +kernel)

-- It rejects a checker that tests only the middle of a block: this block's middle is outside the
-- ball, yet the block is within the target.
example : (placeAt 2 ballModel.bubbles.head!).contains endBlock.center = false ∧
    WithinTarget ballModel 2 [endBlock] :=
  ⟨by decide +kernel, (checkWithin_correct _ _ _).1 (by decide +kernel)⟩

/-- `flatBlock` fills the cube (0, 0, 0), which is in the ball. -/
private theorem flat_built : ((0, 0, 0) : GridPt) ∈ blockCells [flatBlock] := by
  simp only [blockCells, mem_dedupe, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact List.mem_filter.2 ⟨by decide +kernel, by decide +kernel⟩

-- checkCovers_correct: a block with a cube in the ball covers it.
example : checkCovers ballModel 2 [flatBlock] = true := by
  refine (checkCovers_correct _ _ _).2 ?_
  intro b hb _
  simp only [ballModel, List.mem_singleton] at hb
  subst hb
  exact ⟨_, flat_built, by decide +kernel⟩

-- With no blocks, the ball is not covered.
example : ¬ CoversTarget ballModel 2 [] := by
  intro h
  obtain ⟨g, hg, _⟩ := h _ (.head _) (by
    intro he
    have hm := (mem_bubbleCells (placeAt 2 ballModel.bubbles.head!) (-1, -1, 0)).2 (by decide +kernel)
    exact List.not_mem_nil (he ▸ hm))
  simp [blockCells, mem_dedupe] at hg

-- score_in_unit_interval: the bound holds, and the wrong formula's 45 / 8 is rejected.
example : score ballModel 2 [flatBlock] ≠ 45 / 8 := by
  intro h
  have := (score_in_unit_interval ballModel 2 [flatBlock]).2
  rw [h] at this
  exact absurd this (by decide +kernel)

#guard score ballModel 2 [flatBlock] == 1 / 52

/-- A block with made-up turn numbers: both are 0, so its turn is not a real rotation. -/
private def fakeBlock : Pose := ⟨.flat, ⟨0, 0⟩, ⟨0, 0, 1 / 2⟩⟩

-- blockCells_correct: on a block with a real turn, the condition holds and a cube is listed.
example : ((0, 0, 0) : GridPt) ∈ blockCells [flatBlock] :=
  (blockCells_correct [flatBlock] (by decide +kernel) _).2 ⟨_, .head _, by decide +kernel⟩

-- It rejects a list that leaves out a cube of the block.
example : ¬ ∀ g : GridPt, g ∈ ([] : List GridPt) ↔
    ∃ blk ∈ [flatBlock], blk.contains g.centre = true := by
  intro h
  exact List.not_mem_nil ((h (0, 0, 0)).2 ⟨_, .head _, by decide +kernel⟩)

-- The condition is needed. The made-up block passes the test at this cube, but the cube is not
-- listed, so without the condition the theorem would be false.
example : fakeBlock.contains (GridPt.centre (5, 5, 0)) = true ∧
    ((5, 5, 0) : GridPt) ∉ blockCells [fakeBlock] := by
  refine ⟨by decide +kernel, ?_⟩
  simp only [blockCells, mem_dedupe, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact fun h => absurd (List.mem_filter.1 h).1 (by decide +kernel)

end KaplaSemantics
