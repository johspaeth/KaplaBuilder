import KaplaSpecs.PhysicsRules.Column
import KaplaPhysics.RobustProofs

/-! # Proof that `Stable` agrees with the column rule (property 6)

* Stable ⇒ rule: add up the balance of every plank from level `k` up. Pushes between two
  of these planks cancel; what is left are the pushes where plank `k` rests, and they carry
  the combined weight at the combined centre of mass. Those pushes sit at corners of the
  patch, so their average point lies in the patch.
* Rule ⇒ stable: let plank `k` pass the weight of everything from level `k` up, at the
  combined centre of mass, to the patch below it, spread over its corners (F4). -/

namespace KaplaPhysics

/-! ## Levels -/

theorem below_inBuild (n i : Nat) (hi : i < n) : (below i).InBuild n := by
  cases i <;> simp [below, Support.InBuild] <;> omega

theorem below_eq_plank (k i : Nat) : below k = .plank i ↔ k = i + 1 := by
  cases k <;> simp [below]

/-- In a column, every allowed push is between a plank and the plank just below it. -/
theorem column_push_lower (b : Build) (hc : IsColumn b) (p : Push) (hp : p.Allowed b) :
    p.lower = below p.upper := by
  obtain ⟨_, hu, hl, hr⟩ := hp
  apply (hc p.upper hu p.lower hl).mp
  revert hr; cases restPatch b p.upper p.lower <;> simp

theorem mem_fromLevel (b : Build) (k m : Nat) : m ∈ fromLevel b k ↔ k ≤ m ∧ m < b.length := by
  simp only [fromLevel, List.mem_range'_1]; omega

theorem fromLevel_succ (b : Build) (i : Nat) (hi : i < b.length) :
    fromLevel b i = i :: fromLevel b (i + 1) := by
  simp only [fromLevel]
  rw [show b.length - i = (b.length - (i + 1)) + 1 by omega, List.range'_succ]

theorem fromLevel_end (b : Build) (i : Nat) (hi : b.length ≤ i) : fromLevel b i = [] := by
  simp only [fromLevel]; rw [show b.length - i = 0 by omega]; rfl

theorem fromLevel_nodup (b : Build) (k : Nat) : (fromLevel b k).Nodup := List.nodup_range'

/-- A sum over a list without repeats of a term that is zero except at `a`. -/
theorem sum_single_nodup (l : List Nat) (hl : l.Nodup) (a : Nat) (f : Nat → Rat) :
    (l.map fun i => if a = i then f i else 0).sum = if a ∈ l then f a else 0 := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have ⟨hj, hl'⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons, List.sum_cons, ih hl', List.mem_cons]
    by_cases h : a = j
    · subst h; simp [hj]; grind
    · simp [h]; grind

/-! ## Stable ⇒ rule -/

/-- Summed over the planks from level `k` up, an allowed push in a column lifts them by its
force if it holds up plank `k`, and by nothing otherwise (it lifts one and presses the
other down by the same amount). -/
theorem column_push_sum (b : Build) (hc : IsColumn b) (k : Nat) (p : Push) (hp : p.Allowed b)
    (X : Rat) :
    ((fromLevel b k).map fun i => p.upOn i * X).sum = if p.upper = k then p.force * X else 0 := by
  have hl := column_push_lower b hc p hp
  have hu := hp.2.1
  have split : ∀ i ∈ fromLevel b k, p.upOn i * X
      = (if p.upper = i then p.force * X else 0)
        - (if p.upper = i + 1 then p.force * X else 0) := by
    intro i _
    simp only [Push.upOn, hl, below_eq_plank]
    split <;> split <;> grind
  rw [sum_map_congr _ _ _ split, sum_map_sub, sum_single_nodup _ (fromLevel_nodup b k)]
  cases hu' : p.upper with
  | zero =>
    have : ((fromLevel b k).map fun i => if 0 = i + 1 then p.force * X else 0).sum = 0 := by
      simp [sum_map_zero]
    simp only [this, mem_fromLevel]
    by_cases hk : k = 0 <;> simp [hk] <;> grind
  | succ v =>
    have : ((fromLevel b k).map fun i => if v + 1 = i + 1 then p.force * X else 0).sum
        = ((fromLevel b k).map fun i => if v = i then p.force * X else 0).sum := by
      apply sum_map_congr; intro i _; simp
    rw [this, sum_single_nodup _ (fromLevel_nodup b k)]
    simp only [mem_fromLevel]
    rw [hu'] at hu
    split <;> split <;> split <;> grind

/-- The number of planks from level `k` up, as a fraction. -/
theorem length_cast (l : List Nat) : (l.length : Rat) = (l.map fun _ => (1 : Rat)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons, ← ih]; grind

/-- If `x0 * W ≤ S` and `W > 0`, then `x0 ≤ S / W`. -/
theorem le_div_of_mul_le (x0 S W : Rat) (hW : 0 < W) (h : x0 * W ≤ S) : x0 ≤ S / W := by
  have e : S / W * W = S := by
    have : W ≠ 0 := by grind
    grind
  by_cases hn : x0 ≤ S / W
  · exact hn
  · have := Rat.mul_pos (show 0 < x0 - S / W by grind) hW
    grind

/-- If `S ≤ x1 * W` and `W > 0`, then `S / W ≤ x1`. -/
theorem div_le_of_le_mul (x1 S W : Rat) (hW : 0 < W) (h : S ≤ x1 * W) : S / W ≤ x1 := by
  have e : S / W * W = S := by
    have : W ≠ 0 := by grind
    grind
  by_cases hn : S / W ≤ x1
  · exact hn
  · have := Rat.mul_pos (show 0 < S / W - x1 by grind) hW
    grind

/-- Stable ⇒ the column rule holds at level `k`, along one axis. `pos p` is the push's
coordinate, `cen i` plank `i`'s centre, `lo`, `hi` the patch edges. -/
theorem column_level_axis (b : Build) (hc : IsColumn b) (ps : List Push)
    (hall : ∀ p ∈ ps, p.Allowed b) (k : Nat) (hk : k < b.length)
    (pos : Push → Rat) (cen : Nat → Rat) (lo hi : Rat)
    (hforce : ∀ i < b.length, (ps.map fun p => p.upOn i).sum = 1)
    (hturn : ∀ i < b.length, (ps.map fun p => p.upOn i * (pos p - cen i)).sum = 0)
    (hin : ∀ p ∈ ps, p.upper = k → lo ≤ pos p ∧ pos p ≤ hi) :
    lo ≤ ((fromLevel b k).map cen).sum / ((fromLevel b k).length : Rat) ∧
      ((fromLevel b k).map cen).sum / ((fromLevel b k).length : Rat) ≤ hi := by
  let L := fromLevel b k
  have memL : ∀ i ∈ L, i < b.length := fun i hi => ((mem_fromLevel b k i).mp hi).2
  -- Total force on the planks from level `k` up.
  have hW : ((ps.map fun p => if p.upper = k then p.force else 0).sum)
      = (L.length : Rat) := by
    rw [length_cast]
    calc (ps.map fun p => if p.upper = k then p.force else 0).sum
        = (ps.map fun p => (L.map fun i => p.upOn i * 1).sum).sum := by
          apply sum_map_congr; intro p hp
          rw [column_push_sum b hc k p (hall p hp) 1]; simp
      _ = (L.map fun i => (ps.map fun p => p.upOn i * 1).sum).sum := (sum_map_sum_comm _ _ _).symm
      _ = (L.map fun _ => (1 : Rat)).sum := by
          apply sum_map_congr; intro i hi
          simp only [Rat.mul_one]; exact hforce i (memL i hi)
  -- Total turning effect, measured from the origin.
  have hS : ((ps.map fun p => if p.upper = k then p.force * pos p else 0).sum)
      = (L.map cen).sum := by
    calc (ps.map fun p => if p.upper = k then p.force * pos p else 0).sum
        = (ps.map fun p => (L.map fun i => p.upOn i * pos p).sum).sum := by
          apply sum_map_congr; intro p hp
          rw [column_push_sum b hc k p (hall p hp) (pos p)]
      _ = (L.map fun i => (ps.map fun p => p.upOn i * pos p).sum).sum :=
          (sum_map_sum_comm _ _ _).symm
      _ = (L.map cen).sum := by
          apply sum_map_congr; intro i hi
          have h1 := hforce i (memL i hi)
          have h2 := hturn i (memL i hi)
          rw [sum_map_congr _ _ (fun p => p.upOn i * pos p - p.upOn i * cen i) (fun _ _ => by grind),
            sum_map_sub, sum_map_mul_right, h1] at h2
          grind
  have hLpos : (0 : Rat) < (L.length : Rat) := by
    show (0 : Rat) < ((fromLevel b k).length : Rat)
    rw [fromLevel_succ b k hk]; simp; grind
  -- The pushes at level `k` lie between `lo` and `hi`, so their weighted sum does too.
  have hlo : 0 ≤ (ps.map fun p => if p.upper = k then p.force * (pos p - lo) else 0).sum := by
    apply sum_map_nonneg; intro p hp
    split
    · exact Rat.mul_nonneg (hall p hp).1 (by have := hin p hp ‹_›; grind)
    · exact Rat.le_refl
  have hhi : 0 ≤ (ps.map fun p => if p.upper = k then p.force * (hi - pos p) else 0).sum := by
    apply sum_map_nonneg; intro p hp
    split
    · exact Rat.mul_nonneg (hall p hp).1 (by have := hin p hp ‹_›; grind)
    · exact Rat.le_refl
  rw [sum_map_congr _ _ (fun p => (if p.upper = k then p.force * pos p else 0)
      - lo * (if p.upper = k then p.force else 0)) (fun _ _ => by split <;> grind),
    sum_map_sub, sum_map_mul_left, hW, hS] at hlo
  rw [sum_map_congr _ _ (fun p => hi * (if p.upper = k then p.force else 0)
      - (if p.upper = k then p.force * pos p else 0)) (fun _ _ => by split <;> grind),
    sum_map_sub, sum_map_mul_left, hW, hS] at hhi
  exact ⟨le_div_of_mul_le _ _ _ hLpos (by grind), div_le_of_le_mul _ _ _ hLpos (by grind)⟩

/-- A contact patch always has an area bigger than zero. -/
theorem restPatch_area (b : Build) (i : Nat) (s : Support) (r : Rect)
    (h : restPatch b i s = some r) : r.HasArea := by
  cases s with
  | ground =>
    simp only [restPatch] at h
    split at h
    · cases h
      have := pose_size_pos (b.get i).pose
      simp only [Rect.HasArea, Plank.footprint, Plank.x1, Plank.y1]; grind
    · cases h
  | plank j =>
    simp only [restPatch] at h
    split at h
    · cases h; exact ‹_ ∧ _›.2
    · cases h

/-- The corners of a rectangle with an area lie in it. -/
theorem corner_contains (r : Rect) (hr : r.HasArea) (c : Rat × Rat) (hc : c ∈ r.corners) :
    r.Contains c.1 c.2 := by
  obtain ⟨hx, hy⟩ := hr
  simp only [Rect.corners, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp only [Rect.Contains] <;> grind

theorem stable_columnRule (b : Build) (hc : IsColumn b) (hs : Stable b) : ColumnRule b := by
  obtain ⟨ps, hall, hbal⟩ := hs
  intro k hk
  have hforce := fun i hi => (hbal i hi).1
  -- Every push holding up plank `k` sits at a corner of the patch below `k`.
  have corner : ∀ p ∈ ps, p.upper = k → ∃ r, restPatch b k (below k) = some r ∧
      r.HasArea ∧ r.Contains p.x p.y := by
    intro p hp hu
    have hl := column_push_lower b hc p (hall p hp)
    obtain ⟨_, _, _, hm⟩ := hall p hp
    rw [hl, hu] at hm
    revert hm
    cases hr : restPatch b k (below k) with
    | none => intro h; exact h.elim
    | some r =>
      intro hm
      exact ⟨r, rfl, restPatch_area b k _ r hr, corner_contains r (restPatch_area b k _ r hr) _ hm⟩
  cases hr : restPatch b k (below k) with
  | none =>
    -- No push can hold up plank `k`; its weight has nowhere to go.
    have := column_level_axis b hc ps hall k hk Push.x (fun i => (b.get i).centerX) 1 0 hforce
      (fun i hi => (hbal i hi).2.1)
      (fun p hp hu => by obtain ⟨r, h, _⟩ := corner p hp hu; rw [hr] at h; cases h)
    grind
  | some r =>
    have hx := column_level_axis b hc ps hall k hk Push.x (fun i => (b.get i).centerX) r.x0 r.x1
      hforce (fun i hi => (hbal i hi).2.1)
      (fun p hp hu => by
        obtain ⟨r', h, _, hcon⟩ := corner p hp hu
        rw [hr] at h; cases h; exact ⟨hcon.1, hcon.2.1⟩)
    have hy := column_level_axis b hc ps hall k hk Push.y (fun i => (b.get i).centerY) r.y0 r.y1
      hforce (fun i hi => (hbal i hi).2.2)
      (fun p hp hu => by
        obtain ⟨r', h, _, hcon⟩ := corner p hp hu
        rw [hr] at h; cases h; exact ⟨hcon.2.2.1, hcon.2.2.2⟩)
    exact ⟨hx.1, hx.2, hy.1, hy.2⟩

/-! ## Rule ⇒ stable -/

/-- Plank `k` passes the weight of everything from level `k` up, at the combined centre
of mass, to what it rests on. -/
def columnPush (b : Build) (k : Nat) : Push :=
  { upper := k, lower := below k, x := comX b k, y := comY b k,
    force := ((fromLevel b k).length : Rat) }

/-- The pushes for a column that meets the rule: each `columnPush`, spread over the corners
of its patch. -/
def columnPushes (b : Build) : List Push :=
  (List.range b.length).flatMap fun k =>
    spreadOver ((restPatch b k (below k)).getD default) (columnPush b k)

/-- The number of planks from level `k` up, times their centre of mass, is the sum of
their centres. -/
theorem length_mul_avg (l : List Nat) (f : Nat → Rat) :
    (l.length : Rat) * ((l.map f).sum / (l.length : Rat)) = (l.map f).sum := by
  cases l with
  | nil => simp
  | cons a l =>
    have : ((a :: l).length : Rat) ≠ 0 := by simp; grind
    grind

/-- Summing over all planks `k` a term that is only there when plank `k` rests on plank
`i` (that is, `k = i + 1`). -/
theorem sum_below (n i : Nat) (g : Nat → Rat) :
    ((List.range n).map fun k => if below k = .plank i then g k else 0).sum
      = if i + 1 < n then g (i + 1) else 0 := by
  rw [sum_map_congr _ _ (fun k => if i + 1 = k then g k else 0)
    (fun k _ => by simp only [below_eq_plank]; split <;> split <;> grind),
    sum_single_nodup _ List.nodup_range]
  simp

/-- If every level's centre of mass is over the patch where that level rests, the build is
stable. (This direction needs no column assumption.) -/
theorem columnRule_stable (b : Build) (hr : ColumnRule b) : Stable b := by
  -- Each level's patch, with the centre of mass inside it.
  have patch : ∀ k < b.length, ∃ r, restPatch b k (below k) = some r ∧ r.HasArea ∧
      r.Contains (comX b k) (comY b k) := by
    intro k hk
    have := hr k hk
    revert this
    cases h : restPatch b k (below k) with
    | none => intro h; exact h.elim
    | some r => intro hin; exact ⟨r, rfl, restPatch_area b k _ r h, hin⟩
  refine ⟨columnPushes b, ?_, ?_⟩
  · intro p hp
    simp only [columnPushes, List.mem_flatMap, List.mem_range] at hp
    obtain ⟨k, hk, hp⟩ := hp
    obtain ⟨r, hr, ⟨hx, hy⟩, h1, h2, h3, h4⟩ := patch k hk
    rw [hr] at hp
    exact spread_allowed b r (columnPush b k) (by simp [columnPush] <;> grind) hk
      (below_inBuild _ _ hk) hr hx hy h1 h2 h3 h4 p hp
  · intro i hi
    have hspread : ∀ k ∈ List.range b.length, ∃ r,
        (restPatch b k (below k)).getD default = r ∧ r.x0 < r.x1 ∧ r.y0 < r.y1 := by
      intro k hk
      obtain ⟨r, hr, ⟨hx, hy⟩, _⟩ := patch k (List.mem_range.mp hk)
      exact ⟨r, by rw [hr]; rfl, hx, hy⟩
    -- Weights and centre sums one level up.
    have hW : ((fromLevel b i).length : Rat) = ((fromLevel b (i + 1)).length : Rat) + 1 := by
      rw [fromLevel_succ b i hi]; simp
    have hSx : ((fromLevel b i).map fun m => (b.get m).centerX).sum
        = (b.get i).centerX + ((fromLevel b (i + 1)).map fun m => (b.get m).centerX).sum := by
      rw [fromLevel_succ b i hi]; simp
    have hSy : ((fromLevel b i).map fun m => (b.get m).centerY).sum
        = (b.get i).centerY + ((fromLevel b (i + 1)).map fun m => (b.get m).centerY).sum := by
      rw [fromLevel_succ b i hi]; simp
    have hend : ¬ i + 1 < b.length → fromLevel b (i + 1) = [] :=
      fun h => fromLevel_end b (i + 1) (by omega)
    have upOn_col : ∀ k, (columnPush b k).upOn i
        = (if i = k then ((fromLevel b k).length : Rat) else 0)
          - (if below k = .plank i then ((fromLevel b k).length : Rat) else 0) := by
      intro k; simp only [Push.upOn, columnPush]
      by_cases h : i = k
      · subst h; simp only [ite_true]; rfl
      · simp only [h, Ne.symm h, ite_false]; rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [columnPushes, sum_flatMap,
        sum_map_congr _ _ _ fun k _ => spread_force _ (columnPush b k) i]
      rw [sum_map_congr _ _ _ fun k _ => upOn_col k, sum_map_sub,
        sum_range_single _ _ hi (fun k => ((fromLevel b k).length : Rat)), sum_below]
      split
      · grind
      · rw [hend ‹_›] at hW; simp at hW; grind
    · rw [columnPushes, sum_flatMap,
        sum_map_congr _ _ _ fun k hk => by
          obtain ⟨r, hr, hx, _⟩ := hspread k hk
          rw [hr]; exact spread_turnX r (columnPush b k) i (b.get i).centerX hx]
      rw [sum_map_congr _ _ (fun k =>
          (if i = k then ((fromLevel b k).length : Rat) * (comX b k - (b.get i).centerX) else 0)
          - (if below k = .plank i then
              ((fromLevel b k).length : Rat) * (comX b k - (b.get i).centerX) else 0))
          (fun k _ => by rw [upOn_col]; simp only [columnPush]; split <;> split <;> grind),
        sum_map_sub, sum_range_single _ _ hi, sum_below]
      have m0 := length_mul_avg (fromLevel b i) fun m => (b.get m).centerX
      have m1 := length_mul_avg (fromLevel b (i + 1)) fun m => (b.get m).centerX
      simp only [comX] at m0 m1 ⊢
      split
      · grind
      · rw [hend ‹_›] at hW hSx; simp at hW hSx; grind
    · rw [columnPushes, sum_flatMap,
        sum_map_congr _ _ _ fun k hk => by
          obtain ⟨r, hr, _, hy⟩ := hspread k hk
          rw [hr]; exact spread_turnY r (columnPush b k) i (b.get i).centerY hy]
      rw [sum_map_congr _ _ (fun k =>
          (if i = k then ((fromLevel b k).length : Rat) * (comY b k - (b.get i).centerY) else 0)
          - (if below k = .plank i then
              ((fromLevel b k).length : Rat) * (comY b k - (b.get i).centerY) else 0))
          (fun k _ => by rw [upOn_col]; simp only [columnPush]; split <;> split <;> grind),
        sum_map_sub, sum_range_single _ _ hi, sum_below]
      have m0 := length_mul_avg (fromLevel b i) fun m => (b.get m).centerY
      have m1 := length_mul_avg (fromLevel b (i + 1)) fun m => (b.get m).centerY
      simp only [comY] at m0 m1 ⊢
      split
      · grind
      · rw [hend ‹_›] at hW hSy; simp at hW hSy; grind

end KaplaPhysics
