import KaplaSpecs.PhysicsRules.Tower
import KaplaPhysics.ColumnProofs

/-! # Square towers are safe to build, at any height (property 9)

After `k` steps the tower is `towerBuild k`: planks `0 .. k-1`. We show it is well-formed
and solid for every `k`, for placement errors up to `ε ≤ 1/2`.

How the weight flows: the tower has four corners, and at every level each corner is
covered by exactly one plank. Each plank splits its own weight between its two corners,
in the ratio that puts the split exactly at its (moved) centre. Each corner then carries
the shares of every plank above it straight down. Every load point stays in a small
"core" square at its corner, which lies inside every contact patch there, whatever the
errors are. -/

namespace KaplaPhysics

/-! ## Planks of the tower -/

/-- What stands after `k` steps. -/
def towerBuild (k : Nat) : Build := (List.range k).map towerPlank

@[simp] theorem towerBuild_length (k : Nat) : (towerBuild k).length = k := by
  simp [towerBuild]

theorem towerBuild_get (k m : Nat) (h : m < k) : (towerBuild k).get m = towerPlank m := by
  simp [towerBuild, Build.get, List.getD_eq_getElem?_getD, h]

theorem squareTower_take (n k : Nat) (hk : k ≤ 2 * n) :
    (squareTower n).take k = towerBuild k := by
  simp [squareTower, towerBuild, ← List.map_take, List.take_range, Nat.min_eq_left hk]

/-- The four kinds of tower plank, by level parity and side. -/
theorem towerPlank_cases (m : Nat) :
    (m / 2 % 2 = 0 ∧ m % 2 = 0 ∧ towerPlank m = ⟨.flatX, 0, 0, ((m / 2 : Nat) : Rat)⟩) ∨
    (m / 2 % 2 = 0 ∧ m % 2 = 1 ∧ towerPlank m = ⟨.flatX, 0, 12, ((m / 2 : Nat) : Rat)⟩) ∨
    (m / 2 % 2 = 1 ∧ m % 2 = 0 ∧ towerPlank m = ⟨.flatY, 0, 0, ((m / 2 : Nat) : Rat)⟩) ∨
    (m / 2 % 2 = 1 ∧ m % 2 = 1 ∧ towerPlank m = ⟨.flatY, 12, 0, ((m / 2 : Nat) : Rat)⟩) := by
  have h1 : m / 2 % 2 = 0 ∨ m / 2 % 2 = 1 := by omega
  have h2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [towerPlank, h1, h2]

/-! ## Well-formed after every step -/

theorem tower_no_overlap (i j : Nat) (hij : i ≠ j) : ¬ Overlap (towerPlank i) (towerPlank j) := by
  intro h
  have hz := h.2.2
  by_cases hl : i / 2 = j / 2
  · -- Same level: the two planks are on opposite sides.
    have hp : i % 2 ≠ j % 2 := by omega
    rcases towerPlank_cases i with ⟨a1, a2, ei⟩ | ⟨a1, a2, ei⟩ | ⟨a1, a2, ei⟩ | ⟨a1, a2, ei⟩ <;>
    rcases towerPlank_cases j with ⟨b1, b2, ej⟩ | ⟨b1, b2, ej⟩ | ⟨b1, b2, ej⟩ | ⟨b1, b2, ej⟩ <;>
    (try omega) <;>
    · rw [ei, ej] at h
      simp only [Overlap, Plank.x1, Plank.y1, Plank.top, Pose.size] at h
      grind
  · -- Different levels: one is at least a full thickness above the other.
    have hc : ((i / 2 : Nat) : Rat) + 1 ≤ ((j / 2 : Nat) : Rat) ∨
        ((j / 2 : Nat) : Rat) + 1 ≤ ((i / 2 : Nat) : Rat) := by
      rcases Nat.lt_or_gt_of_ne hl with h' | h'
      · left; exact_mod_cast h'
      · right; exact_mod_cast h'
    rcases towerPlank_cases i with ⟨_, _, ei⟩ | ⟨_, _, ei⟩ | ⟨_, _, ei⟩ | ⟨_, _, ei⟩ <;>
    rcases towerPlank_cases j with ⟨_, _, ej⟩ | ⟨_, _, ej⟩ | ⟨_, _, ej⟩ | ⟨_, _, ej⟩ <;>
    · rw [ei, ej] at hz
      simp only [Plank.top, Pose.size] at hz
      grind

theorem tower_wellFormed (k : Nat) : WellFormed (towerBuild k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj hij
    simp only [towerBuild_length] at hi hj
    rw [towerBuild_get k i hi, towerBuild_get k j hj]
    exact tower_no_overlap i j hij
  · intro i hi
    simp only [towerBuild_length] at hi
    rw [towerBuild_get k i hi]
    rcases towerPlank_cases i with ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;>
      rw [e] <;> show (0 : Rat) ≤ ((i / 2 : Nat) : Rat) <;> exact_mod_cast Nat.zero_le _
  · intro i hi
    simp only [towerBuild_length] at hi
    by_cases h0 : i / 2 = 0
    · -- Level 0 rests on the ground.
      left
      simp only [restPatch, towerBuild_get k i hi]
      rcases towerPlank_cases i with ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;>
        rw [e] <;> simp [h0]
    · -- Higher levels rest on the first plank of the level below.
      right
      refine ⟨2 * (i / 2 - 1), by simp; omega, ?_⟩
      have hlow : (2 * (i / 2 - 1)) / 2 = i / 2 - 1 := by omega
      have hz : ((i / 2 : Nat) : Rat) = ((i / 2 - 1 : Nat) : Rat) + 1 := by
        rw [show i / 2 = (i / 2 - 1) + 1 by omega]; simp
      simp only [restPatch, towerBuild_get k i hi, towerBuild_get k _ (show 2 * (i / 2 - 1) < k by omega)]
      rcases towerPlank_cases i with ⟨a1, _, e⟩ | ⟨a1, _, e⟩ | ⟨a1, _, e⟩ | ⟨a1, _, e⟩ <;>
      rcases towerPlank_cases (2 * (i / 2 - 1)) with ⟨b1, b2, f⟩ | ⟨b1, b2, f⟩ | ⟨b1, b2, f⟩ | ⟨b1, b2, f⟩ <;>
      (try omega) <;>
      · rw [e, f, hlow]
        simp only [Plank.top, Pose.size, Plank.footprint, Plank.x1, Plank.y1, Rect.inter,
          Rect.HasArea]
        simp only [hz, true_and]
        grind

/-! ## Corners and loads -/

/-- The four corners of the tower: `(a, c)` is the corner near `(12a, 12c)`. -/
def towerCorners : List (Nat × Nat) := [(0, 0), (1, 0), (0, 1), (1, 1)]

/-- The plank of level `L` that covers corner `κ`. -/
def plankAt (L : Nat) (κ : Nat × Nat) : Nat := 2 * L + (if L % 2 = 0 then κ.2 else κ.1)

theorem plankAt_ge (L : Nat) (κ : Nat × Nat) : 2 * L ≤ plankAt L κ := by
  simp only [plankAt]; split <;> omega

theorem plankAt_mono (L L' : Nat) (κ : Nat × Nat) (hκ : κ ∈ towerCorners) (h : L ≤ L') :
    plankAt L κ ≤ plankAt L' κ := by
  simp only [towerCorners, List.mem_cons, List.mem_nil_iff, or_false] at hκ
  simp only [plankAt]
  rcases hκ with rfl | rfl | rfl | rfl <;> split <;> split <;> simp <;> omega

theorem plankAt_bit (L : Nat) (κ : Nat × Nat) (hκ : κ ∈ towerCorners) :
    plankAt L κ = 2 * L ∨ plankAt L κ = 2 * L + 1 := by
  simp only [towerCorners, List.mem_cons, List.mem_nil_iff, or_false] at hκ
  simp only [plankAt]
  rcases hκ with rfl | rfl | rfl | rfl <;> split <;> simp

theorem plankAt_eq_iff (L : Nat) (κ : Nat × Nat) (hκ : κ ∈ towerCorners) (i : Nat) :
    plankAt L κ = i ↔ L = i / 2 ∧ plankAt (i / 2) κ = i := by
  constructor
  · intro h
    have hL : L = i / 2 := by rcases plankAt_bit L κ hκ with h' | h' <;> omega
    exact ⟨hL, hL ▸ h⟩
  · rintro ⟨rfl, h⟩; exact h

variable (d : Nat → Rat × Rat)

/-- The share of its own weight that the level-`L` plank at corner `κ` passes down at `κ`.
The two shares of a plank put its weight exactly at its (moved) centre. -/
def share (L : Nat) (κ : Nat × Nat) : Rat :=
  let e := d (plankAt L κ)
  if L % 2 = 0 then (if κ.1 = 0 then (6 - e.1) / 12 else (6 + e.1) / 12)
  else (if κ.2 = 0 then (6 - e.2) / 12 else (6 + e.2) / 12)

/-- Where that share acts, along `x`. -/
def shareX (L : Nat) (κ : Nat × Nat) : Rat :=
  12 * (κ.1 : Rat) + 3 / 2 + (if L % 2 = 0 then 0 else (d (plankAt L κ)).1)

/-- Where that share acts, along `y`. -/
def shareY (L : Nat) (κ : Nat × Nat) : Rat :=
  12 * (κ.2 : Rat) + 3 / 2 + (if L % 2 = 0 then (d (plankAt L κ)).2 else 0)

/-- Sum, over the planks of levels `L` and up that exist after `k` steps, of `f` at corner `κ`. -/
def fromL (k L : Nat) (κ : Nat × Nat) (f : Nat → Rat) : Rat :=
  ((List.range k).map fun L' => if L ≤ L' ∧ plankAt L' κ < k then f L' else 0).sum

/-- The load passed down at corner `κ` from level `L` to level `L - 1` (or the ground). -/
def load (k L : Nat) (κ : Nat × Nat) : Rat := fromL k L κ fun L' => share d L' κ
/-- The load times its point, along `x`. -/
def momX (k L : Nat) (κ : Nat × Nat) : Rat := fromL k L κ fun L' => share d L' κ * shareX d L' κ
/-- The load times its point, along `y`. -/
def momY (k L : Nat) (κ : Nat × Nat) : Rat := fromL k L κ fun L' => share d L' κ * shareY d L' κ

/-- Level `L` passes its own share plus everything from above. -/
theorem fromL_succ (k L : Nat) (κ : Nat × Nat) (f : Nat → Rat) :
    fromL k L κ f = (if plankAt L κ < k then f L else 0) + fromL k (L + 1) κ f := by
  simp only [fromL]
  rw [sum_map_congr _ _ (fun L' => (if L = L' then (if plankAt L' κ < k then f L' else 0) else 0)
      + (if L + 1 ≤ L' ∧ plankAt L' κ < k then f L' else 0))
    (fun L' _ => by split <;> split <;> split <;> (try split) <;> grind),
    sum_map_add]
  by_cases hL : L < k
  · rw [sum_range_single k L hL (fun L' => if plankAt L' κ < k then f L' else 0)]
  · have : plankAt L κ ≥ k := by have := plankAt_ge L κ; omega
    rw [sum_map_congr _ _ (fun _ => 0) (fun L' hL' => by
      simp at hL'; split <;> grind), sum_map_zero]
    have hn : ¬ plankAt L κ < k := by omega
    simp only [hn, ite_false]

/-- Above the top of the tower, nothing is passed down. -/
theorem fromL_top (k L : Nat) (κ : Nat × Nat) (hκ : κ ∈ towerCorners) (f : Nat → Rat)
    (h : ¬ plankAt L κ < k) : fromL k L κ f = 0 := by
  simp only [fromL]
  rw [sum_map_congr _ _ (fun _ => 0) (fun L' _ => by
    split
    · rename_i h'; have := plankAt_mono L L' κ hκ h'.1; omega
    · rfl), sum_map_zero]

/-! ## Reindexing the sums over (level, corner) -/

/-- The pushes of the tower, as point pushes before spreading, summed for plank `i`: only
the pushes from plank `i` down (level `i / 2`) and onto plank `i` (level `i / 2 + 1`)
count. -/
theorem tower_sum (k i : Nat) (hi : i < k) (F A : Nat → Nat × Nat → Rat) :
    ((List.range k).map fun L => (towerCorners.map fun κ =>
      if plankAt L κ < k then
        ((if plankAt L κ = i then F L κ else 0)
          - (if L ≠ 0 ∧ plankAt (L - 1) κ = i then F L κ else 0)) * A L κ
      else 0).sum).sum
    = (towerCorners.map fun κ => if plankAt (i / 2) κ = i then
        F (i / 2) κ * A (i / 2) κ
          - (if plankAt (i / 2 + 1) κ < k then F (i / 2 + 1) κ * A (i / 2 + 1) κ else 0)
        else 0).sum := by
  rw [sum_map_congr _ _ (fun L => (towerCorners.map fun κ =>
      (if i / 2 = L then (if plankAt L κ = i then F L κ * A L κ else 0) else 0)
      - (if i / 2 + 1 = L then (if plankAt (L - 1) κ = i ∧ plankAt L κ < k then
          F L κ * A L κ else 0) else 0)).sum)]
  · rw [sum_map_congr _ _ (fun L =>
        (if i / 2 = L then (towerCorners.map fun κ => if plankAt L κ = i then F L κ * A L κ else 0).sum else 0)
        - (if i / 2 + 1 = L then (towerCorners.map fun κ => if plankAt (L - 1) κ = i ∧ plankAt L κ < k
            then F L κ * A L κ else 0).sum else 0))
      (fun L _ => by rw [sum_map_sub]; split <;> split <;> simp [sum_map_zero])]
    rw [sum_map_sub, sum_range_single k (i / 2) (by omega)]
    by_cases h1 : i / 2 + 1 < k
    · rw [sum_range_single k (i / 2 + 1) h1, ← sum_map_sub]
      apply sum_map_congr; intro κ _
      simp only [Nat.add_sub_cancel]
      split <;> split <;> grind
    · rw [sum_map_congr (List.range k) _ (fun _ => 0)
        (fun L hL => by simp at hL; split <;> grind), sum_map_zero]
      rw [show ∀ a : Rat, a - 0 = a from fun a => by grind]
      apply sum_map_congr; intro κ _
      have : ¬ plankAt (i / 2 + 1) κ < k := by have := plankAt_ge (i / 2 + 1) κ; omega
      by_cases hp : plankAt (i / 2) κ = i <;> simp only [hp, this, ite_true, ite_false] <;> grind
  · intro L _
    apply sum_map_congr; intro κ hκ
    have e1 := plankAt_eq_iff L κ hκ i
    by_cases hL0 : L = 0
    · subst hL0
      by_cases h : plankAt 0 κ = i
      · have := e1.mp h; simp only [h, ite_true]; split <;> split <;> grind
      · simp only [h, ite_false]; split <;> split <;> (try split) <;> grind
    · have e2 := plankAt_eq_iff (L - 1) κ hκ i
      split <;> split <;> split <;> (try split) <;> (try split) <;> grind

/-! ## Each plank's two shares -/

/-- The tower plank at corner `κ` of level `L`. -/
theorem towerPlank_plankAt (L : Nat) (κ : Nat × Nat) (hκ : κ ∈ towerCorners) :
    towerPlank (plankAt L κ) = if L % 2 = 0 then ⟨.flatX, 0, 12 * (κ.2 : Rat), (L : Rat)⟩
      else ⟨.flatY, 12 * (κ.1 : Rat), 0, (L : Rat)⟩ := by
  simp only [towerCorners, List.mem_cons, List.mem_nil_iff, or_false] at hκ
  have h2 : (2 * L + 1) / 2 = L := by omega
  have h3 : (2 * L + 1) % 2 = 1 := by omega
  rcases hκ with rfl | rfl | rfl | rfl <;> by_cases hL : L % 2 = 0 <;>
    simp [plankAt, towerPlank, hL, h2, h3]

/-- The corners covered by plank `2L + β`: two on the side `β` of the level's direction. -/
theorem corners_of_plank (L β : Nat) (hβ : β < 2) (f : Nat × Nat → Rat) :
    (towerCorners.map fun κ => if plankAt L κ = 2 * L + β then f κ else 0).sum =
      if L % 2 = 0 then f (0, β) + f (1, β) else f (β, 0) + f (β, 1) := by
  have : β = 0 ∨ β = 1 := by omega
  rcases this with rfl | rfl <;> by_cases hL : L % 2 = 0 <;>
    simp [towerCorners, plankAt, hL] <;> grind

/-- A plank's two shares add up to its weight, 1, and put it at its moved centre. -/
theorem own_shares (L β : Nat) (hβ : β < 2) :
    (towerCorners.map fun κ => if plankAt L κ = 2 * L + β then share d L κ else 0).sum = 1 ∧
    (towerCorners.map fun κ => if plankAt L κ = 2 * L + β then
      share d L κ * shareX d L κ else 0).sum
        = (towerPlank (2 * L + β)).centerX + (d (2 * L + β)).1 ∧
    (towerCorners.map fun κ => if plankAt L κ = 2 * L + β then
      share d L κ * shareY d L κ else 0).sum
        = (towerPlank (2 * L + β)).centerY + (d (2 * L + β)).2 := by
  rw [corners_of_plank L β hβ, corners_of_plank L β hβ, corners_of_plank L β hβ]
  have hb : β = 0 ∨ β = 1 := by omega
  by_cases hL : L % 2 = 0
  · have e := towerPlank_plankAt L (0, β) (by rcases hb with rfl | rfl <;> simp [towerCorners])
    have p0 : plankAt L (0, β) = 2 * L + β := by simp [plankAt, hL]
    have p1 : plankAt L (1, β) = 2 * L + β := by simp [plankAt, hL]
    rw [p0] at e
    simp only [hL, ite_true, share, shareX, shareY, p0, p1, e, Plank.centerX, Plank.centerY,
      Pose.size]
    rcases hb with rfl | rfl <;> simp <;> refine ⟨by grind, by grind, by grind⟩
  · have e := towerPlank_plankAt L (β, 0) (by rcases hb with rfl | rfl <;> simp [towerCorners])
    have p0 : plankAt L (β, 0) = 2 * L + β := by simp [plankAt, hL]
    have p1 : plankAt L (β, 1) = 2 * L + β := by simp [plankAt, hL]
    rw [p0] at e
    simp only [hL, ite_false, share, shareX, shareY, p0, p1, e, Plank.centerX, Plank.centerY,
      Pose.size]
    rcases hb with rfl | rfl <;> simp <;> refine ⟨by grind, by grind, by grind⟩

/-! ## Loads are positive and stay in the corner cores -/

theorem fromL_nonneg (k L : Nat) (κ : Nat × Nat) (f : Nat → Rat)
    (hf : ∀ L', plankAt L' κ < k → 0 ≤ f L') : 0 ≤ fromL k L κ f := by
  apply sum_map_nonneg; intro L' _
  split
  · rename_i h; exact hf L' h.2
  · exact Rat.le_refl

theorem fromL_sub_mul (k L : Nat) (κ : Nat × Nat) (f g : Nat → Rat) (c : Rat) :
    fromL k L κ (fun L' => f L' - c * g L') = fromL k L κ f - c * fromL k L κ g := by
  simp only [fromL]
  rw [← sum_map_mul_left, ← sum_map_sub]
  apply sum_map_congr; intro L' _; split <;> grind

/-- With errors of at most `ε ≤ 1/2`, every share is positive and acts inside its corner's
core square `[12a + ε, 12a + 3 - ε] × [12c + ε, 12c + 3 - ε]`. -/
theorem share_bounds (ε : Rat) (hε : ε ≤ 1 / 2) (k L : Nat) (κ : Nat × Nat)
    (hd : SmallShift ε k d) (hk : plankAt L κ < k) :
    0 < share d L κ ∧
    12 * (κ.1 : Rat) + ε ≤ shareX d L κ ∧ shareX d L κ ≤ 12 * (κ.1 : Rat) + 3 - ε ∧
    12 * (κ.2 : Rat) + ε ≤ shareY d L κ ∧ shareY d L κ ≤ 12 * (κ.2 : Rat) + 3 - ε := by
  have e := hd _ hk
  simp only [share, shareX, shareY]
  split <;> (try split) <;> refine ⟨by grind, by grind, by grind, by grind, by grind⟩

/-- The load at a corner that exists is at least that plank's share, so above zero. -/
theorem load_pos (ε : Rat) (hε : ε ≤ 1 / 2) (k L : Nat) (κ : Nat × Nat)
    (hd : SmallShift ε k d) (hk : plankAt L κ < k) :
    0 < load d k L κ := by
  have h1 := (share_bounds d ε hε k L κ hd hk).1
  have h2 := fromL_nonneg k (L + 1) κ (fun L' => share d L' κ)
    (fun L' h => Rat.le_of_lt (share_bounds d ε hε k L' κ hd h).1)
  simp only [load] at h2 ⊢
  rw [fromL_succ]; simp only [hk, ite_true]; grind

/-- The load point at a corner lies in that corner's core square. -/
theorem point_in_core (ε : Rat) (hε : ε ≤ 1 / 2) (k L : Nat) (κ : Nat × Nat)
    (hd : SmallShift ε k d) (hk : plankAt L κ < k) :
    12 * (κ.1 : Rat) + ε ≤ momX d k L κ / load d k L κ ∧
    momX d k L κ / load d k L κ ≤ 12 * (κ.1 : Rat) + 3 - ε ∧
    12 * (κ.2 : Rat) + ε ≤ momY d k L κ / load d k L κ ∧
    momY d k L κ / load d k L κ ≤ 12 * (κ.2 : Rat) + 3 - ε := by
  have hF := load_pos d ε hε k L κ hd hk
  have b := fun L' (h : plankAt L' κ < k) => share_bounds d ε hε k L' κ hd h
  -- Each bound is a sum of terms `share * (distance to the edge) ≥ 0`.
  have lx := fromL_nonneg k L κ (fun L' => share d L' κ * shareX d L' κ
      - (12 * (κ.1 : Rat) + ε) * share d L' κ) fun L' h => by
    have := b L' h; have := Rat.mul_nonneg (Rat.le_of_lt this.1)
      (show 0 ≤ shareX d L' κ - (12 * (κ.1 : Rat) + ε) by grind); grind
  have hx := fromL_nonneg k L κ (fun L' => (12 * (κ.1 : Rat) + 3 - ε) * share d L' κ
      - share d L' κ * shareX d L' κ) fun L' h => by
    have := b L' h; have := Rat.mul_nonneg (Rat.le_of_lt this.1)
      (show 0 ≤ (12 * (κ.1 : Rat) + 3 - ε) - shareX d L' κ by grind); grind
  have ly := fromL_nonneg k L κ (fun L' => share d L' κ * shareY d L' κ
      - (12 * (κ.2 : Rat) + ε) * share d L' κ) fun L' h => by
    have := b L' h; have := Rat.mul_nonneg (Rat.le_of_lt this.1)
      (show 0 ≤ shareY d L' κ - (12 * (κ.2 : Rat) + ε) by grind); grind
  have hy := fromL_nonneg k L κ (fun L' => (12 * (κ.2 : Rat) + 3 - ε) * share d L' κ
      - share d L' κ * shareY d L' κ) fun L' h => by
    have := b L' h; have := Rat.mul_nonneg (Rat.le_of_lt this.1)
      (show 0 ≤ (12 * (κ.2 : Rat) + 3 - ε) - shareY d L' κ by grind); grind
  rw [fromL_sub_mul] at lx ly
  rw [show (fun L' => (12 * (κ.1 : Rat) + 3 - ε) * share d L' κ - share d L' κ * shareX d L' κ)
      = (fun L' => -(share d L' κ * shareX d L' κ - (12 * (κ.1 : Rat) + 3 - ε) * share d L' κ))
      from funext fun _ => by grind] at hx
  rw [show (fun L' => (12 * (κ.2 : Rat) + 3 - ε) * share d L' κ - share d L' κ * shareY d L' κ)
      = (fun L' => -(share d L' κ * shareY d L' κ - (12 * (κ.2 : Rat) + 3 - ε) * share d L' κ))
      from funext fun _ => by grind] at hy
  have neg : ∀ f, fromL k L κ (fun L' => -(f L')) = -(fromL k L κ f) := fun f => by
    simp only [fromL]; rw [← sum_map_neg]; apply sum_map_congr; intro _ _; split <;> grind
  rw [neg, fromL_sub_mul] at hx hy
  simp only [load, momX, momY] at hF ⊢
  exact ⟨le_div_of_mul_le _ _ _ hF (by grind), div_le_of_le_mul _ _ _ hF (by grind),
    le_div_of_mul_le _ _ _ hF (by grind), div_le_of_le_mul _ _ _ hF (by grind)⟩

/-! ## Contact patches contain the corner cores -/

/-- What the level-`L` plank at corner `κ` rests on there: the ground, or the plank of the
level below at the same corner. -/
def lowerOf (L : Nat) (κ : Nat × Nat) : Support :=
  if L = 0 then .ground else .plank (plankAt (L - 1) κ)

theorem corner_cases (κ : Nat × Nat) (hκ : κ ∈ towerCorners) :
    ((κ.1 : Rat) = 0 ∨ (κ.1 : Rat) = 1) ∧ ((κ.2 : Rat) = 0 ∨ (κ.2 : Rat) = 1) := by
  simp only [towerCorners, List.mem_cons, List.mem_nil_iff, or_false] at hκ
  rcases hκ with rfl | rfl | rfl | rfl <;> simp

/-- With errors of at most `ε ≤ 1/2`, the real patch at corner `κ` between level `L` and
what it rests on contains the core square of `κ`. -/
theorem tower_patch (ε : Rat) (hε : ε ≤ 1 / 2) (k L : Nat) (κ : Nat × Nat)
    (hκ : κ ∈ towerCorners) (hd : SmallShift ε k d) (hk : plankAt L κ < k) :
    ∃ r, restPatch ((towerBuild k).shift d) (plankAt L κ) (lowerOf L κ) = some r ∧
      r.x0 ≤ 12 * (κ.1 : Rat) + ε ∧ 12 * (κ.1 : Rat) + 3 - ε ≤ r.x1 ∧
      r.y0 ≤ 12 * (κ.2 : Rat) + ε ∧ 12 * (κ.2 : Rat) + 3 - ε ≤ r.y1 := by
  have ⟨c1, c2⟩ := corner_cases κ hκ
  have du := hd _ hk
  have hku : plankAt L κ < (towerBuild k).length := by simpa using hk
  cases L with
  | zero =>
    simp only [lowerOf, ite_true, restPatch, shift_get _ d _ hku, towerBuild_get k _ hk,
      towerPlank_plankAt 0 κ hκ]
    split
    · exact ⟨_, rfl, by simp [Plank.footprint, Plank.x1, Pose.size]; grind,
        by simp [Plank.footprint, Plank.x1, Pose.size]; grind,
        by simp [Plank.footprint, Plank.y1, Pose.size]; grind,
        by simp [Plank.footprint, Plank.y1, Pose.size]; grind⟩
    · exfalso; grind
  | succ L' =>
    have hl : plankAt L' κ < k := by
      have := plankAt_ge (L' + 1) κ; rcases plankAt_bit L' κ hκ with h | h <;> omega
    have hkl : plankAt L' κ < (towerBuild k).length := by simpa using hl
    have dl := hd _ hl
    simp only [lowerOf, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, restPatch,
      shift_get _ d _ hku, shift_get _ d _ hkl, towerBuild_get k _ hk, towerBuild_get k _ hl,
      towerPlank_plankAt _ κ hκ]
    have hz : ((L' + 1 : Nat) : Rat) = (L' : Rat) + 1 := by simp
    by_cases hp : L' % 2 = 0
    · have hp' : ¬ (L' + 1) % 2 = 0 := by omega
      simp only [hp, hp', ite_true, ite_false]
      split
      · refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩ <;>
          simp only [Plank.footprint, Rect.inter, Plank.x1, Plank.y1, Pose.size] <;> grind
      · exfalso; rename_i hn; apply hn
        simp only [Plank.top, Pose.size, Rect.HasArea, Plank.footprint, Rect.inter, Plank.x1,
          Plank.y1]
        refine ⟨by grind, by grind, by grind⟩
    · have hp' : (L' + 1) % 2 = 0 := by omega
      simp only [hp, hp', ite_true, ite_false]
      split
      · refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩ <;>
          simp only [Plank.footprint, Rect.inter, Plank.x1, Plank.y1, Pose.size] <;> grind
      · exfalso; rename_i hn; apply hn
        simp only [Plank.top, Pose.size, Rect.HasArea, Plank.footprint, Rect.inter, Plank.x1,
          Plank.y1]
        refine ⟨by grind, by grind, by grind⟩

/-! ## The pushes, and balance for every error -/

/-- The point push at corner `κ` from level `L`: the corner's load, at its load point. -/
def towerPoint (k L : Nat) (κ : Nat × Nat) : Push :=
  { upper := plankAt L κ, lower := lowerOf L κ, x := momX d k L κ / load d k L κ,
    y := momY d k L κ / load d k L κ, force := load d k L κ }

/-- All pushes of the tower after `k` steps, for errors `d`, spread over patch corners. -/
def towerPushes (k : Nat) : List Push :=
  (List.range k).flatMap fun L => towerCorners.flatMap fun κ =>
    if plankAt L κ < k then
      spreadOver ((restPatch ((towerBuild k).shift d) (plankAt L κ) (lowerOf L κ)).getD default)
        (towerPoint d k L κ)
    else []

theorem lowerOf_eq_plank (L : Nat) (κ : Nat × Nat) (i : Nat) :
    lowerOf L κ = .plank i ↔ L ≠ 0 ∧ plankAt (L - 1) κ = i := by
  simp only [lowerOf]; split <;> simp_all

theorem towerPoint_upOn (k L : Nat) (κ : Nat × Nat) (i : Nat) :
    (towerPoint d k L κ).upOn i = (if plankAt L κ = i then load d k L κ else 0)
      - (if L ≠ 0 ∧ plankAt (L - 1) κ = i then load d k L κ else 0) := by
  simp only [Push.upOn, towerPoint, lowerOf_eq_plank]
  by_cases h1 : plankAt L κ = i <;> by_cases h2 : (L ≠ 0 ∧ plankAt (L - 1) κ = i) <;>
    simp only [h1, h2, ite_true, ite_false]

theorem sum_ite_list {α : Type} (c : Prop) [Decidable c] (l : List α) (g : α → Rat) :
    ((if c then l else []).map g).sum = if c then (l.map g).sum else 0 := by
  split <;> simp

theorem tower_allowed (ε : Rat) (hε : ε ≤ 1 / 2) (k : Nat) (hd : SmallShift ε k d) :
    ∀ p ∈ towerPushes d k, p.Allowed ((towerBuild k).shift d) := by
  intro p hp
  simp only [towerPushes, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨L, _, κ, hκ, hp⟩ := hp
  split at hp
  · rename_i hk
    obtain ⟨r, hr, h1, h2, h3, h4⟩ := tower_patch d ε hε k L κ hκ hd hk
    have hF := load_pos d ε hε k L κ hd hk
    have pc := point_in_core d ε hε k L κ hd hk
    rw [hr] at hp
    refine spread_allowed _ r (towerPoint d k L κ) (Rat.le_of_lt hF) (by simpa [towerPoint] using hk) ?_ hr
      (by grind) (by grind) (by simp [towerPoint]; grind) (by simp [towerPoint]; grind)
      (by simp [towerPoint]; grind) (by simp [towerPoint]; grind) p hp
    simp only [towerPoint, lowerOf]
    split
    · trivial
    · show plankAt (L - 1) κ < ((towerBuild k).shift d).length
      have := plankAt_ge L κ; rcases plankAt_bit (L - 1) κ hκ with h | h <;> simp <;> omega
  · simp at hp

/-- At a corner of plank `i`: what goes down there, minus what comes from above, is
plank `i`'s share (and the same with each load times its point). -/
theorem corner_step (ε : Rat) (hε : ε ≤ 1 / 2) (k i : Nat) (hi : i < k) (κ : Nat × Nat)
    (hκ : κ ∈ towerCorners) (hd : SmallShift ε k d) (hκi : plankAt (i / 2) κ = i)
    (c : Rat) (M : Nat → Nat → Rat) (g : Nat → Rat)
    (hM : ∀ L, M k L = fromL k L κ (fun L' => share d L' κ * g L')) :
    load d k (i / 2) κ * (M k (i / 2) / load d k (i / 2) κ - c)
      - (if plankAt (i / 2 + 1) κ < k then
          load d k (i / 2 + 1) κ * (M k (i / 2 + 1) / load d k (i / 2 + 1) κ - c) else 0)
    = share d (i / 2) κ * g (i / 2) - c * share d (i / 2) κ := by
  have hk : plankAt (i / 2) κ < k := by omega
  have F0 := load_pos d ε hε k (i / 2) κ hd hk
  have sF := fromL_succ k (i / 2) κ (fun L' => share d L' κ)
  have sM := fromL_succ k (i / 2) κ (fun L' => share d L' κ * g L')
  simp only [hk, ite_true] at sF sM
  rw [hM, hM]
  simp only [load] at F0 ⊢
  split
  · rename_i h1
    have F1 := load_pos d ε hε k (i / 2 + 1) κ hd h1
    simp only [load] at F1
    have : fromL k (i / 2) κ (fun L' => share d L' κ) ≠ 0 := by grind
    have : fromL k (i / 2 + 1) κ (fun L' => share d L' κ) ≠ 0 := by grind
    grind
  · rename_i h1
    rw [fromL_top k _ κ hκ _ h1] at sF sM
    have : fromL k (i / 2) κ (fun L' => share d L' κ) ≠ 0 := by grind
    grind

theorem tower_balanced (ε : Rat) (hε : ε ≤ 1 / 2) (k : Nat) (hd : SmallShift ε k d) (i : Nat)
    (hi : i < k) : Balanced ((towerBuild k).shift d) (towerPushes d k) i := by
  have hik : i < (towerBuild k).length := by simpa using hi
  -- The planks of level `i / 2` and corner `κ` that exist have a patch with an area.
  have patch : ∀ L κ, κ ∈ towerCorners → plankAt L κ < k → ∃ r,
      (restPatch ((towerBuild k).shift d) (plankAt L κ) (lowerOf L κ)).getD default = r ∧
        r.x0 < r.x1 ∧ r.y0 < r.y1 := fun L κ hκ hk => by
    obtain ⟨r, hr, h1, h2, h3, h4⟩ := tower_patch d ε hε k L κ hκ hd hk
    exact ⟨r, by rw [hr]; rfl, by grind, by grind⟩
  obtain ⟨own1, ownX, ownY⟩ := own_shares d (i / 2) (i % 2) (by omega)
  rw [Nat.div_add_mod] at own1 ownX ownY
  -- Turn the sum over all pushes into the sum of `tower_sum`.
  have reduce : ∀ (h : Push → Rat) (A : Nat → Nat × Nat → Rat),
      (∀ L κ, κ ∈ towerCorners → plankAt L κ < k →
        ((spreadOver ((restPatch ((towerBuild k).shift d) (plankAt L κ) (lowerOf L κ)).getD default)
          (towerPoint d k L κ)).map fun q => q.upOn i * h q).sum
          = (towerPoint d k L κ).upOn i * A L κ) →
      ((towerPushes d k).map fun q => q.upOn i * h q).sum
        = (towerCorners.map fun κ => if plankAt (i / 2) κ = i then
            load d k (i / 2) κ * A (i / 2) κ
              - (if plankAt (i / 2 + 1) κ < k then
                  load d k (i / 2 + 1) κ * A (i / 2 + 1) κ else 0)
            else 0).sum := by
    intro h A hA
    rw [← tower_sum k i hi (load d k) A, towerPushes, sum_flatMap]
    apply sum_map_congr; intro L _
    rw [sum_flatMap]
    apply sum_map_congr; intro κ hκ
    rw [sum_ite_list]
    split
    · rw [hA L κ hκ ‹_›, towerPoint_upOn]
    · rfl
  have cx : (((towerBuild k).shift d).get i).centerX = (towerPlank i).centerX + (d i).1 := by
    rw [shift_get _ d i hik, towerBuild_get k i hi]; simp only [Plank.centerX]; grind
  have cy : (((towerBuild k).shift d).get i).centerY = (towerPlank i).centerY + (d i).2 := by
    rw [shift_get _ d i hik, towerBuild_get k i hi]; simp only [Plank.centerY]; grind
  refine ⟨?_, ?_, ?_⟩
  · -- Net push up is 1.
    have := reduce (fun _ => 1) (fun _ _ => 1) fun L κ hκ hk => by
      simp only [Rat.mul_one]; exact spread_force _ _ i
    simp only [Rat.mul_one] at this
    rw [this, ← own1]
    apply sum_map_congr; intro κ hκ
    split
    · rename_i hκi
      have := corner_step d ε hε k i hi κ hκ hd hκi 0 (fun k L => load d k L κ) (fun _ => 1)
        (fun L => by simp [load])
      have F0 := load_pos d ε hε k (i / 2) κ hd (by omega)
      split
      · rename_i h1
        have F1 := load_pos d ε hε k (i / 2 + 1) κ hd h1
        simp only [h1, ite_true] at this
        have : load d k (i / 2) κ ≠ 0 := by grind
        have : load d k (i / 2 + 1) κ ≠ 0 := by grind
        grind
      · rename_i h1
        simp only [h1, ite_false] at this
        have : load d k (i / 2) κ ≠ 0 := by grind
        grind
    · rfl
  · -- No turning about `y`.
    rw [reduce _ (fun L κ => momX d k L κ / load d k L κ - (((towerBuild k).shift d).get i).centerX)
      fun L κ hκ hk => by
        obtain ⟨r, hr, hx, _⟩ := patch L κ hκ hk
        rw [hr]; exact spread_turnX r _ i _ hx]
    rw [sum_map_congr _ _ (fun κ => if plankAt (i / 2) κ = i then
        share d (i / 2) κ * shareX d (i / 2) κ - (((towerBuild k).shift d).get i).centerX
          * share d (i / 2) κ else 0)]
    · rw [sum_map_congr _ _ (fun κ => (if plankAt (i / 2) κ = i then
          share d (i / 2) κ * shareX d (i / 2) κ else 0)
          - (((towerBuild k).shift d).get i).centerX
            * (if plankAt (i / 2) κ = i then share d (i / 2) κ else 0))
          (fun κ _ => by split <;> grind),
        sum_map_sub, sum_map_mul_left, ownX, own1, cx]
      grind
    · intro κ hκ
      split
      · exact corner_step d ε hε k i hi κ hκ hd ‹_› _ (fun k L => momX d k L κ) (fun L' => shareX d L' κ)
          (fun L => rfl)
      · rfl
  · -- No turning about `x`.
    rw [reduce _ (fun L κ => momY d k L κ / load d k L κ - (((towerBuild k).shift d).get i).centerY)
      fun L κ hκ hk => by
        obtain ⟨r, hr, _, hy⟩ := patch L κ hκ hk
        rw [hr]; exact spread_turnY r _ i _ hy]
    rw [sum_map_congr _ _ (fun κ => if plankAt (i / 2) κ = i then
        share d (i / 2) κ * shareY d (i / 2) κ - (((towerBuild k).shift d).get i).centerY
          * share d (i / 2) κ else 0)]
    · rw [sum_map_congr _ _ (fun κ => (if plankAt (i / 2) κ = i then
          share d (i / 2) κ * shareY d (i / 2) κ else 0)
          - (((towerBuild k).shift d).get i).centerY
            * (if plankAt (i / 2) κ = i then share d (i / 2) κ else 0))
          (fun κ _ => by split <;> grind),
        sum_map_sub, sum_map_mul_left, ownY, own1, cy]
      grind
    · intro κ hκ
      split
      · exact corner_step d ε hε k i hi κ hκ hd ‹_› _ (fun k L => momY d k L κ) (fun L' => shareY d L' κ)
          (fun L => rfl)
      · rfl

/-- After `k` steps, the square tower is solid for placement errors up to `ε ≤ 1/2`. -/
theorem tower_solid (ε : Rat) (hε : ε ≤ 1 / 2) (k : Nat) : SolidWithin ε (towerBuild k) := by
  intro d hd
  simp only [towerBuild_length] at hd
  refine ⟨towerPushes d k, tower_allowed d ε hε k hd, ?_⟩
  intro i hi
  simp only [shift_length, towerBuild_length] at hi
  exact tower_balanced d ε hε k hd i hi

end KaplaPhysics
