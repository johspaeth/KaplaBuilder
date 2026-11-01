import KaplaPhysics.Engine
import KaplaPhysics.Sums
import KaplaPhysics.RobustProofs
import KaplaPhysics.ColumnProofs
import KaplaPhysics.TowerProofs
import KaplaPhysics.CoreAdapter

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

theorem fallAboveAnswer_ne_stable (b : Build) (i : Nat) : fallAboveAnswer b i ≠ .stable := by
  unfold fallAboveAnswer; split
  · split <;> simp
  · simp

theorem fallbackAnswer_stable_sound (b : Build) (i : Nat) (h : fallbackAnswer b i = .stable) :
    Stable b := by
  unfold fallbackAnswer at h
  split at h
  · exact globalAnswer_stable_sound b h
  · exact absurd h (fallAboveAnswer_ne_stable b i)

theorem stabilityAnswer_stable_sound (b : Build) (h : stabilityAnswer b = .stable) :
    Stable b := by
  unfold stabilityAnswer at h
  split at h
  · split at h
    · exact checkPushes_sound b _ (by assumption)
    · exact fallbackAnswer_stable_sound b 0 h
  · exact fallbackAnswer_stable_sound b _ h

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

theorem fallAboveAnswer_falls_sound (b : Build) (i : Nat) (h : fallAboveAnswer b i = .falls) :
    ¬ Stable b := by
  unfold fallAboveAnswer at h
  split at h
  · split at h
    · exact fallCertificate_sound b _ (of_decide_eq_true (by assumption))
    · cases h
  · cases h

theorem fallbackAnswer_falls_sound (b : Build) (i : Nat) (h : fallbackAnswer b i = .falls) :
    ¬ Stable b := by
  unfold fallbackAnswer at h
  split at h
  · exact globalAnswer_falls_sound b h
  · exact fallAboveAnswer_falls_sound b i h

theorem stabilityAnswer_falls_sound (b : Build) (h : stabilityAnswer b = .falls) :
    ¬ Stable b := by
  unfold stabilityAnswer at h
  split at h
  · split at h
    · cases h
    · exact fallbackAnswer_falls_sound b 0 h
  · exact fallbackAnswer_falls_sound b _ h

/-- No build gets both answers: a push set that passes the check and a fall certificate
cannot exist for the same build. -/
theorem not_stands_and_falls (b : Build) (ps : List Push) (ms : List Motion)
    (h1 : checkPushes b ps = true) (h2 : FallCertificate b ms) : False :=
  fallCertificate_sound b ms h2 (checkPushes_sound b ps h1)

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
  rcases h.2 with h | ⟨_, h⟩ <;> exact passes_sound ε b _ h

/-- Property 3: when the engine's verdict is "solid", the build is stable for every
combination of placement errors up to `ε` (R3). -/
theorem verdict_solid_sound (ε : Rat) (b : Build) (h : verdict ε b = .solid) :
    SolidWithin ε b := by
  unfold verdict at h
  split at h
  · exact solidAnswer_sound ε b (by assumption)
  · split at h <;> cases h

/-- A "solid" verdict is only given for an error `ε` not below zero, and the build then
stands at the exact positions too. -/
theorem verdict_solid_stable (ε : Rat) (b : Build) (h : verdict ε b = .solid) :
    0 ≤ ε ∧ Stable b :=
  ⟨(verdict_solid_sound ε b h).1, solid_stable ε b (verdict_solid_sound ε b h)⟩

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

/-- Two planks that are clear of each other (`ClearPair`) and do not meet do not overlap
after moves of at most `ε` along `x` and `y`. -/
theorem clearPair_moved (ε : Rat) (p q : Plank) (hc : ClearPair ε p q) (hm : ¬ Meets p q)
    (a b c e : Rat)
    (ha : -ε ≤ a ∧ a ≤ ε) (hb : -ε ≤ b ∧ b ≤ ε) (hc' : -ε ≤ c ∧ c ≤ ε) (he : -ε ≤ e ∧ e ≤ ε) :
    ¬ Overlap { p with x := p.x + a, y := p.y + b } { q with x := q.x + c, y := q.y + e } := by
  rcases hc with hc | hc
  · exact absurd hc hm
  simp only [Plank.x1, Plank.y1, Plank.top] at hc
  simp only [Overlap, Plank.x1, Plank.y1, Plank.top]
  grind

/-- Every plank meets itself. -/
theorem meets_self (p : Plank) : Meets p p := by
  obtain ⟨pose, x, y, z⟩ := p
  cases pose <;> simp only [Meets, Plank.x1, Plank.y1, Plank.top, Pose.size] <;> grind

/-- A build that passes the clearance check (`Clear`) keeps its gaps for every placement
error up to `ε`. -/
theorem keepsGaps_of_clear (ε : Rat) (b : Build) (hc : Clear ε b) : KeepsGaps ε b := by
  intro d hd i hi j hj hm
  have hij : i ≠ j := by rintro rfl; exact hm (meets_self _)
  rw [shift_get b d i hi, shift_get b d j hj]
  have hi' := hd i hi
  have hj' := hd j hj
  exact clearPair_moved ε _ _ (hc i hi j hj hij) hm _ _ _ _
    ⟨hi'.1, hi'.2.1⟩ ⟨hi'.2.2.1, hi'.2.2.2⟩ ⟨hj'.1, hj'.2.1⟩ ⟨hj'.2.2.1, hj'.2.2.2⟩

/-- Property 4: an accepted plan uses at most `maxPlanks` planks, and after every step the
build so far is well-formed, keeps its gaps with placement errors up to `ε` and puts no
plank into a tight slot (when `opts.clearance` is on), and is solid for those errors
(K4, K5, H6). -/
theorem checkPlan_sound (opts : PlanOptions) (ε : Rat) (maxPlanks : Nat) (steps : Build)
    (h : checkPlan opts ε maxPlanks steps = true) : SafePlan opts ε maxPlanks steps := by
  simp only [checkPlan, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  refine ⟨h.1, fun k hk1 hk2 => ?_⟩
  obtain ⟨⟨hw, hc⟩, hs⟩ := h.2 (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at hw hc hs
  have hs := solidAnswer_sound ε _ hs
  refine ⟨hw, fun ho => ?_, hs⟩
  rcases hc with hc | ⟨hc, hslot⟩
  · rw [hc] at ho; cases ho
  · exact ⟨keepsGaps_of_clear ε _ hc, of_decide_eq_false hslot⟩

/-! ## The simple rule for a column (property 6) -/

/-- Property 6: for a single column of planks, "stable" (S2) means exactly the simple
rule: at every level, the combined centre of mass of everything from that level up is over
the patch below that level. -/
theorem column_stable_iff (b : Build) (hc : IsColumn b) : Stable b ↔ ColumnRule b :=
  ⟨stable_columnRule b hc, columnRule_stable b⟩

/-! ## Friction cannot hurt (property 8, F3) -/

theorem upOn_eq_side (i : Nat) (p : Push) : p.upOn i = p.side i * p.force := by
  simp only [Push.upOn, Push.side]; split <;> split <;> grind

/-- Property 8: a build that is stable without friction is stable with friction
coefficient `μ ≥ 0`: use the same pushes with no sideways part. -/
theorem stable_withFriction (μ : Rat) (hμ : 0 ≤ μ) (b : Build) (h : Stable b) :
    StableWithFriction μ b := by
  obtain ⟨ps, hall, hbal⟩ := h
  refine ⟨ps.map fun p => ⟨p, 0, 0⟩, ?_, ?_⟩
  · intro q hq
    simp only [List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hf := (hall p hp).1
    have := Rat.mul_nonneg hμ hf
    exact ⟨hall p hp, by grind, by grind, by grind, by grind⟩
  · intro i hi
    obtain ⟨h1, h2, h3⟩ := hbal i hi
    simp only [BalancedWithFriction, List.map_map, Function.comp_def]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← h1]; apply sum_map_congr; intro p _; rw [upOn_eq_side]
    · rw [sum_map_congr _ _ (fun _ => 0) (fun _ _ => by grind), sum_map_zero]
    · rw [sum_map_congr _ _ (fun _ => 0) (fun _ _ => by grind), sum_map_zero]
    · rw [← h3]; apply sum_map_congr; intro p _; rw [upOn_eq_side]; grind
    · rw [sum_map_congr _ _ (fun p => -(p.upOn i * (p.x - (b.get i).centerX)))
        (fun p _ => by rw [upOn_eq_side]; grind), sum_map_neg, h2]; grind
    · rw [sum_map_congr _ _ (fun _ => 0) (fun _ _ => by grind), sum_map_zero]

/-! ## Square towers, at any height (property 9) -/

/-- Two planks of the square tower are clear of each other for errors up to `ε ≤ 1/2`:
planks on different levels share no height, and the two planks of one level are 9 apart. -/
theorem tower_clearPair (ε : Rat) (hε : ε ≤ 1 / 2) (i j : Nat) (hij : i ≠ j) :
    ClearPair ε (towerPlank i) (towerPlank j) := by
  refine Or.inr ?_
  by_cases hl : i / 2 = j / 2
  · -- Same level: the two planks are on opposite sides, 9 apart.
    have hp : i % 2 ≠ j % 2 := by omega
    right
    rcases towerPlank_cases i with ⟨a1, a2, ei⟩ | ⟨a1, a2, ei⟩ | ⟨a1, a2, ei⟩ | ⟨a1, a2, ei⟩ <;>
    rcases towerPlank_cases j with ⟨b1, b2, ej⟩ | ⟨b1, b2, ej⟩ | ⟨b1, b2, ej⟩ | ⟨b1, b2, ej⟩ <;>
    (try omega) <;>
    · rw [ei, ej]
      simp only [Plank.x1, Plank.y1, Pose.size]
      grind
  · -- Different levels: one is at least a full thickness above the other.
    have hc : ((i / 2 : Nat) : Rat) + 1 ≤ ((j / 2 : Nat) : Rat) ∨
        ((j / 2 : Nat) : Rat) + 1 ≤ ((i / 2 : Nat) : Rat) := by
      rcases Nat.lt_or_gt_of_ne hl with h' | h'
      · left; exact_mod_cast h'
      · right; exact_mod_cast h'
    left
    rcases towerPlank_cases i with ⟨_, _, ei⟩ | ⟨_, _, ei⟩ | ⟨_, _, ei⟩ | ⟨_, _, ei⟩ <;>
    rcases towerPlank_cases j with ⟨_, _, ej⟩ | ⟨_, _, ej⟩ | ⟨_, _, ej⟩ | ⟨_, _, ej⟩ <;>
    · rw [ei, ej]
      simp only [Plank.top, Pose.size]
      grind

/-- Two different planks of the square tower never touch side by side: planks on different
levels share no height, and the two planks of one level are 9 apart. -/
theorem tower_noSideTouch (i j : Nat) (hij : i ≠ j) :
    (FacingAlongX (towerPlank i) (towerPlank j) →
      (towerPlank j).x1 ≠ (towerPlank i).x ∧ (towerPlank i).x1 ≠ (towerPlank j).x) ∧
    (FacingAlongY (towerPlank i) (towerPlank j) →
      (towerPlank j).y1 ≠ (towerPlank i).y ∧ (towerPlank i).y1 ≠ (towerPlank j).y) := by
  by_cases hl : i / 2 = j / 2
  · have hp : i % 2 ≠ j % 2 := by omega
    rcases towerPlank_cases i with ⟨a1, a2, ei⟩ | ⟨a1, a2, ei⟩ | ⟨a1, a2, ei⟩ | ⟨a1, a2, ei⟩ <;>
    rcases towerPlank_cases j with ⟨b1, b2, ej⟩ | ⟨b1, b2, ej⟩ | ⟨b1, b2, ej⟩ | ⟨b1, b2, ej⟩ <;>
    (try omega) <;>
    · rw [ei, ej]
      simp only [FacingAlongX, FacingAlongY, Plank.x1, Plank.y1, Plank.top, Pose.size]
      grind
  · have hc : ((i / 2 : Nat) : Rat) + 1 ≤ ((j / 2 : Nat) : Rat) ∨
        ((j / 2 : Nat) : Rat) + 1 ≤ ((i / 2 : Nat) : Rat) := by
      rcases Nat.lt_or_gt_of_ne hl with h' | h'
      · left; exact_mod_cast h'
      · right; exact_mod_cast h'
    rcases towerPlank_cases i with ⟨_, _, ei⟩ | ⟨_, _, ei⟩ | ⟨_, _, ei⟩ | ⟨_, _, ei⟩ <;>
    rcases towerPlank_cases j with ⟨_, _, ej⟩ | ⟨_, _, ej⟩ | ⟨_, _, ej⟩ | ⟨_, _, ej⟩ <;>
    · rw [ei, ej]
      simp only [FacingAlongX, FacingAlongY, Plank.top, Pose.size]
      grind

/-- No plank of the square tower goes into a tight slot. -/
theorem tower_noTightSlot (m : Nat) : ¬ InTightSlot (towerBuild m) (towerPlank m) := by
  rintro (⟨a, ha, c, -, h1, -, h3, -⟩ | ⟨a, ha, c, -, h1, -, h3, -⟩) <;>
  · simp only [towerBuild, List.mem_map, List.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    first
      | exact ((tower_noSideTouch m i (by omega)).1 h3).1 h1
      | exact ((tower_noSideTouch m i (by omega)).2 h3).1 h1

theorem squareTower_get (n m : Nat) (h : m < 2 * n) : (squareTower n).get m = towerPlank m := by
  simp [squareTower, Build.get, List.getD_eq_getElem?_getD, h]

/-- The square tower passes the clearance check for errors up to `ε ≤ 1/2`. -/
theorem tower_clear (ε : Rat) (hε : ε ≤ 1 / 2) (k : Nat) : Clear ε (towerBuild k) := by
  intro i hi j hj hij
  simp only [towerBuild_length] at hi hj
  rw [towerBuild_get k i hi, towerBuild_get k j hj]
  exact tower_clearPair ε hε i j hij

/-- Property 9: building the square tower level by level is a safe plan, at any height
`n`: after every step it is well-formed, keeps its gaps with placement errors up to `ε`,
and is solid for those errors, for any `ε` from 0 to 1/2 (3.9 mm; this is also the default).
This holds with the clearance check on or off. -/
theorem squareTower_safe (opts : PlanOptions) (ε : Rat) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (n : Nat) : SafePlan opts ε (2 * n) (squareTower n) := by
  have hlen : (squareTower n).length = 2 * n := by simp [squareTower]
  refine ⟨by omega, fun k _ hk => ?_⟩
  rw [squareTower_take n k (by omega)]
  have hs := tower_solid ε hε0 hε k
  refine ⟨tower_wellFormed k, fun _ => ⟨keepsGaps_of_clear ε _ (tower_clear ε hε k), ?_⟩, hs⟩
  rw [squareTower_take n (k - 1) (by omega), squareTower_get n (k - 1) (by omega)]
  exact tower_noTightSlot (k - 1)

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
path and a drop that share no inside space with a placed plank (K3; touching is allowed). -/
theorem reachDir_sound (placed : Build) (p : Plank) (h : Rat) (d : Dir)
    (hd : reachDir? placed p h = some d) : StraightPath placed p h d.vec := by
  unfold reachDir? at hd
  split at hd
  case isFalse => cases hd
  rename_i hh
  have hm := List.find?_some hd
  simp only [decide_eq_true_eq] at hm
  refine ⟨hh, by cases d <;> decide, by cases d <;> decide +kernel, ?_, ?_⟩
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

/-! ## The engine behind KaplaCore's interface -/

/-- For a block with a physics pose, core's box and the plank's box are the same, so the
plank is the same block in the same place. -/
theorem plankOf_box (p : KaplaCore.Pose) (q : Plank) (h : plankOf p = some q) :
    p.box = q.toBox := by
  obtain ⟨up, r, ⟨cx, cy, cz⟩⟩ := p
  have h1 : Rat.abs 1 = 1 := by decide +kernel
  have hm1 : Rat.abs (-1) = 1 := by decide +kernel
  have h0 : Rat.abs 0 = 0 := by decide +kernel
  simp only [plankOf, poseOf, isStraightTurn, isQuarterTurn] at h
  split at h
  · rename_i hr
    rcases hr with rfl | rfl <;> cases up <;> simp at h <;> subst h <;>
    simp [KaplaCore.Pose.box, Plank.toBox, KaplaCore.Upright.dims, Plank.x1, Plank.y1, Plank.top,
      Pose.size, KaplaCore.Q3.sub, KaplaCore.Q3.add, KaplaCore.blockLength, KaplaCore.blockWidth,
      KaplaCore.blockThickness, h1, hm1, h0] <;> grind
  · split at h
    · rename_i _ hr
      rcases hr with rfl | rfl <;> cases up <;> simp at h <;> subst h <;>
      simp [KaplaCore.Pose.box, Plank.toBox, KaplaCore.Upright.dims, Plank.x1, Plank.y1, Plank.top,
        Pose.size, KaplaCore.Q3.sub, KaplaCore.Q3.add, KaplaCore.blockLength, KaplaCore.blockWidth,
        KaplaCore.blockThickness, h1, hm1, h0] <;> grind
    · simp at h

/-- No step diagnostics means every step places 1 to `hands` blocks. -/
theorem stepDiagnostics_nil (h : KaplaCore.HumanModel) (plan : KaplaCore.BuildPlan)
    (hs : (stepDiagnostics h plan).isEmpty = true) :
    ∀ st ∈ plan.steps, 1 ≤ st.blocks.length ∧ st.blocks.length ≤ h.hands := by
  intro st hst
  obtain ⟨k, hk⟩ : ∃ k, (st, k) ∈ plan.steps.zipIdx := by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hst
    exact ⟨k, List.mem_iff_getElem.mpr ⟨k, by simp [hk], by simp⟩⟩
  simp only [stepDiagnostics, List.isEmpty_iff, List.flatMap_eq_nil_iff] at hs
  have := hs _ hk
  simp only [List.append_eq_nil_iff] at this
  obtain ⟨h1, h2⟩ := this
  constructor
  · cases hb : st.blocks with
    | nil => simp [hb] at h1
    | cons _ _ => simp
  · split at h2
    · simp at h2
    · omega

/-- When the engine says a core plan is `ok`: every step places 1 to `hands` blocks, every
block has a physics pose, and the blocks, one per step, are a safe plan (K4, K5). -/
theorem coreCheck_ok_sound (opts : PlanOptions) (h : KaplaCore.HumanModel) (maxBlocks : Nat)
    (plan : KaplaCore.BuildPlan) (hok : (coreCheck opts h maxBlocks plan).ok = true) :
    (∀ st ∈ plan.steps, 1 ≤ st.blocks.length ∧ st.blocks.length ≤ h.hands) ∧
      ∃ b, buildOf plan.blocks = some b ∧ SafePlan opts h.epsRel maxBlocks b := by
  unfold coreCheck at hok
  split at hok
  · simp at hok
  · rename_i b hb
    simp only [Bool.and_eq_true] at hok
    exact ⟨stepDiagnostics_nil h plan hok.1, b, hb, checkPlan_sound _ _ _ _ hok.2⟩

end KaplaPhysics
