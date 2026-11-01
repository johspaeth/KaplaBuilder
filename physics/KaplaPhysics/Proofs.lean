import KaplaPhysics.Engine
import KaplaPhysics.Sums
import KaplaPhysics.RobustProofs
import KaplaPhysics.ColumnProofs
import KaplaPhysics.TowerProofs
import KaplaPhysics.CoreAdapter
import KaplaPhysics.TurnProofs

/-! # Proofs of the physics theorems

The statements are in `specs/KaplaSpecs/Physics.lean`; `lake comparator` checks that the
names and statements here match them exactly. -/

namespace KaplaPhysics

open Solver (Motion allSupports)
open KaplaCore (Pose)

/-! ## Planks are Core's blocks (property 7) -/

/-- A point that Core counts as inside a block is under the plank seen from above (edges
included) and between its bottom and its top. -/
theorem covers_of_contains (p : Plank) (q : KaplaCore.Q3) (h : p.contains q = true) :
    p.Covers q.x q.y ∧ p.bottom ≤ q.z ∧ q.z < p.top := by
  simp only [KaplaCore.Pose.contains, Bool.and_eq_true, KaplaCore.Q3.sub] at h
  obtain ⟨⟨hx, hy⟩, hz⟩ := h
  simp only [Pose.Covers, Pose.alongLength, Pose.alongWidth, Pose.size, Pose.bottom, Pose.top]
  split at hx <;> split at hy <;> simp only [Bool.and_eq_true] at hx hy hz <;>
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> grind

/-- A point strictly inside the plank seen from above and strictly between its bottom and
its top is inside the block for Core. -/
theorem contains_of_inside (p : Plank) (q : KaplaCore.Q3) (hxy : p.CoversInside q.x q.y)
    (hb : p.bottom < q.z) (ht : q.z < p.top) : p.contains q = true := by
  simp only [Pose.CoversInside, Pose.alongLength, Pose.alongWidth, Pose.size] at hxy
  simp only [Pose.bottom, Pose.top, Pose.size] at hb ht
  simp only [KaplaCore.Pose.contains, Bool.and_eq_true, KaplaCore.Q3.sub]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> (try split) <;> simp only [Bool.and_eq_true] <;>
    refine ⟨?_, ?_⟩ <;> grind

/-! ## "Stable" answers are right -/

theorem pushCheck_sound (b : Build) (p : Push) (h : pushCheck b p = true) : p.Allowed b := by
  simp only [pushCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, restsCheck_sound b _ _ h4, h5⟩

/-- If the push check passes, the build is stable (S2). -/
theorem checkPushes_sound (b : Build) (ps : List Push) (h : checkPushes b ps = true) :
    Stable b := by
  simp only [checkPushes, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨ps, fun p hp => pushCheck_sound b p (h.1 p hp), h.2⟩

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
  obtain ⟨_, hup, hlow, _, _⟩ := hp
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

theorem riseForm_eval (b : Build) (ms : List Motion) (s : Support) (x y : Rat) :
    (riseForm b ms s).eval x y = rise b ms s x y := by
  cases s <;> simp only [riseForm, rise, Aff.eval] <;> grind

theorem sub_eval (f g : Aff) (x y : Rat) : (f.sub g).eval x y = f.eval x y - g.eval x y := by
  simp only [Aff.sub, Aff.eval]; grind

theorem nonnegCheck_sound (gs : List Aff) (f : Aff) (h : nonnegCheck gs f = true) (x y : Rat)
    (hnn : ∀ g ∈ gs, 0 ≤ g.eval x y) : 0 ≤ f.eval x y := by
  simp only [nonnegCheck, List.any_eq_true, nonnegOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨C, -, ⟨⟨hU, ha⟩, hb⟩, hc⟩ := h
  exact Cert.nonneg_on C gs f hU ha hb hc x y hnn

/-- Where the check passes, plank `i` rises at least as much as its support `s` at every
point of the patch. -/
theorem noPushCheck_sound (b : Build) (ms : List Motion) (i : Nat) (s : Support)
    (h : noPushCheck b ms i s = true) (hr : RestsOn b i s) (x y : Rat)
    (hin : InPatch b i s x y) : rise b ms s x y ≤ rise b ms (.plank i) x y := by
  simp only [noPushCheck, Bool.or_eq_true] at h
  rcases h with h | h
  · exact absurd hr (notRestsCheck_sound b i s h)
  · have := nonnegCheck_sound _ _ h x y ((inPatch_iff b i s x y).mp hin)
    rw [sub_eval, riseForm_eval, riseForm_eval] at this
    grind

/-- Under a fall certificate, every allowed push does work at least zero. -/
theorem push_work_nonneg (b : Build) (ms : List Motion) (hc : checkFall b ms = true)
    (p : Push) (hp : p.Allowed b) :
    0 ≤ p.force * (rise b ms (.plank p.upper) p.x p.y - rise b ms p.lower p.x p.y) := by
  obtain ⟨hf, hup, hlow, hrest, hin⟩ := hp
  have hs : p.lower ∈ allSupports b.length := by
    cases hl : p.lower with
    | ground => simp [allSupports]
    | plank j => rw [hl] at hlow; simp [allSupports, Support.InBuild] at hlow ⊢; exact hlow
  simp only [checkFall, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  have := noPushCheck_sound b ms p.upper p.lower (hc.1 p.upper hup p.lower hs) hrest p.x p.y hin
  exact Rat.mul_nonneg hf (by grind)

/-- A motion that passes `checkFall` shows that the build is not stable (S3). -/
theorem fallCertificate_sound (b : Build) (ms : List Motion) (hc : checkFall b ms = true) :
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
  -- ... which is at least zero, but the check says it is below zero.
  have := sum_map_nonneg ps _ fun p hp => push_work_nonneg b ms hc p (hallowed p hp)
  simp only [checkFall, Bool.and_eq_true, decide_eq_true_eq] at hc
  have := hc.2
  grind

/-- Property 2: when the engine answers "falls", the build is not stable (S3). -/
theorem globalAnswer_falls_sound (b : Build) (h : globalAnswer b = .falls) :
    ¬ Stable b := by
  unfold globalAnswer at h
  split at h
  · split at h <;> cases h
  · split at h
    · exact fallCertificate_sound b _ (by assumption)
    · cases h
  · cases h

theorem fallAboveAnswer_falls_sound (b : Build) (i : Nat) (h : fallAboveAnswer b i = .falls) :
    ¬ Stable b := by
  unfold fallAboveAnswer at h
  split at h
  · split at h
    · exact fallCertificate_sound b _ (by assumption)
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
    (h1 : checkPushes b ps = true) (h2 : checkFall b ms = true) : False :=
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

/-- Two planks that pass `clearPairCheck` and do not meet do not share inside space after
moves of at most `ε` along `x` and `y`. -/
theorem clearPair_moved (ε : Rat) (p q : Plank) (hc : clearPairCheck ε p q = true)
    (hm : ¬ Meets p q) (a b c e : Rat)
    (ha : -ε ≤ a ∧ a ≤ ε) (hb : -ε ≤ b ∧ b ≤ ε) (hc' : -ε ≤ c ∧ c ≤ ε) (he : -ε ≤ e ∧ e ≤ ε) :
    ¬ Overlap (p.moveBy a b 0) (q.moveBy c e 0) := by
  simp only [clearPairCheck, Bool.or_eq_true] at hc
  rcases hc with (hc | hc) | hc
  · exact absurd (meetsCheck_sound p q hc) hm
  · rintro ⟨hz, -⟩
    simp only [heightsApart, Bool.or_eq_true, decide_eq_true_eq] at hc
    rw [moveBy_bottom, moveBy_top, moveBy_bottom, moveBy_top] at hz
    grind
  · obtain ⟨s, hf, hv⟩ := sepCheck_sound ε p q hc
    exact fun ho => s.no_share_within p q hf ε hv a b c e ha hb hc' he ho.2

/-- A build that passes the clearance check keeps its gaps for every placement error up
to `ε`. -/
theorem keepsGaps_of_clear (ε : Rat) (b : Build) (hc : clearCheck ε b = true) :
    KeepsGaps ε b := by
  intro d hd i hi j hj hm
  have hij : i ≠ j := by rintro rfl; exact hm (meets_self _)
  simp only [clearCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hc
  have hp := (hc i hi j hj).resolve_left hij
  rw [shift_get b d i hi, shift_get b d j hj]
  have hi' := hd i hi
  have hj' := hd j hj
  exact clearPair_moved ε _ _ hp hm _ _ _ _
    ⟨hi'.1, hi'.2.1⟩ ⟨hi'.2.2.1, hi'.2.2.2⟩ ⟨hj'.1, hj'.2.1⟩ ⟨hj'.2.2.1, hj'.2.2.2⟩

/-- Property 4: an accepted plan uses at most `maxPlanks` planks, and after every step the
build so far is well-formed, keeps its gaps with placement errors up to `ε` (when
`opts.clearance` is on), and is solid for those errors (K4, K5). -/
theorem checkPlan_sound (opts : PlanOptions) (ε : Rat) (maxPlanks : Nat) (steps : Build)
    (h : checkPlan opts ε maxPlanks steps = true) : SafePlan opts ε maxPlanks steps := by
  simp only [checkPlan, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  refine ⟨h.1, fun k hk1 hk2 => ?_⟩
  obtain ⟨⟨hw, hc⟩, hs⟩ := h.2 (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at hw hc hs
  have hs := solidAnswer_sound ε _ hs
  refine ⟨wellFormedCheck_sound _ hw, fun ho => ?_, hs⟩
  rcases hc with hc | hc
  · rw [hc] at ho; cases ho
  · exact keepsGaps_of_clear ε _ hc

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

/-- Property 9: building the square tower level by level is a safe plan, at any height
`n`: after every step it is well-formed, keeps its gaps with placement errors up to `ε`,
and is solid for those errors, for any `ε` from 0 to 1/2 (3.9 mm; the default is 2 mm).
This holds with the clearance check on or off. -/
theorem squareTower_safe (opts : PlanOptions) (ε : Rat) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (n : Nat) : SafePlan opts ε (2 * n) (squareTower n) := by
  have hlen : (squareTower n).length = 2 * n := by simp [squareTower]
  refine ⟨by omega, fun k _ hk => ?_⟩
  rw [squareTower_take n k (by omega)]
  exact ⟨tower_wellFormed k, fun _ => tower_keepsGaps ε hε k, tower_solid ε hε0 hε k⟩

/-- Property 9 for a turned tower: the square tower turned as a whole by an allowed turn
`r` (for example about 45°) is a safe plan, for placement errors up to `ε` with
`ε * (|cos| + |sin|) ≤ 1/2`. -/
theorem turnedTower_safe (opts : PlanOptions) (r : KaplaCore.Rot) (hr : r.Allowed) (ε : Rat)
    (hε0 : 0 ≤ ε) (hε : ε * (max r.cos (-r.cos) + max r.sin (-r.sin)) ≤ 1 / 2) (n : Nat) :
    SafePlan opts ε (2 * n) (turnedTower r n) := by
  have hs : 0 ≤ spread r := by simp only [spread]; grind
  have hsafe := squareTower_safe opts (ε * spread r) (Rat.mul_nonneg hε0 hs) hε n
  refine safePlan_turn r hr.1 opts ε (ε * spread r) hε0 (Rat.le_refl) _ _ ?_ hsafe
  intro i hi
  have hlen : (squareTower n).length = 2 * n := by simp [squareTower]
  rw [show (squareTower n).get i = towerPlank i by
    simp [squareTower, Build.get, List.getD_eq_getElem?_getD, show i < 2 * n by omega]]
  rcases towerPlank_cases i with ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;>
    rw [e] <;> simp only [Plank.at, AxisPose.rot]
  · exact allowed_comp_id r hr
  · exact allowed_comp_id r hr
  · exact allowed_comp_quarter r hr
  · exact allowed_comp_quarter r hr

/-! ## Reaching the spot (property 5, K3) -/

theorem dropMisses_sound (p q : Plank) (h : Rat) (hm : dropMisses p h q = true) (s : Rat)
    (hs0 : 0 ≤ s) (hsh : s ≤ h) : ¬ Overlap (p.moveBy 0 0 s) q := by
  rintro ⟨hz, ha⟩
  rw [moveBy_bottom, moveBy_top] at hz
  simp only [dropMisses, Bool.or_eq_true, decide_eq_true_eq] at hm
  rcases hm with (hm | hm) | hm
  · obtain ⟨c, hf, hv⟩ := sepCheck_sound 0 p q hm
    have := c.no_share_moved p q hf 0 0 s 0 0 0 (by grind)
    rw [moveBy_zero] at this
    exact this ha
  · grind
  · grind

theorem rayMisses_sound (d : Dir) (p q : Plank) (h : Rat) (hm : rayMisses d p h q = true)
    (t : Rat) (ht : 0 ≤ t) :
    ¬ Overlap (p.moveBy (t * d.vec.1) (t * d.vec.2.1) (h + t * d.vec.2.2)) q := by
  rintro ⟨hz, ha⟩
  rw [moveBy_bottom, moveBy_top] at hz
  cases d with
  | fromAbove =>
    simp only [Dir.vec] at hz ha
    simp only [rayMisses, Bool.or_eq_true, decide_eq_true_eq] at hm
    rcases hm with hm | hm
    · obtain ⟨c, hf, hv⟩ := sepCheck_sound 0 p q hm
      have := c.no_share_moved p q hf (t * 0) (t * 0) (h + t * 1) 0 0 0 (by grind)
      rw [moveBy_zero] at this
      exact this ha
    · grind
  | side vx vy =>
    simp only [Dir.vec] at hz ha
    simp only [rayMisses, Bool.or_eq_true, decide_eq_true_eq] at hm
    rcases hm with (hm | hm) | hm
    · grind
    · grind
    · simp only [slideCheck, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨c, -, ⟨hf, hv⟩, hdir⟩ := hm
      have hpos := Rat.mul_nonneg ht hdir
      have := c.no_share_moved p q hf (t * vx) (t * vy) (h + t * 0) 0 0 0 (by grind)
      rw [moveBy_zero] at this
      exact this ha

/-- Property 5 ("reachable" is right): a direction the checker accepts gives a straight
path and a drop that share no inside space with a placed plank (K3; touching is allowed). -/
theorem reachDir_sound (placed : Build) (p : Plank) (h : Rat) (d : Dir)
    (hd : reachDir? placed p h = some d) : StraightPath placed p h d.vec := by
  unfold reachDir? at hd
  split at hd
  case isFalse => cases hd
  rename_i hh
  have hm := List.find?_some hd
  simp only [Bool.and_eq_true, List.all_eq_true] at hm
  obtain ⟨hok, hall⟩ := hm
  refine ⟨hh, ?_, ?_, ?_, ?_⟩
  · cases d with
    | fromAbove => simp [Dir.vec]
    | side vx vy =>
      simp only [Dir.ok, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hok
      simp only [Dir.vec, ne_eq, Prod.mk.injEq, and_true]
      grind
  · cases d <;> simp only [Dir.vec] <;> decide +kernel
  · intro t ht q hq; exact rayMisses_sound d p q h (hall q hq).2 t ht
  · intro s hs0 hsh q hq; exact dropMisses_sound p q h (hall q hq).1 s hs0 hsh

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

/-- When the engine says a core plan is `ok`: every step places 1 to `hands` blocks, and
the blocks, one per step, are a safe plan (K4, K5). -/
theorem coreCheck_ok_sound (opts : PlanOptions) (h : KaplaCore.HumanModel) (maxBlocks : Nat)
    (plan : KaplaCore.BuildPlan) (hok : (coreCheck opts h maxBlocks plan).ok = true) :
    (∀ st ∈ plan.steps, 1 ≤ st.blocks.length ∧ st.blocks.length ≤ h.hands) ∧
      SafePlan opts h.epsRel maxBlocks plan.blocks := by
  simp only [coreCheck, Bool.and_eq_true] at hok
  exact ⟨stepDiagnostics_nil h plan hok.1, checkPlan_sound _ _ _ _ hok.2⟩

end KaplaPhysics
