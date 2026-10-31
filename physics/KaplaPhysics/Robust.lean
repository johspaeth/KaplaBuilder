import KaplaPhysics.FastCheck

/-!
# KaplaPhysics.Robust — robustness to placement error (H1, H2), proven sound

**Idea (DESIGN §2.2).** Take the nominal contact forces. In the misplaced structure every
force moves with the block *above* it, and then all forces under block `j` shift together
by a vector `s_j`. The shift is forced by `j`'s moment balance: the blocks resting on `j` are
misaligned against it, which moves their loads; `s_j` is the load-weighted average of those
moves. The certificate bounds `|s_j| ≤ σ_j` (the *shift budget*), and every force point keeps
a margin of at least `κ·(r + σ)` to the edges of both faces it acts on, where `r` bounds the
misalignment of the two blocks. Then the moved forces are again admissible — so every
admissible misplacement stands.

All bounds are in the max-norm on the plane; `κ_b = |cos| + |sin|` converts it to the
block's own axes. Everything is exact rational arithmetic.
-/

namespace Kapla.Physics

open Kapla

/-! ## Max-norm facts -/

theorem ninf_nonneg (v : Q2) : 0 ≤ ninf v := le_max_of_le_left (abs_nonneg _)

theorem abs_x_le (v : Q2) : |v.x| ≤ ninf v := le_max_left _ _
theorem abs_y_le (v : Q2) : |v.y| ≤ ninf v := le_max_right _ _

theorem ninf_le {v : Q2} {b : Q} (hx : |v.x| ≤ b) (hy : |v.y| ≤ b) : ninf v ≤ b := max_le hx hy

theorem ninf_tri (a b c : Q2) : ninf (Q2.sub a c) ≤ ninf (Q2.sub a b) + ninf (Q2.sub b c) := by
  apply ninf_le
  · have := abs_add_le (a.x - b.x) (b.x - c.x)
    simp only [Q2.sub] at *
    have h1 := abs_x_le (Q2.sub a b); have h2 := abs_x_le (Q2.sub b c)
    simp only [Q2.sub] at h1 h2
    calc |a.x - c.x| = |(a.x - b.x) + (b.x - c.x)| := by ring_nf
      _ ≤ _ := this
      _ ≤ _ := add_le_add h1 h2
  · have := abs_add_le (a.y - b.y) (b.y - c.y)
    simp only [Q2.sub] at *
    have h1 := abs_y_le (Q2.sub a b); have h2 := abs_y_le (Q2.sub b c)
    simp only [Q2.sub] at h1 h2
    calc |a.y - c.y| = |(a.y - b.y) + (b.y - c.y)| := by ring_nf
      _ ≤ _ := this
      _ ≤ _ := add_le_add h1 h2

theorem ninf_symm (a b : Q2) : ninf (Q2.sub a b) = ninf (Q2.sub b a) := by
  simp only [ninf, Q2.sub, abs_sub_comm]

theorem ninf_sub_le (a b : Q2) : ninf (Q2.sub a b) ≤ ninf a + ninf b := by
  apply ninf_le
  · simp only [Q2.sub]
    exact (abs_sub _ _).trans (add_le_add (abs_x_le a) (abs_x_le b))
  · simp only [Q2.sub]
    exact (abs_sub _ _).trans (add_le_add (abs_y_le a) (abs_y_le b))

/-! ## Shifting a block -/

/-- Converts the max-norm to the block's horizontal axes. -/
def kappa (b : Pose) : Q := |b.rot.c| + |b.rot.s|

theorem kappa_nonneg (b : Pose) : 0 ≤ kappa b := add_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Local coordinate `k ∈ {0,1}` of a moved point in a moved block. -/
def dAxis (b : Pose) (k : Fin 3) (v : Q2) : Q := (b.axis k).x * v.x + (b.axis k).y * v.y

theorem loc_shift (b : Pose) (k : Fin 3) (p : Q3) (u t : Q2) :
    (b.shift t).loc k (shiftPt p u) = b.loc k p + dAxis b k (Q2.sub u t) := by
  have hax : (b.shift t).axis k = b.axis k := by
    fin_cases k <;> rfl
  have hz : (b.axis k).z = 0 ∨ k = 2 := by fin_cases k <;> simp [Pose.axis, Pose.e1, Pose.e2]
  unfold Pose.loc dAxis
  rw [hax]
  simp only [Q3.dot, Pose.shift, shiftPt, Q3.sub_x, Q3.sub_y, Q3.sub_z, Q2.sub]
  ring

theorem dAxis_le (b : Pose) (k : Fin 3) (hk : k ≠ 2) (v : Q2) :
    |dAxis b k v| ≤ kappa b * ninf v := by
  have hx := abs_x_le v; have hy := abs_y_le v
  have key : ∀ a c : Q, |a * v.x + c * v.y| ≤ (|a| + |c|) * ninf v := by
    intro a c
    calc |a * v.x + c * v.y| ≤ |a * v.x| + |c * v.y| := abs_add_le _ _
      _ = |a| * |v.x| + |c| * |v.y| := by rw [abs_mul, abs_mul]
      _ ≤ |a| * ninf v + |c| * ninf v := by gcongr
      _ = _ := by ring
  unfold dAxis kappa
  fin_cases k
  · exact key _ _
  · have := key (-b.rot.s) b.rot.c
    simp only [abs_neg] at this
    simpa [Pose.axis, Pose.e2, add_comm] using this
  · exact absurd rfl hk

theorem shift_topZ (b : Pose) (t : Q2) : (b.shift t).topZ = b.topZ := rfl
theorem shift_bottomZ (b : Pose) (t : Q2) : (b.shift t).bottomZ = b.bottomZ := rfl
theorem shift_halfAlong (b : Pose) (t : Q2) (k : Fin 3) :
    (b.shift t).halfAlong k = b.halfAlong k := rfl

theorem blk_perturb (bs : List Pose) (t : Nat → Q2) (i : Nat) (hi : i < bs.length) :
    blk (perturb bs t) i = (blk bs i).shift (t i) := by
  unfold blk perturb
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  simp [List.getElem?_eq_getElem hi]

theorem length_perturb (bs : List Pose) (t : Nat → Q2) : (perturb bs t).length = bs.length := by
  simp [perturb]

/-! ## Alignment paths bound relative misplacement -/

def Linked (plan : BuildPlan) (a b : Nat) : Prop := plan.refOf a = some b ∨ plan.refOf b = some a

instance (plan : BuildPlan) (a b : Nat) : Decidable (Linked plan a b) := by
  unfold Linked; infer_instance

/-- `path` runs from `j` to `i` along alignment links between blocks `< n`. -/
def PathOK (plan : BuildPlan) (n : Nat) (path : List Nat) (j i : Nat) : Prop :=
  path.head? = some j ∧ path.getLast? = some i ∧ (∀ v ∈ path, v < n) ∧
    path.IsChain (Linked plan)

instance (plan n path j i) : Decidable (PathOK plan n path j i) := by
  unfold PathOK; infer_instance

theorem path_bound (H : HumanModel) (plan : BuildPlan) (n : Nat) (t : Nat → Q2)
    (ht : Admissible H plan n t) :
    ∀ (path : List Nat) (j i : Nat), PathOK plan n path j i →
      ninf (Q2.sub (t j) (t i)) ≤ ((path.length : Q) - 1) * H.epsRel := by
  intro path
  induction path with
  | nil => intro j i h; simp [PathOK] at h
  | cons a rest ih =>
    intro j i ⟨hh, hl, hv, hc⟩
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      simp [Q2.sub, ninf]
    | cons b rest' =>
      have hab : Linked plan a b := (List.isChain_cons_cons.mp hc).1
      have hrest : PathOK plan n (b :: rest') b i := by
        refine ⟨rfl, ?_, fun v hv' => hv v (List.mem_cons_of_mem _ hv'), (List.isChain_cons_cons.mp hc).2⟩
        simpa [List.getLast?_cons_cons] using hl
      have h1 := ih b i hrest
      have hj : a < n := hv a List.mem_cons_self
      have hb : b < n := hv b (List.mem_cons_of_mem _ List.mem_cons_self)
      have h2 : ninf (Q2.sub (t a) (t b)) ≤ H.epsRel := by
        rcases hab with h | h
        · exact ht.2 a hj b h
        · rw [ninf_symm]; exact ht.2 b hb a h
      have := ninf_tri (t a) (t b) (t i)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h1 ⊢
      linarith

/-! ## Robust certificates -/

/-- A contact force with its robustness data: `r` bounds the misalignment between its two
blocks, justified by `path` (an alignment path) or by the drift cap `2·eAbs`. -/
structure RForce where
  f : PointForce
  r : Q := 0
  path : List Nat := []
  deriving DecidableEq, Repr, Inhabited, Lean.ToJson, Lean.FromJson

/-- Load carried from above: `Σ` over forces pushing `j` up. -/
def upS (rfs : List RForce) (j : Nat) : Q :=
  (rfs.map fun rf => if rf.f.upper = j then rf.f.mag else 0).sum

/-- `Σ g` over forces pushing `j` down (from the blocks resting on `j`). -/
def dnS (rfs : List RForce) (j : Nat) (g : RForce → Q) : Q :=
  (rfs.map fun rf => if rf.f.lower = some j then g rf else 0).sum

def loadS (loads : List Load) (j : Nat) : Q := (loads.map (loadOn j)).sum

/-- A point keeps margin `m` (in max-norm, converted by `κ`) inside the footprint of `b`. -/
def MarginOK (m : Q) (b : Pose) (p : Q3) : Prop :=
  |b.loc 0 p| + kappa b * m ≤ b.half.x ∧ |b.loc 1 p| + kappa b * m ≤ b.half.y

instance (m b p) : Decidable (MarginOK m b p) := by unfold MarginOK; infer_instance

/-- `r` is justified by an alignment path, or by the drift cap. -/
def RJust (H : HumanModel) (plan : BuildPlan) (n : Nat) (rf : RForce) : Prop :=
  match rf.f.lower with
  | none => True
  | some i => 2 * H.eAbs ≤ rf.r ∨
      (PathOK plan n rf.path rf.f.upper i ∧ ((rf.path.length : Q) - 1) * H.epsRel ≤ rf.r)

instance (H plan n rf) : Decidable (RJust H plan n rf) := by
  unfold RJust; split <;> infer_instance

def RMargins (bs : List Pose) (σ : Nat → Q) (rf : RForce) : Prop :=
  MarginOK (σ rf.f.upper) (blk bs rf.f.upper) rf.f.pt ∧
  match rf.f.lower with
  | none => True
  | some i => MarginOK (rf.r + σ rf.f.upper) (blk bs i) rf.f.pt

instance (bs σ rf) : Decidable (RMargins bs σ rf) := by
  unfold RMargins; split <;> infer_instance

def RankOK (rank : Nat → Nat) (rf : RForce) : Prop :=
  match rf.f.lower with
  | none => True
  | some i => rank rf.f.upper < rank i

instance (rank rf) : Decidable (RankOK rank rf) := by unfold RankOK; split <;> infer_instance

/-- The robustness conditions in plain (list) form. -/
def RobustL (H : HumanModel) (plan : BuildPlan) (bs : List Pose) (loads : List Load)
    (rfs : List RForce) (σ : Nat → Q) (rank : Nat → Nat) : Prop :=
  ForcesOK bs loads (rfs.map (·.f)) ∧
  (∀ rf ∈ rfs, RankOK rank rf ∧ RMargins bs σ rf ∧ RJust H plan bs.length rf) ∧
  ∀ j, j < bs.length → rank j < bs.length ∧ 0 ≤ σ j ∧ 0 < upS rfs j ∧
    dnS rfs j (fun rf => rf.f.mag * (rf.r + σ rf.f.upper)) ≤ σ j * upS rfs j

/-! ## The shift field -/

/-- Where the forces under `j` move to, given where the forces of the blocks above went:
`(1 + loads)·t_j + Σ_down F·u_up` divided by the load carried. -/
def stepU (rfs : List RForce) (loads : List Load) (t : Nat → Q2) (u : Nat → Q2) (j : Nat) : Q2 :=
  ⟨((1 + loadS loads j) * (t j).x + dnS rfs j (fun rf => rf.f.mag * (u rf.f.upper).x)) / upS rfs j,
   ((1 + loadS loads j) * (t j).y + dnS rfs j (fun rf => rf.f.mag * (u rf.f.upper).y)) / upS rfs j⟩

def iterU (rfs : List RForce) (loads : List Load) (t : Nat → Q2) : Nat → Nat → Q2
  | 0 => t
  | m + 1 => stepU rfs loads t (iterU rfs loads t m)

theorem dnS_congr (rfs : List RForce) (j : Nat) (g g' : RForce → Q)
    (h : ∀ rf ∈ rfs, rf.f.lower = some j → g rf = g' rf) : dnS rfs j g = dnS rfs j g' := by
  unfold dnS
  congr 1
  apply List.map_congr_left
  intro rf hrf
  split
  · rename_i hl; rw [h rf hrf hl]
  · rfl

theorem stepU_congr (rfs loads t) (u u' : Nat → Q2) (j : Nat)
    (h : ∀ rf ∈ rfs, rf.f.lower = some j → u rf.f.upper = u' rf.f.upper) :
    stepU rfs loads t u j = stepU rfs loads t u' j := by
  unfold stepU
  rw [dnS_congr rfs j (fun rf => rf.f.mag * (u rf.f.upper).x) (fun rf => rf.f.mag * (u' rf.f.upper).x)
        (fun rf hrf hl => by simp only [h rf hrf hl]),
      dnS_congr rfs j (fun rf => rf.f.mag * (u rf.f.upper).y) (fun rf => rf.f.mag * (u' rf.f.upper).y)
        (fun rf hrf hl => by simp only [h rf hrf hl])]

/-- After `m` rounds, the shift of every block of rank `< m` is final. -/
theorem iterU_stable (rfs loads t) (rank : Nat → Nat) (hr : ∀ rf ∈ rfs, RankOK rank rf) :
    ∀ m j, rank j < m → iterU rfs loads t m j = iterU rfs loads t (m + 1) j := by
  intro m
  induction m with
  | zero => intro j h; omega
  | succ m ih =>
    intro j hj
    show stepU rfs loads t (iterU rfs loads t m) j = stepU rfs loads t (iterU rfs loads t (m + 1)) j
    apply stepU_congr
    intro rf hrf hl
    have := hr rf hrf
    unfold RankOK at this
    rw [hl] at this
    exact ih _ (by simp at this; omega)

/-! ## Sum identities -/

theorem sgn_sum (rfs : List RForce) (k : Nat) (g : RForce → Q) :
    (rfs.map fun rf => sgn k rf.f * g rf).sum
      = (rfs.map fun rf => if rf.f.upper = k then g rf else 0).sum - dnS rfs k g := by
  unfold dnS
  induction rfs with
  | nil => simp
  | cons rf rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    unfold sgn
    split_ifs <;> ring

theorem upS_eq (rfs : List RForce) (k : Nat) :
    upS rfs k = (rfs.map fun rf => if rf.f.upper = k then rf.f.mag else 0).sum := rfl

theorem sum_if_upper_mul (rfs : List RForce) (k : Nat) (c : Q) :
    (rfs.map fun rf => if rf.f.upper = k then rf.f.mag * c else 0).sum = upS rfs k * c := by
  unfold upS
  induction rfs with
  | nil => simp
  | cons rf rest ih => simp only [List.map_cons, List.sum_cons, ih]; split_ifs <;> ring

/-- Nominal vertical balance: load carried = own weight + loads + what rests on it. -/
theorem fz_balance (loads : List Load) (rfs : List RForce) (k : Nat)
    (h : netFz (rfs.map (·.f)) loads k = 0) :
    upS rfs k - dnS rfs k (fun rf => rf.f.mag) = 1 + loadS loads k := by
  unfold netFz at h
  rw [List.map_map] at h
  have := sgn_sum rfs k (fun rf => rf.f.mag)
  simp only [Function.comp_def] at h
  rw [this] at h
  unfold loadS Block.weight at *
  rw [upS_eq]
  linarith

theorem abs_dnS_le (rfs : List RForce) (j : Nat) (g b : RForce → Q)
    (h : ∀ rf ∈ rfs, rf.f.lower = some j → |g rf| ≤ b rf) :
    |dnS rfs j g| ≤ dnS rfs j b := by
  unfold dnS
  induction rfs with
  | nil => simp
  | cons rf rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have ih' := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    calc _ ≤ |(if rf.f.lower = some j then g rf else 0)|
              + |(rest.map fun rf => if rf.f.lower = some j then g rf else 0).sum| := abs_add_le _ _
      _ ≤ _ := by
        apply add_le_add _ ih'
        split
        · rename_i hl; exact h rf List.mem_cons_self hl
        · simp

theorem dnS_sub (rfs : List RForce) (j : Nat) (a : RForce → Q) (c : Q) :
    dnS rfs j (fun rf => rf.f.mag * (a rf - c))
      = dnS rfs j (fun rf => rf.f.mag * a rf) - dnS rfs j (fun rf => rf.f.mag) * c := by
  unfold dnS
  induction rfs with
  | nil => simp
  | cons rf rest ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; split_ifs <;> ring

/-! ## The shift budget bounds the shift -/

theorem shift_bound (H : HumanModel) (plan : BuildPlan) (bs : List Pose) (loads : List Load)
    (rfs : List RForce) (σ : Nat → Q) (rank : Nat → Nat)
    (hR : RobustL H plan bs loads rfs σ rank) (t : Nat → Q2) (ht : Admissible H plan bs.length t) :
    let U := iterU rfs loads t bs.length
    ∀ m j, rank j = m → j < bs.length → ninf (Q2.sub (U j) (t j)) ≤ σ j := by
  intro U m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro j hjr hj
  obtain ⟨hF, hrf, hblk⟩ := hR
  obtain ⟨hrk, hσ, hW, hD⟩ := hblk j hj
  have hfix : U j = stepU rfs loads t U j :=
    iterU_stable rfs loads t rank (fun rf h => (hrf rf h).1) _ j hrk
  have hbal := fz_balance loads rfs j (hF.2 j hj).1
  -- every force pushing `j` down comes from a block that has moved at most σ + r against `j`
  have hdown : ∀ rf ∈ rfs, rf.f.lower = some j →
      ninf (Q2.sub (U rf.f.upper) (t j)) ≤ σ rf.f.upper + rf.r := by
    intro rf hmem hl
    have hfo := hF.1 rf.f (List.mem_map_of_mem hmem)
    have hup : rf.f.upper < bs.length := hfo.2.1
    have hrank : rank rf.f.upper < m := by
      have := (hrf rf hmem).1; unfold RankOK at this; rw [hl] at this; omega
    have h1 := ih _ hrank rf.f.upper rfl hup
    have hr : ninf (Q2.sub (t rf.f.upper) (t j)) ≤ rf.r := by
      have hj' := (hrf rf hmem).2.2
      unfold RJust at hj'; rw [hl] at hj'
      rcases hj' with h2 | ⟨hp, hl2⟩
      · exact (ninf_sub_le _ _).trans (by linarith [ht.1 _ hup, ht.1 _ hj])
      · exact (path_bound H plan _ t ht _ _ _ hp).trans hl2
    exact (ninf_tri _ (t rf.f.upper) _).trans (by linarith)
  have hWne : upS rfs j ≠ 0 := ne_of_gt hW
  -- U_j − t_j = Σ_down F (U_up − t_j) / W
  have comp : ∀ (proj : Q2 → Q),
      (proj = Q2.x ∨ proj = Q2.y) →
      proj (U j) - proj (t j)
        = dnS rfs j (fun rf => rf.f.mag * (proj (U rf.f.upper) - proj (t j))) / upS rfs j := by
    intro proj hp
    rw [dnS_sub, eq_div_iff hWne]
    have key : proj (U j) * upS rfs j
        = (1 + loadS loads j) * proj (t j) + dnS rfs j (fun rf => rf.f.mag * proj (U rf.f.upper)) := by
      rw [hfix]
      rcases hp with rfl | rfl <;> simp only [stepU] <;> field_simp
    linear_combination key - proj (t j) * hbal
  have bnd : ∀ (proj : Q2 → Q), (proj = Q2.x ∨ proj = Q2.y) →
      |proj (U j) - proj (t j)| ≤ σ j := by
    intro proj hp
    rw [comp proj hp, abs_div, abs_of_pos hW, div_le_iff₀ hW]
    refine (abs_dnS_le rfs j _ (fun rf => rf.f.mag * (rf.r + σ rf.f.upper)) ?_).trans hD
    intro rf hmem hl
    have hm := (hF.1 rf.f (List.mem_map_of_mem hmem)).1
    rw [abs_mul, abs_of_nonneg hm]
    apply mul_le_mul_of_nonneg_left _ hm
    have := hdown rf hmem hl
    rcases hp with rfl | rfl
    · exact (abs_x_le (Q2.sub (U rf.f.upper) (t j))).trans (by linarith)
    · exact (abs_y_le (Q2.sub (U rf.f.upper) (t j))).trans (by linarith)
  exact ninf_le (bnd Q2.x (Or.inl rfl)) (bnd Q2.y (Or.inr rfl))

/-! ## Moving the forces -/

def shiftLoads (loads : List Load) (t : Nat → Q2) : List Load :=
  loads.map fun l => { l with pt := shiftPt l.pt (t l.block) }

/-- A force moved by the shift of the block it holds up. -/
def moveF (U : Nat → Q2) (f : PointForce) : PointForce := { f with pt := shiftPt f.pt (U f.upper) }

theorem r_bound (H : HumanModel) (plan : BuildPlan) (n : Nat) (t : Nat → Q2)
    (ht : Admissible H plan n t) (rf : RForce) (i : Nat) (hl : rf.f.lower = some i)
    (hj : RJust H plan n rf) (hup : rf.f.upper < n) (hi : i < n) :
    ninf (Q2.sub (t rf.f.upper) (t i)) ≤ rf.r := by
  unfold RJust at hj; rw [hl] at hj
  rcases hj with h2 | ⟨hp, hl2⟩
  · exact (ninf_sub_le _ _).trans (by linarith [ht.1 _ hup, ht.1 _ hi])
  · exact (path_bound H plan _ t ht _ _ _ hp).trans hl2

theorem footprint_moved (b : Pose) (p : Q3) (u tb : Q2) (m : Q)
    (hm : MarginOK m b p) (hu : ninf (Q2.sub u tb) ≤ m) :
    (b.shift tb).InFootprint (shiftPt p u) := by
  have k0 := dAxis_le b 0 (by decide) (Q2.sub u tb)
  have k1 := dAxis_le b 1 (by decide) (Q2.sub u tb)
  have hk := kappa_nonneg b
  have hmk : kappa b * ninf (Q2.sub u tb) ≤ kappa b * m := mul_le_mul_of_nonneg_left hu hk
  obtain ⟨h0, h1⟩ := hm
  constructor
  · show |(b.shift tb).loc 0 (shiftPt p u)| ≤ (b.shift tb).half.x
    rw [loc_shift]
    exact (abs_add_le _ _).trans (by
      show |b.loc 0 p| + |dAxis b 0 (Q2.sub u tb)| ≤ b.half.x; linarith)
  · show |(b.shift tb).loc 1 (shiftPt p u)| ≤ (b.shift tb).half.y
    rw [loc_shift]
    exact (abs_add_le _ _).trans (by
      show |b.loc 1 p| + |dAxis b 1 (Q2.sub u tb)| ≤ b.half.y; linarith)

theorem sum_if_upper_fun (rfs : List RForce) (k : Nat) (U : Nat → Q2) (proj : Q2 → Q) :
    (rfs.map fun rf => if rf.f.upper = k then rf.f.mag * proj (U rf.f.upper) else 0).sum
      = upS rfs k * proj (U k) := by
  unfold upS
  induction rfs with
  | nil => simp
  | cons rf rest ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    split_ifs with h
    · rw [h]; ring
    · ring

theorem moment_move (rfs : List RForce) (k : Nat) (U : Nat → Q2) (proj3 : Q3 → Q) (proj : Q2 → Q)
    (hp : ∀ p v, proj3 (shiftPt p v) = proj3 p + proj v) (c tk : Q) :
    (rfs.map fun rf => sgn k rf.f * rf.f.mag * (proj3 (moveF U rf.f).pt - (c + tk))).sum
      = (rfs.map fun rf => sgn k rf.f * rf.f.mag * (proj3 rf.f.pt - c)).sum
        + (rfs.map fun rf => sgn k rf.f * (rf.f.mag * proj (U rf.f.upper))).sum
        - tk * (rfs.map fun rf => sgn k rf.f * rf.f.mag).sum := by
  induction rfs with
  | nil => simp
  | cons rf rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [moveF, hp]
    ring

theorem loads_move (loads : List Load) (t : Nat → Q2) (k : Nat) (proj3 : Q3 → Q) (proj : Q2 → Q)
    (hp : ∀ p v, proj3 (shiftPt p v) = proj3 p + proj v) (c : Q) :
    ((shiftLoads loads t).map fun l => loadOn k l * (proj3 l.pt - (c + proj (t k)))).sum
      = (loads.map fun l => loadOn k l * (proj3 l.pt - c)).sum := by
  unfold shiftLoads
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply, loadOn, hp]
  split_ifs with h
  · rw [h]; ring
  · ring

theorem loadOn_shift (loads : List Load) (t : Nat → Q2) (k : Nat) :
    (shiftLoads loads t).map (loadOn k) = loads.map (loadOn k) := by
  unfold shiftLoads; rw [List.map_map]; rfl

/-- **Robustness, list form.** If the robust conditions hold, then every admissible
misplacement of the blocks is in equilibrium (with the loads moving with their blocks). -/
theorem robustL_sound (H : HumanModel) (plan : BuildPlan) (bs : List Pose) (loads : List Load)
    (rfs : List RForce) (σ : Nat → Q) (rank : Nat → Nat)
    (hR : RobustL H plan bs loads rfs σ rank) (t : Nat → Q2) (ht : Admissible H plan bs.length t) :
    Equilibrium (perturb bs t) (shiftLoads loads t) := by
  let U := iterU rfs loads t bs.length
  have hsb := shift_bound H plan bs loads rfs σ rank hR t ht
  obtain ⟨hF, hrf, hblk⟩ := hR
  have hU : ∀ j, j < bs.length → ninf (Q2.sub (U j) (t j)) ≤ σ j :=
    fun j hj => hsb (rank j) j rfl hj
  refine ⟨rfs.map fun rf => moveF U rf.f, ?_, ?_⟩
  · -- every moved force is admissible in the misplaced structure
    intro f' hf'
    simp only [List.mem_map] at hf'
    obtain ⟨rf, hmem, rfl⟩ := hf'
    obtain ⟨hmag, hup, hbot, hlow⟩ := hF.1 rf.f (List.mem_map_of_mem hmem)
    obtain ⟨-, ⟨hmj, hmi⟩, hjust⟩ := hrf rf hmem
    have hup' : rf.f.upper < (perturb bs t).length := by rw [length_perturb]; exact hup
    refine ⟨hmag, hup', ?_, ?_⟩
    · show (blk (perturb bs t) rf.f.upper).OnBottom (shiftPt rf.f.pt (U rf.f.upper))
      rw [blk_perturb _ _ _ hup]
      exact ⟨hbot.1, footprint_moved _ _ _ _ _ hmj (hU _ hup)⟩
    · show LowerOK (perturb bs t) { rf.f with pt := shiftPt rf.f.pt (U rf.f.upper) }
      unfold LowerOK at hlow ⊢
      simp only
      split at hlow
      · simpa [shiftPt] using hlow
      · rename_i i hl
        rw [hl] at hmi
        obtain ⟨hi, htop⟩ := hlow
        refine ⟨by simpa [length_perturb] using hi, ?_⟩
        rw [blk_perturb _ _ _ hi]
        refine ⟨htop.1, footprint_moved _ _ _ _ _ hmi ?_⟩
        have h1 := hU _ hup
        have h2 := r_bound H plan _ t ht rf i hl hjust hup hi
        exact (ninf_tri _ (t rf.f.upper) _).trans (by linarith)
  · -- every block is balanced
    intro k hk
    rw [length_perturb] at hk
    obtain ⟨hz, hx, hy⟩ := hF.2 k hk
    obtain ⟨-, -, hW, -⟩ := hblk k hk
    have hbal := fz_balance loads rfs k hz
    have hfix : U k = stepU rfs loads t U k :=
      iterU_stable rfs loads t rank (fun rf h => (hrf rf h).1) _ k (hblk k hk).1
    have hWne : upS rfs k ≠ 0 := ne_of_gt hW
    have extra : ∀ (proj : Q2 → Q), (proj = Q2.x ∨ proj = Q2.y) →
        (rfs.map fun rf => sgn k rf.f * (rf.f.mag * proj (U rf.f.upper))).sum
          - proj (t k) * (rfs.map fun rf => sgn k rf.f * rf.f.mag).sum = 0 := by
      intro proj hp
      rw [sgn_sum rfs k (fun rf => rf.f.mag * proj (U rf.f.upper)), sum_if_upper_fun,
          sgn_sum rfs k (fun rf => rf.f.mag), ← upS_eq]
      have key : proj (U k) * upS rfs k
          = (1 + loadS loads k) * proj (t k) + dnS rfs k (fun rf => rf.f.mag * proj (U rf.f.upper)) := by
        rw [hfix]
        rcases hp with rfl | rfl <;> simp only [stepU] <;> field_simp
      linear_combination key - proj (t k) * hbal
    have hc := blk_perturb bs t k hk
    refine ⟨?_, ?_, ?_⟩
    · unfold netFz at hz ⊢
      rw [loadOn_shift, List.map_map]
      rw [List.map_map] at hz
      exact hz
    · unfold netMx at hx ⊢
      rw [hc]
      simp only [List.map_map, Function.comp_def, Pose.shift]
      rw [show (fun rf : RForce => sgn k (moveF U rf.f) * (moveF U rf.f).mag *
              ((moveF U rf.f).pt.x - ((blk bs k).center.x + (t k).x)))
            = (fun rf : RForce => sgn k rf.f * rf.f.mag *
              ((moveF U rf.f).pt.x - ((blk bs k).center.x + (t k).x))) from rfl]
      rw [moment_move rfs k U (·.x) Q2.x (fun _ _ => rfl),
          loads_move loads t k (·.x) Q2.x (fun _ _ => rfl)]
      rw [List.map_map] at hx
      have e := extra Q2.x (Or.inl rfl)
      simp only [Function.comp_def] at hx
      linarith
    · unfold netMy at hy ⊢
      rw [hc]
      simp only [List.map_map, Function.comp_def, Pose.shift]
      rw [show (fun rf : RForce => sgn k (moveF U rf.f) * (moveF U rf.f).mag *
              ((moveF U rf.f).pt.y - ((blk bs k).center.y + (t k).y)))
            = (fun rf : RForce => sgn k rf.f * rf.f.mag *
              ((moveF U rf.f).pt.y - ((blk bs k).center.y + (t k).y))) from rfl]
      rw [moment_move rfs k U (·.y) Q2.y (fun _ _ => rfl),
          loads_move loads t k (·.y) Q2.y (fun _ _ => rfl)]
      rw [List.map_map] at hy
      have e := extra Q2.y (Or.inr rfl)
      simp only [Function.comp_def] at hy
      linarith

end Kapla.Physics
