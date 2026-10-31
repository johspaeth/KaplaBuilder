import KaplaPhysics.Robust
import KaplaPhysics.Press

/-!
# KaplaPhysics.RobustCheck — the robust certificate checker (H1/H2, translations)

`certifyRobust` accepts a plan and robust certificates (forces with misalignment data,
shift budgets, ranks — for every step and every pressed corner) and returns a proof of
`Robust H plan`. The per-block sums are accumulated in one pass (as in `FastCheck`);
`checkRobust_sound` connects the check to the spec through `robustL_sound` and, for the
press, the convexity argument `press_from_corners`.
-/

namespace Kapla.Physics

open Kapla

/-! ## Moving a pressed point with its block -/

theorem topCorner_shift (b : Pose) (v : Q2) (j : Fin 4) :
    topCorner (b.shift v) j = shiftPt (topCorner b j) v := by
  have e : ∀ a : Q3, a = ⟨a.x, a.y, a.z⟩ := fun _ => rfl
  rw [e (topCorner (b.shift v) j)]
  unfold topCorner Pose.toWorld shiftPt
  simp only [Q3.add_x, Q3.add_y, Q3.add_z, Q3.smul_x, Q3.smul_y, Q3.smul_z, Pose.shift, Pose.half, Pose.e1,
    Pose.e2, Pose.e3]
  congr 1 <;> ring

theorem onTop_shift (b : Pose) (p : Q3) (v : Q2) (hp : b.OnTop p) :
    (b.shift v).OnTop (shiftPt p v) := by
  refine ⟨hp.1, footprint_moved b p v v 0 ?_ ?_⟩
  · obtain ⟨h1, h2⟩ := hp.2
    exact ⟨by simpa using h1, by simpa using h2⟩
  · simp [Q2.sub, ninf]

/-- **Robust press.** Robust certificates at the four top corners of block `i` give
equilibrium, under every admissible misplacement, for a press anywhere on its top face. -/
theorem robust_press (H : HumanModel) (plan : BuildPlan) (pre : List Pose) (i : Nat)
    (hi : i < pre.length) (m : Q)
    (rfs : Fin 4 → List RForce) (σ : Fin 4 → Nat → Q) (rank : Fin 4 → Nat → Nat)
    (h : ∀ j, RobustL H plan pre [⟨i, topCorner (blk pre i) j, m⟩] (rfs j) (σ j) (rank j))
    (t : Nat → Q2) (ht : Admissible H plan pre.length t) (p : Q3) (hp : (blk pre i).OnTop p) :
    Equilibrium (perturb pre t) [⟨i, shiftPt p (t i), m⟩] := by
  have e : ∀ j : Fin 4, ∃ fs, ForcesOK (perturb pre t)
      [⟨i, topCorner ((blk pre i).shift (t i)) j, m⟩] fs := by
    intro j
    have := robustL_sound H plan pre _ _ _ _ (h j) t ht
    rw [topCorner_shift]
    simpa [shiftLoads, Equilibrium] using this
  choose fs hfs using e
  exact press_from_corners (perturb pre t) i m ((blk pre i).shift (t i)) (shiftPt p (t i))
    (blk_perturb pre t i hi).symm (onTop_shift _ _ _ hp) fs hfs

/-! ## Alignment references, array form -/

theorem refs_getD (plan : BuildPlan) (a : Nat) : plan.refs.toArray.getD a none = plan.refOf a := by
  unfold BuildPlan.refOf
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

def LinkedA (ra : Array (Option Nat)) (a b : Nat) : Prop :=
  ra.getD a none = some b ∨ ra.getD b none = some a

instance (ra : Array (Option Nat)) (a b : Nat) : Decidable (LinkedA ra a b) := by
  unfold LinkedA; infer_instance

theorem linkedA_eq (plan : BuildPlan) : LinkedA plan.refs.toArray = Linked plan := by
  funext a b; unfold LinkedA Linked; rw [refs_getD, refs_getD]

def PathOKA (ra : Array (Option Nat)) (n : Nat) (path : List Nat) (j i : Nat) : Prop :=
  path.head? = some j ∧ path.getLast? = some i ∧ (∀ v ∈ path, v < n) ∧ path.IsChain (LinkedA ra)

instance (ra n path j i) : Decidable (PathOKA ra n path j i) := by
  unfold PathOKA; infer_instance

def RJustA (H : HumanModel) (ra : Array (Option Nat)) (n : Nat) (rf : RForce) : Prop :=
  match rf.f.lower with
  | none => True
  | some i => 2 * H.eAbs ≤ rf.r ∨
      (PathOKA ra n rf.path rf.f.upper i ∧ ((rf.path.length : Q) - 1) * H.epsRel ≤ rf.r)

instance (H ra n rf) : Decidable (RJustA H ra n rf) := by
  unfold RJustA; split <;> infer_instance

theorem rJustA_sound (H : HumanModel) (plan : BuildPlan) (n : Nat) (rf : RForce)
    (h : RJustA H plan.refs.toArray n rf) : RJust H plan n rf := by
  unfold RJustA PathOKA at h
  unfold RJust PathOK
  rw [linkedA_eq] at h
  exact h

/-- `RefsOK`, checked on the array of references. -/
def RefsCheck (ra : Array (Option Nat)) (n : Nat) : Prop :=
  ∀ j, j < n → (ra.getD j none).all (· < j) = true

instance (ra n) : Decidable (RefsCheck ra n) := by
  unfold RefsCheck; infer_instance

theorem refsCheck_sound (plan : BuildPlan) (h : RefsCheck plan.refs.toArray plan.blockCount) :
    RefsOK plan := by
  intro j hj i hi
  have := h j hj
  rw [refs_getD, hi] at this
  simpa using this

/-! ## One-pass sums keyed by block -/

def accKey (key : RForce → Option Nat) (val : RForce → Q) (acc : Array Q) (rf : RForce) :
    Array Q :=
  match key rf with
  | some j => acc.modify j (· + val rf)
  | none => acc

theorem size_accKey (key val acc rf) : (accKey key val acc rf).size = acc.size := by
  unfold accKey; split <;> simp

theorem getD_foldl_accKey (key : RForce → Option Nat) (val : RForce → Q) (k : Nat) :
    ∀ (rfs : List RForce) (acc : Array Q), k < acc.size →
      (rfs.foldl (accKey key val) acc).getD k 0
        = acc.getD k 0 + (rfs.map fun rf => if key rf = some k then val rf else 0).sum := by
  intro rfs
  induction rfs with
  | nil => intro acc _; simp
  | cons rf rest ih =>
    intro acc hk
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih _ (by rwa [size_accKey])]
    unfold accKey
    split
    · rename_i j hj
      rw [getD_modify]
      by_cases e : j = k
      · subst e; simp [hk, hj]; ring
      · have : ¬ (some j = some k) := by simpa using e
        simp [e, hj]
    · rename_i hj
      simp [hj]

def accK (n : Nat) (key : RForce → Option Nat) (val : RForce → Q) (rfs : List RForce) : Array Q :=
  rfs.foldl (accKey key val) (Array.replicate n 0)

theorem accK_spec (n : Nat) (key : RForce → Option Nat) (val : RForce → Q) (rfs : List RForce)
    (k : Nat) (hk : k < n) :
    (accK n key val rfs).getD k 0 = (rfs.map fun rf => if key rf = some k then val rf else 0).sum := by
  unfold accK
  rw [getD_foldl_accKey _ _ _ _ _ (by simpa using hk)]
  simp [Array.getD, hk]

/-! ## The robust check for one structure -/

def RMarginsA (arr : Array Pose) (σ : Nat → Q) (rf : RForce) : Prop :=
  MarginOK (σ rf.f.upper) (blkA arr rf.f.upper) rf.f.pt ∧
  match rf.f.lower with
  | none => True
  | some i => MarginOK (rf.r + σ rf.f.upper) (blkA arr i) rf.f.pt

instance (arr σ rf) : Decidable (RMarginsA arr σ rf) := by
  unfold RMarginsA; split <;> infer_instance

/-- Shift budgets, given the accumulated `Up = upS` and `Dn = dnS(F·(r + σ_up))`. -/
def BudgetArrays (n : Nat) (σ : Nat → Q) (rank : Nat → Nat) (Up Dn : Array Q) : Prop :=
  ∀ j, j < n → rank j < n ∧ 0 ≤ σ j ∧ 0 < Up.getD j 0 ∧ Dn.getD j 0 ≤ σ j * Up.getD j 0

instance (n σ rank Up Dn) : Decidable (BudgetArrays n σ rank Up Dn) := by
  unfold BudgetArrays; infer_instance

/-- Robust certificate for one structure. -/
structure RCert where
  rfs : List RForce := []
  sigma : Array Q := #[]
  rank : Array Nat := #[]
  deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson

def RCert.σ (c : RCert) (j : Nat) : Q := c.sigma.getD j 0
def RCert.rk (c : RCert) (j : Nat) : Nat := c.rank.getD j 0

def RobustA (H : HumanModel) (ra : Array (Option Nat)) (arr : Array Pose) (loads : List Load)
    (c : RCert) : Prop :=
  ForcesOKFast arr loads (c.rfs.map (·.f)) ∧
  (∀ rf ∈ c.rfs, RankOK c.rk rf ∧ RMarginsA arr c.σ rf ∧ RJustA H ra arr.size rf) ∧
  BudgetArrays arr.size c.σ c.rk (accK arr.size (fun rf => some rf.f.upper) (·.f.mag) c.rfs)
    (accK arr.size (·.f.lower) (fun rf => rf.f.mag * (rf.r + c.σ rf.f.upper)) c.rfs)

instance (H ra arr loads c) : Decidable (RobustA H ra arr loads c) := by
  unfold RobustA; infer_instance

theorem robustA_sound (H : HumanModel) (plan : BuildPlan) (bs : List Pose) (loads : List Load)
    (c : RCert) (h : RobustA H plan.refs.toArray bs.toArray loads c) :
    RobustL H plan bs loads c.rfs c.σ c.rk := by
  obtain ⟨hF, hrf, hB⟩ := h
  refine ⟨forcesOKFast_sound _ _ _ hF, fun rf hm => ?_, fun j hj => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hrf rf hm
    refine ⟨h1, ?_, by simpa using rJustA_sound H plan _ rf h3⟩
    unfold RMarginsA at h2; unfold RMargins
    obtain ⟨a, b⟩ := h2
    refine ⟨by simpa only [blkA_toArray] using a, ?_⟩
    split at b <;> rename_i heq <;> simp only [heq]
    simpa only [blkA_toArray] using b
  · have hj' : j < bs.toArray.size := by simpa using hj
    obtain ⟨h1, h2, h3, h4⟩ := hB j hj'
    simp only [List.size_toArray] at h1 h3 h4
    rw [accK_spec _ _ _ _ _ hj] at h3 h4
    rw [accK_spec _ _ _ _ _ hj] at h4
    simp only [Option.some.injEq] at h3 h4
    exact ⟨by simpa using h1, h2, h3, h4⟩

/-! ## Certificates for a whole plan -/

/-- `steps[k]`: robust certificate of the structure after step `k`; `press[k][t][j]`: the
same while the builder presses top corner `j` of the `t`-th block placed in step `k`. -/
structure RobustCertificate where
  steps : List RCert := []
  press : List (List (List RCert)) := []
  deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson

def RobustCertificate.stepAt (c : RobustCertificate) (k : Nat) : RCert := c.steps.getD k default

def RobustCertificate.pressAt (c : RobustCertificate) (k t : Nat) (j : Fin 4) : RCert :=
  ((c.press.getD k []).getD t []).getD j.val default

/-- Checked form of `RobustOK H plan k`. -/
def RobustStepCheck (H : HumanModel) (plan : BuildPlan) (ra : Array (Option Nat))
    (rc : RobustCertificate) (k : Nat) : Prop :=
  RobustA H ra (plan.prefixBlocks (k + 1)).toArray [] (rc.stepAt k) ∧
  ∀ t, t < (plan.steps.getD k default).blocks.length → ∀ j : Fin 4,
    RobustA H ra (plan.prefixBlocks (k + 1)).toArray
      [pressLoad H ((plan.prefixBlocks k).length + t)
        (topCorner (blk (plan.prefixBlocks (k + 1)) ((plan.prefixBlocks k).length + t)) j)]
      (rc.pressAt k t j)

instance (H plan ra rc k) : Decidable (RobustStepCheck H plan ra rc k) := by
  unfold RobustStepCheck; infer_instance

/-- Everything `certifyRobust` checks. `ra` is `plan.refs.toArray` (passed in so it is
computed once). -/
def CheckRobust (H : HumanModel) (plan : BuildPlan) (ra : Array (Option Nat))
    (rc : RobustCertificate) : Prop :=
  RefsCheck ra plan.blockCount ∧ ∀ k, k < plan.steps.length → RobustStepCheck H plan ra rc k

instance (H plan ra rc) : Decidable (CheckRobust H plan ra rc) := by
  unfold CheckRobust; infer_instance

theorem prefix_length_le (plan : BuildPlan) (k : Nat) (hk : k < plan.steps.length) :
    (plan.prefixBlocks k).length + (plan.steps.getD k default).blocks.length
      = (plan.prefixBlocks (k + 1)).length := by
  unfold BuildPlan.prefixBlocks
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  simp only [List.map_take, List.length_flatten, Option.getD_some]
  rw [List.take_add_one, List.sum_append]
  simp [hk]

theorem robustStep_sound (H : HumanModel) (plan : BuildPlan) (rc : RobustCertificate) (k : Nat)
    (hk : k < plan.steps.length) (h : RobustStepCheck H plan plan.refs.toArray rc k) :
    RobustOK H plan k := by
  obtain ⟨hn, hp⟩ := h
  intro t ht
  refine ⟨?_, ?_⟩
  · have := robustL_sound H plan _ _ _ _ _ (robustA_sound H plan _ _ _ hn) t ht
    simpa [shiftLoads] using this
  · intro i hi p hpt
    simp only [newIndices, List.mem_range'_1] at hi
    obtain ⟨hlo, hhi⟩ := hi
    have hlen := prefix_length_le plan k hk
    have ht' : i - (plan.prefixBlocks k).length < (plan.steps.getD k default).blocks.length := by
      omega
    have hidx : (plan.prefixBlocks k).length + (i - (plan.prefixBlocks k).length) = i := by omega
    have hc := hp _ ht'
    rw [hidx] at hc
    exact robust_press H plan _ i (by omega) H.press _ _ _
      (fun j => robustA_sound H plan _ _ _ (hc j)) t ht p hpt

theorem checkRobust_sound {H plan rc} (h : CheckRobust H plan plan.refs.toArray rc) :
    Robust H plan :=
  ⟨refsCheck_sound plan h.1, fun k hk => robustStep_sound H plan rc k hk (h.2 k hk)⟩

/-- **The robust checker.** Returns a proof of `Robust H plan`, or `none`. -/
def certifyRobust (H : HumanModel) (plan : BuildPlan) (rc : RobustCertificate) :
    Option (PLift (Robust H plan)) :=
  if h : CheckRobust H plan plan.refs.toArray rc then some ⟨checkRobust_sound h⟩ else none

end Kapla.Physics
