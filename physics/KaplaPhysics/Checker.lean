import KaplaPhysics.Press
import KaplaPhysics.Clearance

/-!
# KaplaPhysics.Checker — the verified certificate checker

`certify` accepts a plan together with an (untrusted) certificate — one list of contact
forces per build step — and returns a plan *carrying a proof* of `Valid H N plan`, or the
reasons for rejection. The checks are exact rational arithmetic, decided by the kernel-
checked `Decidable` instances of the spec itself; `checkAll_sound` connects them to `Valid`.
-/

namespace Kapla.Physics

open Kapla

instance (bs : List Pose) : Decidable (AboveGround bs) := by unfold AboveGround; infer_instance

/-- Certificate:
* `forces[k]`: contact forces of the structure after step `k`;
* `press[k][t][j]`: the same while the builder presses top corner `j` of the `t`-th block
  placed in step `k`;
* `touch[j]`: common points `(i, p)` of block `j` with earlier blocks it touches. -/
structure Certificate where
  forces : List (List PointForce)
  press : List (List (List (List PointForce))) := []
  touch : TouchWitnesses := #[]
  deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson

/-- The press certificate for corner `j` of block `t` of step `k`. -/
def Certificate.pressAt (c : Certificate) (k t : Nat) (j : Fin 4) : List PointForce :=
  ((c.press.getD k []).getD t []).getD j.val []

/-- Checked form of H4 for step `k`. -/
def PressCheck (H : HumanModel) (plan : BuildPlan) (cert : Certificate) (k : Nat) : Prop :=
  ∀ t, t < (plan.steps.getD k default).blocks.length → ∀ j : Fin 4,
    ForcesOKFast (plan.prefixBlocks (k + 1)).toArray
      [pressLoad H ((plan.prefixBlocks k).length + t)
        (topCorner (blk (plan.prefixBlocks (k + 1)) ((plan.prefixBlocks k).length + t)) j)]
      (cert.pressAt k t j)

instance (H plan cert k) : Decidable (PressCheck H plan cert k) := by
  unfold PressCheck; infer_instance

theorem pressCheck_sound {H plan cert k} (h : PressCheck H plan cert k) : PressOK H plan k := by
  intro i hi p hp
  simp only [newIndices, List.mem_range'_1] at hi
  obtain ⟨hlo, hhi⟩ := hi
  have ht : i - (plan.prefixBlocks k).length < (plan.steps.getD k default).blocks.length := by
    omega
  have hidx : (plan.prefixBlocks k).length + (i - (plan.prefixBlocks k).length) = i := by omega
  have hc := h _ ht
  rw [hidx] at hc
  exact press_from_corners _ i H.press _ p rfl hp _
    (fun j => forcesOKFast_sound _ _ _ (hc j))

/-- Everything `certify` checks, as one decidable proposition. -/
def CheckAll (H : HumanModel) (N : Nat) (plan : BuildPlan) (cert : Certificate) : Prop :=
  plan.blockCount ≤ N ∧
  (∀ s ∈ plan.steps, 1 ≤ s.blocks.length ∧ s.blocks.length ≤ H.hands) ∧
  AboveGround plan.blocks ∧
  PairsSeparatedA plan.blocks.toArray ∧
  ClearanceCheck H.clear plan.blocks.toArray cert.touch ∧
  (∀ k, k < plan.steps.length →
    ForcesOKFast (plan.prefixBlocks (k + 1)).toArray [] (cert.forces.getD k [])) ∧
  ∀ k, k < plan.steps.length → PressCheck H plan cert k

instance (H N plan cert) : Decidable (CheckAll H N plan cert) := by
  unfold CheckAll; infer_instance

theorem checkAll_sound {H N plan cert} (h : CheckAll H N plan cert) : Valid H N plan := by
  obtain ⟨hN, hHands, hGround, hSep, hClear, hEq, hPress⟩ := h
  exact ⟨hN, hHands, hGround, pairsSeparated_sound _ (pairsSeparatedA_sound _ hSep),
    clearanceCheck_sound H _ _ hClear,
    fun k hk => ⟨_, forcesOKFast_sound _ _ _ (hEq k hk)⟩,
    fun k hk => pressCheck_sound (hPress k hk)⟩

/-- Human-readable reasons why `CheckAll` fails (only computed on rejection). -/
def diagnose (H : HumanModel) (N : Nat) (plan : BuildPlan) (cert : Certificate) :
    List Diagnostic := Id.run do
  let bs := plan.blocks
  let arr := bs.toArray
  let mut ds : List Diagnostic := []
  if bs.length > N then ds := ds ++ [.tooManyBlocks bs.length N]
  for h : k in [0:plan.steps.length] do
    let s := plan.steps[k]
    if s.blocks.isEmpty then ds := ds ++ [.emptyStep k]
    if s.blocks.length > H.hands then ds := ds ++ [.tooManyHands k]
  for h : i in [0:arr.size] do
    if arr[i].bottomZ < 0 then ds := ds ++ [.belowGround i]
  for j in [0:arr.size] do
    for i in [0:j] do
      unless decide (Separated (blkA arr i) (blkA arr j)) do ds := ds ++ [.overlap i j]
      unless decide (ClearPairCheck H.clear arr cert.touch i j) do ds := ds ++ [.clearance i j]
  for k in [0:plan.steps.length] do
    let pre := (plan.prefixBlocks (k + 1)).toArray
    let fs := cert.forces.getD k []
    unless decide (ForcesOKFast pre [] fs) do
      -- blame the blocks whose balance fails, or that receive an inadmissible force
      let A := accum pre.size (·.mag) fs
      let bad := (List.range pre.size).filter fun b => A.getD b 0 ≠ Block.weight
      let badF := (fs.filter fun f => !decide (ForceOKA pre f)).map (·.upper)
      let blame := (bad ++ badF).eraseDups
      ds := ds ++ (if blame.isEmpty then [.unstable k (pre.size - 1)] else blame.map (.unstable k))
  for k in [0:plan.steps.length] do
    if decide (ForcesOKFast (plan.prefixBlocks (k + 1)).toArray [] (cert.forces.getD k [])) then
      for t in [0:(plan.steps.getD k default).blocks.length] do
        for j in [0:4] do
          if hj : j < 4 then
            let pre := plan.prefixBlocks (k + 1)
            let i := (plan.prefixBlocks k).length + t
            unless decide (ForcesOKFast pre.toArray [pressLoad H i (topCorner (blk pre i) ⟨j, hj⟩)]
                (cert.pressAt k t ⟨j, hj⟩)) do
              ds := ds ++ [.pressTips k (4 * t + j)]
  return ds.eraseDups

/-- **The verified checker.** Only a plan with a proof of `Valid` can come out. -/
def certify (H : HumanModel) (N : Nat) (plan : BuildPlan) (cert : Certificate) :
    Except (List Diagnostic) { p : BuildPlan // Valid H N p } :=
  if h : CheckAll H N plan cert then .ok ⟨plan, checkAll_sound h⟩
  else .error (diagnose H N plan cert)

theorem certify_sound {H N plan cert bp} (_h : certify H N plan cert = .ok bp) :
    Valid H N bp.val := bp.property

/-- `certify` returns exactly the plan it was given. -/
theorem certify_val {H N plan cert bp} (h : certify H N plan cert = .ok bp) :
    bp.val = plan := by
  unfold certify at h
  split at h
  · cases h; rfl
  · cases h

end Kapla.Physics
