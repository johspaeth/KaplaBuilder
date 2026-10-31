import KaplaPhysics.Separation

/-!
# KaplaPhysics.FastCheck — an efficient checker, proven to imply the spec

The spec (`ForcesOK`) sums over *all* forces for *every* block and looks blocks up in a
list, which is cubic over a whole build. Here the per-block sums are accumulated in one
pass into arrays, and blocks are looked up in an array; `forcesOKFast_sound` shows that
this check implies `ForcesOK`.
-/

namespace Kapla.Physics

open Kapla

/-! ## Array lookup agrees with list lookup -/

def blkA (arr : Array Pose) (i : Nat) : Pose := arr.getD i default

theorem blkA_toArray (bs : List Pose) (i : Nat) : blkA bs.toArray i = blk bs i := by
  unfold blkA blk
  rw [List.getD_eq_getElem?_getD]
  simp only [Array.getD]
  split
  · rename_i h
    simp [List.getElem?_eq_getElem (by simpa using h)]
  · rename_i h
    simp at h
    simp [List.getElem?_eq_none (by omega)]

def LowerOKA (arr : Array Pose) (f : PointForce) : Prop :=
  match f.lower with
  | none => f.pt.z = 0
  | some i => i < arr.size ∧ (blkA arr i).OnTop f.pt

instance (arr : Array Pose) (f : PointForce) : Decidable (LowerOKA arr f) := by
  unfold LowerOKA; split <;> infer_instance

def ForceOKA (arr : Array Pose) (f : PointForce) : Prop :=
  0 ≤ f.mag ∧ f.upper < arr.size ∧ (blkA arr f.upper).OnBottom f.pt ∧ LowerOKA arr f

instance (arr : Array Pose) (f : PointForce) : Decidable (ForceOKA arr f) := by
  unfold ForceOKA; infer_instance

theorem forceOKA_toArray (bs : List Pose) (f : PointForce) (h : ForceOKA bs.toArray f) :
    ForceOK bs f := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, by simpa using h2, by rwa [blkA_toArray] at h3, ?_⟩
  unfold LowerOKA at h4; unfold LowerOK
  split at h4 <;> rename_i heq <;> simp only [heq]
  · exact h4
  · exact ⟨by simpa using h4.1, by rw [← blkA_toArray]; exact h4.2⟩

/-! ## One-pass accumulation of per-block sums -/

def accStep (val : PointForce → Q) (acc : Array Q) (f : PointForce) : Array Q :=
  let acc := acc.modify f.upper (· + val f)
  match f.lower with
  | some i => acc.modify i (· - val f)
  | none => acc

theorem size_accStep (val : PointForce → Q) (acc : Array Q) (f : PointForce) :
    (accStep val acc f).size = acc.size := by
  unfold accStep; split <;> simp

theorem getD_modify (xs : Array Q) (j i : Nat) (g : Q → Q) :
    (xs.modify j g).getD i 0 = if j = i ∧ i < xs.size then g (xs.getD i 0) else xs.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h : i < xs.size <;> by_cases hj : j = i <;> simp [h, hj]

theorem getD_accStep (val : PointForce → Q) (acc : Array Q) (f : PointForce) (k : Nat)
    (hk : k < acc.size) :
    (accStep val acc f).getD k 0 = acc.getD k 0 + sgn k f * val f := by
  unfold accStep sgn
  split
  · rename_i i heq
    rw [getD_modify, getD_modify]
    simp only [Array.size_modify, heq, Option.some.injEq, hk, and_true]
    by_cases h1 : f.upper = k <;> by_cases h2 : i = k <;> simp [h1, h2]
    ring
  · rename_i heq
    rw [getD_modify]
    simp only [hk, and_true, heq]
    by_cases h1 : f.upper = k <;> simp [h1]

theorem getD_foldl_accStep (val : PointForce → Q) (k : Nat) :
    ∀ (fs : List PointForce) (acc : Array Q), k < acc.size →
      (fs.foldl (accStep val) acc).getD k 0
        = acc.getD k 0 + (fs.map fun f => sgn k f * val f).sum := by
  intro fs
  induction fs with
  | nil => intro acc _; simp
  | cons f fs ih =>
    intro acc hk
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih _ (by rwa [size_accStep]), getD_accStep _ _ _ _ hk]
    ring

/-- Per-block `Σ sgn · val` for all blocks `< n`. -/
def accum (n : Nat) (val : PointForce → Q) (fs : List PointForce) : Array Q :=
  fs.foldl (accStep val) (Array.replicate n 0)

theorem accum_spec (n : Nat) (val : PointForce → Q) (fs : List PointForce) (k : Nat)
    (hk : k < n) : (accum n val fs).getD k 0 = (fs.map fun f => sgn k f * val f).sum := by
  unfold accum
  rw [getD_foldl_accStep _ _ _ _ (by simpa using hk)]
  simp [Array.getD, hk]

theorem sum_lever (fs : List PointForce) (k : Nat) (c : Q) (proj : Q3 → Q) :
    (fs.map fun f => sgn k f * f.mag * (proj f.pt - c)).sum
      = (fs.map fun f => sgn k f * (f.mag * proj f.pt)).sum
        - c * (fs.map fun f => sgn k f * f.mag).sum := by
  induction fs with
  | nil => simp
  | cons f fs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Balance of every block, given the accumulated sums `A = Σ sgn·F`, `Bx = Σ sgn·F·x`,
`By = Σ sgn·F·y` (passed as arguments so they are computed once). -/
def BalancedArrays (arr : Array Pose) (loads : List Load) (A Bx By : Array Q) : Prop :=
  ∀ k, k < arr.size →
    let c := (blkA arr k).center
    A.getD k 0 - (loads.map (loadOn k)).sum - Block.weight = 0 ∧
    Bx.getD k 0 - c.x * A.getD k 0 - (loads.map fun l => loadOn k l * (l.pt.x - c.x)).sum = 0 ∧
    By.getD k 0 - c.y * A.getD k 0 - (loads.map fun l => loadOn k l * (l.pt.y - c.y)).sum = 0

instance (arr loads A Bx By) : Decidable (BalancedArrays arr loads A Bx By) := by
  unfold BalancedArrays; infer_instance

/-- The fast force check. -/
def ForcesOKFast (arr : Array Pose) (loads : List Load) (fs : List PointForce) : Prop :=
  (∀ f ∈ fs, ForceOKA arr f) ∧
  BalancedArrays arr loads (accum arr.size (·.mag) fs)
    (accum arr.size (fun f => f.mag * f.pt.x) fs) (accum arr.size (fun f => f.mag * f.pt.y) fs)

instance (arr loads fs) : Decidable (ForcesOKFast arr loads fs) := by
  unfold ForcesOKFast; infer_instance

theorem forcesOKFast_sound (bs : List Pose) (loads : List Load) (fs : List PointForce)
    (h : ForcesOKFast bs.toArray loads fs) : ForcesOK bs loads fs := by
  obtain ⟨hf, hb⟩ := h
  refine ⟨fun f hf' => forceOKA_toArray bs f (hf f hf'), fun k hk => ?_⟩
  have hk' : k < bs.toArray.size := by simpa using hk
  obtain ⟨h1, h2, h3⟩ := hb k hk'
  simp only [List.size_toArray] at h1 h2 h3
  rw [accum_spec _ _ _ _ hk] at h1 h2 h3
  rw [accum_spec _ _ _ _ hk] at h2 h3
  rw [blkA_toArray] at h2 h3
  refine ⟨h1, ?_, ?_⟩
  · unfold netMx; rw [sum_lever fs k _ (·.x)]; exact h2
  · unfold netMy; rw [sum_lever fs k _ (·.y)]; exact h3

/-! ## Fast pairwise separation -/

def PairsSeparatedA (arr : Array Pose) : Prop :=
  ∀ j, j < arr.size → ∀ i, i < j → Separated (blkA arr i) (blkA arr j)

instance (arr : Array Pose) : Decidable (PairsSeparatedA arr) := by
  unfold PairsSeparatedA; infer_instance

theorem pairsSeparatedA_sound (bs : List Pose) (h : PairsSeparatedA bs.toArray) :
    PairsSeparated bs := by
  intro j hj i hij
  have := h j (by simpa using hj) i hij
  rwa [blkA_toArray, blkA_toArray] at this

end Kapla.Physics
