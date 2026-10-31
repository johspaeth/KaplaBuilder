import KaplaPhysics.FastCheck

/-!
# KaplaPhysics.Clearance — no near-miss gaps (H6), proven sound

A pair passes when the blocks grown by `c/2` are separated along a face axis (exact SAT,
as in `Separation`), or when an explicit common point shows that they touch.
-/

namespace Kapla.Physics

open Kapla

/-- Projected half-width of block `b` grown by `g`. -/
def projRadiusG (b : Pose) (g : Q) (u : Q3) : Q :=
  |Q3.dot u (b.axis 0)| * (b.halfAlong 0 + g) + |Q3.dot u (b.axis 1)| * (b.halfAlong 1 + g)
    + |Q3.dot u (b.axis 2)| * (b.halfAlong 2 + g)

def SepAlongG (g : Q) (a b : Pose) (k : Fin 3) : Prop :=
  let u := a.axis k
  let a0 := Q3.dot u (b.center - a.center)
  a.halfAlong k + g ≤ a0 - projRadiusG b g u ∨ a0 + projRadiusG b g u ≤ -(a.halfAlong k + g)

instance (g : Q) (a b : Pose) (k : Fin 3) : Decidable (SepAlongG g a b k) := by
  unfold SepAlongG; infer_instance

def SeparatedG (g : Q) (a b : Pose) : Prop := (∃ k, SepAlongG g a b k) ∨ (∃ k, SepAlongG g b a k)

instance (g : Q) (a b : Pose) : Decidable (SeparatedG g a b) := by
  unfold SeparatedG; infer_instance

theorem proj_boundG (b : Pose) (g : Q) (u p : Q3) (hp : b.InteriorGrown g p) :
    |Q3.dot u (p - b.center)| ≤ projRadiusG b g u := by
  rw [b.dot_expand u (p - b.center)]
  have term : ∀ m : Fin 3,
      |Q3.dot u (b.axis m) * Q3.dot (b.axis m) (p - b.center)|
        ≤ |Q3.dot u (b.axis m)| * (b.halfAlong m + g) := by
    intro m
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (le_of_lt (hp m)) (abs_nonneg _)
  unfold projRadiusG
  calc _ ≤ |Q3.dot u (b.axis 0) * Q3.dot (b.axis 0) (p - b.center)
            + Q3.dot u (b.axis 1) * Q3.dot (b.axis 1) (p - b.center)|
          + |Q3.dot u (b.axis 2) * Q3.dot (b.axis 2) (p - b.center)| := abs_add_le _ _
    _ ≤ (|Q3.dot u (b.axis 0) * Q3.dot (b.axis 0) (p - b.center)|
          + |Q3.dot u (b.axis 1) * Q3.dot (b.axis 1) (p - b.center)|)
          + |Q3.dot u (b.axis 2) * Q3.dot (b.axis 2) (p - b.center)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith [term 0, term 1, term 2]

theorem sepAlongG_sound (g : Q) (a b : Pose) (k : Fin 3) (h : SepAlongG g a b k) :
    ∀ p, ¬ (a.InteriorGrown g p ∧ b.InteriorGrown g p) := by
  rintro p ⟨ha, hb⟩
  have hx : |a.loc k p| < a.halfAlong k + g := ha k
  have hb' := proj_boundG b g (a.axis k) p hb
  have split := dot_sub_split (a.axis k) p a.center b.center
  unfold Pose.loc at hx
  rw [split] at hx
  obtain ⟨hx1, hx2⟩ := abs_lt.mp hx
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb'
  unfold SepAlongG at h
  rcases h with h | h <;> linarith

theorem separatedG_sound (g : Q) (a b : Pose) (h : SeparatedG g a b) :
    ∀ p, ¬ (a.InteriorGrown g p ∧ b.InteriorGrown g p) := by
  rcases h with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact sepAlongG_sound g a b k hk
  · intro p hp
    exact sepAlongG_sound g b a k hk p ⟨hp.2, hp.1⟩

/-- Touch witnesses: for block `j`, a list of `(i, p)` with `i < j` and `p` in both. -/
abbrev TouchWitnesses := Array (List (Nat × Q3))

/-- The checked form of clearance for one pair `i < j`. -/
def ClearPairCheck (c : Q) (arr : Array Pose) (w : TouchWitnesses) (i j : Nat) : Prop :=
  SeparatedG (c / 2) (blkA arr i) (blkA arr j) ∨
    ∃ e ∈ w.getD j [], e.1 = i ∧ (blkA arr i).Mem e.2 ∧ (blkA arr j).Mem e.2

instance (c arr w i j) : Decidable (ClearPairCheck c arr w i j) := by
  unfold ClearPairCheck; infer_instance

def ClearanceCheck (c : Q) (arr : Array Pose) (w : TouchWitnesses) : Prop :=
  ∀ j, j < arr.size → ∀ i, i < j → ClearPairCheck c arr w i j

instance (c arr w) : Decidable (ClearanceCheck c arr w) := by
  unfold ClearanceCheck; infer_instance

theorem clearPair_symm (c : Q) (a b : Pose) (h : ClearPair c a b) : ClearPair c b a := by
  rcases h with ⟨p, ha, hb⟩ | h
  · exact Or.inl ⟨p, hb, ha⟩
  · exact Or.inr fun p hp => h p ⟨hp.2, hp.1⟩

theorem clearanceCheck_sound (H : HumanModel) (bs : List Pose) (w : TouchWitnesses)
    (h : ClearanceCheck H.clear bs.toArray w) : Clearance H bs := by
  have pair : ∀ i j, i < j → j < bs.length → ClearPair H.clear (blk bs i) (blk bs j) := by
    intro i j hij hj
    have hc := h j (by simpa using hj) i hij
    rw [ClearPairCheck, blkA_toArray, blkA_toArray] at hc
    rcases hc with hs | ⟨e, -, -, h1, h2⟩
    · exact Or.inr (separatedG_sound _ _ _ hs)
    · exact Or.inl ⟨e.2, h1, h2⟩
  intro i j hi hj hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact pair i j hlt hj
  · exact clearPair_symm _ _ _ (pair j i hlt hi)

end Kapla.Physics
