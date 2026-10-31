import KaplaPhysics.Spec

/-!
# KaplaPhysics.Separation — exact separating-axis test, proven sound

Two blocks are certified disjoint (in their interiors) when one of the six face axes
separates them. The test is exact in ℚ: the half-width of block `b` projected on a unit
axis `u` is `Σₘ |u·bₘ| hₘ`, a rational number. For yaw-only blocks (common vertical axis)
the six face axes are also *complete*: any two such boxes with disjoint interiors are
separated by one of them, so touching blocks are never rejected.
-/

namespace Kapla.Physics

open Kapla

/-- Projected half-width of block `b` on direction `u`. -/
def projRadius (b : Pose) (u : Q3) : Q :=
  |Q3.dot u (b.axis 0)| * b.halfAlong 0 + |Q3.dot u (b.axis 1)| * b.halfAlong 1
    + |Q3.dot u (b.axis 2)| * b.halfAlong 2

/-- Axis `k` of block `a` separates `a` from `b`. -/
def SepAlong (a b : Pose) (k : Fin 3) : Prop :=
  let u := a.axis k
  let a0 := Q3.dot u (b.center - a.center)
  a.halfAlong k ≤ a0 - projRadius b u ∨ a0 + projRadius b u ≤ -a.halfAlong k

instance (a b : Pose) (k : Fin 3) : Decidable (SepAlong a b k) := by
  unfold SepAlong; infer_instance

def Separated (a b : Pose) : Prop := (∃ k, SepAlong a b k) ∨ (∃ k, SepAlong b a k)

instance (a b : Pose) : Decidable (Separated a b) := by unfold Separated; infer_instance

theorem dot_sub_split (u p ca cb : Q3) :
    Q3.dot u (p - ca) = Q3.dot u (cb - ca) + Q3.dot u (p - cb) := by
  simp only [Q3.dot, Q3.sub_x, Q3.sub_y, Q3.sub_z]; ring

/-- Points inside `b` project within `projRadius` of `b`'s centre. -/
theorem proj_bound (b : Pose) (u p : Q3) (hp : b.Interior p) :
    |Q3.dot u (p - b.center)| ≤ projRadius b u := by
  rw [b.dot_expand u (p - b.center)]
  have term : ∀ m : Fin 3,
      |Q3.dot u (b.axis m) * Q3.dot (b.axis m) (p - b.center)|
        ≤ |Q3.dot u (b.axis m)| * b.halfAlong m := by
    intro m
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (le_of_lt (hp m)) (abs_nonneg _)
  unfold projRadius
  calc _ ≤ |Q3.dot u (b.axis 0) * Q3.dot (b.axis 0) (p - b.center)
            + Q3.dot u (b.axis 1) * Q3.dot (b.axis 1) (p - b.center)|
          + |Q3.dot u (b.axis 2) * Q3.dot (b.axis 2) (p - b.center)| := abs_add_le _ _
    _ ≤ (|Q3.dot u (b.axis 0) * Q3.dot (b.axis 0) (p - b.center)|
          + |Q3.dot u (b.axis 1) * Q3.dot (b.axis 1) (p - b.center)|)
          + |Q3.dot u (b.axis 2) * Q3.dot (b.axis 2) (p - b.center)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith [term 0, term 1, term 2]

theorem sepAlong_sound (a b : Pose) (k : Fin 3) (h : SepAlong a b k) :
    ∀ p, ¬ (a.Interior p ∧ b.Interior p) := by
  rintro p ⟨ha, hb⟩
  have hx : |a.loc k p| < a.halfAlong k := ha k
  have hb' := proj_bound b (a.axis k) p hb
  have split := dot_sub_split (a.axis k) p a.center b.center
  unfold Pose.loc at hx
  rw [split] at hx
  obtain ⟨hx1, hx2⟩ := abs_lt.mp hx
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb'
  unfold SepAlong at h
  rcases h with h | h <;> linarith

/-- **Separating-axis soundness.** -/
theorem separated_sound (a b : Pose) (h : Separated a b) :
    ∀ p, ¬ (a.Interior p ∧ b.Interior p) := by
  rcases h with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact sepAlong_sound a b k hk
  · intro p hp
    exact sepAlong_sound b a k hk p ⟨hp.2, hp.1⟩

/-- Every pair `i < j` is certified separated. -/
def PairsSeparated (bs : List Pose) : Prop :=
  ∀ j, j < bs.length → ∀ i, i < j → Separated (blk bs i) (blk bs j)

instance (bs : List Pose) : Decidable (PairsSeparated bs) := by
  unfold PairsSeparated; infer_instance

theorem pairsSeparated_sound (bs : List Pose) (h : PairsSeparated bs) : NonOverlap bs := by
  intro i j hi hj hne p
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact separated_sound _ _ (h j hj i hlt) p
  · intro hp
    exact separated_sound _ _ (h i hi j hlt) p ⟨hp.2, hp.1⟩

end Kapla.Physics
