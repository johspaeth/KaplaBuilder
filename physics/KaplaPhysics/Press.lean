import KaplaPhysics.FastCheck

/-!
# KaplaPhysics.Press — four corners cover the whole top face (H4)

The loads under which a structure stands form a convex set: force certificates can be scaled
and added. Every point of a block's top face is a convex combination of its four top corners,
so certificates for a press at the four corners give one for a press anywhere on the face.
-/

namespace Kapla.Physics

open Kapla

/-! ## Combining certificates -/

def scaleF (l : Q) (fs : List PointForce) : List PointForce :=
  fs.map fun f => { f with mag := l * f.mag }

/-- Sum of a "magnitude-linear" quantity `mag · g` over a combination. `g` must not look at
`mag` (it is applied to the scaled force). -/
theorem sum_combine (ws : List (Q × Q3 × List PointForce)) (g : PointForce → Q)
    (hg : ∀ f (m : Q), g { f with mag := m } = g f) :
    ((ws.flatMap fun w => scaleF w.1 w.2.2).map fun f => f.mag * g f).sum
      = (ws.map fun w => w.1 * (w.2.2.map fun f => f.mag * g f).sum).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, ih]
    congr 1
    unfold scaleF
    generalize w.2.2 = fs
    induction fs with
    | nil => simp
    | cons f fs ih2 => simp only [List.map_cons, List.sum_cons, ih2, hg]; ring

theorem forceOK_scale (bs : List Pose) (f : PointForce) (l : Q) (hl : 0 ≤ l)
    (h : ForceOK bs f) : ForceOK bs { f with mag := l * f.mag } := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨mul_nonneg hl h1, h2, h3, h4⟩

theorem sum_map_sub' {α : Type} (l : List α) (f g : α → Q) :
    (l.map fun a => f a - g a).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Weighted sums of the per-certificate equations. -/
private theorem wsum_eq (ws : List (Q × Q3 × List PointForce)) (a b : (Q × Q3 × List PointForce) → Q)
    (h : ∀ w ∈ ws, a w = b w) :
    (ws.map fun w => w.1 * a w).sum = (ws.map fun w => w.1 * b w).sum := by
  congr 1
  exact List.map_congr_left fun w hw => by rw [h w hw]

/-- **Convexity.** Certificates for single loads of size `m` on block `i` at points `c_w`
combine (weights `λ_w ≥ 0` summing to 1) into a certificate for the load at `Σ λ_w c_w`. -/
theorem combine (bs : List Pose) (i : Nat) (m : Q) (p : Q3)
    (ws : List (Q × Q3 × List PointForce))
    (hnn : ∀ w ∈ ws, 0 ≤ w.1) (hsum : (ws.map (·.1)).sum = 1)
    (hx : (ws.map fun w => w.1 * w.2.1.x).sum = p.x)
    (hy : (ws.map fun w => w.1 * w.2.1.y).sum = p.y)
    (hok : ∀ w ∈ ws, ForcesOK bs [⟨i, w.2.1, m⟩] w.2.2) :
    ForcesOK bs [⟨i, p, m⟩] (ws.flatMap fun w => scaleF w.1 w.2.2) := by
  constructor
  · intro f hf
    simp only [List.mem_flatMap, scaleF, List.mem_map] at hf
    obtain ⟨w, hw, g, hg, rfl⟩ := hf
    exact forceOK_scale bs g w.1 (hnn w hw) ((hok w hw).1 g hg)
  · intro k hk
    have e := fun w (hw : w ∈ ws) => (hok w hw).2 k hk
    let c := (blk bs k).center
    let L : Q := loadOn k ⟨i, p, m⟩
    have hL : ∀ q : Q3, loadOn k ⟨i, q, m⟩ = L := fun _ => rfl
    -- rewrite every spec sum as `Σ mag · g`
    have rz : ∀ fs : List PointForce, (fs.map fun f => sgn k f * f.mag)
        = fs.map fun f => f.mag * sgn k f := fun fs => by
      congr 1; funext f; ring
    have rx : ∀ fs : List PointForce, (fs.map fun f => sgn k f * f.mag * (f.pt.x - c.x))
        = fs.map fun f => f.mag * (sgn k f * (f.pt.x - c.x)) := fun fs => by
      congr 1; funext f; ring
    have ry : ∀ fs : List PointForce, (fs.map fun f => sgn k f * f.mag * (f.pt.y - c.y))
        = fs.map fun f => f.mag * (sgn k f * (f.pt.y - c.y)) := fun fs => by
      congr 1; funext f; ring
    have sumL : ∀ (v : Q), (ws.map fun w => w.1 * v).sum = v := fun v => by
      rw [List.sum_map_mul_right, hsum, one_mul]
    refine ⟨?_, ?_, ?_⟩
    · unfold netFz
      rw [rz, sum_combine _ _ (fun _ _ => rfl)]
      rw [wsum_eq ws _ (fun _ => L + Block.weight) (fun w hw => by
        have := (e w hw).1; unfold netFz at this; rw [rz] at this
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          hL] at this; linarith)]
      rw [sumL]; simp [L]
    · unfold netMx
      rw [rx, sum_combine _ _ (fun _ _ => rfl)]
      rw [wsum_eq ws _ (fun w => L * (w.2.1.x - c.x)) (fun w hw => by
        have := (e w hw).2.1; unfold netMx at this; rw [rx] at this
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          hL] at this; linarith)]
      have : (ws.map fun w => w.1 * (L * (w.2.1.x - c.x))).sum
          = L * (ws.map fun w => w.1 * w.2.1.x).sum - (L * c.x) * (ws.map (·.1)).sum := by
        rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, ← sum_map_sub']
        congr 1; apply List.map_congr_left; intro w _; ring
      rw [this, hx, hsum]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, L, c]
      ring
    · unfold netMy
      rw [ry, sum_combine _ _ (fun _ _ => rfl)]
      rw [wsum_eq ws _ (fun w => L * (w.2.1.y - c.y)) (fun w hw => by
        have := (e w hw).2.2; unfold netMy at this; rw [ry] at this
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          hL] at this; linarith)]
      have : (ws.map fun w => w.1 * (L * (w.2.1.y - c.y))).sum
          = L * (ws.map fun w => w.1 * w.2.1.y).sum - (L * c.y) * (ws.map (·.1)).sum := by
        rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, ← sum_map_sub']
        congr 1; apply List.map_congr_left; intro w _; ring
      rw [this, hy, hsum]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, L, c]
      ring

/-! ## The top face is the convex hull of its corners -/

def cornerSigns : Fin 4 → Q × Q
  | 0 => (-1, -1) | 1 => (1, -1) | 2 => (1, 1) | 3 => (-1, 1)

/-- Top corner `j` of a block. -/
def topCorner (b : Pose) (j : Fin 4) : Q3 :=
  b.toWorld ⟨(cornerSigns j).1 * b.half.x, (cornerSigns j).2 * b.half.y, b.half.z⟩

/-- Bilinear weight of corner `j` for the point `p`. -/
def cornerWeight (b : Pose) (p : Q3) (j : Fin 4) : Q :=
  (b.half.x + (cornerSigns j).1 * b.loc 0 p) * (b.half.y + (cornerSigns j).2 * b.loc 1 p)
    / (4 * b.half.x * b.half.y)

theorem loc_x (b : Pose) (p : Q3) :
    p.x = b.center.x + b.loc 0 p * b.rot.c - b.loc 1 p * b.rot.s := by
  have := b.dot_expand ⟨1, 0, 0⟩ (p - b.center)
  simp only [Pose.loc, Pose.axis, Pose.e1, Pose.e2, Pose.e3, Q3.dot, Q3.sub_x, Q3.sub_y,
    Q3.sub_z] at this ⊢
  linarith

theorem loc_y (b : Pose) (p : Q3) :
    p.y = b.center.y + b.loc 0 p * b.rot.s + b.loc 1 p * b.rot.c := by
  have := b.dot_expand ⟨0, 1, 0⟩ (p - b.center)
  simp only [Pose.loc, Pose.axis, Pose.e1, Pose.e2, Pose.e3, Q3.dot, Q3.sub_x, Q3.sub_y,
    Q3.sub_z] at this ⊢
  linarith

/-- The four corners with their weights, as a combination list. -/
def cornerCombo (b : Pose) (p : Q3) (fs : Fin 4 → List PointForce) :
    List (Q × Q3 × List PointForce) :=
  [0, 1, 2, 3].map fun j => (cornerWeight b p j, topCorner b j, fs j)

theorem press_from_corners (bs : List Pose) (i : Nat) (m : Q) (b : Pose) (p : Q3)
    (_hb : b = blk bs i) (hp : b.OnTop p) (fs : Fin 4 → List PointForce)
    (hok : ∀ j, ForcesOK bs [⟨i, topCorner b j, m⟩] (fs j)) :
    Equilibrium bs [⟨i, p, m⟩] := by
  obtain ⟨hxpos, hypos, -⟩ := b.up.half_pos
  have hx0 : b.half.x ≠ 0 := ne_of_gt hxpos
  have hy0 : b.half.y ≠ 0 := ne_of_gt hypos
  obtain ⟨-, hu, hv⟩ := And.intro hp.1 hp.2
  obtain ⟨hu1, hu2⟩ := abs_le.mp hu
  obtain ⟨hv1, hv2⟩ := abs_le.mp hv
  have hw : ∀ j, 0 ≤ cornerWeight b p j := by
    intro j
    unfold cornerWeight
    apply div_nonneg
    · apply mul_nonneg <;> fin_cases j <;> simp [cornerSigns, Pose.half] at * <;> linarith
    · exact mul_nonneg (mul_nonneg (by norm_num) hxpos.le) hypos.le
  refine ⟨_, combine bs i m p (cornerCombo b p fs) ?_ ?_ ?_ ?_ ?_⟩
  · intro w hw'
    simp only [cornerCombo, List.mem_map] at hw'
    obtain ⟨j, -, rfl⟩ := hw'
    exact hw j
  · simp only [cornerCombo, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      cornerWeight, cornerSigns]
    field_simp
    ring
  · rw [loc_x b p]
    simp only [cornerCombo, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      cornerWeight, cornerSigns, topCorner, Pose.toWorld, Pose.e1, Pose.e2, Pose.e3,
      Q3.add_x, Q3.smul_x]
    field_simp
    ring
  · rw [loc_y b p]
    simp only [cornerCombo, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      cornerWeight, cornerSigns, topCorner, Pose.toWorld, Pose.e1, Pose.e2, Pose.e3,
      Q3.add_y, Q3.smul_y]
    field_simp
    ring
  · intro w hw'
    simp only [cornerCombo, List.mem_map] at hw'
    obtain ⟨j, -, rfl⟩ := hw'
    exact hok j

end Kapla.Physics
