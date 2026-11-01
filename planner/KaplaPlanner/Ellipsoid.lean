import KaplaCore

/-! # Ellipsoids, for the proof of the inside check

A `KaplaCore.Bubble` is an ellipsoid with its axes along x, y and z. The proof that
`insideBubbles` is correct works for any ellipsoid, also a turned one, so we state it for the
general form below and connect the two with `bubble_contains_iff`.

A point `x` is inside the ellipsoid when
`(u₁·(x − c))² + (u₂·(x − c))² + (u₃·(x − c))² ≤ 1`, where `c` is the centre. Each `uᵢ` is an
axis direction divided by the half-width along that axis. -/

namespace KaplaPlanner
open KaplaCore

/-- An ellipsoid: its centre and three vectors (axis direction divided by half-width). -/
structure Ellipsoid where
  center : Q3
  u1     : Q3
  u2     : Q3
  u3     : Q3
  deriving Repr, BEq, Inhabited

/-- The ellipsoid formula at point `p`: at most 1 inside, more than 1 outside. -/
def Ellipsoid.value (e : Ellipsoid) (p : Q3) : Q :=
  let d := p.sub e.center
  (e.u1.dot d) ^ 2 + (e.u2.dot d) ^ 2 + (e.u3.dot d) ^ 2

/-- The point `p` is inside the ellipsoid (on its surface counts too). -/
def Ellipsoid.contains (e : Ellipsoid) (p : Q3) : Prop := e.value p ≤ 1

instance (e : Ellipsoid) (p : Q3) : Decidable (e.contains p) := by
  unfold Ellipsoid.contains; infer_instance

/-- A bubble as an ellipsoid. -/
def bubbleEllipsoid (b : Bubble) : Ellipsoid :=
  ⟨b.center, ⟨1 / b.semi.x, 0, 0⟩, ⟨0, 1 / b.semi.y, 0⟩, ⟨0, 0, 1 / b.semi.z⟩⟩

/-- A bubble contains a point exactly when its half-widths are above 0 and its ellipsoid
contains the point. -/
theorem bubble_contains_iff (b : Bubble) (p : Q3) :
    b.contains p = true ↔
      (0 < b.semi.x ∧ 0 < b.semi.y ∧ 0 < b.semi.z) ∧ (bubbleEllipsoid b).contains p := by
  have key : (bubbleEllipsoid b).value p =
      (p.x - b.center.x) / b.semi.x * ((p.x - b.center.x) / b.semi.x) +
      (p.y - b.center.y) / b.semi.y * ((p.y - b.center.y) / b.semi.y) +
      (p.z - b.center.z) / b.semi.z * ((p.z - b.center.z) / b.semi.z) := by
    simp only [Ellipsoid.value, bubbleEllipsoid, Q3.dot, Q3.sub]
    grind
  simp only [Bubble.contains, Ellipsoid.contains, key, Bool.and_eq_true, decide_eq_true_eq]
  grind

-- a ball of radius 10 contains (6, 8, 0) but not (6, 8, 1)
#guard decide ((bubbleEllipsoid ⟨"b", [], ⟨0, 0, 0⟩, ⟨10, 10, 10⟩⟩).contains ⟨6, 8, 0⟩)
#guard !decide ((bubbleEllipsoid ⟨"b", [], ⟨0, 0, 0⟩, ⟨10, 10, 10⟩⟩).contains ⟨6, 8, 1⟩)

end KaplaPlanner
