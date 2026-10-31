/-! # Planks and space (rules W1–W3, B1–B5 of `spec/physics-rules.md`)

One unit is the thickness of a plank (7.8 mm). All numbers are exact fractions (`Rat`). -/

namespace KaplaPhysics

/-- The size of a box along `x`, `y` and `z`. -/
structure Size where
  dx : Rat
  dy : Rat
  dz : Rat
  deriving Repr, DecidableEq

/-- B4. The six ways to place a plank. Its sides are always parallel to the axes. -/
inductive Pose where
  /-- Flat, long side along `x`: 15 × 3 × 1. -/
  | flatX
  /-- Flat, long side along `y`: 3 × 15 × 1. -/
  | flatY
  /-- On edge, long side along `x`: 15 × 1 × 3. -/
  | edgeX
  /-- On edge, long side along `y`: 1 × 15 × 3. -/
  | edgeY
  /-- Standing, wide side facing `y`: 3 × 1 × 15. -/
  | standFacingY
  /-- Standing, wide side facing `x`: 1 × 3 × 15. -/
  | standFacingX
  deriving Repr, DecidableEq, Inhabited

/-- B1, B4. The size of a plank in each pose (length 15, width 3, thickness 1). -/
def Pose.size : Pose → Size
  | .flatX        => ⟨15, 3, 1⟩
  | .flatY        => ⟨3, 15, 1⟩
  | .edgeX        => ⟨15, 1, 3⟩
  | .edgeY        => ⟨1, 15, 3⟩
  | .standFacingY => ⟨3, 1, 15⟩
  | .standFacingX => ⟨1, 3, 15⟩

example : Pose.flatX.size = ⟨15, 3, 1⟩ := rfl

/-- B5. A plank: its pose and the corner with the smallest `x`, `y` and `z`. -/
structure Plank where
  pose : Pose
  x : Rat
  y : Rat
  z : Rat
  deriving Repr, DecidableEq, Inhabited

namespace Plank

/-- Far end of the plank along `x`. -/
def x1 (p : Plank) : Rat := p.x + p.pose.size.dx
/-- Far end of the plank along `y`. -/
def y1 (p : Plank) : Rat := p.y + p.pose.size.dy
/-- Height of the plank's top face. -/
def top (p : Plank) : Rat := p.z + p.pose.size.dz

/-- B2. `x` of the plank's centre (its balance point). -/
def centerX (p : Plank) : Rat := p.x + p.pose.size.dx / 2
/-- B2. `y` of the plank's centre (its balance point). -/
def centerY (p : Plank) : Rat := p.y + p.pose.size.dy / 2

/-- Example: a flat plank along `x` at the origin has its centre at (7.5, 1.5). -/
example : (Plank.mk .flatX 0 0 0).centerX = 15 / 2 := by decide +kernel

end Plank

/-- An upright rectangle in the horizontal plane, from `(x0, y0)` to `(x1, y1)`. -/
structure Rect where
  x0 : Rat
  x1 : Rat
  y0 : Rat
  y1 : Rat
  deriving Repr, DecidableEq, Inhabited

namespace Rect

/-- The rectangle where two rectangles overlap. It may be empty or flat. -/
def inter (r s : Rect) : Rect := ⟨max r.x0 s.x0, min r.x1 s.x1, max r.y0 s.y0, min r.y1 s.y1⟩

/-- The rectangle has an area bigger than zero (it is not empty, a line or a point). -/
def HasArea (r : Rect) : Prop := r.x0 < r.x1 ∧ r.y0 < r.y1

instance (r : Rect) : Decidable r.HasArea := by unfold HasArea; infer_instance

/-- The point `(x, y)` lies in the rectangle (edges included). -/
def Contains (r : Rect) (x y : Rat) : Prop := r.x0 ≤ x ∧ x ≤ r.x1 ∧ r.y0 ≤ y ∧ y ≤ r.y1

/-- The four corners of the rectangle. -/
def corners (r : Rect) : List (Rat × Rat) :=
  [(r.x0, r.y0), (r.x1, r.y0), (r.x0, r.y1), (r.x1, r.y1)]

/-- Example: two rectangles that share only an edge have no area in common (C3). -/
example : ¬ (inter ⟨0, 1, 0, 1⟩ ⟨1, 2, 0, 1⟩).HasArea := by decide +kernel

end Rect

/-- The rectangle a plank covers when seen from above. -/
def Plank.footprint (p : Plank) : Rect := ⟨p.x, p.x1, p.y, p.y1⟩

/-- A build: the planks in the order they are placed. Planks are named by their position
in this list (0, 1, 2, ...). -/
abbrev Build := List Plank

/-- Plank number `i` of the build (a dummy plank if there is none). -/
def Build.get (b : Build) (i : Nat) : Plank := b.getD i default

end KaplaPhysics
