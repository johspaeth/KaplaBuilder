import KaplaCore

/-! # Planks and space (rules W1–W3, B1–B6 of `spec/physics-rules.md`)

One unit is the thickness of a plank (7.8 mm). All numbers are exact fractions (`Rat`).

A plank is a KaplaCore block (`KaplaCore.Pose`): which face is down, how it is turned about
the vertical axis, and where its centre is. Planks are never tilted, so the bottom and the
top of a plank are flat. -/

namespace KaplaCore.Rot

/-- B6. The turns a plank may have:
1. it is a real turn: `cos² + sin² = 1`, and
2. it is a quarter turn (`sin²` is 0 or 1), or close to 30°, 45° or 60° or one of their
   mirror images: `sin²` is within `1/200` of `1/4`, `1/2` or `3/4` (about ±0.3°).

The exact angles 30°, 45°, 60° are not fractions, so turns close to them are allowed
(for example `Rot.deg45`, 45.24°). -/
def Allowed (r : Rot) : Prop :=
  r.cos * r.cos + r.sin * r.sin = 1 ∧
    (r.sin * r.sin = 0 ∨ r.sin * r.sin = 1 ∨ near (1 / 4) ∨ near (1 / 2) ∨ near (3 / 4))
where
  /-- `sin²` is within `1/200` of `t`. -/
  near (t : Rat) : Prop := t - 1 / 200 ≤ r.sin * r.sin ∧ r.sin * r.sin ≤ t + 1 / 200

instance (r : Rot) : Decidable r.Allowed := by
  unfold Allowed Allowed.near; infer_instance

/-- Example: the quarter turn and the three named turns are allowed. -/
example : Rot.quarter.Allowed ∧ Rot.deg30.Allowed ∧ Rot.deg45.Allowed ∧ Rot.deg60.Allowed := by
  decide +kernel

/-- Example: a turn by the 3-4-5 angle (36.87°) is not allowed, and neither is a "turn"
that also stretches. -/
example : ¬ (Rot.ofTriple 3 4 5).Allowed ∧ ¬ (Rot.mk 1 1).Allowed := by decide +kernel

end KaplaCore.Rot

namespace KaplaPhysics

open KaplaCore (Rot Upright Q3)

/-- B1, B5. A plank: a KaplaCore block. -/
abbrev Plank := KaplaCore.Pose

end KaplaPhysics

/-! The definitions about one plank live next to the block type, in `KaplaCore.Pose`, so
that `p.bottom`, `p.Covers x y`, ... work for every plank `p`. -/

namespace KaplaCore.Pose

open KaplaPhysics (Plank)

/-- B1, B4. The plank's size along its own length, its own width, and up: 15 × 3 × 1
lying flat, 15 × 1 × 3 on edge, 3 × 1 × 15 standing. -/
def size (p : Plank) : Q3 := p.up.dims

/-- B2. `x` of the plank's centre (its balance point). -/
def centerX (p : Plank) : Rat := p.center.x
/-- B2. `y` of the plank's centre. -/
def centerY (p : Plank) : Rat := p.center.y
/-- Height of the plank's centre. -/
def centerZ (p : Plank) : Rat := p.center.z

/-- Height of the plank's bottom face. -/
def bottom (p : Plank) : Rat := p.center.z - p.size.z / 2
/-- Height of the plank's top face. -/
def top (p : Plank) : Rat := p.center.z + p.size.z / 2

/-- How far the point `(x, y)` is from the plank's centre, measured along the plank's own
length (its turned `x` axis). -/
def alongLength (p : Plank) (x y : Rat) : Rat :=
  p.rot.cos * (x - p.center.x) + p.rot.sin * (y - p.center.y)

/-- How far the point `(x, y)` is from the plank's centre, measured along the plank's own
width (its turned `y` axis). -/
def alongWidth (p : Plank) (x y : Rat) : Rat :=
  -p.rot.sin * (x - p.center.x) + p.rot.cos * (y - p.center.y)

/-- B3. Seen from above, the point `(x, y)` is under the plank, edges included: it is at
most half the length from the centre along the length, and at most half the width along
the width. -/
def Covers (p : Plank) (x y : Rat) : Prop :=
  -p.size.x ≤ 2 * p.alongLength x y ∧ 2 * p.alongLength x y ≤ p.size.x ∧
    -p.size.y ≤ 2 * p.alongWidth x y ∧ 2 * p.alongWidth x y ≤ p.size.y

/-- Seen from above, the point `(x, y)` is strictly inside the plank (not on an edge). -/
def CoversInside (p : Plank) (x y : Rat) : Prop :=
  -p.size.x < 2 * p.alongLength x y ∧ 2 * p.alongLength x y < p.size.x ∧
    -p.size.y < 2 * p.alongWidth x y ∧ 2 * p.alongWidth x y < p.size.y

instance (p : Plank) (x y : Rat) : Decidable (p.Covers x y) := by
  unfold Covers; infer_instance

instance (p : Plank) (x y : Rat) : Decidable (p.CoversInside x y) := by
  unfold CoversInside; infer_instance

/-- The plank moved by `dx`, `dy`, `dz`. -/
def moveBy (p : Plank) (dx dy dz : Rat) : Plank :=
  { p with center := ⟨p.center.x + dx, p.center.y + dy, p.center.z + dz⟩ }

/-- The plank turned by `r` about the vertical line through the origin: its centre turns
along, and so does its direction. -/
def turn (r : Rot) (p : Plank) : Plank :=
  { p with rot := r.comp p.rot, center := r.apply p.center }

/-- Example: a flat block turned by 45° covers a point 7 along its length from its centre,
but not one 2 along its width. -/
example : (⟨.flat, .deg45, ⟨0, 0, 1 / 2⟩⟩ : Plank).Covers (7 * 119 / 169) (7 * 120 / 169) ∧
    ¬ (⟨.flat, .deg45, ⟨0, 0, 1 / 2⟩⟩ : Plank).Covers (-2 * 120 / 169) (2 * 119 / 169) := by
  decide +kernel

end KaplaCore.Pose

namespace KaplaPhysics

open KaplaCore (Rot Upright Q3 Pose)

/-! ## Planks with sides along the axes

Most examples use planks whose sides are along the axes. They are easier to write down by
their lowest corner, as before. -/

/-- B4. The six ways to place a plank with its sides along the axes. -/
inductive AxisPose where
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

namespace AxisPose

/-- Which face is down. -/
def up : AxisPose → Upright
  | .flatX | .flatY => .flat
  | .edgeX | .edgeY => .onEdge
  | .standFacingY | .standFacingX => .standing

/-- No turn, or a quarter turn. -/
def rot : AxisPose → Rot
  | .flatX | .edgeX | .standFacingY => .id
  | .flatY | .edgeY | .standFacingX => .quarter

/-- The size along `x`, `y` and `z`. -/
def size : AxisPose → Q3
  | .flatX        => ⟨15, 3, 1⟩
  | .flatY        => ⟨3, 15, 1⟩
  | .edgeX        => ⟨15, 1, 3⟩
  | .edgeY        => ⟨1, 15, 3⟩
  | .standFacingY => ⟨3, 1, 15⟩
  | .standFacingX => ⟨1, 3, 15⟩

end AxisPose

/-- The plank in pose `q` whose corner with the smallest `x`, `y` and `z` is `(x, y, z)`. -/
def Plank.at (q : AxisPose) (x y z : Rat) : Plank :=
  ⟨q.up, q.rot, ⟨x + q.size.x / 2, y + q.size.y / 2, z + q.size.z / 2⟩⟩

/-- Example: a flat plank along `x` at the origin has its centre at (7.5, 1.5, 0.5). -/
example : Plank.at .flatX 0 0 0 = ⟨.flat, .id, ⟨15 / 2, 3 / 2, 1 / 2⟩⟩ := by decide +kernel

/-- A plank placed by its lowest corner covers exactly the points of its box seen from
above (edges included). -/
theorem Plank.at_covers (q : AxisPose) (x y z px py : Rat) :
    (Plank.at q x y z).Covers px py ↔
      x ≤ px ∧ px ≤ x + q.size.x ∧ y ≤ py ∧ py ≤ y + q.size.y := by
  cases q <;>
    simp only [Plank.at, Pose.Covers, Pose.alongLength, Pose.alongWidth, Pose.size,
      AxisPose.up, AxisPose.rot, AxisPose.size, Rot.id, Rot.quarter, Upright.dims,
      KaplaCore.blockLength, KaplaCore.blockWidth, KaplaCore.blockThickness] <;> grind

/-- The same, strictly inside. -/
theorem Plank.at_coversInside (q : AxisPose) (x y z px py : Rat) :
    (Plank.at q x y z).CoversInside px py ↔
      x < px ∧ px < x + q.size.x ∧ y < py ∧ py < y + q.size.y := by
  cases q <;>
    simp only [Plank.at, Pose.CoversInside, Pose.alongLength, Pose.alongWidth, Pose.size,
      AxisPose.up, AxisPose.rot, AxisPose.size, Rot.id, Rot.quarter, Upright.dims,
      KaplaCore.blockLength, KaplaCore.blockWidth, KaplaCore.blockThickness] <;> grind

/-- The bottom of a plank placed by its lowest corner is at that corner's height. -/
theorem Plank.at_bottom (q : AxisPose) (x y z : Rat) : (Plank.at q x y z).bottom = z := by
  cases q <;> simp only [Plank.at, Pose.bottom, Pose.size, AxisPose.up, AxisPose.size,
    Upright.dims, KaplaCore.blockLength, KaplaCore.blockWidth, KaplaCore.blockThickness] <;>
    grind

/-- The top of a plank placed by its lowest corner is its height above that corner. -/
theorem Plank.at_top (q : AxisPose) (x y z : Rat) : (Plank.at q x y z).top = z + q.size.z := by
  cases q <;> simp only [Plank.at, Pose.top, Pose.size, AxisPose.up, AxisPose.size,
    Upright.dims, KaplaCore.blockLength, KaplaCore.blockWidth, KaplaCore.blockThickness] <;>
    grind

/-- Moving a plank placed by its lowest corner moves the corner. -/
theorem Plank.at_moveBy (q : AxisPose) (x y z dx dy dz : Rat) :
    (Plank.at q x y z).moveBy dx dy dz = Plank.at q (x + dx) (y + dy) (z + dz) := by
  simp only [Plank.at, Pose.moveBy, KaplaCore.Pose.mk.injEq, KaplaCore.Q3.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- A build: the planks in the order they are placed. Planks are named by their position
in this list (0, 1, 2, ...). -/
abbrev Build := List Plank

/-- Plank number `i` of the build (a dummy plank if there is none). -/
def Build.get (b : Build) (i : Nat) : Plank := b.getD i default

end KaplaPhysics
