import KaplaCore.Num
import Mathlib

/-!
# KaplaCore.Geometry

Basic geometry shared by every component (DESIGN §3):

* `Rot`: an exact rotation about the vertical axis, `(cos, sin) ∈ ℚ²` with `c² + s² = 1`.
  Every such rotation is "Pythagorean": `c = (1-t²)/(1+t²)`, `s = 2t/(1+t²)` for rational
  `t = tan(θ/2)`, and these angles are dense, so any angle is approximated arbitrarily well.
* `Upright`: how the block lies (flat, on edge, upright).
* `Pose`: orientation + yaw + centre. Corners, local coordinates, membership.

v1 (M1–M2) only allows yaw rotations; tilted poses (roofs, M3) will extend `Pose`.
-/

namespace Kapla

open Lean

/-! ## Block dimensions: 7.8 × 23.4 × 117 mm (1 : 3 : 15) -/

namespace Block
/-- Long side, mm. -/
def L : Q := 117
/-- Width, mm (23.4). -/
def W : Q := 117 / 5
/-- Thickness, mm (7.8). -/
def T : Q := 39 / 5
/-- Every block has weight 1 (forces are measured in block weights). -/
def weight : Q := 1
end Block

/-! ## Rotations about the vertical axis -/

/-- An exact rotation about `z`: `(c, s) = (cos θ, sin θ)` with `c² + s² = 1` in ℚ. -/
structure Rot where
  c : Q
  s : Q
  unit : c * c + s * s = 1

namespace Rot

instance : DecidableEq Rot := fun a b =>
  if h : a.c = b.c ∧ a.s = b.s then
    isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

instance : Repr Rot := ⟨fun r _ => s!"Rot(c := {r.c}, s := {r.s})"⟩

def id : Rot := ⟨1, 0, by norm_num⟩
instance : Inhabited Rot := ⟨id⟩

/-- Quarter turn (90°). -/
def quarter : Rot := ⟨0, 1, by norm_num⟩

/-- Composition of rotations (angles add). Stays exact. -/
def mul (a b : Rot) : Rot :=
  ⟨a.c * b.c - a.s * b.s, a.s * b.c + a.c * b.s, by
    linear_combination (b.c * b.c + b.s * b.s) * a.unit + b.unit⟩

/-- The Pythagorean rotation with `tan(θ/2) = t`. -/
def ofTanHalf (t : Q) : Rot :=
  ⟨(1 - t * t) / (1 + t * t), (2 * t) / (1 + t * t), by
    have h : (1 + t * t) ≠ 0 := ne_of_gt (by nlinarith [mul_self_nonneg t])
    field_simp
    ring⟩

/-- Display only. -/
def toDeg (r : Rot) : Float :=
  Float.atan2 r.s.toFloat r.c.toFloat * 180 / 3.141592653589793

/-- **Untrusted helper**: the Pythagorean rotation closest to `deg` degrees whose
`tan(θ/2)` has denominator at most `maxDen`. (A Stern–Brocot search would be optimal; a
scan over small denominators is plenty for building blocks.) -/
def approxDeg (deg : Float) (maxDen : Nat := 64) : Rot := Id.run do
  -- reduce to a residual in [-45°, 45°] plus a number of quarter turns
  let q := (deg / 90).round
  let resid := deg - q * 90
  let target := Float.tan (resid * 3.141592653589793 / 360)
  let mut best : Q := 0
  let mut bestErr : Float := target.abs
  for d in [1:maxDen+1] do
    let n := (target * d.toFloat).round
    let cand : Q := (Int.ofNat n.abs.toUInt64.toNat * (if n < 0 then -1 else 1) : Int) / (d : Q)
    let err := (cand.toFloat - target).abs
    if err + 1e-12 < bestErr then
      best := cand
      bestErr := err
  let base := ofTanHalf best
  let k := ((q.toInt64.toInt % 4) + 4) % 4
  let mut r := base
  for _ in [0:k.toNat] do r := mul quarter r
  return r

instance : ToJson Rot := ⟨fun r => Json.mkObj [("c", toJson r.c), ("s", toJson r.s)]⟩

instance : FromJson Rot where
  fromJson? j := do
    if let .ok t := j.getObjValAs? Q "tanHalf" then return ofTanHalf t
    if let .ok d := j.getObjValAs? Float "approxDeg" then return approxDeg d
    let c ← j.getObjValAs? Q "c"
    let s ← j.getObjValAs? Q "s"
    if h : c * c + s * s = 1 then return ⟨c, s, h⟩
    else throw s!"rotation ({c}, {s}) is not exactly orthogonal: c²+s² ≠ 1"

end Rot

/-! ## Orientation -/

/-- How a block lies. In the block frame (before yaw), the long side is along `x` for
`flat` and `edge`, and along `z` for `upright`. -/
inductive Upright where
  /-- 117 × 23.4 footprint, 7.8 tall. -/
  | flat
  /-- 117 × 7.8 footprint, 23.4 tall. -/
  | edge
  /-- 23.4 × 7.8 footprint, 117 tall. -/
  | upright
  deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

/-- Half extents `(hx, hy, hz)` of the block in its own frame. -/
def Upright.half : Upright → Q3
  | .flat => ⟨Block.L / 2, Block.W / 2, Block.T / 2⟩
  | .edge => ⟨Block.L / 2, Block.T / 2, Block.W / 2⟩
  | .upright => ⟨Block.W / 2, Block.T / 2, Block.L / 2⟩

theorem Upright.half_pos (u : Upright) : 0 < u.half.x ∧ 0 < u.half.y ∧ 0 < u.half.z := by
  cases u <;> simp [Upright.half, Block.L, Block.W, Block.T]

/-! ## Poses -/

/-- Position of one block: orientation, yaw and centre (mm). -/
structure Pose where
  up : Upright
  rot : Rot
  center : Q3
  deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

namespace Pose

def half (b : Pose) : Q3 := b.up.half

/-- World direction of the block's local `x` axis. -/
def e1 (b : Pose) : Q3 := ⟨b.rot.c, b.rot.s, 0⟩
/-- World direction of the block's local `y` axis. -/
def e2 (b : Pose) : Q3 := ⟨-b.rot.s, b.rot.c, 0⟩
/-- World direction of the block's local `z` axis (always vertical in v1). -/
def e3 (_ : Pose) : Q3 := ⟨0, 0, 1⟩

/-- Axis `k` (0, 1, 2) and the half extent along it. -/
def axis (b : Pose) : Fin 3 → Q3 | 0 => b.e1 | 1 => b.e2 | 2 => b.e3
def halfAlong (b : Pose) : Fin 3 → Q | 0 => b.half.x | 1 => b.half.y | 2 => b.half.z

/-- Coordinate of world point `p` along local axis `k`, relative to the centre. -/
def loc (b : Pose) (k : Fin 3) (p : Q3) : Q := Q3.dot (b.axis k) (p - b.center)

def bottomZ (b : Pose) : Q := b.center.z - b.half.z
def topZ (b : Pose) : Q := b.center.z + b.half.z

/-- `p` lies strictly inside the block. -/
def Interior (b : Pose) (p : Q3) : Prop := ∀ k : Fin 3, |b.loc k p| < b.halfAlong k

/-- `p` lies in the closed block. -/
def Mem (b : Pose) (p : Q3) : Prop := ∀ k : Fin 3, |b.loc k p| ≤ b.halfAlong k

instance (b : Pose) (p : Q3) : Decidable (b.Interior p) := by unfold Interior; infer_instance
instance (b : Pose) (p : Q3) : Decidable (b.Mem p) := by unfold Mem; infer_instance

/-- `p` (any height) is inside the closed footprint of the block. -/
def InFootprint (b : Pose) (p : Q3) : Prop := |b.loc 0 p| ≤ b.half.x ∧ |b.loc 1 p| ≤ b.half.y
instance (b : Pose) (p : Q3) : Decidable (b.InFootprint p) := by
  unfold InFootprint; infer_instance

/-- World point from local coordinates. -/
def toWorld (b : Pose) (l : Q3) : Q3 :=
  b.center + (l.x * b.e1 + (l.y * b.e2 + l.z * b.e3))

/-- The 8 corners. -/
def corners (b : Pose) : List Q3 := Id.run do
  let h := b.half
  let mut out := []
  for sz in [-1, 1] do
    for sy in [-1, 1] do
      for sx in [-1, 1] do
        out := out ++ [b.toWorld ⟨sx * h.x, sy * h.y, sz * h.z⟩]
  return out

/-- Footprint corners, counter-clockwise, as 2D points. -/
def footprint (b : Pose) : List Q2 :=
  let h := b.half
  [(-1, -1), (1, -1), (1, 1), (-1, 1)].map fun (sx, sy) =>
    let p := b.toWorld ⟨sx * h.x, sy * h.y, 0⟩
    ⟨p.x, p.y⟩

/-- **Frame identity.** The axes of a pose form an orthonormal basis, so any dot product
can be expanded along them. This is the only place `c² + s² = 1` is used. -/
theorem dot_expand (b : Pose) (u d : Q3) :
    Q3.dot u d = Q3.dot u (b.axis 0) * Q3.dot (b.axis 0) d
      + Q3.dot u (b.axis 1) * Q3.dot (b.axis 1) d
      + Q3.dot u (b.axis 2) * Q3.dot (b.axis 2) d := by
  have h := b.rot.unit
  simp only [Q3.dot, axis, e1, e2, e3]
  linear_combination (-(u.x * d.x) - u.y * d.y) * h

end Pose

/-- The volume of one block in mm³ (for reports). -/
def Block.volume : Q := Block.L * Block.W * Block.T

end Kapla
