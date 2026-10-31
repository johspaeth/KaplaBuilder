import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Lean.Data.Json

/-!
# KaplaCore.Basic

Exact rational numbers and 3-vectors, plus their JSON codecs.

All lengths are exact rational millimetres (`Q = ℚ`). In JSON a rational is written either
as a JSON number (decoded *exactly*, e.g. `23.4` is `117/5`) or as a string `"117/5"`.
Rationals are encoded as a JSON number when they are integers and as `"n/d"` otherwise, so
round trips are exact.
-/

namespace Kapla

open Lean

/-- Exact rationals: the only number type used by the trusted spec. -/
abbrev Q := ℚ

/-! ## JSON for rationals -/

/-- Parse a string such as `"117/5"`, `"-3"`, or `"23.4"` into an exact rational. -/
def parseQ (s : String) : Except String Q := do
  let s := s.trimAscii.toString
  match s.splitOn "/" with
  | [n, d] =>
    let some n := n.trimAscii.toString.toInt? | throw s!"bad numerator in '{s}'"
    let some d := d.trimAscii.toString.toNat? | throw s!"bad denominator in '{s}'"
    if d = 0 then throw s!"zero denominator in '{s}'"
    return (n : Q) / (d : Q)
  | [x] =>
    match Json.parse x with
    | .ok (.num n) => return (n.mantissa : Q) / (10 ^ n.exponent : ℕ)
    | _ => throw s!"not a rational: '{s}'"
  | _ => throw s!"not a rational: '{s}'"

instance : ToJson Q where
  toJson q :=
    if q.den = 1 then .num (JsonNumber.fromInt q.num)
    else .str s!"{q.num}/{q.den}"

instance : FromJson Q where
  fromJson?
    | .num n => .ok ((n.mantissa : Q) / (10 ^ n.exponent : ℕ))
    | .str s => parseQ s
    | j => .error s!"expected a rational, got {j.compress}"

/-- Lossy conversion for display only (never used by the checker). -/
def Q.toFloat (q : Q) : Float := Float.ofInt q.num / q.den.toFloat

/-! ## 3-vectors -/

/-- A point or vector in ℚ³ (millimetres). `z` points up; the ground is `z = 0`. -/
structure Q3 where
  x : Q
  y : Q
  z : Q
  deriving DecidableEq, Repr, Inhabited

namespace Q3

instance : Add Q3 := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩⟩
instance : Sub Q3 := ⟨fun a b => ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩⟩
instance : Neg Q3 := ⟨fun a => ⟨-a.x, -a.y, -a.z⟩⟩
instance : HMul Q Q3 Q3 := ⟨fun k a => ⟨k * a.x, k * a.y, k * a.z⟩⟩

@[simp] theorem add_x (a b : Q3) : (a + b).x = a.x + b.x := rfl
@[simp] theorem add_y (a b : Q3) : (a + b).y = a.y + b.y := rfl
@[simp] theorem add_z (a b : Q3) : (a + b).z = a.z + b.z := rfl
@[simp] theorem sub_x (a b : Q3) : (a - b).x = a.x - b.x := rfl
@[simp] theorem sub_y (a b : Q3) : (a - b).y = a.y - b.y := rfl
@[simp] theorem sub_z (a b : Q3) : (a - b).z = a.z - b.z := rfl

@[simp] theorem smul_x (k : Q) (a : Q3) : (k * a).x = k * a.x := rfl
@[simp] theorem smul_y (k : Q) (a : Q3) : (k * a).y = k * a.y := rfl
@[simp] theorem smul_z (k : Q) (a : Q3) : (k * a).z = k * a.z := rfl

def zero : Q3 := ⟨0, 0, 0⟩

/-- Dot product. -/
def dot (a b : Q3) : Q := a.x * b.x + a.y * b.y + a.z * b.z

def toFloats (a : Q3) : Array Float := #[a.x.toFloat, a.y.toFloat, a.z.toFloat]

instance : ToJson Q3 := ⟨fun a => toJson [a.x, a.y, a.z]⟩
instance : FromJson Q3 where
  fromJson? j := do
    match (← fromJson? j : List Q) with
    | [x, y, z] => return ⟨x, y, z⟩
    | _ => throw "expected [x, y, z]"

end Q3

/-- A point in the horizontal plane. -/
structure Q2 where
  x : Q
  y : Q
  deriving DecidableEq, Repr, Inhabited

instance : ToJson Q2 := ⟨fun a => toJson [a.x, a.y]⟩
instance : FromJson Q2 where
  fromJson? j := do
    match (← fromJson? j : List Q) with
    | [x, y] => return ⟨x, y⟩
    | _ => throw "expected [x, y]"

end Kapla
