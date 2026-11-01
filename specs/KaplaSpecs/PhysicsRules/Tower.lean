import KaplaSpecs.PhysicsRules.Rules

/-! # The square tower (example E8, property 9) -/

namespace KaplaPhysics

/-- E8. Plank `m` of the square tower. It sits on level `m / 2` (at height `m / 2`), and is
the first or second plank of that level.
* Even levels: flat along `x`, at `y = 0` (first) or `y = 12` (second).
* Odd levels: flat along `y`, at `x = 0` (first) or `x = 12` (second). -/
def towerPlank (m : Nat) : Plank :=
  let side : Rat := if m % 2 = 0 then 0 else 12
  let z : Rat := ((m / 2 : Nat) : Rat)
  if m / 2 % 2 = 0 then ⟨.flatX, 0, side, z⟩ else ⟨.flatY, side, 0, z⟩

/-- E8. The square tower with `n` levels, in building order: level by level, two planks
per level. -/
def squareTower (n : Nat) : Build := (List.range (2 * n)).map towerPlank

/-- Example: two levels. -/
example : squareTower 2 =
    [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 0, 12, 0⟩, ⟨.flatY, 0, 0, 1⟩, ⟨.flatY, 12, 0, 1⟩] := by
  decide +kernel

end KaplaPhysics
