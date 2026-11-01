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
  if m / 2 % 2 = 0 then Plank.at .flatX 0 side z else Plank.at .flatY side 0 z

/-- E8. The square tower with `n` levels, in building order: level by level, two planks
per level. -/
def squareTower (n : Nat) : Build := (List.range (2 * n)).map towerPlank

/-- Example: two levels. -/
example : squareTower 2 =
    [Plank.at .flatX 0 0 0, Plank.at .flatX 0 12 0, Plank.at .flatY 0 0 1,
      Plank.at .flatY 12 0 1] := by
  decide +kernel

/-- E19. The square tower with `n` levels, turned as a whole by `r` about the vertical line
through the origin. With `r = Rot.deg45`, every plank is turned by about 45° or 135°. -/
def turnedTower (r : KaplaCore.Rot) (n : Nat) : Build := (squareTower n).map (·.turn r)

/-- Example: the first plank of the tower turned by 45° has its centre where the turn puts
(7.5, 1.5), and it is turned by 45° itself. -/
example : (turnedTower .deg45 1).get 0 =
    ⟨.flat, .deg45, ⟨(119 * 15 / 2 - 120 * 3 / 2) / 169, (120 * 15 / 2 + 119 * 3 / 2) / 169, 1 / 2⟩⟩ := by
  decide +kernel

end KaplaPhysics
