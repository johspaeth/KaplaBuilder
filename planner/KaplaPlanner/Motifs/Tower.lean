import KaplaPlanner.Motif

/-! # Log-cabin tower

Each layer has two flat blocks lying parallel, at opposite sides of a square of
117 × 117 mm. Each layer is turned 90° against the one below, like the
walls of a log cabin. Every block rests on both blocks of the layer below. -/

namespace KaplaPlanner.Motifs

/-- The two blocks of layer `k` (counting from 0 at the ground). -/
def towerLayer (k : Nat) : List GridBlock :=
  if k % 2 == 0 then [⟨.flatX, 0, 0, 4 * k⟩, ⟨.flatX, 0, 48, 4 * k⟩]
  else [⟨.flatY, 0, 0, 4 * k⟩, ⟨.flatY, 48, 0, 4 * k⟩]

/-- The first `n` layers, bottom to top. -/
def towerLayers : Nat → List GridBlock
  | 0 => []
  | n + 1 => towerLayers n ++ towerLayer n

theorem towerLayer_length (k : Nat) : (towerLayer k).length = 2 := by
  unfold towerLayer; split <;> rfl

theorem towerLayers_length (n : Nat) : (towerLayers n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [towerLayers, ih, towerLayer_length]; omega

/-- A log-cabin tower with the given number of layers (7.8 mm each). -/
def tower : Motif Nat where
  name := "log-cabin tower"
  blocks := towerLayers
  cost := fun n => 2 * n
  cost_eq := towerLayers_length

#guard (tower.blocks 3).length == 6
#guard tower.blocks 2 ==
  [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 0, 48, 0⟩, ⟨.flatY, 0, 0, 4⟩, ⟨.flatY, 48, 0, 4⟩]
-- every block above the ground rests on both blocks of the layer below
#guard
  let bs := tower.blocks 4
  bs.all fun b => b.onGround || (bs.filter fun c => b.restsOn c).length == 2

end KaplaPlanner.Motifs
