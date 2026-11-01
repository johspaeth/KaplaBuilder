import KaplaPlanner.Motif

/-! # Solid column

Like the log-cabin tower, but each layer is filled: 5 flat blocks side by side make a
square of 15 × 15 cells. Each layer is turned 90° against the one below.
It costs 5 blocks per layer instead of 2, but it fills solid shapes. -/

namespace KaplaPlanner.Motifs

/-- The five blocks of layer `k` (counting from 0 at the ground). -/
def columnLayer (k : Nat) : List GridBlock :=
  if k % 2 == 0 then [0, 12, 24, 36, 48].map fun y => ⟨.flatX, 0, y, 4 * k⟩
  else [0, 12, 24, 36, 48].map fun x => ⟨.flatY, x, 0, 4 * k⟩

/-- The first `n` layers, bottom to top. -/
def columnLayers : Nat → List GridBlock
  | 0 => []
  | n + 1 => columnLayers n ++ columnLayer n

theorem columnLayer_length (k : Nat) : (columnLayer k).length = 5 := by
  unfold columnLayer; split <;> rfl

theorem columnLayers_length (n : Nat) : (columnLayers n).length = 5 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [columnLayers, ih, columnLayer_length]; omega

/-- A solid column with the given number of layers (height 1 each). -/
def column : Motif Nat where
  name := "solid column"
  blocks := columnLayers
  cost := fun n => 5 * n
  cost_eq := columnLayers_length

#guard (column.blocks 2).length == 10
-- no two blocks overlap, and every block above the ground rests on all 5 blocks below
#guard
  let bs := column.blocks 3
  bs.all fun b => (bs.filter fun c => b.overlaps c).length == 1 &&
    (b.onGround || (bs.filter fun c => b.restsOn c).length == 5)

end KaplaPlanner.Motifs
