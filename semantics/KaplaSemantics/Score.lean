import KaplaSemantics.Voxel

/-!
# KaplaSemantics.Score — IoU, the score ceiling and the verdict (DESIGN §5)

* `iou`: `|V(bp) ∩ T| / |V(bp) ∪ T|` over grid centres.
* `maxScore`: one block in any pose contains at most `K_h` grid centres, so with `N` blocks
  `iou ≤ min(K_h·N, |T|) / |T|`.

`K_h`: the cells (side `h`) around distinct grid centres are disjoint, and every such cell
around a centre inside a block lies in the block grown by `h/2·(|cos|+|sin|) ≤ h/√2` along
its horizontal axes and `h/2` vertically. For the default `h = 7.8 mm` (one thickness) this is
`(15 + √2)(3 + √2)(1 + 1) < 145` cells. The formal proof of `iou_le_bound` is on the M4 list.
-/

namespace Kapla.Semantics

open Kapla

/-- Max grid centres inside one block for grid spacing `defaultH`. -/
def Kh : Nat := 145

def interCount (a b : Std.HashSet Cell) : Nat :=
  let (small, big) := if a.size ≤ b.size then (a, b) else (b, a)
  small.fold (fun n c => if big.contains c then n + 1 else n) 0

def iouOf (bv tv : Std.HashSet Cell) : Q × Nat × Nat :=
  let i := interCount bv tv
  let u := bv.size + tv.size - i
  ((if u = 0 then 0 else (i : Q) / u), tv.size - i, bv.size - i)

/-- Score blocks against a target already in mm. -/
def scoreBlocks (t : TargetSpec) (bs : List Pose) (h : Q := defaultH) : ScoreReport :=
  let tv := voxelizeShape h t.shape
  let bv := voxelizePoses h bs
  let (iou, missing, extra) := iouOf bv tv
  let perPart := t.shape.taggedParts.map fun (tag, s) =>
    let pv := voxelizeShape h s
    { tag, iou := if pv.size = 0 then 0 else (interCount bv pv : Q) / pv.size : PartScore }
  { score := iou, iou, perPart, missing, extra, targetVoxels := tv.size, scale := t.unitMM }

/-- The ceiling on the score with `N` blocks. -/
def boundFor (t : TargetSpec) (N : Nat) (h : Q := defaultH) : Bound :=
  let tv := (voxelizeShape h t.shape).size
  let m : Q := if tv = 0 then 0 else (min (Kh * N) tv : Nat) / (tv : Q)
  { maxScore := m, verdict := Verdict.ofScore m }

end Kapla.Semantics
