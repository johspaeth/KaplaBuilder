import KaplaCore

/-!
# KaplaSemantics.Voxel — meaning of the Shape DSL and the voxelizer

`Shape.mem s p` (in `KaplaCore.ShapeMem`) is the meaning of a shape: exact point membership
over ℚ. The voxelizer samples it at the grid centres `((i+½)h, (j+½)h, (k+½)h)` and is *defined*
as a filter of that meaning over a box that contains the shape, so it is correct by
construction as long as the box is (`Shape.bbox` — the containment lemma is on the M4 list).
-/

namespace Kapla.Semantics

open Kapla

/-- Default grid spacing: one block thickness (7.8 mm). -/
def defaultH : Q := Block.T

/-- Grid cell index. -/
abbrev Cell := Int × Int × Int

def cellCenter (h : Q) (c : Cell) : Q3 :=
  ⟨(c.1 + 1/2) * h, (c.2.1 + 1/2) * h, (c.2.2 + 1/2) * h⟩

/-- Cell indices whose centres may lie in `[lo, hi]` along one axis. -/
def idxRange (h lo hi : Q) : List Int :=
  let a := Rat.floor (lo / h - 1/2)
  let b := Rat.ceil (hi / h - 1/2)
  (List.range (b - a + 1).toNat).map fun n => a + n

/-- All grid cells whose centre satisfies `mem`, searched inside the box `[lo, hi]`. -/
def cellsIn (h : Q) (lo hi : Q3) (mem : Q3 → Bool) : Std.HashSet Cell := Id.run do
  let mut out : Std.HashSet Cell := {}
  for i in idxRange h lo.x hi.x do
    for j in idxRange h lo.y hi.y do
      for k in idxRange h lo.z hi.z do
        let c : Cell := (i, j, k)
        if mem (cellCenter h c) then out := out.insert c
  return out

/-- Voxels of a target shape. -/
def voxelizeShape (h : Q) (s : Shape) : Std.HashSet Cell :=
  let (lo, hi) := s.bbox
  cellsIn h lo hi s.mem

/-- Voxels of one block (closed). -/
def voxelizePose (h : Q) (b : Pose) : Std.HashSet Cell :=
  let cs := b.corners
  let lo : Q3 := ⟨(cs.map (·.x)).min?.getD 0, (cs.map (·.y)).min?.getD 0, (cs.map (·.z)).min?.getD 0⟩
  let hi : Q3 := ⟨(cs.map (·.x)).max?.getD 0, (cs.map (·.y)).max?.getD 0, (cs.map (·.z)).max?.getD 0⟩
  cellsIn h lo hi fun p => decide (b.Mem p)

def voxelizePoses (h : Q) (bs : List Pose) : Std.HashSet Cell :=
  bs.foldl (fun acc b => (voxelizePose h b).fold (fun a c => a.insert c) acc) {}

end Kapla.Semantics
