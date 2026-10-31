import KaplaCore

/-!
# KaplaPlanner.Motifs — block layouts (untrusted)

Every function here only *proposes* blocks; the physics engine decides.
-/

namespace Kapla.Planning

open Kapla

def W : Q := Block.W
def L : Q := Block.L
def T : Q := Block.T

/-- Centre height of flat layer `k` standing on height `base`. -/
def layerZ (k : Nat) (base : Q := 0) : Q := base + T / 2 + k * T

def flatAt (x y z : Q) (alongX : Bool) : Pose :=
  { up := .flat, rot := if alongX then Rot.id else Rot.quarter, center := ⟨x, y, z⟩ }

def uprightAt (x y : Q) (base : Q := 0) : Pose :=
  { up := .upright, rot := Rot.id, center := ⟨x, y, base + L / 2⟩ }

/-- Log-cabin tower: two parallel flat blocks per layer, turning 90° every layer. Square
footprint `L × L`, hollow. -/
def cabinTower (cx cy : Q) (layers : Nat) (base : Q := 0) : List Pose :=
  (List.range layers).flatMap fun k =>
    let z := layerZ k base
    let o := L / 2 - W / 2
    if k % 2 = 0 then [flatAt cx (cy + o) z true, flatAt cx (cy - o) z true]
    else [flatAt (cx + o) cy z false, flatAt (cx - o) cy z false]

/-- Tree: an upright trunk, then a crown of crossing flat blocks on top. -/
def tree (cx cy : Q) (crown : Nat) : List Pose :=
  uprightAt cx cy :: (List.range crown).map fun k => flatAt cx cy (layerZ k L) (k % 2 = 0)

/-- Stepped roof (DESIGN §4, v1 only): flat courses stepping inward by `step` each layer,
along `x`, over a rectangle `sx × sy` starting at height `base`. -/
def steppedRoof (cx cy sx sy base step : Q) (maxLayers : Nat) : List Pose := Id.run do
  let mut out := []
  let mut halfY := sy / 2
  for k in [0:maxLayers] do
    if halfY < W / 2 then break
    let rows := ((2 * halfY / W).floor).toNat
    let y0 := cy - (rows : Q) * W / 2 + W / 2
    let cols := max 1 ((sx / L).floor.toNat)
    let x0 := cx - (cols : Q) * L / 2 + L / 2
    for r in [0:rows] do
      for c in [0:cols] do
        out := out ++ [flatAt (x0 + c * L) (y0 + r * W) (layerZ k base) true]
    halfY := halfY - step
  return out

end Kapla.Planning
