import KaplaCore
import KaplaSpecs.PhysicsRules.Geometry

/-! # From KaplaCore blocks to physics planks

KaplaCore and the physics rules describe a block in two ways:

* Core gives which face is down (`Upright`), a turn about the vertical axis (`Rot`, any
  exact angle) and the block's **centre**.
* The physics rules (B4, B5) give one of six poses, all with sides parallel to the axes,
  and the block's **lowest corner**.

This file turns the first into the second. Only quarter turns (0°, 90°, 180°, 270°) have a
physics pose; for any other turn there is none, and the engine refuses the plan.

Both use the same units (one block thickness) and the same axes (`z` up, ground at
`z = 0`), so nothing is scaled. -/

namespace KaplaPhysics

/-- The turn is 0° or 180°: the block's long side stays along `x`. -/
def isStraightTurn (r : KaplaCore.Rot) : Prop := r = ⟨1, 0⟩ ∨ r = ⟨-1, 0⟩

/-- The turn is 90° or 270°: the block's long side ends up along `y`. -/
def isQuarterTurn (r : KaplaCore.Rot) : Prop := r = ⟨0, 1⟩ ∨ r = ⟨0, -1⟩

instance (r : KaplaCore.Rot) : Decidable (isStraightTurn r) := by
  unfold isStraightTurn; infer_instance

instance (r : KaplaCore.Rot) : Decidable (isQuarterTurn r) := by
  unfold isQuarterTurn; infer_instance

/-- The physics pose (B4) of a core block with face `up` down and turn `r`, if there is one.

Before turning, core lays a block with its long side along `x` (`Upright.dims`); a quarter
turn swaps `x` and `y`. A standing block is 3 wide along `x` and 1 along `y` before
turning, so its wide side faces `y`. -/
def poseOf (up : KaplaCore.Upright) (r : KaplaCore.Rot) : Option Pose :=
  if isStraightTurn r then
    some (match up with
      | .flat => .flatX
      | .onEdge => .edgeX
      | .standing => .standFacingY)
  else if isQuarterTurn r then
    some (match up with
      | .flat => .flatY
      | .onEdge => .edgeY
      | .standing => .standFacingX)
  else none

/-- Example: a flat block turned by 90° lies along `y`. -/
example : poseOf .flat .quarter = some .flatY := by decide +kernel

/-- Example: a turn by the 3-4-5 angle has no physics pose. -/
example : poseOf .flat (.ofTriple 3 4 5) = none := by decide +kernel

/-- The physics plank for a core block, if its turn is a quarter turn: the same pose, with
the position moved from the centre to the lowest corner. -/
def plankOf (p : KaplaCore.Pose) : Option Plank :=
  (poseOf p.up p.rot).map fun q =>
    ⟨q, p.center.x - q.size.dx / 2, p.center.y - q.size.dy / 2, p.center.z - q.size.dz / 2⟩

/-- Example: core's example block (flat, centre `(0, 0, 1/2)`) is a flat plank along `x`
with its lowest corner at `(-15/2, -3/2, 0)`. -/
example : plankOf KaplaCore.Pose.example = some ⟨.flatX, -15 / 2, -3 / 2, 0⟩ := by
  decide +kernel

/-- The physics build for a list of core blocks, in the same order, if every block has a
physics pose. -/
def buildOf (ps : List KaplaCore.Pose) : Option Build := ps.mapM plankOf

/-- Example: one block turned by the 3-4-5 angle makes the whole list have no build. -/
example : buildOf [KaplaCore.Pose.example, ⟨.flat, .ofTriple 3 4 5, ⟨0, 0, 3 / 2⟩⟩] = none := by
  decide +kernel

/-- The box a plank fills, written as a core `Box` (lowest and highest corner). -/
def Plank.toBox (p : Plank) : KaplaCore.Box := ⟨⟨p.x, p.y, p.z⟩, ⟨p.x1, p.y1, p.top⟩⟩

end KaplaPhysics
