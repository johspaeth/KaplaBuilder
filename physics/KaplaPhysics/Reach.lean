import KaplaSpecs.PhysicsRules.Rules

/-! # Can each plank be put in place? (K3)

The checker tries five straight paths: from above, and from each of the four sides at
the height of the drop gap. For each, a short test per placed plank says whether the
moving plank could ever share inside space with it. `reachDir_sound` (in `Proofs.lean`)
proves that a direction the checker accepts gives a `StraightPath`. -/

namespace KaplaPhysics

/-- The directions the checker tries. -/
inductive Dir where
  | fromAbove
  | fromPlusX
  | fromMinusX
  | fromPlusY
  | fromMinusY
  deriving Repr, DecidableEq

/-- The direction as a vector `v`: the plank starts far out along `v`. -/
def Dir.vec : Dir → Rat × Rat × Rat
  | .fromAbove => (0, 0, 1)
  | .fromPlusX => (1, 0, 0)
  | .fromMinusX => (-1, 0, 0)
  | .fromPlusY => (0, 1, 0)
  | .fromMinusY => (0, -1, 0)

/-- Seen from above, the two planks share inside area. -/
def OverlapXY (p q : Plank) : Prop := (p.x < q.x1 ∧ q.x < p.x1) ∧ (p.y < q.y1 ∧ q.y < p.y1)

/-- `p`, lifted by `h`, overlaps `q` in height. -/
def OverlapZ (p q : Plank) (h : Rat) : Prop := p.z + h < q.top ∧ q.z < p.top + h

/-- During the drop from `h` above, plank `p` never shares inside space with `q`. -/
def DropMisses (p : Plank) (h : Rat) (q : Plank) : Prop :=
  ¬ OverlapXY p q ∨ q.top ≤ p.z ∨ p.top + h ≤ q.z

/-- On the straight path along `d`, plank `p` (lifted by `h`) never shares inside space
with `q`: either they never line up across the path, or `q` lies behind the plank's spot. -/
def RayMisses : Dir → Plank → Rat → Plank → Prop
  | .fromAbove, p, h, q => ¬ OverlapXY p q ∨ q.top ≤ p.z + h
  | .fromPlusX, p, h, q => ¬ ((p.y < q.y1 ∧ q.y < p.y1) ∧ OverlapZ p q h) ∨ q.x1 ≤ p.x
  | .fromMinusX, p, h, q => ¬ ((p.y < q.y1 ∧ q.y < p.y1) ∧ OverlapZ p q h) ∨ p.x1 ≤ q.x
  | .fromPlusY, p, h, q => ¬ ((p.x < q.x1 ∧ q.x < p.x1) ∧ OverlapZ p q h) ∨ q.y1 ≤ p.y
  | .fromMinusY, p, h, q => ¬ ((p.x < q.x1 ∧ q.x < p.x1) ∧ OverlapZ p q h) ∨ p.y1 ≤ q.y

instance : (d : Dir) → (p : Plank) → (h : Rat) → (q : Plank) → Decidable (RayMisses d p h q)
  | .fromAbove, p, h, q => by unfold RayMisses OverlapXY; infer_instance
  | .fromPlusX, p, h, q => by unfold RayMisses OverlapZ; infer_instance
  | .fromMinusX, p, h, q => by unfold RayMisses OverlapZ; infer_instance
  | .fromPlusY, p, h, q => by unfold RayMisses OverlapZ; infer_instance
  | .fromMinusY, p, h, q => by unfold RayMisses OverlapZ; infer_instance

instance (p : Plank) (h : Rat) (q : Plank) : Decidable (DropMisses p h q) := by
  unfold DropMisses OverlapXY; infer_instance

/-- The first direction whose path and drop miss every placed plank, if any. -/
def reachDir? (placed : Build) (p : Plank) (h : Rat) : Option Dir :=
  [Dir.fromAbove, .fromPlusX, .fromMinusX, .fromPlusY, .fromMinusY].find? fun d =>
    decide (∀ q ∈ placed, DropMisses p h q ∧ RayMisses d p h q)

/-- The steps of a plan (numbered from 0) for which the checker finds no straight path.
The app shows a warning "this step may be hard to reach" for each. -/
def hardToReach (h : Rat) (steps : Build) : List Nat :=
  (List.range steps.length).filter fun k => (reachDir? (steps.take k) (steps.get k) h).isNone

end KaplaPhysics
