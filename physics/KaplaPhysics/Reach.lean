import KaplaPhysics.Contacts

/-! # Can each plank be put in place? (K3)

The checker tries a few straight paths: from above, and from the sides at the height of
the drop gap, along `x`, along `y`, and along the plank's own length and width. For each,
a short test per placed plank says whether the moving plank could ever share inside space
with it. `reachDir_sound` (in `Proofs.lean`) proves that a direction the checker accepts
gives a `StraightPath`. -/

namespace KaplaPhysics

open KaplaCore (Pose)

/-- The directions the checker tries. -/
inductive Dir where
  /-- Straight down from above. -/
  | fromAbove
  /-- From far away along `(vx, vy)`, at the height of the drop gap. -/
  | side (vx vy : Rat)
  deriving Repr, DecidableEq

/-- The direction as a vector `v`: the plank starts far out along `v`. -/
def Dir.vec : Dir → Rat × Rat × Rat
  | .fromAbove => (0, 0, 1)
  | .side vx vy => (vx, vy, 0)

/-- The plank moving along `(vx, vy)` never shares area with `q` seen from above: weights
on the sides show the two are apart, with `q` behind the plank as it comes in. -/
def slideCheck (p q : Plank) (vx vy : Rat) : Bool :=
  (sepCandidates p q).any fun s =>
    decide (s.Fits p q) && decide (s.value ≤ 0) &&
      decide (0 ≤ s.P.combo.a * vx + s.P.combo.b * vy)

/-- During the drop from `h` above, plank `p` never shares inside space with `q`. -/
def dropMisses (p : Plank) (h : Rat) (q : Plank) : Bool :=
  sepCheck 0 p q || decide (q.top ≤ p.bottom) || decide (p.top + h ≤ q.bottom)

/-- On the straight path along `d`, plank `p` (lifted by `h`) never shares inside space
with `q`. -/
def rayMisses : Dir → Plank → Rat → Plank → Bool
  | .fromAbove, p, h, q => sepCheck 0 p q || decide (q.top ≤ p.bottom + h)
  | .side vx vy, p, h, q =>
      decide (q.top ≤ p.bottom + h) || decide (p.top + h ≤ q.bottom) || slideCheck p q vx vy

/-- The directions to try for plank `p`. -/
def directions (p : Plank) : List Dir :=
  let c := p.rot.cos
  let s := p.rot.sin
  [.fromAbove, .side 1 0, .side (-1) 0, .side 0 1, .side 0 (-1),
   .side c s, .side (-c) (-s), .side (-s) c, .side s (-c)]

/-- The direction is a real one: from above, or along a vector that is not zero. -/
def Dir.ok : Dir → Bool
  | .fromAbove => true
  | .side vx vy => !(vx == 0 && vy == 0)

/-- The first direction whose path and drop miss every placed plank, if any. A gap `h`
that is not above zero gives no drop, so then no direction is accepted. -/
def reachDir? (placed : Build) (p : Plank) (h : Rat) : Option Dir :=
  if 0 < h then
    (directions p).find? fun d =>
      d.ok && placed.all fun q => dropMisses p h q && rayMisses d p h q
  else none

/-- The steps of a plan (numbered from 0) for which the checker finds no straight path.
The app shows a warning "this step may be hard to reach" for each. -/
def hardToReach (h : Rat) (steps : Build) : List Nat :=
  (List.range steps.length).filter fun k => (reachDir? (steps.take k) (steps.get k) h).isNone

end KaplaPhysics
