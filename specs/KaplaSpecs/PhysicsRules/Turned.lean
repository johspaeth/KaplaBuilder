import KaplaCore
import KaplaSpecs.PhysicsRules.Rules

/-! # Turned planks (rule B6)

B6. Besides the six poses of B4, a plank may be turned about the vertical axis in steps of
15° (`KaplaCore.Rot.step15`). It is never tilted: its top and bottom faces stay horizontal.
So every contact is still a flat, horizontal patch, gravity is the only force, and
friction is never needed (F3).

This first version checks turned plans only at the planned positions: well-formed
(P1–P3) and stable (S2) after every step. It does not check placement errors (R1), gaps
or reach for them. Plans with only quarter turns keep the full check (`SafePlan`).

A turned plank is given by its centre, as in KaplaCore. Its sides are no longer along the
axes, so we measure points in the plank's own directions: `along` its long side and
`across` it. -/

namespace KaplaPhysics

open KaplaCore (Upright Rot)

/-- B6. A plank turned about the vertical axis: which face is down, the turn, its centre
seen from above, and the height of its bottom face. -/
structure TPlank where
  up : Upright
  rot : Rot
  cx : Rat
  cy : Rat
  z : Rat
  deriving Repr, DecidableEq, Inhabited

/-- The size of a number, ignoring its sign. -/
def absQ (q : Rat) : Rat := max q (-q)

namespace TPlank

/-- Half the plank's length along its own long side. -/
def halfLength (p : TPlank) : Rat := (Upright.dims p.up).x / 2
/-- Half the plank's width across its long side. -/
def halfWidth (p : TPlank) : Rat := (Upright.dims p.up).y / 2
/-- Height of the plank's top face. -/
def top (p : TPlank) : Rat := p.z + (Upright.dims p.up).z

/-- How far the point `(x, y)` is from the centre, measured along the plank's long side. -/
def along (p : TPlank) (x y : Rat) : Rat := p.rot.cos * (x - p.cx) + p.rot.sin * (y - p.cy)
/-- How far the point `(x, y)` is from the centre, measured across the plank. -/
def across (p : TPlank) (x y : Rat) : Rat := -p.rot.sin * (x - p.cx) + p.rot.cos * (y - p.cy)

/-- The point `(x, y)` lies under the plank's bottom face (edges included). -/
def Covers (p : TPlank) (x y : Rat) : Prop :=
  -p.halfLength ≤ p.along x y ∧ p.along x y ≤ p.halfLength ∧
    -p.halfWidth ≤ p.across x y ∧ p.across x y ≤ p.halfWidth

instance (p : TPlank) (x y : Rat) : Decidable (p.Covers x y) := by
  unfold Covers; infer_instance

/-- Half the length of the plank's shadow on a line in the direction `(nx, ny)`. -/
def reach (p : TPlank) (nx ny : Rat) : Rat :=
  p.halfLength * absQ (nx * p.rot.cos + ny * p.rot.sin) +
    p.halfWidth * absQ (-nx * p.rot.sin + ny * p.rot.cos)

end TPlank

/-- The shadows of `p` and `q` on a line in the direction `(nx, ny)` overlap by more than a
point. -/
def ShadowsOverlap (p q : TPlank) (nx ny : Rat) : Prop :=
  absQ (nx * (q.cx - p.cx) + ny * (q.cy - p.cy)) < p.reach nx ny + q.reach nx ny

instance (p q : TPlank) (nx ny : Rat) : Decidable (ShadowsOverlap p q nx ny) := by
  unfold ShadowsOverlap; infer_instance

/-- The faces of `p` and `q`, seen from above, overlap in an area bigger than zero.

Two rectangles overlap exactly when their shadows overlap on each of the four directions
of their sides (along and across `p`, along and across `q`). If some direction shows a gap
or a touch, a straight line separates them. Touching at a side, an edge or a corner is not
an overlap. -/
def FacesOverlap (p q : TPlank) : Prop :=
  ShadowsOverlap p q p.rot.cos p.rot.sin ∧ ShadowsOverlap p q (-p.rot.sin) p.rot.cos ∧
    ShadowsOverlap p q q.rot.cos q.rot.sin ∧ ShadowsOverlap p q (-q.rot.sin) q.rot.cos

instance (p q : TPlank) : Decidable (FacesOverlap p q) := by
  unfold FacesOverlap; infer_instance

/-- P1. Two turned planks share inside space: they share some height, and their faces
overlap seen from above. -/
def TOverlap (p q : TPlank) : Prop :=
  (p.z < q.top ∧ q.z < p.top) ∧ FacesOverlap p q

instance (p q : TPlank) : Decidable (TOverlap p q) := by unfold TOverlap; infer_instance

/-- B6. The turn is one of the 24 steps of 15° (`KaplaCore.Rot.step15`). -/
def IsStep15 (r : Rot) : Prop := ∃ k < 24, r = Rot.step15 k

instance (r : Rot) : Decidable (IsStep15 r) := by unfold IsStep15; infer_instance

/-- A build of turned planks, in the order they are placed. -/
abbrev TBuild := List TPlank

/-- Plank number `i` of the build (a dummy plank if there is none). -/
def TBuild.get (b : TBuild) (i : Nat) : TPlank := b.getD i default

/-- C1–C3. Plank `i` rests on support `s`: on the ground when its bottom is at `z = 0`; on
plank `j` when its bottom is at the height of `j`'s top and their faces overlap in an area
bigger than zero. -/
def TRestsOn (b : TBuild) (i : Nat) : Support → Prop
  | .ground => (b.get i).z = 0
  | .plank j => (b.get i).z = (b.get j).top ∧ FacesOverlap (b.get i) (b.get j)

instance (b : TBuild) (i : Nat) (s : Support) : Decidable (TRestsOn b i s) := by
  cases s <;> unfold TRestsOn <;> infer_instance

/-- B6, P1–P3. The build is well-formed:
0. every turn is one of the 15° steps,
1. no two planks share inside space,
2. every plank is above the ground,
3. every plank rests on the ground or on another plank. -/
def TWellFormed (b : TBuild) : Prop :=
  (∀ p ∈ b, IsStep15 p.rot) ∧
  (∀ i < b.length, ∀ j < b.length, i ≠ j → ¬ TOverlap (b.get i) (b.get j)) ∧
  (∀ i < b.length, 0 ≤ (b.get i).z) ∧
  (∀ i < b.length, TRestsOn b i .ground ∨ ∃ j < b.length, TRestsOn b i (.plank j))

instance (b : TBuild) : Decidable (TWellFormed b) := by unfold TWellFormed; infer_instance

/-- F2, F4. A push between turned planks is allowed: it pushes, never pulls; it is between
planks of the build; the upper plank rests on the lower one; and the push acts at a point
of their contact patch: under the upper plank and on top of the lower one.

F4 says one push at each corner of the patch is enough. Here any point of the patch is
allowed, which means the same: a push inside the patch acts like a mix of corner pushes. -/
def TPushAllowed (b : TBuild) (p : Push) : Prop :=
  0 ≤ p.force ∧ p.upper < b.length ∧ p.lower.InBuild b.length ∧
    TRestsOn b p.upper p.lower ∧ (b.get p.upper).Covers p.x p.y ∧
    match p.lower with
    | .ground => True
    | .plank j => (b.get j).Covers p.x p.y

instance (b : TBuild) (p : Push) : Decidable (TPushAllowed b p) := by
  unfold TPushAllowed; cases p.lower <;> infer_instance

/-- S1. Turned plank `i` is balanced by the pushes `ps`: the net push up is its weight, 1,
and the pushes do not turn it about either horizontal axis through its centre. -/
def TBalanced (b : TBuild) (ps : List Push) (i : Nat) : Prop :=
  (ps.map fun p => p.upOn i).sum = 1 ∧
  (ps.map fun p => p.upOn i * (p.x - (b.get i).cx)).sum = 0 ∧
  (ps.map fun p => p.upOn i * (p.y - (b.get i).cy)).sum = 0

instance (b : TBuild) (ps : List Push) (i : Nat) : Decidable (TBalanced b ps i) := by
  unfold TBalanced; infer_instance

/-- S2. The turned build is stable at its planned positions: some allowed pushes balance
every plank at once. -/
def TStable (b : TBuild) : Prop :=
  ∃ ps : List Push, (∀ p ∈ ps, TPushAllowed b p) ∧ ∀ i < b.length, TBalanced b ps i

/-- K1, K4, K5 for turned plans: at most `maxPlanks` planks, and after every step the
build so far is well-formed and stable at the planned positions. Placement errors are not
checked. -/
def TSafePlan (maxPlanks : Nat) (steps : TBuild) : Prop :=
  steps.length ≤ maxPlanks ∧
    ∀ k, 1 ≤ k → k ≤ steps.length → TWellFormed (steps.take k) ∧ TStable (steps.take k)

/-! ## From KaplaCore blocks -/

/-- The turned plank for a core block, if its turn is one of the 15° steps. -/
def turnedOf (p : KaplaCore.Pose) : Option TPlank :=
  if IsStep15 p.rot then
    some ⟨p.up, p.rot, p.center.x, p.center.y, p.center.z - (Upright.dims p.up).z / 2⟩
  else none

/-- The turned build for a list of core blocks, if every turn is one of the 15° steps. -/
def turnedBuildOf (ps : List KaplaCore.Pose) : Option TBuild := ps.mapM turnedOf

/-! ## Examples -/

/-- A flat plank turned 45°, on the ground, centred at the origin. -/
def flat45 : TPlank := ⟨.flat, .step15 3, 0, 0, 0⟩

/-- Example: alone on the ground it is well-formed. -/
example : TWellFormed [flat45] := by decide +kernel

/-- Example: it is stable: a quarter of its weight at each corner of its bottom face. -/
example : TStable [flat45] :=
  ⟨[⟨0, .ground, -1425 / 338, -2157 / 338, 1 / 4⟩, ⟨0, .ground, 165 / 26, 111 / 26, 1 / 4⟩,
    ⟨0, .ground, 1425 / 338, 2157 / 338, 1 / 4⟩, ⟨0, .ground, -165 / 26, -111 / 26, 1 / 4⟩],
   by decide +kernel, by decide +kernel⟩

/-- Example: a plank at 45° lying across a plank along `x` shares no inside space with it,
and rests on it. -/
example : TWellFormed [⟨.flat, .id, 0, 0, 0⟩, ⟨.flat, .step15 3, 0, 0, 1⟩] := by decide +kernel

/-- Ruled out: two planks crossing at 45° at the same height share inside space. -/
example : TOverlap ⟨.flat, .id, 0, 0, 0⟩ flat45 := by decide +kernel

/-- Ruled out: two planks at 45° side by side, touching along a long side, do not share
inside space. -/
example : ¬ TOverlap flat45 ⟨.flat, .step15 3, -360 / 169, 357 / 169, 0⟩ := by decide +kernel

/-- Ruled out: a plank at 45° one unit above the ground, resting on nothing. -/
example : ¬ TWellFormed [⟨.flat, .step15 3, 0, 0, 1⟩] := by decide +kernel

/-- Ruled out: a turn that is not a 15° step (the 3-4-5 turn, about 36.87°). -/
example : ¬ TWellFormed [⟨.flat, .ofTriple 3 4 5, 0, 0, 0⟩] := by decide +kernel

end KaplaPhysics
