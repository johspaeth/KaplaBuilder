import KaplaSpecs.PhysicsRules.Geometry

/-! # The physics rules (P1–P3, C1–C4, F1–F4, S1–S4 of `spec/physics-rules.md`)

This file is the trusted surface of the physics theorems: read it to know what
"well-formed" and "stable" mean. Nothing here is computed by a search; every definition
is a direct translation of a rule. -/

namespace KaplaPhysics

/-! ## Legal placement (P1–P3) -/

/-- Seen from above, two planks share some area: a point lies strictly inside both. Touching
along an edge or at a corner does not count (C3). -/
def SharesArea (a b : Plank) : Prop := ∃ x y, a.CoversInside x y ∧ b.CoversInside x y

/-- Two planks share some inside space: seen from above they share some area, and their
heights overlap by more than a face. -/
def Overlap (a b : Plank) : Prop :=
  (a.bottom < b.top ∧ b.bottom < a.top) ∧ SharesArea a b

/-- Example: two flat planks side by side, touching along a face, do not overlap. -/
example : ¬ Overlap (Plank.at .flatX 0 0 0) (Plank.at .flatX 0 3 0) := by
  rintro ⟨-, x, y, h1, h2⟩
  rw [Plank.at_coversInside] at h1 h2
  simp only [AxisPose.size] at h1 h2
  grind

/-- Example: a flat block turned by 45° on the middle of a flat block along `x`, at the
same height, overlaps it. -/
example : Overlap (Plank.at .flatX 0 0 0) ⟨.flat, .deg45, ⟨15 / 2, 3 / 2, 1 / 2⟩⟩ :=
  ⟨by decide +kernel, 15 / 2, 3 / 2, by decide +kernel, by decide +kernel⟩

/-- What a plank can rest on: the ground, or plank number `j`. -/
inductive Support where
  | ground
  | plank (j : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- C1–C3. Plank `i` rests on support `s`:
* on the ground: its bottom is at `z = 0`;
* on plank `j`: its bottom is at the height of `j`'s top, and seen from above the two share
  some area. Edge and corner touches do not count (C3).

Side-by-side touches never count (C4). -/
def RestsOn (b : Build) (i : Nat) : Support → Prop
  | .ground => (b.get i).bottom = 0
  | .plank j => (b.get i).bottom = (b.get j).top ∧ SharesArea (b.get i) (b.get j)

instance (b : Build) (i : Nat) : Decidable (RestsOn b i .ground) := by
  unfold RestsOn; infer_instance

/-- C2. The point `(x, y)` is in the contact patch where plank `i` rests on `s`: it is
under plank `i`, and under plank `j` if `s` is plank `j` (edges included). -/
def InPatch (b : Build) (i : Nat) (s : Support) (x y : Rat) : Prop :=
  (b.get i).Covers x y ∧
    match s with
    | .ground => True
    | .plank j => (b.get j).Covers x y

instance (b : Build) (i : Nat) (s : Support) (x y : Rat) : Decidable (InPatch b i s x y) := by
  unfold InPatch; cases s <;> infer_instance

/-- Example (E2): a flat plank shifted 5 along `x` on top of another rests on it, and the
point (10, 1) is in the patch they share. -/
example : RestsOn [Plank.at .flatX 0 0 0, Plank.at .flatX 5 0 1] 1 (.plank 0) ∧
    InPatch [Plank.at .flatX 0 0 0, Plank.at .flatX 5 0 1] 1 (.plank 0) 10 1 :=
  ⟨⟨by decide +kernel, 10, 1, by decide +kernel, by decide +kernel⟩, by decide +kernel⟩

/-- `s` names the ground or a plank that is part of a build of `n` planks. -/
def Support.InBuild (n : Nat) : Support → Prop
  | .ground => True
  | .plank j => j < n

instance (n : Nat) (s : Support) : Decidable (s.InBuild n) := by
  cases s <;> unfold Support.InBuild <;> infer_instance

/-- The build is well-formed (P1–P3, B6):
0. every plank is turned by an allowed turn (B6),
1. no two planks share inside space,
2. every plank is above the ground,
3. every plank rests on the ground or on another plank. -/
structure WellFormed (b : Build) : Prop where
  turnsAllowed : ∀ i < b.length, (b.get i).rot.Allowed
  noOverlap : ∀ i < b.length, ∀ j < b.length, i ≠ j → ¬ Overlap (b.get i) (b.get j)
  aboveGround : ∀ i < b.length, 0 ≤ (b.get i).bottom
  resting : ∀ i < b.length, RestsOn b i .ground ∨ ∃ j < b.length, RestsOn b i (.plank j)

/-! ## Forces and balance (F1–F4, S1–S4)

Each plank weighs 1 (B2), so all pushes are measured in plank weights. -/

/-- F2, F4. One push between two planks: plank `upper` is pushed up with strength `force`
at the point `(x, y)`, and its support `lower` is pushed down with the same strength. -/
structure Push where
  upper : Nat
  lower : Support
  x : Rat
  y : Rat
  force : Rat
  deriving Repr, DecidableEq

/-- The push is allowed (F2, F4): it pushes, never pulls; it is between planks of the
build; `upper` rests on `lower`; and the push acts at a point of their contact patch
(edges included).

F4: a push anywhere in the patch has the same effect as pushes at the patch's corners
that add up to it, because the patch is convex. So it does not matter which of the two
ways the rule is written. -/
def Push.Allowed (b : Build) (p : Push) : Prop :=
  0 ≤ p.force ∧ p.upper < b.length ∧ p.lower.InBuild b.length ∧
    RestsOn b p.upper p.lower ∧ InPatch b p.upper p.lower p.x p.y

/-- How much push `p` lifts plank `i`: `+force` if `i` is the upper plank, `-force` if
`i` is the lower plank, `0` otherwise. -/
def Push.upOn (i : Nat) (p : Push) : Rat :=
  (if p.upper = i then p.force else 0) - (if p.lower = .plank i then p.force else 0)

/-- S1. Plank `i` is balanced by the pushes `ps`:
1. the net push up equals its weight, 1;
2. the pushes do not turn it about the `y` axis (lever arms along `x`, from its centre);
3. the pushes do not turn it about the `x` axis (lever arms along `y`, from its centre). -/
def Balanced (b : Build) (ps : List Push) (i : Nat) : Prop :=
  (ps.map fun p => p.upOn i).sum = 1 ∧
  (ps.map fun p => p.upOn i * (p.x - (b.get i).centerX)).sum = 0 ∧
  (ps.map fun p => p.upOn i * (p.y - (b.get i).centerY)).sum = 0

instance (b : Build) (ps : List Push) (i : Nat) : Decidable (Balanced b ps i) := by
  unfold Balanced; infer_instance

/-- S2. The build is stable: some choice of allowed pushes balances every plank at once.
(S4: a push of size zero is allowed, so a centre exactly over an edge counts as stable.) -/
def Stable (b : Build) : Prop :=
  ∃ ps : List Push, (∀ p ∈ ps, p.Allowed b) ∧ ∀ i < b.length, Balanced b ps i

end KaplaPhysics

namespace KaplaPhysics

/-! ## Placement errors (R1–R3) -/

/-- R1. The default placement error: 2 mm, which is 10/39 of a unit. -/
def placementError : Rat := 10 / 39

/-- R1, R2. The build after plank `i` lands `(d i).1` off along `x` and `(d i).2` off
along `y`. Heights and turns do not change. -/
def Build.shift (b : Build) (d : Nat → Rat × Rat) : Build :=
  b.mapIdx fun i p => p.moveBy (d i).1 (d i).2 0

/-- Example: moving plank 1 of E2 by 1/4 along `x`. -/
example : Build.shift [Plank.at .flatX 0 0 0, Plank.at .flatX 5 0 1]
      (fun i => if i = 1 then (1/4, 0) else (0, 0))
    = [Plank.at .flatX 0 0 0, Plank.at .flatX (21/4) 0 1] := by decide +kernel

/-- R1. Every plank of a build of `n` planks lands at most `ε` off along `x` and at most
`ε` off along `y`. -/
def SmallShift (ε : Rat) (n : Nat) (d : Nat → Rat × Rat) : Prop :=
  ∀ i < n, -ε ≤ (d i).1 ∧ (d i).1 ≤ ε ∧ -ε ≤ (d i).2 ∧ (d i).2 ≤ ε

/-- R3. The build is solid: the error `ε` is not below zero, and the build is stable for
every combination of placement errors of at most `ε`.

A negative `ε` allows no errors at all, so "stable for every error" would then say
nothing; that is why `0 ≤ ε` is part of this rule.

R5 (a plank pushed against its neighbour moves with it) only removes some of these
combinations, so a build that is solid here is also solid under R5. -/
def SolidWithin (ε : Rat) (b : Build) : Prop :=
  0 ≤ ε ∧ ∀ d, SmallShift ε b.length d → Stable (b.shift d)

/-- R3 with the default error of 2 mm. -/
def Solid (b : Build) : Prop := SolidWithin placementError b

/-! ## Build plans (K1, K4, K5) -/

/-- Planks `a` and `b` meet: they touch at a face, an edge or a corner, or share inside
space. Seen from above some point is under both (edges included), and there is no gap
between them in height. -/
def Meets (a b : Plank) : Prop :=
  (a.bottom ≤ b.top ∧ b.bottom ≤ a.top) ∧ ∃ x y, a.Covers x y ∧ b.Covers x y

/-- Example: two flat planks side by side, touching along a face, meet. -/
example : Meets (Plank.at .flatX 0 0 0) (Plank.at .flatX 0 3 0) :=
  ⟨by decide +kernel, 1, 3, by decide +kernel, by decide +kernel⟩

/-- Example: with a gap of 1/4 between them, they do not meet. -/
example : ¬ Meets (Plank.at .flatX 0 0 0) (Plank.at .flatX 0 (13 / 4) 0) := by
  rintro ⟨-, x, y, h1, h2⟩
  rw [Plank.at_covers] at h1 h2
  simp only [AxisPose.size] at h1 h2
  grind

/-- R1 with P1 (H6 in docs/DESIGN.md: gaps are 0 or big enough). Planks with a gap between
them in the plan keep a gap: for every combination of placement errors of at most `ε`, two
planks that do not meet at the planned positions do not share inside space.

Planks that meet in the plan (side by side and touching, or one on another) are left out
on purpose: they touch by design, and R5 says a plank pushed against its neighbour moves
with it. So walls of touching planks are fine. Only near misses fail: a gap above 0 but
small enough that an error can close it. -/
def KeepsGaps (ε : Rat) (b : Build) : Prop :=
  ∀ d, SmallShift ε b.length d → ∀ i < b.length, ∀ j < b.length,
    ¬ Meets (b.get i) (b.get j) → ¬ Overlap ((b.shift d).get i) ((b.shift d).get j)

/-- Which checks a plan must pass. -/
structure PlanOptions where
  /-- Also ask that no placement error can close a small gap (`KeepsGaps`). Off by
  default. Planks that touch by design are allowed either way. -/
  clearance : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- K1, K4, K5: the plan places one plank per step, uses at most `maxPlanks` planks, and
after every step the build so far is
1. well-formed at the planned positions,
2. if `opts.clearance` is on: planks with a gap keep it with placement errors up to `ε`,
   and
3. solid with placement errors up to `ε`. -/
def SafePlan (opts : PlanOptions) (ε : Rat) (maxPlanks : Nat) (steps : Build) : Prop :=
  steps.length ≤ maxPlanks ∧
    ∀ k, 1 ≤ k → k ≤ steps.length →
      WellFormed (steps.take k) ∧ (opts.clearance → KeepsGaps ε (steps.take k)) ∧
        SolidWithin ε (steps.take k)

end KaplaPhysics

namespace KaplaPhysics

/-! ## Reaching the spot (K2, K3) -/

/-- K3. The gap `h` for the final drop: 1 unit (7.8 mm). -/
def dropGap : Rat := 1

/-- K2, K3. A straight path that places `p` among the planks already `placed`: the plank,
in its final pose, comes in a straight line from far away along direction `v` to a point
`h` above its spot, then drops `h` straight down.
0. the gap `h` is above zero (there is a real drop at the end);
1. `v` is not zero (so the path starts far away) and never points down (it stays above
   the table);
2. on the straight line, at every distance `t ≥ 0` back along `v`, the plank shares no
   inside space with a placed plank;
3. during the drop, at every height `s` between `0` and `h`, the same holds.
Touching a placed plank at a face, edge or corner is allowed. -/
def StraightPath (placed : Build) (p : Plank) (h : Rat) (v : Rat × Rat × Rat) : Prop :=
  0 < h ∧ v ≠ (0, 0, 0) ∧ 0 ≤ v.2.2 ∧
  (∀ t, 0 ≤ t → ∀ q ∈ placed, ¬ Overlap (p.moveBy (t * v.1) (t * v.2.1) (h + t * v.2.2)) q) ∧
  (∀ s, 0 ≤ s → s ≤ h → ∀ q ∈ placed, ¬ Overlap (p.moveBy 0 0 s) q)

/-- K3. Plank `p` can be put in place among `placed` by some straight path and a drop. -/
def Reachable (placed : Build) (p : Plank) (h : Rat) : Prop :=
  ∃ v, StraightPath placed p h v

/-- K3 for a whole plan: every step's plank can be put in place, with the planks of the
earlier steps already there. -/
def EveryStepReachable (h : Rat) (steps : Build) : Prop :=
  ∀ k < steps.length, Reachable (steps.take k) (steps.get k) h

end KaplaPhysics

namespace KaplaPhysics

/-! ## Friction (F3, property 8)

The engine never uses friction. This model adds it, so we can prove that ignoring it is
safe: a build that is stable without friction is stable with any amount of it. -/

/-- A push with friction: besides pushing `upper` up by `force` at `(x, y)`, the contact
pushes `upper` sideways by `fx` along `x` and `fy` along `y`. The lower plank gets the
opposite pushes (Newton's third law). -/
structure FrictionPush where
  push : Push
  fx : Rat
  fy : Rat
  deriving Repr

/-- The push is allowed with friction coefficient `μ`: the up-push is allowed (F2, F4),
and each sideways push is at most `μ` times the up-push. -/
def FrictionPush.Allowed (μ : Rat) (b : Build) (p : FrictionPush) : Prop :=
  p.push.Allowed b ∧ -(μ * p.push.force) ≤ p.fx ∧ p.fx ≤ μ * p.push.force ∧
    -(μ * p.push.force) ≤ p.fy ∧ p.fy ≤ μ * p.push.force

/-- `+1` if plank `i` is the upper plank of the push, `-1` if it is the lower, else `0`. -/
def Push.side (i : Nat) (p : Push) : Rat :=
  (if p.upper = i then 1 else 0) - (if p.lower = .plank i then 1 else 0)

/-- Height of a push: the bottom of its upper plank. -/
def Push.height (b : Build) (p : Push) : Rat := (b.get p.upper).bottom

/-- Plank `i` is balanced by pushes with friction: all six conditions of S1.
1. net push up is 1 (its weight); net push along `x` and along `y` is 0;
2. no turning about the `x`, `y` and `z` axes through its centre. -/
def BalancedWithFriction (b : Build) (ps : List FrictionPush) (i : Nat) : Prop :=
  let c := b.get i
  let s := fun (p : FrictionPush) => p.push.side i
  let dx := fun (p : FrictionPush) => p.push.x - c.centerX
  let dy := fun (p : FrictionPush) => p.push.y - c.centerY
  let dz := fun (p : FrictionPush) => p.push.height b - c.centerZ
  (ps.map fun p => s p * p.push.force).sum = 1 ∧
  (ps.map fun p => s p * p.fx).sum = 0 ∧
  (ps.map fun p => s p * p.fy).sum = 0 ∧
  -- turning about `x`: `dy · up − dz · fy`
  (ps.map fun p => s p * (dy p * p.push.force - dz p * p.fy)).sum = 0 ∧
  -- turning about `y`: `dz · fx − dx · up`
  (ps.map fun p => s p * (dz p * p.fx - dx p * p.push.force)).sum = 0 ∧
  -- turning about `z`: `dx · fy − dy · fx`
  (ps.map fun p => s p * (dx p * p.fy - dy p * p.fx)).sum = 0

/-- F3 with friction coefficient `μ`: some allowed pushes with friction balance every
plank. -/
def StableWithFriction (μ : Rat) (b : Build) : Prop :=
  ∃ ps : List FrictionPush, (∀ p ∈ ps, p.Allowed μ b) ∧
    ∀ i < b.length, BalancedWithFriction b ps i

end KaplaPhysics
