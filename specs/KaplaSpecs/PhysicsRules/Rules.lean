import KaplaSpecs.PhysicsRules.Geometry

/-! # The physics rules (P1–P3, C1–C4, F1–F4, S1–S4 of `spec/physics-rules.md`)

This file is the trusted surface of the physics theorems: read it to know what
"well-formed" and "stable" mean. Nothing here is computed by a search; every definition
is a direct translation of a rule. -/

namespace KaplaPhysics

/-! ## Legal placement (P1–P3) -/

/-- Two planks share some inside space: their boxes overlap by more than a face, edge or
corner along all three axes. -/
def Overlap (a b : Plank) : Prop :=
  (a.x < b.x1 ∧ b.x < a.x1) ∧ (a.y < b.y1 ∧ b.y < a.y1) ∧ (a.z < b.top ∧ b.z < a.top)

instance (a b : Plank) : Decidable (Overlap a b) := by unfold Overlap; infer_instance

/-- Example: two flat planks side by side, touching along a face, do not overlap. -/
example : ¬ Overlap ⟨.flatX, 0, 0, 0⟩ ⟨.flatX, 0, 3, 0⟩ := by decide +kernel

/-- What a plank can rest on: the ground, or plank number `j`. -/
inductive Support where
  | ground
  | plank (j : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- C1–C3. The contact patch where plank `i` rests on support `s`, if there is one.

* On the ground: the plank's bottom is at `z = 0`; the patch is its whole bottom face.
* On plank `j`: `i`'s bottom is at the height of `j`'s top, and the two faces overlap in
  a rectangle with area bigger than zero. Edge and corner touches do not count (C3).

Side-by-side touches never give a patch (C4). -/
def restPatch (b : Build) (i : Nat) : Support → Option Rect
  | .ground =>
      if (b.get i).z = 0 then some (b.get i).footprint else none
  | .plank j =>
      let r := (b.get i).footprint.inter (b.get j).footprint
      if (b.get i).z = (b.get j).top ∧ r.HasArea then some r else none

/-- Example (E2): a flat plank shifted 5 along `x` on top of another rests on the
10 × 3 patch they share. -/
example : restPatch [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 5, 0, 1⟩] 1 (.plank 0)
    = some ⟨5, 15, 0, 3⟩ := by decide +kernel

/-- `s` names the ground or a plank that is part of a build of `n` planks. -/
def Support.InBuild (n : Nat) : Support → Prop
  | .ground => True
  | .plank j => j < n

instance (n : Nat) (s : Support) : Decidable (s.InBuild n) := by
  cases s <;> unfold Support.InBuild <;> infer_instance

/-- The build is well-formed (P1–P3):
1. no two planks share inside space,
2. every plank is above the ground,
3. every plank rests on the ground or on another plank. -/
structure WellFormed (b : Build) : Prop where
  noOverlap : ∀ i < b.length, ∀ j < b.length, i ≠ j → ¬ Overlap (b.get i) (b.get j)
  aboveGround : ∀ i < b.length, 0 ≤ (b.get i).z
  resting : ∀ i < b.length,
    (restPatch b i .ground).isSome ∨ ∃ j < b.length, (restPatch b i (.plank j)).isSome

instance (b : Build) : Decidable (WellFormed b) :=
  if h : (∀ i < b.length, ∀ j < b.length, i ≠ j → ¬ Overlap (b.get i) (b.get j)) ∧
      (∀ i < b.length, 0 ≤ (b.get i).z) ∧
      (∀ i < b.length,
        (restPatch b i .ground).isSome ∨ ∃ j < b.length, (restPatch b i (.plank j)).isSome)
  then isTrue ⟨h.1, h.2.1, h.2.2⟩
  else isFalse fun w => h ⟨w.noOverlap, w.aboveGround, w.resting⟩

/-! ## Forces and balance (F1–F4, S1–S4)

Each plank weighs 1 (B2), so all pushes are measured in plank weights. -/

/-- F2, F4. One push at a corner of a contact patch: plank `upper` is pushed up with
strength `force` at the point `(x, y)`, and its support `lower` is pushed down with the
same strength. -/
structure Push where
  upper : Nat
  lower : Support
  x : Rat
  y : Rat
  force : Rat
  deriving Repr, DecidableEq

/-- The push is allowed (F2, F4): it pushes, never pulls; it is between planks of the
build; and it sits at a corner of the patch where `upper` rests on `lower`. -/
def Push.Allowed (b : Build) (p : Push) : Prop :=
  0 ≤ p.force ∧ p.upper < b.length ∧ p.lower.InBuild b.length ∧
    match restPatch b p.upper p.lower with
    | some r => (p.x, p.y) ∈ r.corners
    | none => False

instance (b : Build) (p : Push) : Decidable (p.Allowed b) := by
  unfold Push.Allowed
  cases restPatch b p.upper p.lower <;> infer_instance

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
along `y`. Heights do not change. -/
def Build.shift (b : Build) (d : Nat → Rat × Rat) : Build :=
  b.mapIdx fun i p => { p with x := p.x + (d i).1, y := p.y + (d i).2 }

/-- Example: moving plank 1 of E2 by 1/4 along `x`. -/
example : Build.shift [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 5, 0, 1⟩] (fun i => if i = 1 then (1/4, 0) else (0, 0))
    = [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 21/4, 0, 1⟩] := by decide +kernel

/-- R1. Every plank of a build of `n` planks lands at most `ε` off along `x` and at most
`ε` off along `y`. -/
def SmallShift (ε : Rat) (n : Nat) (d : Nat → Rat × Rat) : Prop :=
  ∀ i < n, -ε ≤ (d i).1 ∧ (d i).1 ≤ ε ∧ -ε ≤ (d i).2 ∧ (d i).2 ≤ ε

/-- R3. The build is solid: it is stable for every combination of placement errors of
at most `ε`.

R5 (a plank pushed against its neighbour moves with it) only removes some of these
combinations, so a build that is solid here is also solid under R5. -/
def SolidWithin (ε : Rat) (b : Build) : Prop :=
  ∀ d, SmallShift ε b.length d → Stable (b.shift d)

/-- R3 with the default error of 2 mm. -/
def Solid (b : Build) : Prop := SolidWithin placementError b

/-! ## Build plans (K1, K4, K5) -/

/-- K1, K4, K5: the plan places one plank per step, uses at most `maxPlanks` planks, and
after every step the build so far is well-formed and solid (placement error up to `ε`). -/
def SafePlan (ε : Rat) (maxPlanks : Nat) (steps : Build) : Prop :=
  steps.length ≤ maxPlanks ∧
    ∀ k, 1 ≤ k → k ≤ steps.length → WellFormed (steps.take k) ∧ SolidWithin ε (steps.take k)

end KaplaPhysics

namespace KaplaPhysics

/-! ## Reaching the spot (K2, K3) -/

/-- The plank moved by `dx`, `dy`, `dz`. -/
def Plank.moveBy (p : Plank) (dx dy dz : Rat) : Plank :=
  { p with x := p.x + dx, y := p.y + dy, z := p.z + dz }

/-- K3. The gap `h` for the final drop: 1 unit (7.8 mm). -/
def dropGap : Rat := 1

/-- K2, K3. A straight path that places `p` among the planks already `placed`: the plank,
in its final pose, comes in a straight line from far away along direction `v` to a point
`h` above its spot, then drops `h` straight down.
1. `v` is not zero (so the path starts far away) and never points down (it stays above
   the table);
2. on the straight line, at every distance `t ≥ 0` back along `v`, the plank shares no
   inside space with a placed plank;
3. during the drop, at every height `s` between `0` and `h`, the same holds.
Touching a placed plank at a face, edge or corner is allowed. -/
def StraightPath (placed : Build) (p : Plank) (h : Rat) (v : Rat × Rat × Rat) : Prop :=
  v ≠ (0, 0, 0) ∧ 0 ≤ v.2.2 ∧
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
def Push.height (b : Build) (p : Push) : Rat := (b.get p.upper).z

/-- Height of plank `i`'s centre. -/
def Plank.centerZ (p : Plank) : Rat := p.z + p.pose.size.dz / 2

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
