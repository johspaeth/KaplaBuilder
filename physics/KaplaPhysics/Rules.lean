import KaplaPhysics.Geometry

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
