import KaplaPhysics.RobustSolver
import KaplaPhysics.Reach
import KaplaPhysics.Column

/-! # The physics engine: untrusted solver, checked answers

`stabilityAnswer` asks the untrusted solver for a proposal and then checks it:

* "stable": the proposed pushes are allowed and balance every plank. Then the build is
  stable by definition (`Proofs.lean`: `stabilityAnswer_stable_sound`).
* "falls": the proposed motion is a *fall certificate* (below). Then no allowed pushes
  can balance the build (`Proofs.lean`: `stabilityAnswer_falls_sound`).
* "unknown": the proposal did not pass the check. This should not happen; it is never
  reported as stable.

`verdict` adds placement errors (R4): "solid" when a solidity certificate passes
(`Robust.lean`), "risky" when the build only stands at the exact positions. -/

namespace KaplaPhysics

open Solver (Motion allSupports)

/-- How much the point `(x, y)` of support `s` rises under the motion `ms` (one entry per
plank, missing entries mean "does not move"). The ground does not move. -/
def rise (b : Build) (ms : List Motion) (s : Support) (x y : Rat) : Rat :=
  match s with
  | .ground => 0
  | .plank j =>
      let m := ms.getD j default
      m.lift + m.tiltX * (x - (b.get j).centerX) + m.tiltY * (y - (b.get j).centerY)

/-- At every corner of the patch where plank `i` rests on `s` (if they touch), plank `i`
rises at least as much as `s` under the motion `ms`. -/
def NoPushInto (b : Build) (ms : List Motion) (i : Nat) (s : Support) : Prop :=
  match restPatch b i s with
  | some r => ∀ c ∈ r.corners, rise b ms s c.1 c.2 ≤ rise b ms (.plank i) c.1 c.2
  | none => True

instance (b : Build) (ms : List Motion) (i : Nat) (s : Support) :
    Decidable (NoPushInto b ms i s) := by
  unfold NoPushInto; cases restPatch b i s <;> infer_instance

/-- A reason the build must fall: a small motion of the planks such that
1. at every corner of every contact patch, the upper plank rises at least as much as its
   support (no plank moves into what holds it up), and
2. the sum of the planks' centre lifts is below zero (the total weight goes down).

If balancing pushes existed, they would do work on this motion that is at least zero, while
the weight does work below zero; the two must be equal. So no such pushes exist. -/
def FallCertificate (b : Build) (ms : List Motion) : Prop :=
  (∀ i < b.length, ∀ s ∈ allSupports b.length, NoPushInto b ms i s) ∧
  ((List.range b.length).map fun i => (ms.getD i default).lift).sum < 0

instance (b : Build) (ms : List Motion) : Decidable (FallCertificate b ms) := by
  unfold FallCertificate; infer_instance

/-- The engine's answer to "does the build stand at the exact positions?" -/
inductive Answer where
  | stable
  | falls
  | unknown
  deriving Repr, DecidableEq

/-- Check that the pushes are allowed and balance every plank (S2). -/
def checkPushes (b : Build) (ps : List Push) : Bool :=
  decide (∀ p ∈ ps, p.Allowed b) && decide (∀ i < b.length, Balanced b ps i)

/-- Builds up to this many planks also get the global LPs, which are slow but find more
answers than the top-down solvers. -/
def globalLimit : Nat := 40

/-- Ask the global solver, then check what it proposes. -/
def globalAnswer (b : Build) : Answer :=
  match Solver.solve b with
  | .stands ps => if checkPushes b ps then .stable else .unknown
  | .falls ms => if decide (FallCertificate b ms) then .falls else .unknown
  | .gaveUp => .unknown

/-- For a large build where the top-down solver got stuck at plank `i`: look for a fall
certificate that moves only `i` and the planks above it, and check it. -/
def fallAboveAnswer (b : Build) (i : Nat) : Answer :=
  match Solver.solveAbove b i with
  | some ms => if decide (FallCertificate b ms) then .falls else .unknown
  | none => .unknown

/-- The global answer for small builds; for large ones, a fall check around plank `i`. -/
def fallbackAnswer (b : Build) (i : Nat) : Answer :=
  if b.length ≤ globalLimit then globalAnswer b else fallAboveAnswer b i

/-- Ask the fast top-down solver; if it finds no pushes that pass the check, ask the global
solver (small builds) or look for a fall certificate where it got stuck (large builds). -/
def stabilityAnswer (b : Build) : Answer :=
  match Solver.solveLocal b with
  | .ok ps => if checkPushes b ps then .stable else fallbackAnswer b 0
  | .error i => fallbackAnswer b i

/-- Is the build solid for placement errors up to `ε`? Ask the untrusted solver for a
certificate, then check it. "No" can mean "not solid" or "the cautious check could not
show it". -/
def solidAnswer (ε : Rat) (b : Build) : Bool :=
  passes (RobustSolver.proposeLoadsLocal ε b) ||
    (b.length ≤ globalLimit && passes (RobustSolver.proposeLoads ε b))
where
  /-- The proposed certificate exists and passes the check. -/
  passes : Option (List Load) → Bool
    | some ls => decide (SolidCertificate ε b ls)
    | none => false

/-- R4. The three answers, plus "unknown" if a check fails. -/
inductive Verdict where
  /-- Stands even with placement errors up to `ε`. -/
  | solid
  /-- Stands at the exact positions; not shown to stand with errors. -/
  | risky
  /-- Does not stand even at the exact positions. -/
  | falls
  | unknown
  deriving Repr, DecidableEq

/-- The engine's verdict for a build, for placement errors up to `ε`. -/
def verdict (ε : Rat) (b : Build) : Verdict :=
  if solidAnswer ε b then .solid
  else match stabilityAnswer b with
    | .stable => .risky
    | .falls => .falls
    | .unknown => .unknown

/-- Check a build plan (K4, K5): at most `maxPlanks` planks, and after every step the
build so far is well-formed and solid for placement errors up to `ε`. -/
def checkPlan (ε : Rat) (maxPlanks : Nat) (steps : Build) : Bool :=
  decide (steps.length ≤ maxPlanks) &&
    (List.range steps.length).all fun k =>
      decide (WellFormed (steps.take (k + 1))) && solidAnswer ε (steps.take (k + 1))

end KaplaPhysics
