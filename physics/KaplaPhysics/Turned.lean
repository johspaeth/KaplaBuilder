import KaplaSpecs.PhysicsRules.Turned
import KaplaPhysics.Solver

/-! # Checking turned plans (B6)

The solver here is untrusted, like `Solver.lean`: it finds the corners of every contact
patch by clipping one plank's face with the other's, and asks the simplex for pushes at
those corners. `checkTPushes` checks the pushes against the rules, so a wrong corner or a
wrong push only makes the answer "not shown to stand". -/

namespace KaplaPhysics

namespace Turned

/-- The four corners of the plank's bottom face, going round counter-clockwise. -/
def corners (p : TPlank) : List (Rat × Rat) :=
  let c := p.rot.cos
  let s := p.rot.sin
  let a := p.halfLength
  let w := p.halfWidth
  [(-1, -1), (1, -1), (1, 1), (-1, 1)].map fun (σ, τ) =>
    (p.cx + σ * a * c - τ * w * s, p.cy + σ * a * s + τ * w * c)

/-- Keep the part of a polygon where `f ≤ 0` (`f` is linear), adding the points where its
sides cross `f = 0`. -/
def clipBy (f : Rat × Rat → Rat) (poly : List (Rat × Rat)) : List (Rat × Rat) :=
  let n := poly.length
  (List.range n).flatMap fun i =>
    let p := poly.getD i (0, 0)
    let q := poly.getD ((i + 1) % n) (0, 0)
    let fp := f p
    let fq := f q
    let cross : List (Rat × Rat) :=
      if (fp < 0 && 0 < fq) || (0 < fp && fq < 0) then
        let t := fp / (fp - fq)
        [(p.1 + t * (q.1 - p.1), p.2 + t * (q.2 - p.2))]
      else []
    (if fp ≤ 0 then [p] else []) ++ cross

/-- The corners of the part of `poly` that lies under plank `q`. -/
def clipTo (q : TPlank) (poly : List (Rat × Rat)) : List (Rat × Rat) :=
  let along := fun (pt : Rat × Rat) => q.along pt.1 pt.2
  let across := fun (pt : Rat × Rat) => q.across pt.1 pt.2
  poly |> clipBy (fun pt => along pt - q.halfLength) |> clipBy (fun pt => -along pt - q.halfLength)
    |> clipBy (fun pt => across pt - q.halfWidth) |> clipBy (fun pt => -across pt - q.halfWidth)

/-- One unknown push: plank `upper` rests on `lower`, at the point `(x, y)`. -/
structure Unknown where
  upper : Nat
  lower : Support
  x : Rat
  y : Rat
  deriving Inhabited

/-- Every corner of every contact patch of the build. -/
def unknowns (b : TBuild) : Array Unknown := Id.run do
  let mut out := #[]
  for i in List.range b.length do
    for s in Solver.allSupports b.length do
      if decide (TRestsOn b i s) then
        let pts := match s with
          | .ground => corners (b.get i)
          | .plank j => clipTo (b.get j) (corners (b.get i))
        for (x, y) in pts do out := out.push ⟨i, s, x, y⟩
  return out

/-- The column of the equations for one unknown: rows `3i`, `3i+1`, `3i+2` are the force
and the two turnings of plank `i`, as in `Solver.column`. -/
def column (b : TBuild) (m : Nat) (u : Unknown) : Array Rat := Id.run do
  let mut col := Array.replicate m 0
  let p := b.get u.upper
  col := col.set! (3 * u.upper) 1
  col := col.set! (3 * u.upper + 1) (u.x - p.cx)
  col := col.set! (3 * u.upper + 2) (u.y - p.cy)
  match u.lower with
  | .plank j =>
      let q := b.get j
      col := col.modify (3 * j) (· - 1)
      col := col.modify (3 * j + 1) (· - (u.x - q.cx))
      col := col.modify (3 * j + 2) (· - (u.y - q.cy))
  | .ground => pure ()
  return col

/-- Propose pushes that balance every plank, if the simplex finds some. -/
def solve (b : TBuild) (fuel : Nat := 100000) : Option (List Push) :=
  let m := 3 * b.length
  let us := unknowns b
  let rhs := (Array.range m).map fun r => if r % 3 == 0 then (1 : Rat) else 0
  match Solver.phaseOne m (us.map (column b m)) rhs fuel with
  | .feasible x =>
    some <| (List.range us.size).filterMap fun j =>
      let u : Unknown := us[j]!
      if x[j]! == 0 then none
      else some { upper := u.upper, lower := u.lower, x := u.x, y := u.y, force := x[j]! }
  | _ => none

end Turned

/-- Check that the pushes are allowed and balance every turned plank (S2). -/
def checkTPushes (b : TBuild) (ps : List Push) : Bool :=
  decide (∀ p ∈ ps, TPushAllowed b p) && decide (∀ i < b.length, TBalanced b ps i)

/-- The turned build is shown to stand at its planned positions: the solver proposes pushes
and they pass the check. -/
def tStands (b : TBuild) : Bool :=
  match Turned.solve b with
  | some ps => checkTPushes b ps
  | none => false

/-- Check a turned plan: at most `maxPlanks` planks, and after every step the build so far
is well-formed and shown to stand at the planned positions. -/
def checkTurnedPlan (maxPlanks : Nat) (steps : TBuild) : Bool :=
  decide (steps.length ≤ maxPlanks) &&
    (List.range steps.length).all fun k =>
      decide (TWellFormed (steps.take (k + 1))) && tStands (steps.take (k + 1))

end KaplaPhysics

namespace KaplaPhysics.TurnedTests

/-- A flat plank at 45° on the ground, centred at the origin. -/
private def p45 : TPlank := ⟨.flat, .step15 3, 0, 0, 0⟩
/-- A flat plank along `x` on the ground. -/
private def base : TPlank := ⟨.flat, .id, 0, 0, 0⟩
/-- `p` lifted so it rests on a flat plank on the ground. -/
private def onTop (p : TPlank) : TPlank := { p with z := 1 }

#guard checkTurnedPlan 200 [p45]
-- A spiral: each plank turned 15° more than the one below, centred.
#guard checkTurnedPlan 200 ((List.range 6).map fun k => ⟨.flat, .step15 k, 0, 0, (k : Rat)⟩)
-- A plank at 45° across a plank along `x`.
#guard checkTurnedPlan 200 [base, onTop p45]
-- Off-centre so far that its centre is past the plank below: not shown to stand.
#guard !checkTurnedPlan 200 [base, { onTop p45 with cx := 10, cy := 10 }]
-- A bridge at 30° across two rails 9 apart.
#guard checkTurnedPlan 200 [⟨.flat, .id, 0, -6, 0⟩, ⟨.flat, .id, 0, 6, 0⟩,
  ⟨.flat, .step15 8, 0, 0, 1⟩]
-- Crossing at the same height: overlap, refused.
#guard !checkTurnedPlan 200 [base, p45]
-- More planks than allowed.
#guard !checkTurnedPlan 1 [base, onTop p45]

end KaplaPhysics.TurnedTests
