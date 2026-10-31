import KaplaPhysics.Rules

/-! # Untrusted force solver

Nothing here is trusted or proven. The solver only proposes an answer; `Engine.lean`
checks every proposal with a checker that has a proof.

The question "do allowed pushes exist that balance every plank?" is a set of linear
equations in unknown pushes `f ≥ 0`. We solve it exactly, with fractions, by the simplex
method (phase one, Bland's rule so it cannot cycle). It ends in one of two ways:

* the equations have a solution: we return those pushes;
* they do not: the simplex gives numbers `y`, one per equation, that prove it
  (Farkas' lemma). Read as a small motion of every plank (lift and tilt), they lift no
  plank into its support and still lower the total weight. `Engine.lean` checks this. -/

namespace KaplaPhysics.Solver

/-- A small motion of one plank: lift its centre by `lift`, and tilt it so a point
`dx` along `x` and `dy` along `y` from the centre rises by `tiltX * dx + tiltY * dy`. -/
structure Motion where
  lift : Rat := 0
  tiltX : Rat := 0
  tiltY : Rat := 0
  deriving Repr, DecidableEq, Inhabited

/-- What the solver proposes. -/
inductive Proposal where
  | stands (pushes : List Push)
  | falls (motion : List Motion)
  | gaveUp
  deriving Repr

/-- The ground and every plank of a build with `n` planks. -/
def allSupports (n : Nat) : List Support := .ground :: (List.range n).map .plank

/-- One unknown of the equations: a push at a corner `(x, y)` of the patch where
`upper` rests on `lower`. -/
structure Unknown where
  upper : Nat
  lower : Support
  x : Rat
  y : Rat
  deriving Inhabited

/-- Every corner of every contact patch of the build. -/
def unknowns (b : Build) : Array Unknown := Id.run do
  let mut out := #[]
  for i in List.range b.length do
    for s in allSupports b.length do
      match restPatch b i s with
      | some r => for (x, y) in r.corners do out := out.push ⟨i, s, x, y⟩
      | none => pure ()
  return out

/-- The column of the equations for one unknown. Plank `i` has rows `3i` (force),
`3i+1` (turning, lever along `x`), `3i+2` (turning, lever along `y`). -/
def column (b : Build) (m : Nat) (u : Unknown) : Array Rat := Id.run do
  let mut col := Array.replicate m 0
  let p := b.get u.upper
  col := col.set! (3 * u.upper) 1
  col := col.set! (3 * u.upper + 1) (u.x - p.centerX)
  col := col.set! (3 * u.upper + 2) (u.y - p.centerY)
  match u.lower with
  | .plank j =>
      let q := b.get j
      col := col.modify (3 * j) (· - 1)
      col := col.modify (3 * j + 1) (· - (u.x - q.centerX))
      col := col.modify (3 * j + 2) (· - (u.y - q.centerY))
  | .ground => pure ()
  return col

/-- Simplex table for phase one: `rows` hold `[A | I | b]`, `cost` holds the reduced
costs (last entry: minus the current sum of the helper variables). -/
structure Table where
  rows : Array (Array Rat)
  basis : Array Nat
  cost : Array Rat

/-- Pivot on row `r`, column `j`. -/
def Table.pivot (t : Table) (r j : Nat) : Table := Id.run do
  let pr := t.rows[r]!
  let a := pr[j]!
  let pr := pr.map (· / a)
  let mut rows := t.rows.set! r pr
  for r' in List.range rows.size do
    if r' != r then
      let row := rows[r']!
      let c := row[j]!
      if c != 0 then
        rows := rows.set! r' (row.zipWith (fun v w => v - c * w) pr)
  let c := t.cost[j]!
  let cost := t.cost.zipWith (fun v w => v - c * w) pr
  return { rows, basis := t.basis.set! r j, cost }

/-- Bland's rule: the first column with a negative reduced cost. -/
def Table.entering (t : Table) (ncols : Nat) : Option Nat :=
  (List.range ncols).find? fun j => t.cost[j]! < 0

/-- Ratio test, ties broken by the smallest basic variable (Bland's rule). -/
def Table.leaving (t : Table) (j rhs : Nat) : Option Nat := Id.run do
  let mut best : Option (Nat × Rat × Nat) := none
  for r in List.range t.rows.size do
    let a := t.rows[r]![j]!
    if a > 0 then
      let ratio := t.rows[r]![rhs]! / a
      let bv := t.basis[r]!
      best := match best with
        | none => some (r, ratio, bv)
        | some (r0, q0, b0) =>
            if ratio < q0 || (ratio == q0 && bv < b0) then some (r, ratio, bv)
            else some (r0, q0, b0)
  return best.map (·.1)

/-- Run phase one for at most `fuel` pivots. -/
def Table.run (t : Table) (ncols rhs : Nat) : Nat → Option Table
  | 0 => none
  | fuel + 1 =>
    match t.entering ncols with
    | none => some t
    | some j =>
      match t.leaving j rhs with
      | none => none
      | some r => (t.pivot r j).run ncols rhs fuel

/-- The result of phase one on `A x = rhs, x ≥ 0`. -/
inductive LPResult where
  /-- A solution `x`. -/
  | feasible (x : Array Rat)
  /-- Numbers `y`, one per row, with `yᵀA ≤ 0` and `yᵀrhs > 0`: no solution exists. -/
  | infeasible (y : Array Rat)
  | gaveUp

/-- Phase one of the simplex method for `A x = rhs, x ≥ 0`. `cols` holds the columns of
`A`, each with `m` entries. Rows with a negative right side are flipped first. -/
def phaseOne (m : Nat) (cols : Array (Array Rat)) (rhsIn : Array Rat) (fuel : Nat := 100000) :
    LPResult := Id.run do
  let k := cols.size
  let rhs := k + m
  let flip := (Array.range m).map fun r => if rhsIn[r]! < 0 then (-1 : Rat) else 1
  -- Row `r` is `flip_r * [A_r | e_r | rhs_r]` with the helper `e_r` not flipped.
  let rows := (Array.range m).map fun r =>
    let a := cols.map fun c => flip[r]! * c[r]!
    let e := (Array.range m).map fun r' => if r' == r then (1 : Rat) else 0
    (a ++ e).push (flip[r]! * rhsIn[r]!)
  -- All helper variables start in the basis, each with cost 1.
  let cost := (Array.range (rhs + 1)).map fun j =>
    if k ≤ j && j < rhs then (0 : Rat) else -(rows.foldl (fun s row => s + row[j]!) 0)
  match ({ rows, basis := (Array.range m).map (k + ·), cost } : Table).run rhs rhs fuel with
  | none => return .gaveUp
  | some t =>
    if t.cost[rhs]! == 0 then
      let mut x := Array.replicate k (0 : Rat)
      for r in List.range m do
        let j := t.basis[r]!
        if j < k then x := x.set! j t.rows[r]![rhs]!
      return .feasible x
    else
      -- The reduced cost of helper column `r` is `1 - y_r` (for the flipped rows).
      return .infeasible <| (Array.range m).map fun r => flip[r]! * (1 - t.cost[k + r]!)

/-- Propose pushes that balance every plank, or a motion showing that none exist. -/
def solve (b : Build) (fuel : Nat := 100000) : Proposal :=
  let n := b.length
  let m := 3 * n
  let us := unknowns b
  -- The right side is 1 on force rows (each plank weighs 1), 0 on turning rows.
  let rhs := (Array.range m).map fun r => if r % 3 == 0 then (1 : Rat) else 0
  match phaseOne m (us.map (column b m)) rhs fuel with
  | .gaveUp => .gaveUp
  | .feasible x =>
    .stands <| (List.range us.size).filterMap fun j =>
      let u : Unknown := us[j]!
      if x[j]! == 0 then none
      else some { upper := u.upper, lower := u.lower, x := u.x, y := u.y, force := x[j]! }
  | .infeasible y =>
    -- `yᵀA ≤ 0` and `yᵀrhs > 0`; the motion is `-y`.
    .falls <| (List.range n).map fun i =>
      { lift := -y[3 * i]!, tiltX := -y[3 * i + 1]!, tiltY := -y[3 * i + 2]! }

/-- Insert `i` into `order`, keeping higher planks first. -/
def insertByHeight (b : Build) (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: js => if (b.get i).z ≥ (b.get j).z then i :: j :: js else j :: insertByHeight b i js

/-- Fast version of `solve` for builds that stand: settle one plank at a time, from the top
down. Each plank passes its weight and what it carries to the corners of its contact
patches, using a small LP. It never revisits a choice, so it can miss pushes that the
global LP finds; then the engine falls back to `solve`. -/
def solveLocal (b : Build) (fuel : Nat := 10000) : Option (List Push) := Id.run do
  let n := b.length
  let mut inF := Array.replicate n (0 : Rat)   -- push from above
  let mut inX := Array.replicate n (0 : Rat)   -- push times its x
  let mut inY := Array.replicate n (0 : Rat)
  let mut out : List Push := []
  for i in (List.range n).foldr (insertByHeight b) [] do
    let p := b.get i
    let us := (allSupports n).flatMap fun s =>
      match restPatch b i s with
      | some r => r.corners.map fun (x, y) => (s, x, y)
      | none => []
    let cols := us.toArray.map fun (_, x, y) => #[1, x - p.centerX, y - p.centerY]
    let rhs := #[1 + inF[i]!, inX[i]! - inF[i]! * p.centerX, inY[i]! - inF[i]! * p.centerY]
    let some f := (match phaseOne 3 cols rhs fuel with
      | .feasible f => some f
      | _ => none) | return none
    for k in List.range us.length do
      let (s, x, y) := us[k]!
      let fk := f[k]!
      if fk != 0 then
        out := { upper := i, lower := s, x, y, force := fk } :: out
        if let .plank j := s then
          inF := inF.modify j (· + fk)
          inX := inX.modify j (· + fk * x)
          inY := inY.modify j (· + fk * y)
  return some out

end KaplaPhysics.Solver
