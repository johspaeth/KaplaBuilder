import KaplaPhysics.Robust
import KaplaPhysics.Solver

/-! # Untrusted search for a solidity certificate

Nothing here is trusted. The engine checks the result with `SolidCertificate`.

1. **Loads and points (an LP).** For each contact `e` (plank `i` on support `s`) we look for
   a load `L ≥ 0` and a point `p` with balance for every plank in the planned build. Every
   side `g` of the patch must be at least `μ · slope g` at `p`, with a margin `μ` large
   enough for the drift the checker will measure:
   * on a plank: `μ = 2ε` (the point and either plank can each move by `ε`);
   * on the ground: `μ = 2ε · (L - 1) / L`, since the plank's own weight moves with the
     plank and its footprint. Written for the LP: `L · μ = 2ε · (load from above)`.
   With `P = L · p`, all of this is linear in `L` and `P`.
2. **How points move (top to bottom).** Plank `i` carries its weight and the loads from
   above. Their combined point moves with the errors as `G / Ltot`, where `G` sums
   `e_i` (its own error) and `L · mix` of each load from above. Every load from `i` to
   its supports gets that same `mix`.
3. **A point inside the patch.** For a contact on a plank, the average of the patch's
   corners. -/

namespace KaplaPhysics.RobustSolver

open Solver (allSupports phaseOne LPResult insertByHeight)

/-- A contact in the planned build: plank `upper` rests on `lower`; `forms` are the sides of
the patch. -/
structure Contact where
  upper : Nat
  lower : Support
  forms : List Aff
  deriving Inhabited

/-- Every contact of the planned build. -/
def contacts (b : Build) : Array Contact := Id.run do
  let mut out := #[]
  for i in List.range b.length do
    for s in allSupports b.length do
      if restsCheck b i s then out := out.push ⟨i, s, contactForms b i s⟩
  return out

/-- A column with the given entries, zero elsewhere. -/
def column (m : Nat) (entries : List (Nat × Rat)) : Array Rat :=
  entries.foldl (fun c (r, v) => c.modify r (· + v)) (Array.replicate m 0)

/-- The point inside the patch that moves with the upper plank. -/
def witness (b : Build) (i : Nat) (s : Support) : Rat × Rat :=
  match s with
  | .ground => ((b.get i).center.x, (b.get i).center.y)
  | .plank j => (average (patchPoly (b.get i) (b.get j))).getD (0, 0)

/-- How the load points of each plank move with the errors (step 2), given every contact's
load. -/
def mixes (b : Build) (cs : Array Contact) (load : Nat → Rat) : Array (Array Rat) := Id.run do
  let n := b.length
  let order := (List.range n).foldr (insertByHeight b) []
  let mut mixOf : Array (Array Rat) := Array.replicate n (Array.replicate n 0)
  for i in order do
    let mut g := (Array.replicate n (0 : Rat)).set! i 1
    let mut total : Rat := 0
    for e in List.range cs.size do
      let c := cs[e]!
      if c.lower == .plank i && load e != 0 then
        g := g.zipWith (fun a v => a + load e * v) mixOf[c.upper]!
      if c.upper == i then total := total + load e
    if total != 0 then mixOf := mixOf.set! i (g.map (· / total))
  return mixOf

/-- Propose a solidity certificate for errors up to `ε` with one LP for the whole build,
or give up. Slow for large builds. -/
def proposeLoads (ε : Rat) (b : Build) (fuel : Nat := 100000) : Option (List Load) := Id.run do
  let n := b.length
  let cs := contacts b
  let nc := cs.size
  -- Unknowns of contact `e`, from `var e`: L, Px⁺, Px⁻, Py⁺, Py⁻, then one slack per side.
  -- Rows: plank `i`: force 3i, turning x 3i+1, turning y 3i+2; then one row per side of
  -- each contact, from `row e`.
  let var := fun e => ((List.range e).map fun e' => 5 + (cs[e']!).forms.length).sum
  let row := fun e => 3 * n + ((List.range e).map fun e' => (cs[e']!).forms.length).sum
  let m := row nc
  -- The ground contact of each plank, if any.
  let groundOf := fun i => cs.findIdx? fun c => c.upper == i && c.lower == .ground
  let mut cols : Array (Array Rat) := #[]
  for e in List.range nc do
    let c := cs[e]!
    let i := c.upper
    let fs := c.forms.zipIdx
    let μ : Rat := if c.lower == .ground then 0 else 2 * ε
    let below : List (Nat × Rat) := match c.lower with
      | .plank j => [(3 * j, -1)]
      | .ground => []
    -- This load widens the margin of plank `j`'s ground contact.
    let widen : List (Nat × Rat) := match c.lower with
      | .plank j => match groundOf j with
        | some g => (cs[g]!).forms.zipIdx.map fun (f, k) => (row g + k, -(2 * ε * f.slope))
        | none => []
      | .ground => []
    let colL := column m ([(3 * i, 1)] ++ below ++ widen ++
      fs.map fun (f, k) => (row e + k, f.c - μ * f.slope))
    let side := fun (r : Nat) (coef : Aff → Rat) (sign : Rat) =>
      column m ([(3 * i + r, sign)] ++
        (match c.lower with | .plank j => [(3 * j + r, -sign)] | .ground => []) ++
        fs.map fun (f, k) => (row e + k, sign * coef f))
    cols := cols.push colL
    cols := cols.push (side 1 (·.a) 1)
    cols := cols.push (side 1 (·.a) (-1))
    cols := cols.push (side 2 (·.b) 1)
    cols := cols.push (side 2 (·.b) (-1))
    for (_, k) in fs do
      cols := cols.push (column m [(row e + k, -1)])
  let rhs := (Array.range m).map fun r =>
    if r < 3 * n then
      let p := b.get (r / 3)
      if r % 3 == 0 then (1 : Rat) else if r % 3 == 1 then p.centerX else p.centerY
    else 0
  let some x := (match phaseOne m cols rhs fuel with
    | .feasible x => some x
    | _ => none) | return none
  let load := fun e => x[var e]!
  let mixOf := mixes b cs load
  return some <| (List.range nc).filterMap fun e =>
    let c := cs[e]!
    let L := load e
    if L == 0 then none
    else
      let v := var e
      let (wx, wy) := witness b c.upper c.lower
      some { upper := c.upper, lower := c.lower, force := L,
             x := (x[v + 1]! - x[v + 2]!) / L, y := (x[v + 3]! - x[v + 4]!) / L,
             mix := mixOf[c.upper]!, wx, wy }

/-- Fast version of `proposeLoads`: settle one plank at a time, from the top down. Each
plank passes its own weight and the loads it carries to its supports, using a small LP
with the same margins as above. It can miss certificates that the global LP finds (it
never revisits a choice), so the engine falls back to `proposeLoads` for small builds. -/
def proposeLoadsLocal (ε : Rat) (b : Build) (fuel : Nat := 10000) : Option (List Load) :=
    Id.run do
  let n := b.length
  let mut inL := Array.replicate n (0 : Rat)    -- load from above
  let mut inPx := Array.replicate n (0 : Rat)   -- load times its point
  let mut inPy := Array.replicate n (0 : Rat)
  let mut inG := Array.replicate n (Array.replicate n (0 : Rat))  -- load times its mix
  let mut out : List Load := []
  for i in (List.range n).foldr (insertByHeight b) [] do
    let p := b.get i
    let lin := inL[i]!
    let sup := (allSupports n).filter fun s => restsCheck b i s
    let forms := sup.map fun s => contactForms b i s
    let k := sup.length
    -- Rows: force 0, turning 1 and 2, then one row per side of each support, from `row t`.
    let row := fun t => 3 + ((forms.take t).map List.length).sum
    let m := row k
    let mut cols : Array (Array Rat) := #[]
    let mut rhs := (Array.replicate m (0 : Rat)).set! 0 (1 + lin)
      |>.set! 1 (p.centerX + inPx[i]!) |>.set! 2 (p.centerY + inPy[i]!)
    for t in List.range k do
      let s := sup[t]!
      let fs := forms[t]!.zipIdx
      let onPlank := s != .ground
      let μ : Rat := if onPlank then 2 * ε else 0
      cols := cols.push (column m ([(0, 1)] ++ fs.map fun (f, j) => (row t + j, f.c - μ * f.slope)))
      cols := cols.push (column m ([(1, 1)] ++ fs.map fun (f, j) => (row t + j, f.a)))
      cols := cols.push (column m ([(1, -1)] ++ fs.map fun (f, j) => (row t + j, -f.a)))
      cols := cols.push (column m ([(2, 1)] ++ fs.map fun (f, j) => (row t + j, f.b)))
      cols := cols.push (column m ([(2, -1)] ++ fs.map fun (f, j) => (row t + j, -f.b)))
      for (_, j) in fs do
        cols := cols.push (column m [(row t + j, -1)])
      if !onPlank then
        -- On the ground the margin is `2ε · lin`, a known number here.
        for (f, j) in fs do
          rhs := rhs.set! (row t + j) (2 * ε * lin * f.slope)
    let some x := (match phaseOne m cols rhs fuel with
      | .feasible x => some x
      | _ => none) | return none
    let total := 1 + lin
    let g := ((Array.replicate n (0 : Rat)).set! i 1).zipWith (· + ·) inG[i]! |>.map (· / total)
    let var := fun t => ((forms.take t).map fun fs => 5 + fs.length).sum
    for t in List.range k do
      let s := sup[t]!
      let v := var t
      let L := x[v]!
      if L != 0 then
        let px := (x[v + 1]! - x[v + 2]!) / L
        let py := (x[v + 3]! - x[v + 4]!) / L
        let (wx, wy) := witness b i s
        out := { upper := i, lower := s, force := L, x := px, y := py, mix := g, wx, wy } :: out
        if let .plank j := s then
          inL := inL.modify j (· + L)
          inPx := inPx.modify j (· + L * px)
          inPy := inPy.modify j (· + L * py)
          inG := inG.modify j fun a => a.zipWith (fun u v => u + L * v) g
  return some out

end KaplaPhysics.RobustSolver
