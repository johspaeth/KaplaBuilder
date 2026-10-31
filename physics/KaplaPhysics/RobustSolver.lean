import KaplaPhysics.Robust
import KaplaPhysics.Solver

/-! # Untrusted search for a solidity certificate

Nothing here is trusted. The engine checks the result with `SolidCertificate`.

1. **Loads and points (an LP).** For each contact `e` (plank `i` on support `s`, patch
   `[ax, bx] × [ay, by]`) we look for a load `L ≥ 0` and a point `(px, py)` with balance for
   every plank in the planned build. The point keeps a margin `μ` from each patch edge,
   large enough for the drift the checker will measure:
   * on a plank: `μ = 2ε` (the point and either plank can each move by `ε`);
   * on the ground: `μ = 2ε · (L - 1) / L`, since the plank's own weight moves with the
     plank and its footprint. Written for the LP: `L · μ = 2ε · (load from above)`.
   With `P = L · p`, all of this is linear in `L` and `P`.
2. **How points move (top to bottom).** Plank `i` carries its weight and the loads from
   above. Their combined point moves with the errors as `G / Ltot`, where `G` sums
   `e_i` (its own error) and `L · mix` of each load from above. Every load from `i` to
   its supports gets that same `mix`. -/

namespace KaplaPhysics.RobustSolver

open Solver (allSupports phaseOne LPResult)

/-- A contact in the planned build: plank `upper` rests on `lower` over `patch`. -/
structure Contact where
  upper : Nat
  lower : Support
  patch : Rect
  deriving Inhabited

/-- Every contact of the planned build. -/
def contacts (b : Build) : Array Contact := Id.run do
  let mut out := #[]
  for i in List.range b.length do
    for s in allSupports b.length do
      if let some r := restPatch b i s then out := out.push ⟨i, s, r⟩
  return out

/-- Insert `i` into `order`, keeping higher planks first. -/
def insertByHeight (b : Build) (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: js => if (b.get i).z ≥ (b.get j).z then i :: j :: js else j :: insertByHeight b i js

/-- Propose a solidity certificate for errors up to `ε`, or give up. -/
def proposeLoads (ε : Rat) (b : Build) (fuel : Nat := 100000) : Option (List Load) := Id.run do
  let n := b.length
  let cs := contacts b
  let nc := cs.size
  -- Unknowns of contact `e`: L = 5e, Qx = 5e+1, Qy = 5e+2, Sx = 5e+3, Sy = 5e+4.
  -- Rows: plank `i`: force 3i, turning x 3i+1, turning y 3i+2.
  --       contact `e`: room along x 3n+2e, room along y 3n+2e+1.
  let m := 3 * n + 2 * nc
  let mut cols := Array.replicate (5 * nc) (Array.replicate m (0 : Rat))
  let add := fun (cols : Array (Array Rat)) (c r : Nat) (v : Rat) =>
    cols.modify c fun col => col.modify r (· + v)
  -- The ground contact of each plank, if any.
  let groundOf := fun i => cs.findIdx? fun c => c.upper == i && c.lower == .ground
  for e in List.range nc do
    let c := cs[e]!
    let i := c.upper
    let r := c.patch
    let (L, Qx, Qy, Sx, Sy) := (5 * e, 5 * e + 1, 5 * e + 2, 5 * e + 3, 5 * e + 4)
    let (rx, ry) := (3 * n + 2 * e, 3 * n + 2 * e + 1)
    -- P = L · a + μ + Q acts up on plank `i`.
    cols := add cols L (3 * i) 1
    cols := add cols L (3 * i + 1) r.x0
    cols := add cols L (3 * i + 2) r.y0
    cols := add cols Qx (3 * i + 1) 1
    cols := add cols Qy (3 * i + 2) 1
    -- Room: Q + S = L · (b - a) - 2μ.
    cols := add cols L rx (r.x1 - r.x0)
    cols := add cols L ry (r.y1 - r.y0)
    cols := add cols Qx rx (-1)
    cols := add cols Qy ry (-1)
    cols := add cols Sx rx (-1)
    cols := add cols Sy ry (-1)
    match c.lower with
    | .plank j =>
      -- μ = 2ε on both sides; the same load acts down on plank `j`.
      cols := add cols L (3 * i + 1) (2 * ε)
      cols := add cols L (3 * i + 2) (2 * ε)
      cols := add cols L rx (-4 * ε)
      cols := add cols L ry (-4 * ε)
      cols := add cols L (3 * j) (-1)
      cols := add cols L (3 * j + 1) (-(r.x0 + 2 * ε))
      cols := add cols L (3 * j + 2) (-(r.y0 + 2 * ε))
      cols := add cols Qx (3 * j + 1) (-1)
      cols := add cols Qy (3 * j + 2) (-1)
      -- This load also widens the margin of plank `j`'s ground contact.
      -- The ground contact's `μ` acts up on `j` (+2ε per unit of load from above) and
      -- takes room on both sides (-4ε).
      if let some g := groundOf j then
        cols := add cols L (3 * j + 1) (2 * ε)
        cols := add cols L (3 * j + 2) (2 * ε)
        cols := add cols L (3 * n + 2 * g) (-(4 * ε))
        cols := add cols L (3 * n + 2 * g + 1) (-(4 * ε))
    | .ground => pure ()
  let rhs := (Array.range m).map fun r =>
    if r < 3 * n then
      let p := b.get (r / 3)
      if r % 3 == 0 then (1 : Rat) else if r % 3 == 1 then p.centerX else p.centerY
    else 0
  let some x := (match phaseOne m cols rhs fuel with
    | .feasible x => some x
    | _ => none) | return none
  -- Load points.
  let load := fun e => x[5 * e]!
  let fromAbove := fun i =>
    (List.range nc).foldl (fun s e => if cs[e]!.lower == .plank i then s + load e else s) 0
  let point := fun e =>
    let c := cs[e]!
    let L := load e
    let μ := match c.lower with
      | .plank _ => 2 * ε * L
      | .ground => 2 * ε * fromAbove c.upper
    ((c.patch.x0 * L + μ + x[5 * e + 1]!) / L, (c.patch.y0 * L + μ + x[5 * e + 2]!) / L)
  -- How points move: top planks first.
  let order := (List.range n).foldr (insertByHeight b) []
  let mut mixOf : Array (Array Rat) := Array.replicate n (Array.replicate n 0)
  for i in order do
    let mut g := (Array.replicate n (0 : Rat)).set! i 1
    let mut total : Rat := 0
    for e in List.range nc do
      let c := cs[e]!
      if c.lower == .plank i && load e != 0 then
        g := g.zipWith (fun a v => a + load e * v) mixOf[c.upper]!
      if c.upper == i then total := total + load e
    if total != 0 then mixOf := mixOf.set! i (g.map (· / total))
  return some <| (List.range nc).filterMap fun e =>
    let c := cs[e]!
    if load e == 0 then none
    else
      let (px, py) := point e
      some { upper := c.upper, lower := c.lower, force := load e, x := px, y := py,
             mix := mixOf[c.upper]!.toList }

end KaplaPhysics.RobustSolver
