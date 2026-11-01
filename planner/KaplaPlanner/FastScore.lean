import Std.Data.HashMap
import Std.Data.HashSet
import KaplaPlanner.Table

/-! # The fast score

The planner's own copy of the scorer's formula (`semantics/APPROACH.md` §4), updated one block
at a time. A cell of a bubble is covered when it lies between two built cells of that same
bubble on one grid line along x, y or z. So for each bubble and each grid line we keep only the
first and the last built cell (the span). Adding a block widens some spans; the cells that the
wider spans newly reach become covered.

    score = covered / (target + extra)

`extra` counts built cells in no bubble. The planner may not import the scorer, so the tests
below compare the fast score with `refCounts`, a direct version of the same definition that
recomputes everything from the block list. See `planner/DESIGN.md` §4.2. -/

namespace KaplaPlanner

open KaplaCore

/-- The coordinate of a cell along axis `a` (0 = x, 1 = y, 2 = z). -/
def coordOf (a : Nat) (c : Cell) : Int :=
  if a == 0 then c.1 else if a == 1 then c.2.1 else c.2.2

/-- The cell with its coordinate along axis `a` replaced by `t`. -/
def withCoord (a : Nat) (c : Cell) (t : Int) : Cell :=
  if a == 0 then (t, c.2.1, c.2.2) else if a == 1 then (c.1, t, c.2.2) else (c.1, c.2.1, t)

/-- A number for the grid line through `c` along axis `a`, inside bubble `b`. -/
def Table.lineKey (t : Table) (b a : Nat) (c : Cell) : Nat :=
  let x := (c.1 - t.x0).toNat
  let y := (c.2.1 - t.y0).toNat
  let z := c.2.2.toNat
  let line := if a == 0 then z * t.ny + y else if a == 1 then z * t.nx + x else y * t.nx + x
  (line * 3 + a) * 64 + b

/-- Is bit `b` set in the mask? -/
def hasBit (m : UInt64) (b : Nat) : Bool := (m >>> b.toUInt64) &&& 1 == 1

/-- The fast score's state for a partly built plan. -/
structure ScoreState where
  /-- Cells that are covered (block cells in a bubble, and the filled insides). -/
  covered : Array Bool
  /-- For each (bubble, axis, line) with a built cell: the first and last built position. -/
  spans : Std.HashMap Nat (Int × Int)
  /-- The number of covered cells. -/
  coveredCount : Nat
  /-- The number of built cells in no bubble. -/
  extra : Nat
  /-- Bit `i` is set when bubble `i` has a built cell. -/
  touched : UInt64 := 0
  deriving Inhabited

/-- The state with nothing built. -/
def ScoreState.empty (t : Table) : ScoreState :=
  { covered := Array.replicate t.mask.size false, spans := {}, coveredCount := 0, extra := 0 }

/-- The score of a state, as the scorer computes it: 0 when there is nothing to compare. -/
def scoreOf (target covered extra : Nat) : Q :=
  if target + extra == 0 then 0 else (covered : Q) / ((target + extra : Nat) : Q)

/-- The score of the state. -/
def ScoreState.score (t : Table) (s : ScoreState) : Q := scoreOf t.target s.coveredCount s.extra

/-- What adding some cells would change. -/
structure Delta where
  /-- Newly covered cells (positions in the table), each once. -/
  newly : List Nat
  /-- Built cells in no bubble. -/
  dE : Nat
  /-- Of those, the cells with a bubble cell above them in the same column (foundation). -/
  dEUnder : Nat
  /-- Spans that get wider, with their new ends. -/
  spanSets : List (Nat × (Int × Int))
  /-- The bubbles the cells are in. -/
  touches : UInt64 := 0
  deriving Inhabited

/-- How many cells become covered. -/
def Delta.dC (d : Delta) : Nat := d.newly.length

/-- What adding these cells (one block, not yet built) would change. Cells must not be built
already. -/
def delta (t : Table) (s : ScoreState) (cells : List Cell) : Delta := Id.run do
  let mut dE := 0
  let mut dEUnder := 0
  let mut touches : UInt64 := 0
  -- for each (bubble, axis, line): the bubble, the axis, a cell on the line, the lowest and
  -- highest new position
  let mut groups : Std.HashMap Nat (Nat × Nat × Cell × Int × Int) := {}
  for c in cells do
    let m := t.maskAt c
    touches := touches ||| m
    if m == 0 then
      dE := dE + 1
      if t.under c then dEUnder := dEUnder + 1
    else
      for b in [0:t.placed.size] do
        if hasBit m b then
          for a in [0:3] do
            let key := t.lineKey b a c
            let tc := coordOf a c
            groups := match groups[key]? with
              | some (b', a', c', lo, hi) => groups.insert key (b', a', c', min lo tc, max hi tc)
              | none => groups.insert key (b, a, c, tc, tc)
  let mut seen : Std.HashSet Nat := {}
  let mut newly : List Nat := []
  let mut sets : List (Nat × (Int × Int)) := []
  for (key, (b, a, c, tmin, tmax)) in groups.toList do
    let old := s.spans[key]?
    let ranges : List (Int × Int) := match old with
      | none => [(tmin, tmax)]
      | some (lo, hi) => [(tmin, lo - 1), (hi + 1, tmax)]
    match old with
    | none => sets := (key, (tmin, tmax)) :: sets
    | some (lo, hi) => if tmin < lo || hi < tmax then sets := (key, (min lo tmin, max hi tmax)) :: sets
    for (r0, r1) in ranges do
      for tt in intRange r0 r1 do
        let k := t.index (withCoord a c tt)
        if hasBit t.mask[k]! b && !s.covered[k]! && !seen.contains k then
          seen := seen.insert k
          newly := k :: newly
  return { newly, dE, dEUnder, spanSets := sets, touches }

/-- Apply a change. -/
def ScoreState.apply (s : ScoreState) (d : Delta) : ScoreState := Id.run do
  let mut covered := s.covered
  for k in d.newly do covered := covered.set! k true
  let mut spans := s.spans
  for (key, span) in d.spanSets do spans := spans.insert key span
  return { covered, spans, coveredCount := s.coveredCount + d.dC, extra := s.extra + d.dE,
           touched := s.touched ||| d.touches }

/-- The number of set bits. -/
def popCount (m : UInt64) : Nat :=
  (List.range 64).countP fun i => hasBit m i

/-- How many bubbles the change touches that have no built cell yet. -/
def Delta.firstTouches (d : Delta) (s : ScoreState) : Nat := popCount (d.touches &&& ~~~s.touched)

/-- Add one block. -/
def ScoreState.add (t : Table) (s : ScoreState) (b : GBlock) : ScoreState :=
  s.apply (delta t s b.cells)

/-- The fast score of a list of blocks, added one at a time. -/
def fastScore (t : Table) (blocks : List GBlock) : ScoreState :=
  blocks.foldl (ScoreState.add t) (ScoreState.empty t)

/-! ## The reference: the same definition, computed directly -/

/-- Covered and extra cells, computed from the block list in one go: a bubble cell is covered
when some line through it, along x, y or z, has built cells of that bubble on both sides (or at
the cell). Blocks must not overlap. Slow; for tests. -/
def refCounts (t : Table) (blocks : List GBlock) : Nat × Nat := Id.run do
  let built := blocks.flatMap GBlock.cells
  let extra := built.countP fun c => t.maskAt c == 0
  let mut spans : Std.HashMap Nat (Int × Int) := {}
  for c in built do
    let m := t.maskAt c
    for b in [0:t.placed.size] do
      if hasBit m b then
        for a in [0:3] do
          let key := t.lineKey b a c
          let tc := coordOf a c
          spans := spans.insert key (match spans[key]? with
            | some (lo, hi) => (min lo tc, max hi tc)
            | none => (tc, tc))
  let mut covered := 0
  for z in intRange 0 (t.nz - 1) do
    for y in intRange t.y0 (t.y0 + t.ny - 1) do
      for x in intRange t.x0 (t.x0 + t.nx - 1) do
        let c : Cell := (x, y, z)
        let m := t.maskAt c
        let isCovered := (List.range t.placed.size).any fun b => hasBit m b &&
          (List.range 3).any fun a => match spans[t.lineKey b a c]? with
            | some (lo, hi) => lo ≤ coordOf a c && coordOf a c ≤ hi
            | none => false
        if isCovered then covered := covered + 1
  return (covered, extra)

/-- Example: a flat block lying in the ball at height 2. -/
private def flatInBall : GBlock := ⟨.flatX, 0, 0, 0⟩

-- The example of APPROACH.md §6: one cell of the block is in the ball, 44 stick out, the ball
-- has 8 cells, so the score is 1 / 52.
#guard
  let t := Table.make ballModel 2
  let s := fastScore t [flatInBall]
  s.coveredCount == 1 && s.extra == 44 && s.score t == 1 / 52

-- Two walls of a hollow tower in the egg at height 30: the middle between them counts.
private def eggWalls : List GBlock := [⟨.flatX, -7, -6, 15⟩, ⟨.flatX, -7, 3, 15⟩]

#guard
  let t := Table.make BubbleModel.egg 30
  let s := fastScore t eggWalls
  s.coveredCount > 90 && (s.coveredCount, s.extra) == refCounts t eggWalls

-- The fast score equals the direct one, block by block, on a small log-cabin stack in the
-- ball at height 12, in either order.
private def smallCabin : List GBlock :=
  [⟨.flatX, -7, -5, 0⟩, ⟨.flatX, -7, 2, 0⟩, ⟨.flatY, -5, -7, 1⟩, ⟨.flatY, 2, -7, 1⟩,
   ⟨.flatX, -7, -4, 2⟩, ⟨.flatX, -7, 1, 2⟩, ⟨.flatY, -1, -7, 3⟩]

#guard
  let t := Table.make ballModel 12
  (List.range (smallCabin.length + 1)).all fun n =>
    let bs := smallCabin.take n
    let s := fastScore t bs
    (s.coveredCount, s.extra) == refCounts t bs &&
      (fastScore t bs.reverse).coveredCount == s.coveredCount

-- A block far away covers nothing and adds 45 extra cells.
#guard
  let t := Table.make ballModel 2
  let s := fastScore t [⟨.flatX, 100, 0, 0⟩]
  s.coveredCount == 0 && s.extra == 45

end KaplaPlanner
