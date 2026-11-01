import KaplaPlanner.FastScore
import KaplaPlanner.Support

/-! # Build: courses from the ground up

At one height, the planner builds one course (one block thick) at a time, from the ground up
(`planner/DESIGN.md` §4.3). In each course:

1. **Candidates.** Every flat block, along x or along y, that has at least one cell in a bubble
   at this course. Only these can be part of an accepted plan: a block with no cell in any
   bubble is always rejected by the scorer.
2. **Value.** `covered cells it adds − price × cells it puts outside the bubbles`, plus
   `firstBonus` for each bubble the block is the first to reach. Outside
   cells with a bubble cell above them cost only `underShare × price`: they are foundation,
   and without them a ball, which touches the ground at one point, could never be started. The cells it
   adds include the filled insides, so the second wall of a hollow tower is worth much more
   than the first.
3. **Choose.** Take the candidate with the highest value, if that value is at least `lambda`
   and the local stability rule (`Support.lean`) accepts it. Repeat until no candidate is good
   enough.

After a block goes in, the values of the candidates that share a grid line with it (they
overlap it in x or in y) are worked out again. Others can change a little too, through filled
cells on crossing lines, so the chosen candidate's value is always worked out again before it
goes in.

`perCourse` and `maxBlocks` set how many blocks the build uses (`Search.lean` chooses them).
`lambda` is a lower limit on a block's value; a high `lambda` turned out to be a poor way to
save blocks, because it also drops the low-value blocks at the bottom that everything else
rests on. `price` turns the score's ratio into a sum: a block helps the final
score `covered / (target + extra)` when it adds more than `score × extra` covered cells, so
`price` should be close to the score we expect to reach. -/

namespace KaplaPlanner

open KaplaCore

/-- The settings of one build. -/
structure BuildParams where
  /-- A block goes in only if its value is at least this (in cells). -/
  lambda : Q
  /-- What one cell outside the bubbles costs, in covered cells. -/
  price : Q
  /-- Never use more blocks than this. -/
  maxBlocks : Nat
  /-- At most this many blocks in one course; 0 means no limit. This spreads the blocks over
  the whole height, so the budget does not run out before the top. -/
  perCourse : Nat := 0
  /-- The price of a cell outside the bubbles but under a bubble cell higher up, as a share of
  `price`. Such cells are foundation: without them the courses above have nothing to rest on. -/
  underShare : Q := 1 / 4
  /-- Extra value, in cells, for each bubble a block is the first to reach. The scorer accepts a
  plan only when every bubble has a block, and a small bubble (an ear) is otherwise never worth
  a block. -/
  firstBonus : Q := 45
  /-- Extra value, in cells, for a block that lies under a bubble with no block yet that starts
  higher up. Only for the first such block of each course, so this builds one pillar up to a
  part that sits on the side, such as a head over the body. -/
  pillarBonus : Q := 45
  /-- Room left at the ends of a block's contacts (`Support.lean`). -/
  margin : Q := 1
  /-- Strict mode of the local rule (`Stack.place`): no load on an overhang. -/
  strict : Bool := false
  /-- Which way the blocks of a course lie. `some true`: along x on even courses and along y on
  odd ones (a log cabin); `some false`: the other way round; `none`: both ways in every
  course. -/
  cabin : Option Bool := some true
  deriving Repr, Inhabited

/-- The result of one build. -/
structure Built where
  /-- The blocks, in build order. -/
  blocks : Array GBlock
  /-- The fast score after the last block. -/
  state : ScoreState
  /-- The stack, with the contacts of each block. -/
  stack : Stack
  deriving Inhabited

/-- The value of a change: covered cells added, minus `price` per cell outside the bubbles
(less for foundation cells). -/
def value (p : BuildParams) (s : ScoreState) (d : Delta) : Q :=
  (d.dC : Q) - p.price * (((d.dE - d.dEUnder : Nat) : Q) + p.underShare * (d.dEUnder : Q)) +
    p.firstBonus * (d.firstTouches s : Q)

/-- How many footprint cells of `u` lie under a bubble that has no built cell (`touched`) and
starts above `u`'s course. -/
def underUntouched (t : Table) (touched : UInt64) (u : GBlock) : Nat :=
  (u.cells.filter (·.2.2 == u.z)).countP fun c =>
    (List.range t.placed.size).any fun b => !hasBit touched b && u.z < t.lowAt b c.1 c.2.1 &&
      t.lowAt b c.1 c.2.1 < t.nz

/-- The smallest box (x and y ranges) around the bubble cells of course `z`. -/
def sliceBox (t : Table) (z : Int) : Option (Int × Int × Int × Int) := Id.run do
  let mut res : Option (Int × Int × Int × Int) := none
  for y in intRange t.y0 (t.y0 + t.ny - 1) do
    for x in intRange t.x0 (t.x0 + t.nx - 1) do
      if t.maskAt (x, y, z) != 0 then
        res := some (match res with
          | some (a, b, c, d) => (min a x, max b x, min c y, max d y)
          | none => (x, x, y, y))
  return res

/-- Does the block lie inside the table's box? -/
def Table.holds (t : Table) (b : GBlock) : Bool :=
  t.x0 ≤ b.x && b.x + b.sx ≤ t.x0 + t.nx && t.y0 ≤ b.y && b.y + b.sy ≤ t.y0 + t.ny &&
    0 ≤ b.z && b.z + b.sz ≤ t.nz

/-- The ways a block of course `z` may lie. -/
def orientsAt (cabin : Option Bool) (z : Int) : List Orient :=
  match cabin with
  | none => [.flatX, .flatY]
  | some evenX => if (z % 2 == 0) == evenX then [.flatX] else [.flatY]

/-- All flat blocks of course `z`, lying the ways given, with at least one cell in a bubble. -/
def candidatesAt (t : Table) (z : Int) (orients : List Orient) : Array GBlock := Id.run do
  let mut res : Array GBlock := #[]
  match sliceBox t z with
  | none => return res
  | some (xa, xb, ya, yb) =>
    for o in orients do
      let (sx, sy, _) := o.size
      for y in intRange (ya - sy + 1) yb do
        for x in intRange (xa - sx + 1) xb do
          let b : GBlock := ⟨o, x, y, z⟩
          if t.holds b && b.cells.any (fun c => t.maskAt c != 0) then res := res.push b
    return res

/-- Do the two blocks share a grid line along x or y in their course? -/
def sharesLine (a b : GBlock) : Bool :=
  (a.x < b.x + b.sx && b.x < a.x + a.sx) || (a.y < b.y + b.sy && b.y < a.y + a.sy)

/-- Build one course on top of what is there. -/
def buildCourse (t : Table) (p : BuildParams) (z : Int) (start : Built) : Built := Id.run do
  let mut st := start.stack
  let mut sc := start.state
  let mut blocks := start.blocks
  if blocks.size ≥ p.maxBlocks then return start
  let cands := (candidatesAt t z (orientsAt p.cabin z)).filter fun u =>
    z == 0 || match contactsOf st u with
      | some cs => !cs.isEmpty
      | none => false
  let mut ds : Array (Option Delta) := cands.map fun u => some (delta t sc u.cells)
  -- the pillar bonus, while this course has no block under an untouched bubble yet
  let under := cands.map (underUntouched t sc.touched)
  let mut pillarOpen := true
  let mut inCourse := 0
  for _ in [0:cands.size] do
    if blocks.size ≥ p.maxBlocks || (p.perCourse != 0 && inCourse ≥ p.perCourse) then break
    let pillar (i : Nat) : Q := if pillarOpen && under[i]! > 0 then p.pillarBonus else 0
    -- the best candidate still open
    let mut best : Option (Nat × Q) := none
    for i in [0:cands.size] do
      match ds[i]! with
      | some d =>
        let v := value p sc d + pillar i
        if 0 < v && p.lambda ≤ v then
          match best with
          | some (_, bv) => if bv < v then best := some (i, v)
          | none => best := some (i, v)
      | none => pure ()
    match best with
    | none => break
    | some (i, _) =>
      let u := cands[i]!
      -- the stored change can be out of date: a block placed since may have filled cells on
      -- lines that cross this candidate's lines. Work it out again before using it.
      let d := delta t sc u.cells
      ds := ds.set! i none
      let v := value p sc d + pillar i
      if v ≤ 0 || v < p.lambda then continue
      match st.place u p.margin p.strict with
      | none => pure ()
      | some st' =>
        st := st'
        sc := sc.apply d
        blocks := blocks.push u
        inCourse := inCourse + 1
        if under[i]! > 0 then pillarOpen := false
        for j in [0:cands.size] do
          if ds[j]!.isSome then
            let v := cands[j]!
            if v.overlaps u then ds := ds.set! j none
            else if sharesLine u v then ds := ds.set! j (some (delta t sc v.cells))
  return { blocks, state := sc, stack := st }

/-- Build every course, from the ground up. -/
def build (t : Table) (p : BuildParams) : Built :=
  (List.range t.nz).foldl (fun b (z : Nat) => buildCourse t p (z : Int) b)
    { blocks := #[], state := ScoreState.empty t, stack := {} }


end KaplaPlanner
