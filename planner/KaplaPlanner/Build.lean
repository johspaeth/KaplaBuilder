import KaplaPlanner.FastScore
import KaplaPlanner.Support

/-! # Build: courses from the ground up

At one height, the planner builds one course (one block thick) at a time, from the ground up
(`planner/DESIGN.md` §4.3). In each course:

1. **Candidates.** Every block starting at this course, lying a way that the settings allow
   (flat along x or y; with `uprights`, also on edge and standing), that has at least one cell
   in a bubble. Only these can be part of an accepted plan: a block with no cell in any
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
  /-- If set, the flat ways a block may lie in every course; this replaces `cabin`. The tree
  search (`Tree.lean`) chooses them course by course. -/
  orients : Option (List Orient) := none
  /-- Also try blocks on edge and standing. -/
  uprights : Bool := false
  /-- What upright blocks may do (`Support.lean`). -/
  up : UprightRules := {}
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

/-- Does the block have a cell in a bubble? -/
def Table.touchesBubble (t : Table) (b : GBlock) : Bool := Id.run do
  for z in intRange b.z (b.z + b.sz - 1) do
    for y in intRange b.y (b.y + b.sy - 1) do
      for x in intRange b.x (b.x + b.sx - 1) do
        if t.maskAt (x, y, z) != 0 then return true
  return false

/-- The flat ways a block of course `z` may lie. -/
def orientsAt (cabin : Option Bool) (z : Int) : List Orient :=
  match cabin with
  | none => [.flatX, .flatY]
  | some evenX => if (z % 2 == 0) == evenX then [.flatX] else [.flatY]

/-- The ways a block of course `z` may lie under the settings: the flat ones, and the upright
ones if allowed there (on the ground, or anywhere if they may stand on flat blocks). -/
def BuildParams.orientsAt (p : BuildParams) (z : Int) : List Orient :=
  let flats := p.orients.getD (KaplaPlanner.orientsAt p.cabin z)
  if p.uprights && (z == 0 || p.up.onFlat) then flats ++ Orient.uprights else flats

/-- The union of two boxes (x and y ranges). -/
def unionBox : Option (Int × Int × Int × Int) → Option (Int × Int × Int × Int) →
    Option (Int × Int × Int × Int)
  | some (a, b, c, d), some (a', b', c', d') => some (min a a', max b b', min c c', max d d')
  | some r, none | none, some r => some r
  | none, none => none

/-- All blocks starting at course `z`, lying the ways given, inside the table's box, near the
bubbles of the courses they fill (they may still have no cell in a bubble). -/
def positionsAt (t : Table) (z : Int) (orients : List Orient) : Array GBlock := Id.run do
  let mut res : Array GBlock := #[]
  for o in orients do
    let (sx, sy, sz) := o.size
    let box := (intRange z (z + sz - 1)).foldl (fun r zz => unionBox r (sliceBox t zz)) none
    match box with
    | none => pure ()
    | some (xa, xb, ya, yb) =>
      for y in intRange (ya - sy + 1) yb do
        for x in intRange (xa - sx + 1) xb do
          let b : GBlock := ⟨o, x, y, z⟩
          if t.holds b then res := res.push b
  return res

/-- All blocks starting at course `z`, lying the ways given, with at least one cell in a
bubble. -/
def candidatesAt (t : Table) (z : Int) (orients : List Orient) : Array GBlock := Id.run do
  let mut res : Array GBlock := #[]
  for o in orients do
    let (sx, sy, sz) := o.size
    -- the box around the bubble cells of every course the block fills
    let box := (intRange z (z + sz - 1)).foldl (fun r zz => unionBox r (sliceBox t zz)) none
    match box with
    | none => pure ()
    | some (xa, xb, ya, yb) =>
      for y in intRange (ya - sy + 1) yb do
        for x in intRange (xa - sx + 1) xb do
          let b : GBlock := ⟨o, x, y, z⟩
          if t.holds b && t.touchesBubble b then res := res.push b
  return res

/-- Do the two blocks share a grid line along x or y in their course? -/
def sharesLine (a b : GBlock) : Bool :=
  (a.x < b.x + b.sx && b.x < a.x + a.sx) || (a.y < b.y + b.sy && b.y < a.y + a.sy)

/-- The candidates of one course on top of a partial build, with what each would change: worked
out once and shared by every setting tried at that course (`Tree.lean`). -/
structure Prep where
  /-- Blocks that could go in: in the table, with a cell in a bubble, resting on the course
  below (or on the ground), not overlapping, not a refused placement. -/
  cands : Array GBlock
  /-- What each would change, from the start state. -/
  ds : Array Delta
  /-- For each, the footprint cells under a bubble that has no block yet and starts higher. -/
  under : Array Nat
  deriving Inhabited

/-- The candidates of course `z` on top of `start`, lying the ways given. -/
def prepare (t : Table) (p : BuildParams) (z : Int) (start : Built) (orients : List Orient)
    (nogood : Std.HashSet UInt64 := {}) : Prep :=
  let st := start.stack
  -- the support test first: it is cheaper than looking for a bubble cell
  let cands := (positionsAt t z orients).filter fun u =>
    (z == 0 || match contactsOf st u p.up with
      | some cs => !cs.isEmpty
      | none => false) &&
    t.touchesBubble u &&
    (nogood.isEmpty || !nogood.contains (st.supportKey u))
  -- the pillar count matters only while some bubble has no block
  let present := (List.range t.placed.size).any fun b => !hasBit start.state.touched b
  { cands, ds := cands.map (deltaBlock t start.state),
    under := if present then cands.map (underUntouched t start.state.touched) else cands.map fun _ => 0 }

/-- The value of a change in whole numbers: `value` times a common denominator `den` of the
settings, so the search compares integers, not fractions. -/
structure IntValue where
  den : Int
  cell : Int
  out : Int
  under : Int
  first : Int
  pillar : Int
  lambda : Int

/-- The whole-number form of the settings' prices. -/
def IntValue.of (p : BuildParams) : IntValue :=
  let qs : List Q := [1, p.price, p.price * p.underShare, p.firstBonus, p.pillarBonus, p.lambda]
  let den : Int := (qs.foldl (fun d q => Nat.lcm d q.den) 1 : Nat)
  let sc (q : Q) : Int := (q * den).num
  { den, cell := den, out := sc p.price, under := sc (p.price * p.underShare),
    first := sc p.firstBonus, pillar := sc p.pillarBonus, lambda := sc p.lambda }

/-- `value` times `den`. -/
def IntValue.apply (w : IntValue) (s : ScoreState) (d : Delta) : Int :=
  w.cell * d.dC - w.out * ((d.dE - d.dEUnder : Nat) : Int) - w.under * d.dEUnder +
    w.first * d.firstTouches s

-- The whole-number value is `value` times `den`.
#guard
  let p : BuildParams := { lambda := 1, price := 1 / 2, maxBlocks := 5, underShare := -1 / 2 }
  let w := IntValue.of p
  let d : Delta := { newly := [1, 2, 3], dE := 7, dEUnder := 2, spanSets := [], touches := 3 }
  let s : ScoreState := { covered := #[], spans := {}, coveredCount := 0, extra := 0, touched := 1 }
  (w.apply s d : Q) == value p s d * w.den && w.den == 4

/-- Build one course on top of `start`, from its candidates `prep` (only those lying a way the
settings allow at this course). -/
def buildCourseWith (t : Table) (p : BuildParams) (z : Int) (start : Built) (prep : Prep) :
    Built := Id.run do
  let mut st := start.stack
  let mut sc := start.state
  let mut blocks := start.blocks
  if blocks.size ≥ p.maxBlocks then return start
  let allowed := p.orientsAt z
  let cands := prep.cands
  let w := IntValue.of p
  let mut ds : Array (Option Delta) := (cands.zip prep.ds).map fun (u, d) =>
    if allowed.contains u.orient then some d else none
  let under := prep.under
  let mut pillarOpen := true
  let valueOf (sc : ScoreState) (pillarOpen : Bool) (i : Nat) (d : Delta) : Int :=
    w.apply sc d + (if pillarOpen && under[i]! > 0 then w.pillar else 0)
  -- the values of the open candidates, kept up to date
  let mut vs : Array Int := ds.mapIdx fun i d => match d with
    | some d => valueOf sc pillarOpen i d
    | none => 0
  let mut inCourse := 0
  for _ in [0:cands.size] do
    if blocks.size ≥ p.maxBlocks || (p.perCourse != 0 && inCourse ≥ p.perCourse) then break
    -- the best candidate still open
    let mut best : Option (Nat × Int) := none
    for i in [0:cands.size] do
      if ds[i]!.isSome then
        let v := vs[i]!
        if 0 < v && w.lambda ≤ v then
          match best with
          | some (_, bv) => if bv < v then best := some (i, v)
          | none => best := some (i, v)
    match best with
    | none => break
    | some (i, _) =>
      let u := cands[i]!
      -- the stored change can be out of date: a block placed since may have filled cells on
      -- lines that cross this candidate's lines. Work it out again before using it.
      let d := deltaBlock t sc u
      ds := ds.set! i none
      let v := valueOf sc pillarOpen i d
      if v ≤ 0 || v < w.lambda then continue
      match st.place u p.margin p.strict p.up with
      | none => pure ()
      | some st' =>
        st := st'
        let touchedBefore := sc.touched
        sc := sc.apply d
        blocks := blocks.push u
        inCourse := inCourse + 1
        let pillarBefore := pillarOpen
        if under[i]! > 0 then pillarOpen := false
        -- values change for candidates on shared lines; for all if a bubble got its first
        -- block or the pillar bonus closed
        let all := sc.touched != touchedBefore || pillarOpen != pillarBefore
        for j in [0:cands.size] do
          match ds[j]! with
          | some dj =>
            let v := cands[j]!
            if v.overlaps u then ds := ds.set! j none
            else if sharesLine u v then
              let d' := deltaBlock t sc v
              ds := ds.set! j (some d')
              vs := vs.set! j (valueOf sc pillarOpen j d')
            else if all then vs := vs.set! j (valueOf sc pillarOpen j dj)
          | none => pure ()
  return { blocks, state := sc, stack := st }

/-- Build one course on top of what is there. Placements in `nogood` (by `Stack.supportKey`)
are never made. -/
def buildCourse (t : Table) (p : BuildParams) (z : Int) (start : Built)
    (nogood : Std.HashSet UInt64 := {}) : Built :=
  buildCourseWith t p z start (prepare t p z start (p.orientsAt z) nogood)

/-- Build every course, from the ground up. -/
def build (t : Table) (p : BuildParams) : Built :=
  (List.range t.nz).foldl (fun b (z : Nat) => buildCourse t p (z : Int) b)
    { blocks := #[], state := ScoreState.empty t, stack := {} }


end KaplaPlanner
