import Std.Data.HashMap
import KaplaPlanner.Grid

/-! # The local stability rule (cheap, not trusted)

Before a block goes in, the planner checks with a simple load model that the whole stack still
stands. This is not the physics engine. Its purpose is to waste few of the real checks
(`planner/DESIGN.md` §4.4).

The model:

* A block counts as resting on a block below only where the contact covers its full width
  (3 cells) and is at least 2 cells long. Other contacts are ignored. That can only make the
  rule stricter.
* **Upright blocks** (on edge or standing) have a foot only 1 cell wide. The physics engine
  keeps its load points about 0.51 inside every contact edge, so it cannot find forces through
  a contact 1 wide: today it rejects an upright block on any block, and any block on an upright
  one (`planner/DESIGN.md` §11.2). `UprightRules` says what is allowed; by default upright
  blocks stand only on the ground and carry nothing. The planner asks the physics engine at
  the start whether more is allowed (`Search.lean`).
* Every block carries its own weight 1 at its middle, plus what the blocks above pass down.
* Going from the top down, each block passes its whole load to the supports below it. If the
  load point is over one contact (at least 1/2 inside it), everything goes straight down there.
  If it is between two contacts, it is shared between them by the lever rule, at points
  `edgeRoom` inside their near edges. So no load sits on the edge of the block below.
* A block stands when its load point is over the span of its contacts, at least `margin` from
  either end along the block, and at least `edgeRoom` from either long side.

* A block whose contacts span fewer than 6 cells (one crossing block under it, say) carries
  loads only right above its contacts. Such a see-saw balances in the model, but with the hand's
  error the physics engine may find that it tips.
* In **strict mode**, every block carries loads only right above its contacts. Then the
  physics engine's fast solver, which settles one block at a time from the top and never goes
  back, always finds the forces. Without strict mode, overhangs held down by a counterweight
  are allowed; the engine finds those only with its global solver, which it runs for builds of
  at most 40 blocks (`globalLimit` in `physics/KaplaPhysics/Engine.lean`).

The forces this computes balance every block, so a stack that passes has a set of contact
forces that holds it up. Blocks are checked in build order, so this holds after every step.
The margins leave room for the hand's error; the physics engine decides if that is enough. -/

namespace KaplaPlanner

open KaplaCore

/-- One contact of a block with a block below: the lower block, and where the contact is along
the upper block's long side (`lo ≤ position ≤ hi`). -/
structure Contact where
  below : Nat
  lo : Int
  hi : Int
  deriving Repr, BEq, Inhabited

/-- A placed block and the contacts that hold it up. A block on the ground has none. -/
structure Placed where
  blk : GBlock
  contacts : List Contact
  deriving Repr, Inhabited

/-- A stack of placed blocks, in build order. -/
structure Stack where
  blocks : Array Placed := #[]
  /-- For each course, the positions in `blocks` of the blocks that fill a cell of it. -/
  occ : Std.HashMap Int (List Nat) := {}
  /-- For each height, the positions of the blocks whose top is there. -/
  tops : Std.HashMap Int (List Nat) := {}
  deriving Inhabited

/-- What upright blocks (on edge or standing) may do. -/
structure UprightRules where
  /-- An upright block may stand on a flat block, not only on the ground. -/
  onFlat : Bool := false
  /-- A block may rest on an upright block. -/
  carry : Bool := false
  deriving Repr, BEq, Inhabited

/-- The width of the block's foot across its longer side: 3 for a flat block, 1 for an
upright one. -/
def GBlock.crossWidth (b : GBlock) : Int := if b.orient.alongX then b.sy else b.sx

/-- The position of a block along its own long side, and across it, of a point. -/
def alongCross (b : GBlock) (x y : Q) : Q × Q := if b.orient.alongX then (x, y) else (y, x)

/-- The lowest corner of the block along its long side and across it. -/
def startAlongCross (b : GBlock) : Int × Int := if b.orient.alongX then (b.x, b.y) else (b.y, b.x)

/-- The shortest contact, along the upper block, that counts. A contact of one cell at the very
end of a block can almost vanish with the hand's error (2ε ≈ 0.51 between two blocks), and the
physics engine does not rely on it. -/
def minContact : Int := 2

/-- The contacts that count, of a new block `u` with the blocks whose top is at `u`'s bottom:
full width across `u`, at least `minContact` long. `none` when `u` overlaps a placed block, or
is upright and off the ground while `up` does not allow that. Upright blocks below count only
when `up.carry`. A block with a foot 1 wide counts a contact only if the block below reaches
past both sides of the foot. -/
def contactsOf (st : Stack) (u : GBlock) (up : UprightRules := {}) : Option (List Contact) :=
  Id.run do
  if u.z != 0 && !u.orient.isFlat && !up.onFlat then return none
  for z in intRange u.z (u.top - 1) do
    for j in st.occ.getD z [] do
      if (st.blocks[j]!).blk.overlaps u then return none
  let mut res : List Contact := []
  for j in st.tops.getD u.z [] do
    let v := (st.blocks[j]!).blk
    if !v.orient.isFlat && !up.carry then continue
    let x0 := max u.x v.x
    let x1 := min (u.x + u.sx) (v.x + v.sx)
    let y0 := max u.y v.y
    let y1 := min (u.y + u.sy) (v.y + v.sy)
    if x0 < x1 && y0 < y1 then
      let full := if u.orient.alongX then y0 == u.y && y1 == u.y + u.sy
                  else x0 == u.x && x1 == u.x + u.sx
      -- a foot 1 wide: the block below must reach past it on both sides
      let past := u.crossWidth ≥ 3 ||
        (if u.orient.alongX then v.y < u.y && u.y + u.sy < v.y + v.sy
         else v.x < u.x && u.x + u.sx < v.x + v.sx)
      let len := if u.orient.alongX then x1 - x0 else y1 - y0
      if full && past && minContact ≤ len then
        res := (if u.orient.alongX then ⟨j, x0, x1⟩ else ⟨j, y0, y1⟩) :: res
  return some res

/-- How far inside the edge of a contact a load goes down, and how far inside its long sides a
block's load point must be. The physics engine keeps its load points `2ε = 20/39` (about
0.51) inside every contact edge, to allow for the hand's error; this is a little more. -/
def edgeRoom : Q := 3 / 5

/-- A block whose contacts span fewer cells than this (along the block) is a see-saw: it may
carry loads only right above its contacts. The physics engine allows for the hand's error at
every contact, and a see-saw with a load far out may tip under it. -/
def seesawSpan : Int := 6

/-- The span of a placed block's contacts along the block: from the start of the first to the
end of the last. `none` for a block on the ground (it is held everywhere). -/
def Placed.span (p : Placed) : Option (Int × Int) :=
  if p.blk.z == 0 then none
  else match p.contacts.map (·.lo) |>.min?, p.contacts.map (·.hi) |>.max? with
    | some lo, some hi => some (lo, hi)
    | _, _ => some (0, 0)

/-- Does `u` rest on a block outside the span of that block's contacts, where that block's
contacts span fewer than `minSpan` cells? With `minSpan = seesawSpan` this finds loads on the
end of a see-saw. With a huge `minSpan` it finds every load that is not right above the
supports of the block below (strict mode). -/
def loadsOutside (st : Stack) (u : GBlock) (cs : List Contact) (minSpan : Int) : Bool :=
  cs.any fun ct =>
    let p := st.blocks[ct.below]!
    match p.span with
    | none => false
    | some (lo, hi) =>
      if hi - lo ≥ minSpan then false
      else
        let v := p.blk
        -- where `u` touches `v`, along `v`
        let (a, b) := if v.orient.alongX then (max u.x v.x, min (u.x + u.sx) (v.x + v.sx))
                      else (max u.y v.y, min (u.y + u.sy) (v.y + v.sy))
        a < lo || hi < b

/-- A span longer than any build, for strict mode. -/
def anySpan : Int := 1000000

/-- Does every block stand under the load model? Returns the first block that does not, in
build order from the top. `margin` is the room left at the ends of the contact span. -/
def firstFailing (bs : Array Placed) (margin : Q) : Option Nat := Id.run do
  let n := bs.size
  let mut w : Array Q := Array.replicate n 1
  let mut mx : Array Q := bs.map fun p => (p.blk.x : Q) + (p.blk.sx : Q) / 2
  let mut my : Array Q := bs.map fun p => (p.blk.y : Q) + (p.blk.sy : Q) / 2
  for k in [0:n] do
    let i := n - 1 - k
    let p := bs[i]!
    if p.blk.z == 0 then continue
    let wi := w[i]!
    let (l, c) := alongCross p.blk (mx[i]! / wi) (my[i]! / wi)
    let cross0 : Q := ((startAlongCross p.blk).2 : Q)
    let cw : Q := (p.blk.crossWidth : Q)
    let room := min edgeRoom (cw / 2)
    if c < cross0 + room || cross0 + cw - room < c then return some i
    let cs := p.contacts.mergeSort fun a b => a.lo ≤ b.lo
    match cs.head?, cs.getLast? with
    | some first, some last =>
      let lo : Q := (first.lo : Q)
      let hi : Q := (cs.foldl (fun m ct => max m ct.hi) last.hi : Int)
      if l < lo + margin || hi - margin < l then return some i
      -- where the load goes: (block below, share of the load, position along this block).
      -- Loads go down at least 1/2 inside each contact, so they never sit on the edge of the
      -- block below.
      let inLo (ct : Contact) : Q := (ct.lo : Q) + edgeRoom
      let inHi (ct : Contact) : Q := (ct.hi : Q) - edgeRoom
      let shares : List (Nat × Q × Q) :=
        match cs.find? fun ct => inLo ct ≤ l && l ≤ inHi ct with
        | some ct => [(ct.below, 1, l)]
        | none =>
          -- between two contacts: the one whose inside ends last before `l`, and the first
          -- whose inside starts after it
          let left := (cs.filter fun ct => inHi ct < l).foldl
            (fun (acc : Option Contact) ct => match acc with
              | some a => if inHi a < inHi ct then some ct else some a
              | none => some ct) none
          let right := cs.find? fun ct => l < inLo ct
          match left, right with
          | some a, some b =>
            let pa := inHi a
            let pb := inLo b
            [(a.below, (pb - l) / (pb - pa), pa), (b.below, (l - pa) / (pb - pa), pb)]
          | _, _ => []
      if shares.isEmpty then return some i
      for (j, share, pos) in shares do
        let f := share * wi
        let (px, py) := if p.blk.orient.alongX then (pos, c) else (c, pos)
        w := w.modify j (· + f)
        mx := mx.modify j (· + f * px)
        my := my.modify j (· + f * py)
    | _, _ => return some i
  return none

/-- Add a block to the stack if it stands and the stack still stands. In strict mode, a block
may rest on another only right above that block's own contacts: no load on an overhang. -/
def Stack.place (st : Stack) (u : GBlock) (margin : Q) (strict : Bool := false)
    (up : UprightRules := {}) : Option Stack :=
  match contactsOf st u up with
  | none => none
  | some cs =>
    if u.z != 0 && (cs.isEmpty || loadsOutside st u cs (if strict then anySpan else seesawSpan))
    then none
    else
      let blocks := st.blocks.push ⟨u, cs⟩
      if (firstFailing blocks margin).isSome then none
      else
        let i := st.blocks.size
        let occ := (intRange u.z (u.top - 1)).foldl (fun m z => m.insert z (i :: m.getD z [])) st.occ
        some { blocks, occ, tops := st.tops.insert u.top (i :: st.tops.getD u.top []) }

/-- Place blocks in order; `none` if one fails. -/
def Stack.placeAll (st : Stack) (bs : List GBlock) (margin : Q) (strict : Bool := false)
    (up : UprightRules := {}) : Option Stack :=
  bs.foldlM (fun s b => s.place b margin strict up) st

/-- A number for "block `u` on these blocks below": `u` and every block whose top is at `u`'s
bottom and whose top face shares area with `u`'s foot. The search remembers the placements the
physics engine refused by this number (`Tree.lean`). -/
def Stack.supportKey (st : Stack) (u : GBlock) : UInt64 :=
  let below := ((st.tops.getD u.z []).map fun j => (st.blocks[j]!).blk).filter fun v =>
    u.x < v.x + v.sx && v.x < u.x + u.sx && u.y < v.y + v.sy && v.y < u.y + u.sy
  let hs := (below.map hash).mergeSort (· ≤ ·)
  hs.foldl mixHash (hash u)

/-- The blocks that rest on block `i` (have a contact with it). -/
def Stack.carriedBy (st : Stack) (i : Nat) : List Nat :=
  (List.range st.blocks.size).filter fun j => (st.blocks[j]!).contacts.any (·.below == i)

-- A log-cabin tower stands.
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 0, 12, 0⟩, ⟨.flatY, 0, 0, 1⟩,
  ⟨.flatY, 12, 0, 1⟩, ⟨.flatX, 0, 0, 2⟩, ⟨.flatX, 0, 12, 2⟩] 1).isSome
-- A block in the air does not.
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 1⟩] 1).isNone
-- A block resting on another with its middle over the end of the one below tips.
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 8, 0, 1⟩] 1).isNone
-- With its middle 1 unit inside the end, it stands.
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 6, 0, 1⟩] 1).isSome
-- A crossing block centred on the one below stands; off centre by 2 it tips.
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.flatY, 6, -6, 1⟩] 1).isSome
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.flatY, 6, -8, 1⟩] 1).isNone
-- A block overlapping one of its own course is refused.
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 5, 2, 0⟩] 1).isNone
-- In strict mode, a block may not rest on the overhanging end of another.
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 6, 0, 1⟩, ⟨.flatY, 18, -6, 2⟩] 1 true).isNone
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 6, 0, 1⟩, ⟨.flatY, 8, -6, 2⟩] 1 true).isSome
-- A load on the far end of an overhang tips the block below it ...
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 6, 0, 1⟩, ⟨.flatY, 18, -6, 2⟩] 1).isNone
-- ... but not when a counterweight sits on its back end first.
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 6, 0, 1⟩, ⟨.flatY, 6, -6, 2⟩,
  ⟨.flatY, 9, -6, 2⟩, ⟨.flatY, 18, -6, 2⟩] 1).isSome

/-! Upright blocks. The answers match the physics engine on the plans of `DESIGN.md` §11.2. -/

-- A standing block and a block on edge stand on the ground.
#guard (Stack.placeAll {} [⟨.standX, 0, 0, 0⟩, ⟨.edgeY, 5, 0, 0⟩] 1).isSome
-- By default an upright block may not stand on a flat block ...
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.standX, 6, 1, 1⟩] 1).isNone
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.edgeX, 0, 1, 1⟩] 1).isNone
-- ... and nothing may rest on an upright block: a bridge on two standing blocks has no
-- support.
#guard (Stack.placeAll {} [⟨.standX, 0, 1, 0⟩, ⟨.standX, 12, 1, 0⟩, ⟨.flatX, 0, 0, 15⟩] 1).isNone
-- When allowed, a standing block stands in the middle of a flat block, not flush with its side.
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.standX, 6, 1, 1⟩] 1 false ⟨true, false⟩).isSome
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.standX, 6, 0, 1⟩] 1 false ⟨true, false⟩).isNone
-- A standing block fills 15 courses: a flat block may not cross it higher up.
#guard (Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.standX, 20, 0, 0⟩, ⟨.flatY, 21, -5, 0⟩] 1).isNone
-- Which blocks rest on which.
#guard ((Stack.placeAll {} [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 0, 12, 0⟩, ⟨.flatY, 0, 0, 1⟩] 1).map
  (·.carriedBy 0)) == some [2]

end KaplaPlanner
