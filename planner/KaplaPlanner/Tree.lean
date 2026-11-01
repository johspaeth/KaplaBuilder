import KaplaPlanner.Build

/-! # The tree search: branch-and-bound over courses

At one height, the search builds the model course by course (`planner/DESIGN.md` §11.5). It is
an *anytime* search: it always has a best plan so far (the **incumbent**), and it can stop at
any moment. It does not promise the best possible plan: it keeps only a few children per node,
and some pruning rules are heuristic.

* **Branch-and-bound.** A **node** is a partial build: courses below `z` are done. Its
  **children** each add one course. The course's candidates and what each would change are
  worked out once per node (`prepare`); each child then comes from `buildCourseWith` with one
  of a few settings, in parallel (which way the blocks lie, how many blocks the course may
  use, upright blocks or not). Equal children are merged; at most `k` are kept, the default
  setting first, then by score.
* **Limited discrepancy search (LDS):** try the paths that differ least from the default
  first. Nodes wait in buckets by their number of *discrepancies*: how often their path took a
  child other than the first. The search always takes the newest node of the lowest bucket. So
  it first follows the default path to the top (a v1 build), then paths that differ once, then
  twice, and so on.
* **Leaves.** A build that reaches the top, or the block limit, is a leaf. A leaf that beats
  the incumbent is sent to the physics engine (the caller does this, `Search.lean`).
* **Pruning** a node means not exploring it. The rules:
  * **bound pruning** (safe): skip a node when no build below it can beat the incumbent.
    `bound` is a score that no build below the node can beat.
  * **feasibility pruning** (safe): skip a node that can no longer give a plan the scorer
    accepts: a bubble with no block yet whose top is below the node, or too few blocks left
    to reach every bubble.
  * **symmetry breaking** (safe): at the first course, drop a child that is the mirror image of
    another (when the model is its own mirror image).
  * **dominance pruning** (heuristic): of two nodes at the same course with the same top two
    courses, keep only the better.
  * **no-good learning** (heuristic): never again make a placement the physics engine refused
    (`nogood`).
* **Conflict-directed backjumping:** when physics refuses a leaf at block `b`, go back to
  where the failure started, not just one step. The placement of `b` on its supports is stored
  as a no-good, every waiting node that contains the same blocks up to `b` is dropped, and the
  search goes on with the remaining nodes, which branch off below or at `b`'s course. The
  blocks before `b` stood, so they are sent to physics as a smaller plan.
* **Heuristic phase.** When the caller says so, the search also improves the incumbent:
  * **large neighbourhood search (LNS):** keep the incumbent's courses below a course chosen at
    random, and search again above it;
  * **local search (block removal):** try removing single blocks that carry nothing.

Every function here is pure and ends: the caller gives a number of steps. -/

namespace KaplaPlanner

open KaplaCore

/-! ## Facts about the table -/

/-- Facts about a table that the bound and the pruning rules use. -/
structure TableInfo where
  /-- For each course `z` (and `nz`): the number of target cells at course `z` or higher. -/
  targetFrom : Array Nat
  /-- For each course `z` (and `nz`): the number of courses at `z` or higher with a target
  cell. -/
  coursesFrom : Array Nat
  /-- For each bubble and column: one above the bubble's highest cell there, 0 if none. -/
  colHigh : Array (Array Int)
  /-- For each bubble: one above its highest cell, 0 if it has none at this height. -/
  bubbleTop : Array Int
  /-- The bubbles with a cell at this height (bit mask). -/
  present : UInt64
  /-- The model is its own mirror image across the plane `y = 0`: every bubble has a partner
  that is its mirror image (maybe itself). Then a plan and its mirror image score the same. -/
  mirrorY : Bool
  deriving Inhabited

/-- Work out the facts for a table. -/
def TableInfo.make (t : Table) : TableInfo := Id.run do
  let area := t.nx * t.ny
  let mut perCourse : Array Nat := Array.replicate (t.nz + 1) 0
  let mut colHigh : Array (Array Int) := Array.replicate t.placed.size (Array.replicate area 0)
  let mut bubbleTop : Array Int := Array.replicate t.placed.size 0
  for z in [0:t.nz] do
    for k in [0:area] do
      let m := t.mask[z * area + k]!
      if m != 0 then
        perCourse := perCourse.modify z (· + 1)
        for b in [0:t.placed.size] do
          if hasBit m b then
            colHigh := colHigh.modify b (·.set! k ((z : Int) + 1))
            bubbleTop := bubbleTop.set! b ((z : Int) + 1)
  let mut targetFrom : Array Nat := Array.replicate (t.nz + 1) 0
  let mut coursesFrom : Array Nat := Array.replicate (t.nz + 1) 0
  for i in [0:t.nz] do
    let z := t.nz - 1 - i
    targetFrom := targetFrom.set! z (targetFrom[z + 1]! + perCourse[z]!)
    coursesFrom := coursesFrom.set! z (coursesFrom[z + 1]! + if perCourse[z]! > 0 then 1 else 0)
  let present := t.mask.foldl (· ||| ·) 0
  let mirrorY := t.placed.all fun b => t.placed.any fun c =>
    c.center == ⟨b.center.x, -b.center.y, b.center.z⟩ && c.semi == b.semi
  return { targetFrom, coursesFrom, colHigh, bubbleTop, present, mirrorY }

/-- A score that no build can beat which keeps every block of `s` (built below course `z`, or
reaching up from there) and adds at most `left` blocks at course `z` or higher. New blocks can
cover any target cell at course `z` or higher. Below `z`, a cell can only still be covered on
its vertical line: between the highest built cell of its bubble in that column and course `z`. -/
def bound (t : Table) (info : TableInfo) (s : ScoreState) (z left : Nat) : Q :=
  if left == 0 then s.score t else
  let reach := s.spans.fold (init := info.targetFrom[min z t.nz]!) fun r key span =>
    if (key / 64) % 3 == 2 then
      let top := (info.colHigh[key % 64]!)[key / 192]!
      let lim := min top (z : Int)
      if span.2 + 1 < lim then r + (lim - span.2 - 1).toNat else r
    else r
  scoreOf t.target (s.coveredCount + reach) s.extra

-- With no blocks left, the bound is the score. With nothing built, every target cell can
-- still be reached, so the bound is 1.
#guard
  let t := Table.make ballModel 10
  let s := fastScore t [⟨.flatX, -7, -1, 0⟩]
  bound t (.make t) s 1 0 == s.score t && bound t (.make t) (.empty t) 0 5 == 1
-- The ball is its own mirror image; the bunny too (its ears are at y = ±7/100).
#guard (TableInfo.make (Table.make ballModel 10)).mirrorY
#guard (TableInfo.make (Table.make bunnyModel 20)).mirrorY
-- The bound is never below the score of what is built, and never below what a build on top
-- of it reaches.
#guard
  let t := Table.make ballModel 12
  let info := TableInfo.make t
  let bs : List GBlock := [⟨.flatX, -7, -5, 0⟩, ⟨.flatX, -7, 2, 0⟩, ⟨.flatY, -5, -7, 1⟩,
    ⟨.flatY, 2, -7, 1⟩, ⟨.flatX, -7, -4, 2⟩]
  (List.range 6).all fun i =>
    let s := fastScore t (bs.take i)
    let z := ((bs.take i).map (·.top)).foldl max 0
    (List.range (6 - i)).all fun j =>
      s.score t ≤ bound t info s z.toNat (5 - i) &&
        (fastScore t (bs.take (i + j))).score t ≤ bound t info s z.toNat (5 - i)

/-! ## Nodes and leaves -/

/-- A partial build: courses below `z` are done. -/
structure Node where
  z : Nat
  built : Built
  /-- How often the path to this node took a child other than the first. -/
  disc : Nat
  deriving Inhabited

/-- A finished build. -/
structure Leaf where
  blocks : Array GBlock
  /-- The fast score. -/
  fast : Q
  /-- Every bubble with a cell at this height has a built cell. -/
  covers : Bool
  deriving Inhabited

/-- Is leaf `a` better than leaf `b`? A leaf that reaches every bubble comes first (the scorer
accepts only those), then the higher score. -/
def Leaf.better (a b : Leaf) : Bool :=
  (a.covers && !b.covers) || (a.covers == b.covers && a.fast > b.fast)

/-- A number for a list of blocks. -/
def blocksHash (bs : Array GBlock) : UInt64 := bs.foldl (fun h b => mixHash h (hash b)) 7

/-- The leaf of a build. -/
def Leaf.ofBuilt (t : Table) (info : TableInfo) (b : Built) : Leaf :=
  { blocks := b.blocks, fast := b.state.score t,
    covers := info.present &&& b.state.touched == info.present }

/-- The leaf of a list of blocks, by working out the fast score. -/
def Leaf.ofBlocks (t : Table) (info : TableInfo) (bs : Array GBlock) : Leaf :=
  let s := fastScore t bs.toList
  { blocks := bs, fast := s.score t, covers := info.present &&& s.touched == info.present }

/-! ## The search state -/

/-- The search at one height. -/
structure Tree where
  t : Table
  info : TableInfo
  height : Nat
  /-- The block limit. -/
  n : Nat
  /-- The default settings of a course (`maxBlocks` is `n`). -/
  base : BuildParams
  /-- Waiting nodes, by number of discrepancies; each list newest first. -/
  buckets : Array (List Node)
  /-- At most this many children per node. -/
  k : Nat := 3
  /-- At most this many waiting nodes; beyond, those with the most discrepancies go. -/
  maxOpen : Nat := 200
  /-- The best leaf that the physics engine accepted. -/
  incumbent : Option Leaf := none
  /-- Leaves that the physics engine accepted, with their reports; best first, at most 4. -/
  passed : List (Leaf × PhysicsReport) := []
  /-- Leaves waiting for the physics engine, best first. -/
  requests : Array Leaf := #[]
  /-- Leaves already sent (or waiting), by `blocksHash`. -/
  sent : Std.HashSet UInt64 := {}
  /-- Placements the physics engine refused (`Stack.supportKey`; no-good learning). -/
  nogood : Std.HashSet UInt64 := {}
  /-- For a node's course, block count and top two courses: the best score seen (dominance
  pruning). -/
  frontier : Std.HashMap UInt64 Q := {}
  /-- Incumbents already tried for removing single blocks. -/
  trimmed : Std.HashSet UInt64 := {}
  /-- Builds and evaluations done. -/
  tries : Nat := 0
  /-- Nodes pruned, for reports. -/
  pruned : Nat := 0
  /-- A random number, for the heuristic phase. -/
  rng : Nat := 12345
  deriving Inhabited

/-- A new search at a height, with one waiting node: nothing built. -/
def Tree.make (t : Table) (height n : Nat) (base : BuildParams) : Tree :=
  { t, info := .make t, height, n, base := { base with maxBlocks := n },
    buckets := #[[{ z := 0, built := { blocks := #[], state := .empty t, stack := {} }, disc := 0 }]] }

/-- The number of waiting nodes. -/
def Tree.openCount (tr : Tree) : Nat := tr.buckets.foldl (fun n l => n + l.length) 0

/-- No node is waiting. -/
def Tree.idle (tr : Tree) : Bool := tr.buckets.all (·.isEmpty)

/-- The next random number. -/
def Tree.nextRandom (tr : Tree) : Tree × Nat :=
  let r := (tr.rng * 1103515245 + 12345) % 2147483648
  ({ tr with rng := r }, r / 65536)

/-- Add a waiting node; if there are too many, drop one with the most discrepancies. -/
def Tree.push (tr : Tree) (nd : Node) : Tree := Id.run do
  let mut bs := tr.buckets
  while bs.size ≤ nd.disc do bs := bs.push []
  bs := bs.modify nd.disc (nd :: ·)
  let mut tr := { tr with buckets := bs }
  if tr.openCount > tr.maxOpen then
    -- drop the oldest node of the highest non-empty bucket
    let mut i := tr.buckets.size
    while i > 0 && tr.buckets[i - 1]!.isEmpty do i := i - 1
    if i > 0 then tr := { tr with buckets := tr.buckets.modify (i - 1) (·.dropLast) }
  return tr

/-- Take the newest node of the lowest non-empty bucket. -/
def Tree.pop (tr : Tree) : Option (Node × Tree) := Id.run do
  for i in [0:tr.buckets.size] do
    match tr.buckets[i]! with
    | nd :: rest => return some (nd, { tr with buckets := tr.buckets.set! i rest })
    | [] => pure ()
  return none

/-! ## Leaves and the physics engine -/

/-- Offer a leaf: it waits for the physics engine if it is new, has a block, and beats the
incumbent. Requests stay sorted, best first. -/
def Tree.offer (tr : Tree) (lf : Leaf) : Tree :=
  if lf.blocks.isEmpty then tr else
  let h := blocksHash lf.blocks
  if tr.sent.contains h then tr else
  match tr.incumbent with
  | some inc => if lf.better inc then go h else tr
  | none => go h
where
  go (h : UInt64) : Tree :=
    let rs := (tr.requests.push lf).qsort fun a b => a.better b
    { tr with requests := rs, sent := tr.sent.insert h }

/-- Take the best waiting request. -/
def Tree.takeRequest (tr : Tree) : Option (Leaf × Tree) :=
  if h : 0 < tr.requests.size then
    some (tr.requests[0], { tr with requests := tr.requests.extract 1 tr.requests.size })
  else none

/-- The first block the physics engine says is unstable. Plans have one block per step. -/
def firstUnstable (r : PhysicsReport) : Option Nat :=
  (r.diagnostics.filterMap fun | .unstable _ b => some b | _ => none).min?

/-- The stack of these blocks, placed in order by the local rule (skipping any it refuses). -/
def stackOf (p : BuildParams) (bs : List GBlock) : Stack :=
  bs.foldl (fun st b => (st.place b p.margin p.strict p.up).getD st) {}

/-- Take in the physics engine's report on a leaf. If it is ok, the leaf may become the
incumbent. If block `b` is unstable (conflict-directed backjumping): remember the placement of
`b` as a no-good, drop the waiting nodes that contain the same blocks up to `b`, and offer the
blocks before `b`. -/
def Tree.report (tr : Tree) (lf : Leaf) (r : PhysicsReport) : Tree :=
  if r.ok then
    let passed := ((tr.passed ++ [(lf, r)]).mergeSort fun a b => a.1.better b.1).take 4
    let incumbent := match tr.incumbent with
      | some inc => if lf.better inc then some lf else some inc
      | none => some lf
    -- requests that no longer beat the incumbent are dropped
    let requests := tr.requests.filter fun q => match incumbent with
      | some inc => q.better inc
      | none => true
    { tr with passed, incumbent, requests }
  else match firstUnstable r with
    | none => tr
    | some b =>
      if b ≥ lf.blocks.size then tr else
      let pre := lf.blocks.extract 0 b
      let key := (stackOf tr.base pre.toList).supportKey lf.blocks[b]!
      let same (nd : Node) : Bool :=
        nd.built.blocks.size > b && (List.range (b + 1)).all fun i => nd.built.blocks[i]! == lf.blocks[i]!
      let buckets := tr.buckets.map (·.filter fun nd => !same nd)
      let tr := { tr with nogood := tr.nogood.insert key, buckets }
      tr.offer (Leaf.ofBlocks tr.t tr.info pre)

/-! ## Expanding a node -/

/-- The settings for the children of a node at course `z` with `used` blocks: the default
first; then the other way for flat blocks, both ways, one more block in the course, no limit on
blocks in the course, and (where they may stand) upright blocks.

If the default has a limit per course, the limit is the blocks left shared evenly over the
courses left (rounded up): so blocks not used low down are used higher up. -/
def Tree.variants (tr : Tree) (z used : Nat) : List BuildParams :=
  let left := tr.n - used
  let courses := max 1 tr.info.coursesFrom[min z tr.t.nz]!
  let p := if tr.base.perCourse == 0 then tr.base
    else { tr.base with perCourse := max 1 ((left + courses - 1) / courses) }
  let flats := p.orients.getD (orientsAt p.cabin z)
  let other : List Orient := if flats == [.flatX] then [.flatY]
    else if flats == [.flatY] then [.flatX] else [.flatX]
  let cap := p.perCourse
  [p, { p with orients := some other }, { p with orients := some [.flatX, .flatY] }] ++
    (if cap != 0 then [{ p with perCourse := cap + 1 }, { p with perCourse := 0 }] else []) ++
    (if z == 0 || p.up.onFlat then [{ p with uprights := true }] else [])

/-- The mirror image of a block across the plane `y = 0`. -/
def GBlock.mirrorY (b : GBlock) : GBlock := { b with y := -b.y - b.sy }

/-- A number for a set of blocks, the same in any order. -/
def setHash (bs : List GBlock) : UInt64 :=
  ((bs.map hash).mergeSort (· ≤ ·)).foldl mixHash 11

/-- The key of a node for dominance pruning: its course, its block count, which bubbles
have a block, and the blocks in the two courses below it. -/
def Tree.frontierKey (nd : Node) : UInt64 :=
  let st := nd.built.stack
  let near := ((st.occ.getD ((nd.z : Int) - 1) []) ++ (st.occ.getD ((nd.z : Int) - 2) [])).eraseDups
  mixHash (mixHash (hash nd.z) (hash nd.built.blocks.size))
    (mixHash (hash nd.built.state.touched) (setHash (near.map fun j => (st.blocks[j]!).blk)))

/-- Should the node be pruned (bound pruning, feasibility pruning)? Returns the reason, for
counting. -/
def Tree.pruneReason (tr : Tree) (nd : Node) : Option String :=
  let used := nd.built.blocks.size
  let s := nd.built.state
  match tr.incumbent with
  | some inc =>
    if inc.covers && bound tr.t tr.info s nd.z (tr.n - used) ≤ inc.fast then some "bound"
    else
      let missing := (List.range tr.t.placed.size).filter fun b =>
        hasBit tr.info.present b && !hasBit s.touched b
      if inc.covers && missing.any (fun b => tr.info.bubbleTop[b]! ≤ (nd.z : Int)) then some "dead"
      else if inc.covers && used + missing.length > tr.n then some "budget"
      else none
  | none => none

/-- Expand one node: a leaf is offered; otherwise the node is pruned or its children wait. -/
def Tree.expand (tr : Tree) (nd : Node) : Tree := Id.run do
  let used := nd.built.blocks.size
  if nd.z ≥ tr.t.nz || used ≥ tr.n || tr.info.targetFrom[nd.z]! == 0 then
    return tr.offer (Leaf.ofBuilt tr.t tr.info nd.built)
  if (tr.pruneReason nd).isSome then return { tr with pruned := tr.pruned + 1 }
  -- dominance pruning: of two nodes with the same frontier, keep only the better
  let key := Tree.frontierKey nd
  let sc := nd.built.state.score tr.t
  let mut tr := tr
  match tr.frontier[key]? with
  | some v => if sc ≤ v && nd.disc > 0 then return { tr with pruned := tr.pruned + 1 }
  | none => pure ()
  tr := { tr with frontier := tr.frontier.insert key sc }
  -- the children: the candidates of the course are worked out once, for every way a block
  -- may lie here; each setting then builds from them, in parallel
  let vars := tr.variants nd.z used
  let orients := Orient.flats ++
    (if vars.any (·.uprights) then Orient.uprights else [])
  let prep := prepare tr.t tr.base (nd.z : Int) nd.built orients tr.nogood
  let t := tr.t
  let tasks := vars.map fun p => Task.spawn fun _ => buildCourseWith t p (nd.z : Int) nd.built prep
  let mut kids : Array (Built × UInt64) := #[]
  for task in tasks do
    let b := task.get
    tr := { tr with tries := tr.tries + 1 }
    let added := (b.blocks.extract used b.blocks.size).toList
    let h := setHash added
    let mirrored := nd.z == 0 && tr.info.mirrorY && kids.any (·.2 == setHash (added.map GBlock.mirrorY))
    if !kids.any (·.2 == h) && !mirrored then kids := kids.push (b, h)
  -- the default first, then by score
  let rest := (kids.extract 1 kids.size).qsort fun a b => a.1.state.score tr.t > b.1.state.score tr.t
  let chosen := ((kids.extract 0 1) ++ rest).toList.take tr.k
  -- push in reverse, so the first child is the newest of its bucket
  for (b, i) in chosen.zipIdx.reverse do
    tr := tr.push { z := nd.z + 1, built := b.1, disc := nd.disc + i }
  return tr

/-! ## The heuristic phase: large neighbourhood search and local search -/

/-- Large neighbourhood search (LNS): keep the incumbent's blocks below a random course, and
search again above it. -/
def Tree.restart (tr : Tree) : Tree :=
  match tr.incumbent with
  | none => tr
  | some inc =>
    let topZ := (inc.blocks.foldl (fun m (b : GBlock) => max m b.z) 0).toNat
    let (tr, r) := tr.nextRandom
    let z := r % (topZ + 1)
    let pre := inc.blocks.filter (·.z < (z : Int))
    let st := stackOf tr.base pre.toList
    if st.blocks.size != pre.size then tr else
    let built : Built := { blocks := pre, state := fastScore tr.t pre.toList, stack := st }
    { tr.push { z, built, disc := 0 } with tries := tr.tries + 1 }

/-- Local search (block removal): try removing each block of the incumbent that carries
nothing. Every removal that keeps all
bubbles reached and raises the score is offered to the physics engine. -/
def Tree.trim (tr : Tree) : Tree := Id.run do
  match tr.incumbent with
  | none => return tr
  | some inc =>
    let h := blocksHash inc.blocks
    if tr.trimmed.contains h then return tr
    let mut tr := { tr with trimmed := tr.trimmed.insert h }
    let st := stackOf tr.base inc.blocks.toList
    if st.blocks.size != inc.blocks.size then return tr
    for i in [0:inc.blocks.size] do
      if (st.carriedBy i).isEmpty then
        let rest := (inc.blocks.toList.zipIdx.filter (·.2 != i)).map (·.1)
        let lf := Leaf.ofBlocks tr.t tr.info rest.toArray
        tr := { tr with tries := tr.tries + 1 }
        if lf.better inc then tr := tr.offer lf
    return tr

/-- Do at most `steps` steps. In the heuristic phase, start a large neighbourhood search from
the incumbent when no node is waiting, and every 16 steps; and try block removal on the
incumbent. -/
def Tree.run (tr : Tree) (steps : Nat) (heuristic : Bool) : Tree := Id.run do
  let mut tr := tr
  for i in [0:steps] do
    if heuristic && (tr.idle || i % 16 == 15) then
      tr := tr.trim.restart
    match tr.pop with
    | some (nd, tr') => tr := tr'.expand nd
    | none => break
  return tr

/-- Run with a physics engine called right away on every request (for tests and small runs),
for at most `steps` steps, with at most `checks` checks. -/
def Tree.runWith (ph : PhysicsEngine) (human : HumanModel) (toPlan : List GBlock → BuildPlan)
    (tr : Tree) (steps checks : Nat) (heuristic : Bool := false) : Tree := Id.run do
  let mut tr := tr
  let mut left := checks
  for _ in [0:steps] do
    tr := tr.run 1 heuristic
    while left > 0 do
      match tr.takeRequest with
      | some (lf, tr') =>
        left := left - 1
        tr := tr'.report lf (ph.check human tr.n (toPlan lf.blocks.toList))
      | none => break
    if tr.idle && tr.requests.isEmpty && !heuristic then break
  return tr

end KaplaPlanner
