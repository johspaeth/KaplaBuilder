import KaplaPlanner.Tree

/-! # Search: heights, settings, the physics check, and the candidates

The planner (`planner`, `planner/DESIGN.md` §3) runs for at most a time limit (30 s):

1. **Probes.** Two tiny plans tell whether the physics engine lets upright blocks stand on
   flat blocks, and carry blocks (`probeRules`).
2. **First sweep.** Greedy builds at a coarse spread of heights (below), for at most
   `sweepShare` of the time; builds not done by then are left out. The best heights get a
   tree search each (branch-and-bound, `Tree.lean`), starting from the best setting of that
   height.
3. **Rounds.** The tree searches run in parallel, a few steps each per round. Leaves that beat
   a search's incumbent go to the physics engine, each in its own task, at most a few at a
   time. Reports come back to their search. After `treeShare` of the time, the searches also
   improve their incumbents by large neighbourhood search and block removal (the heuristic
   phase). At a third and two thirds of the time, the worse half of the searches stops, but at
   least 4 keep going (so the cores stay busy; each search also builds the children of a node
   in parallel).
4. **Stop** at the time limit (less a reserve for scoring), at `maxTries`, or when nothing is
   left to do. Checks still running are not waited for. A check cannot be stopped, and a
   program does not end before its checks do, so near the end no check starts that would
   likely run past the limit (judged by the longest check so far). The plans that passed are scored by
   the semantic engine and the best few returned (`finalize`).

`planPure` is a pure function with no time limit, used by the tests and proofs. It does only
the greedy sweep, with a check-and-repair step:

1. **Height and settings.** Build at a coarse spread of heights with a few settings, keep the
   best height, then build at heights close to it with every setting (which way the courses
   lie, what foundation cells cost, how many blocks per course). The score decides, not the
   block count: a build may stop early (nothing left that is worth a block). Results differ a
   lot between settings, and building is cheap, so every result is kept. The builds run in
   parallel.
2. **Physics.** Check the best results with the real physics engine, best first and one per
   height first, so the candidates differ. If a block falls, remove it and everything that
   rested on it, and check again.
3. **Score.** Ask the semantic engine for the report of each plan that passed, and return the
   best few. -/

namespace KaplaPlanner

open KaplaCore

/-! ## Plans -/

/-- The build plan for grid blocks: one block per step, in the given order. The phase names the
course, counted from 1. -/
def toPlan (bs : List GBlock) : BuildPlan :=
  ⟨bs.map fun b => { blocks := [b.toPose], phase := s!"level {b.z + (1 : Int)}" }⟩

/-- Does every bubble that has a cell at this height have a built cell? (The scorer's
`uncovered` list is then empty.) -/
def coversAll (t : Table) (bs : List GBlock) : Bool :=
  let used := bs.foldl (fun m b => b.cells.foldl (fun m c => m ||| t.maskAt c) m) (0 : UInt64)
  let present := t.mask.foldl (· ||| ·) (0 : UInt64)
  present &&& used == present

/-! ## Heights -/

/-- How one build is set up, besides the height. -/
structure Setting where
  /-- Which way the courses lie (`BuildParams.cabin`). -/
  cabin : Option Bool
  /-- The price share of foundation cells (`BuildParams.underShare`). -/
  underShare : Q
  /-- Which limit on blocks per course (`perCourseLimits`): 0 = an even share, 1 = one more,
  2 = no limit. -/
  perCourse : Nat
  /-- Strict mode of the local rule (`BuildParams.strict`). -/
  strict : Bool := false
  deriving Repr, BEq, Inhabited

/-- The settings of the coarse height sweep: both log-cabin phases, both directions in every
course; foundation cells free, or worth a little. -/
def coarseSettings : List Setting :=
  [some true, some false, none].flatMap fun cabin => [0, -1 / 2].map fun us => ⟨cabin, us, 0, false⟩

/-- The most blocks for which the physics engine runs its global solver
(`globalLimit` in `physics/KaplaPhysics/Engine.lean`). Larger plans pass only if the engine's
fast solver finds the forces, so the planner builds them in strict mode. -/
def physicsGlobalLimit : Nat := 40

/-- The settings for a budget of `n` blocks: strict mode when `n` is above
`physicsGlobalLimit`. -/
def forBudget (n : Nat) (ss : List Setting) : List Setting :=
  ss.map fun s => { s with strict := decide (physicsGlobalLimit < n) }

/-- The settings of the fine sweep: the coarse ones with each limit per course. -/
def fineSettings : List Setting :=
  coarseSettings.flatMap fun s => [0, 1, 2].map fun pc => { s with perCourse := pc }

/-- What one cell outside the bubbles costs, in covered cells (`BuildParams.price`). -/
def defaultPrice : Q := 1 / 2

/-- Room left at the ends of a block's contacts. With 1/2, a block resting on one crossing
block can be 1/2 off centre, and the physics engine rejects that: the hand's error could tip it. -/
def defaultMargin : Q := 1

/-- The tallest model the planner builds, in block thicknesses. -/
def maxHeight : Nat := 200

/-- One build at one height. -/
structure Trial where
  height : Nat
  /-- The setting it was built with. -/
  setting : Setting := default
  blocks : List GBlock
  /-- The fast score. -/
  fast : Q
  /-- Every bubble with a cell has a built cell. -/
  covers : Bool
  deriving Inhabited

/-- The number of courses with a bubble cell. -/
def Table.courses (t : Table) : Nat :=
  (List.range t.nz).countP fun z => (List.range (t.nx * t.ny)).any fun k => t.mask[z * t.nx * t.ny + k]! != 0

/-- The limit on blocks per course for setting `pc`: an even share of the budget over the
courses (at least 1), one more than that, or no limit (0). -/
def perCourseLimit (t : Table) (n pc : Nat) : Nat :=
  let share := max 1 (n / max 1 t.courses)
  if pc == 0 then share else if pc == 1 then share + 1 else 0

/-- The build settings for a setting, with at most `cap` blocks. -/
def paramsFor (t : Table) (s : Setting) (cap : Nat) : BuildParams :=
  { lambda := 1, price := defaultPrice, maxBlocks := cap, margin := defaultMargin,
    cabin := s.cabin, underShare := s.underShare,
    perCourse := perCourseLimit t cap s.perCourse, strict := s.strict }

/-- Build once, with at most `cap` blocks. -/
def tryBuild (m : BubbleModel) (height : Nat) (s : Setting) (cap : Nat) : Trial :=
  let t := Table.make m height
  let r := build t (paramsFor t s cap)
  let bs := r.blocks.toList
  { height, setting := s, blocks := bs, fast := r.state.score t, covers := coversAll t bs }

/-- Run the builds in parallel. Each build is a pure function, so the result is the same as
running them one after the other. -/
def tryAll (m : BubbleModel) (cap : Nat) (jobs : List (Nat × Setting)) : List Trial :=
  let tasks := jobs.map fun (h, s) => Task.spawn fun _ => tryBuild m h s cap
  (tasks.map Task.get).filter fun tr => !tr.blocks.isEmpty

/-- A first guess of the height from the size of the model: about 2 blocks per course, plus 2
per course for each block-length of the model's width. Only a start for the sweep. -/
def firstHeight (m : BubbleModel) (n : Nat) : Nat :=
  let width : Q := m.bubbles.foldl (fun w b => max w (2 * max b.semi.x b.semi.y)) 0
  let need (h : Nat) : Q := (h : Q) * (2 + 2 * width * (h : Q) / 15)
  ((List.range maxHeight).find? fun h => (n : Q) ≤ need (h + 1)).map (· + 1) |>.getD maxHeight

/-- Is trial `a` better than trial `b`? Plans that build every bubble come first, then the
higher fast score. -/
def Trial.better (a b : Trial) : Bool :=
  (a.covers && !b.covers) || (a.covers == b.covers && a.fast ≥ b.fast)

/-- Heights as multiples of `h` (in percent), without repeats, from 2 to `maxHeight`. -/
def heightsAt (h : Nat) (percents : List Nat) : List Nat :=
  (percents.map fun p => min maxHeight (max 2 (h * p / 100))).eraseDups

/-- All builds with at most `n` blocks each. First a coarse sweep: heights from half to twice
the first guess, with the coarse settings. Then a fine sweep: heights near the two best ones,
with every setting. -/
def allTrials (m : BubbleModel) (n : Nat) : List Trial :=
  if n == 0 then [] else
  let h0 := firstHeight m n
  let coarse := tryAll m n ((heightsAt h0 [50, 75, 100, 125, 150, 200]).flatMap fun h =>
    (forBudget n coarseSettings).map fun s => (h, s))
  let best := ((coarse.mergeSort Trial.better).map (·.height)).eraseDups.take 2
  let near := (best.flatMap fun hb => heightsAt hb [85, 92, 100, 108, 115]).eraseDups
  let fine := tryAll m n (near.flatMap fun h => (forBudget n fineSettings).map fun s => (h, s))
  coarse ++ fine

/-- The order in which trials go to the physics engine: plans that build every bubble first;
then the best plan of each height, best first; then the rest, best first. -/
def checkOrder (trials : List Trial) : List Trial :=
  let better := Trial.better
  let sorted := (trials.mergeSort better).zipIdx
  let heights := (sorted.map (·.1.height)).eraseDups
  let firsts := heights.filterMap fun h => sorted.find? (·.1.height == h)
  let rest := sorted.filter fun (_, i) => !firsts.any (·.2 == i)
  ((firsts.map (·.1)).mergeSort better) ++ rest.map (·.1)

/-! ## Physics and repair -/

/-- The blocks a physics report blames. Every step of a planner plan places one block
(`toPlan_hands`), so a step number is also a block number. -/
def blamed (r : PhysicsReport) : List Nat :=
  r.diagnostics.filterMap fun
    | .unstable _ b => some b
    | .overlap _ j => some j
    | .clearance _ j => some j
    | .tightSlot s => some s
    | .unevenSupports b => some b
    | _ => none

/-- Remove the blamed blocks, and every block that no longer stands without them (by the local
rule). -/
def removeBlocks (bs : List GBlock) (bad : List Nat) (margin : Q) (strict : Bool) : List GBlock :=
  let kept := (bs.zipIdx.filter fun (_, i) => !bad.contains i).map (·.1)
  (kept.foldl (fun (acc : Stack × Array GBlock) b =>
    match acc.1.place b margin strict with
    | some st => (st, acc.2.push b)
    | none => acc) ({}, #[])).2.toList

/-- Check a plan with the physics engine; on failure, remove the blamed blocks and check again,
at most `rounds` more times. Returns the blocks, the last report, and the number of checks
used. -/
def checkAndRepair (ph : PhysicsEngine) (human : HumanModel) (n : Nat) (bs : List GBlock)
    (margin : Q) (budget : Nat) : List GBlock × PhysicsReport × Nat := Id.run do
  let mut cur := bs
  let mut used := 0
  let mut report : PhysicsReport := { ok := false }
  for _ in [0:3] do
    if used ≥ budget || cur.isEmpty then break
    report := ph.check human n (toPlan cur)
    used := used + 1
    if report.ok then break
    let bad := blamed report
    if bad.isEmpty then break
    let next := removeBlocks cur bad.eraseDups margin (decide (physicsGlobalLimit < n))
    -- a repair that throws away much of the plan gives a poor candidate: stop
    if 4 * next.length < 3 * bs.length then break
    cur := next
  return (cur, report, used)

/-! ## Candidates -/

/-- How hard the plan is to build: by its size, one level harder when the physics engine warns
that a step is hard to reach. -/
def difficultyOf (n : Nat) (r : PhysicsReport) : Difficulty :=
  let warned := r.diagnostics.any fun | .unreachable _ => true | _ => false
  let base : Nat := if n ≤ 30 then 0 else if n ≤ 100 then 1 else 2
  match base + (if warned then 1 else 0) with
  | 0 => .easy
  | 1 => .medium
  | _ => .expert

/-- The candidates to return: only plans within the block limit that the physics engine
accepted, plans the scorer accepts first, then by score; at most `k`. -/
def finalize (n k : Nat) (cs : List Candidate) : List Candidate :=
  let ok := cs.filter fun c => decide (c.plan.blockCount ≤ n) && c.physics.ok
  let sorted := ok.mergeSort fun a b =>
    (a.score.accepted && !b.score.accepted) ||
      (a.score.accepted == b.score.accepted && a.score.score ≥ b.score.score)
  sorted.take k

/-- Check the trials with the physics engine, in `checkOrder`, and score the ones that pass:
at most one per height and `req.maxCandidates` in all, using at most `req.maxChecks` checks. -/
def checkTrials (req : PlanRequest) (ph : PhysicsEngine) (sem : SemanticEngine)
    (trials : List Trial) : List Candidate := Id.run do
  let mut checks := 0
  let mut found : Array Candidate := #[]
  let mut heightsDone : List Nat := []
  for tr in checkOrder trials do
    if checks ≥ req.maxChecks || found.size ≥ req.maxCandidates then break
    -- one candidate per height, so the user chooses between real alternatives
    if heightsDone.contains tr.height then continue
    let (bs, report, used) :=
      checkAndRepair ph req.human req.blocks tr.blocks defaultMargin (req.maxChecks - checks)
    checks := checks + used
    if report.ok && !bs.isEmpty then
      let plan := toPlan bs
      let score := sem.score req.target (tr.height : Q) (bs.map GBlock.toPose)
      found := found.push { plan, physics := report, score,
                            difficulty := difficultyOf bs.length report }
      heightsDone := tr.height :: heightsDone
  return found.toList

/-- The whole planner, as a pure function. -/
def planPure (req : PlanRequest) (ph : PhysicsEngine) (sem : SemanticEngine) : List Candidate :=
  finalize req.blocks req.maxCandidates (checkTrials req ph sem (allTrials req.target.model req.blocks))

/-! ## Tree searches under a time limit -/

/-- The settings of the planner (`planner/DESIGN.md` §6). -/
structure PlannerConfig where
  /-- Return within this many milliseconds. -/
  timeLimitMs : Nat := 30000
  /-- Of that, keep this much for scoring and choosing at the end, but never more than a fifth
  of the limit (so a short limit still leaves time to search). -/
  reserveMs : Nat := 2000
  /-- The first sweep gets at most this share (in percent) of the search time; builds not done
  by then are left out. -/
  sweepShare : Nat := 25
  /-- At most this many tries in all (a safety limit; the time limit comes first). -/
  maxTries : Nat := 10000000
  /-- The share of the time (in percent) before the heuristic phase starts. -/
  treeShare : Nat := 60
  /-- Tree searches at this many heights. -/
  heights : Nat := 8
  /-- At most this many physics checks at the same time. -/
  parallelChecks : Nat := 4
  deriving Repr, Inhabited

/-- Probe: a standing block in the middle of a flat block. -/
def probeOnFlat : BuildPlan :=
  .ofBlocks [(GBlock.mk .flatX 0 0 0).toPose, (GBlock.mk .standX 6 1 1).toPose]

/-- Probe: a flat block resting on two standing blocks (E9 of the physics rules). -/
def probeCarry : BuildPlan :=
  .ofBlocks [(GBlock.mk .standX 0 1 0).toPose, (GBlock.mk .standX 12 1 0).toPose,
    (GBlock.mk .flatX 0 0 15).toPose]

/-- What upright blocks may do, by asking the physics engine (2 checks). -/
def probeRules (ph : PhysicsEngine) (human : HumanModel) : UprightRules :=
  { onFlat := (ph.check human 3 probeOnFlat).ok, carry := (ph.check human 3 probeCarry).ok }

/-- The checks the probes use. -/
def probeChecks : Nat := 2

/-- The heights for tree searches, each with the setting to start from: the two best heights
of the first sweep, heights near each of them, then the other heights of the sweep. At most `k`. -/
def treeHeights (trials : List Trial) (k : Nat) : List (Nat × Setting) :=
  let sorted := trials.mergeSort Trial.better
  let firsts := (sorted.map (·.height)).eraseDups.filterMap fun h =>
    (sorted.find? (·.height == h)).map fun tr => (h, tr.setting)
  let near (i : Nat) (ps : List Nat) : List (Nat × Setting) := match firsts[i]? with
    | some (h, s) => (heightsAt h ps).map fun h' => (h', s)
    | none => []
  let all := (firsts.take 2 ++ near 0 [92, 108, 85, 115] ++ near 1 [92, 108, 85, 115] ++ firsts.drop 2).foldl
    (fun acc (h, s) => if acc.any (·.1 == h) then acc else acc ++ [(h, s)]) []
  all.take k

/-- The tree search at a height, starting from a setting, with the best greedy build of that height (if
any) offered to the physics engine first. -/
def startTree (m : BubbleModel) (n : Nat) (up : UprightRules) (trials : List Trial)
    (h : Nat) (s : Setting) : Tree :=
  let t := Table.make m h
  let tr := Tree.make t h n { paramsFor t s n with up }
  match (trials.filter (·.height == h)).mergeSort Trial.better with
  | best :: _ => tr.offer (Leaf.ofBlocks t tr.info best.blocks.toArray)
  | [] => tr

/-- A candidate for the plan of a leaf that passed physics, scored by the semantic engine. -/
def candidateOf (req : PlanRequest) (sem : SemanticEngine) (height : Nat) (lf : Leaf)
    (r : PhysicsReport) : Candidate :=
  let bs := lf.blocks.toList
  { plan := toPlan bs, physics := r,
    score := sem.score req.target (height : Q) (bs.map GBlock.toPose),
    difficulty := difficultyOf bs.length r }

/-- At most `k` candidates: the best of `firsts` (`finalize`), then, if there is room, the best
of `rest`. -/
def pick (n k : Nat) (firsts rest : List Candidate) : List Candidate :=
  finalize n k firsts ++ finalize n (k - (finalize n k firsts).length) rest

/-- The candidates from the searches: the best plan that passed physics at each height first,
then, if there is room, the other plans that passed. The fast score equals the scorer's score,
so plans are chosen by it first, and only the `maxCandidates` best of each group are sent to the
semantic engine (scoring is slow for big models). -/
def candidatesOf (req : PlanRequest) (sem : SemanticEngine) (trees : List Tree) : List Candidate :=
  let k := req.maxCandidates
  let best (l : List (Nat × Leaf × PhysicsReport)) :=
    (l.mergeSort fun a b => a.2.1.better b.2.1).take k
  let firsts := best (trees.filterMap fun tr => tr.passed.head?.map (tr.height, ·))
  let rest := best (trees.flatMap fun tr => (tr.passed.drop 1).map (tr.height, ·))
  pick req.blocks k (firsts.map fun (h, lf, r) => candidateOf req sem h lf r)
    (rest.map fun (h, lf, r) => candidateOf req sem h lf r)

/-- A physics check running in the background, for the leaf of search `tree`. -/
structure Pending where
  tree : Nat
  leaf : Leaf
  task : Task PhysicsReport
  /-- When it started (ms). -/
  since : Nat

/-- What the search did, for reports and tests. -/
structure SearchLog where
  rounds : Nat := 0
  tries : Nat := 0
  checks : Nat := 0
  pruned : Nat := 0
  timedOut : Nat := 0
  up : UprightRules := {}
  /-- Each time the best plan that passed physics got better: the time since the start (ms),
  its fast score, and whether it reaches every bubble. -/
  trace : Array (Nat × Q × Bool) := #[]
  deriving Repr, Inhabited

/-- Run the tree searches for a bubble model, under the time limit. Returns the searches (with
the plans that passed physics) and a log. -/
def runSearch (cfg : PlannerConfig) (req : PlanRequest) (ph : PhysicsEngine) (m : BubbleModel) :
    IO (List Tree × SearchLog) := do
  let start ← IO.monoMsNow
  let reserve := min cfg.reserveMs (cfg.timeLimitMs / 5)
  let stopAt := start + cfg.timeLimitMs - reserve
  let n := req.blocks
  if n == 0 then return ([], {})
  let up := probeRules ph req.human
  let mut log : SearchLog := { checks := probeChecks, up }
  -- the first sweep: greedy builds at a coarse spread of heights, in parallel. Builds not done
  -- by `sweepEnd` are left out (they keep running in the background until done).
  let h0 := firstHeight m n
  let jobs := (heightsAt h0 [50, 75, 100, 125, 150, 200]).flatMap fun h =>
    (forBudget n coarseSettings).map fun s => (h, s)
  let sweepTasks := jobs.map fun (h, s) => Task.spawn fun _ => tryBuild m h s n
  let sweepEnd := start + (stopAt - start) * cfg.sweepShare / 100
  repeat
    if (← IO.monoMsNow) ≥ sweepEnd then break
    if ← sweepTasks.allM (fun t => (IO.hasFinished t : IO Bool)) then break
    IO.sleep 5
  let mut trials : List Trial := []
  for task in sweepTasks do
    if ← IO.hasFinished task then
      let tr := task.get
      if !tr.blocks.isEmpty then trials := trials ++ [tr]
  let mut trees : Array Tree :=
    ((treeHeights trials cfg.heights).map fun (h, s) => startTree m n up trials h s).toArray
  let mut alive : Array Bool := trees.map fun _ => true
  let mut pending : Array Pending := #[]
  let mut steps := 2
  let afterSweep ← IO.monoMsNow
  let treeEnd := afterSweep + (stopAt - min stopAt afterSweep) * cfg.treeShare / 100
  let mut heuristic := false
  let mut halvings := 0
  -- the longest physics check so far (ms). A check cannot be stopped, and the program does not
  -- end before its checks do, so no check starts that would likely end after the limit.
  let mut longest := 0
  repeat
    let now ← IO.monoMsNow
    if now ≥ stopAt || log.tries ≥ cfg.maxTries then break
    if now ≥ treeEnd then heuristic := true
    -- reports that came back
    let mut still : Array Pending := #[]
    for p in pending do
      if ← IO.hasFinished p.task then
        trees := trees.modify p.tree (·.report p.leaf p.task.get)
        longest := max longest (now - min now p.since)
      else
        longest := max longest (now - min now p.since)
        still := still.push p
    pending := still
    -- the best plan so far, for the trace
    let best := trees.foldl (fun (acc : Option Leaf) tr => match acc, tr.incumbent with
      | some a, some b => if b.better a then some b else some a
      | none, b => b
      | a, none => a) none
    match best, log.trace.back? with
    | some b, some (_, f, c) =>
      if b.better { blocks := #[], fast := f, covers := c } then
        log := { log with trace := log.trace.push (now - start, b.fast, b.covers) }
    | some b, none => log := { log with trace := log.trace.push (now - start, b.fast, b.covers) }
    | none, _ => pure ()
    -- new checks, taking turns between the searches
    let mut progress := true
    while progress && pending.size < cfg.parallelChecks && log.checks < req.maxChecks &&
        now + longest < stopAt do
      progress := false
      for i in [0:trees.size] do
        if pending.size < cfg.parallelChecks && log.checks < req.maxChecks then
          match trees[i]!.takeRequest with
          | some (lf, tr') =>
            trees := trees.set! i tr'
            let plan := toPlan lf.blocks.toList
            let task := Task.spawn (prio := .dedicated) fun _ => ph.check req.human n plan
            pending := pending.push { tree := i, leaf := lf, task, since := now }
            log := { log with checks := log.checks + 1 }
            progress := true
          | none => pure ()
    -- successive halving: at a third and two thirds of the time, the worse half stops
    let third := (stopAt - min stopAt afterSweep) / 3
    if halvings < 2 && now ≥ afterSweep + third * (halvings + 1) then
      halvings := halvings + 1
      let ranked := ((List.range trees.size).filter (alive[·]!)).mergeSort fun i j =>
        match trees[i]!.incumbent, trees[j]!.incumbent with
        | some a, some b => a.better b || !b.better a
        | some _, none => true
        | none, _ => false
      let keep := ranked.take (max (min 4 ranked.length) ((ranked.length + 1) / 2))
      alive := (List.range trees.size).toArray.map keep.contains
    -- one round of every live search, in parallel
    let live := (List.range trees.size).filter (alive[·]!)
    let busy := live.filter fun i => !trees[i]!.idle || heuristic
    if busy.isEmpty then
      if pending.isEmpty && trees.all (·.requests.isEmpty) then
        if heuristic || trees.all (·.incumbent.isNone) then break
        heuristic := true
      else IO.sleep 20
      continue
    let t0 ← IO.monoMsNow
    let tasks := busy.map fun i => (i, Task.spawn fun _ => trees[i]!.run steps heuristic)
    for (i, task) in tasks do
      let before := trees[i]!.tries
      let tr ← IO.wait task
      trees := trees.set! i tr
      log := { log with tries := log.tries + (tr.tries - before) }
    let dt := (← IO.monoMsNow) - t0
    steps := if dt < 150 then min 256 (steps * 2) else if dt > 600 then max 1 (steps / 2) else steps
    log := { log with rounds := log.rounds + 1 }
  log := { log with timedOut := pending.size, pruned := trees.foldl (· + ·.pruned) 0 }
  return (trees.toList, log)

/-- The planner with settings: tree searches under the time limit (`runSearch`), then the
candidates. -/
def plannerWith (cfg : PlannerConfig) : Planner :=
  ⟨fun req ph sem => do
    let (trees, _) ← runSearch cfg req ph req.target.model
    return candidatesOf req sem trees⟩

/-- The planner: tree searches for at most 30 seconds. -/
def planner : Planner := plannerWith {}

end KaplaPlanner
