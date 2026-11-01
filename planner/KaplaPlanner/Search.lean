import KaplaPlanner.Build

/-! # Search: heights, settings, the physics check, and the candidates

The outer loop of the planner (`planner/DESIGN.md` §4.1, §4.7, §4.8):

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

/-- Build once, with at most `cap` blocks. -/
def tryBuild (m : BubbleModel) (height : Nat) (s : Setting) (cap : Nat) : Trial :=
  let t := Table.make m height
  let r := build t { lambda := 1, price := defaultPrice, maxBlocks := cap, margin := defaultMargin,
                     cabin := s.cabin, underShare := s.underShare,
                     perCourse := perCourseLimit t cap s.perCourse, strict := s.strict }
  let bs := r.blocks.toList
  { height, blocks := bs, fast := r.state.score t, covers := coversAll t bs }

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

/-- The blocks a physics report blames. -/
def blamed (r : PhysicsReport) : List Nat :=
  r.diagnostics.filterMap fun
    | .unstable _ b => some b
    | .overlap _ j => some j
    | .clearance _ j => some j
    | .pressTips s _ => some s
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
      let score := sem.score req.target (Frame.ofHeight tr.height) (bs.map GBlock.toPose)
      found := found.push { plan, physics := report, score,
                            difficulty := difficultyOf bs.length report }
      heightsDone := tr.height :: heightsDone
  return found.toList

/-- The whole planner, as a pure function. Only bubble targets are supported; any other target
gets no candidates. -/
def planPure (req : PlanRequest) (ph : PhysicsEngine) (sem : SemanticEngine) : List Candidate :=
  match req.target.shape with
  | .bubbles m => finalize req.blocks req.maxCandidates (checkTrials req ph sem (allTrials m req.blocks))
  | _ => []

/-- The planner. -/
def planner : Planner := ⟨fun req ph sem => pure (planPure req ph sem)⟩

end KaplaPlanner
