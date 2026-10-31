import KaplaPlanner.Layers

/-!
# KaplaPlanner.Planner — search, repair, sequencing (untrusted)

For a target and a block budget `N`:
1. **scale search**: candidate scales around the one where the target volume matches the
   budget;
2. **motifs**: the generic layer planner, plus special motifs chosen by tags (tree for
   `trunk`, log-cabin for slender `tower`s);
3. **repair loop**: ask the physics engine; remove blocks it blames (and everything that
   then loses its support); repeat;
4. **sequencer**: bottom-up build order, one block per step, grip and approach, phases;
5. rank by (physics ok, score, fewer blocks).
-/

namespace Kapla.Planning

open Kapla

/-- Display / sorting helper. -/
private def qf (q : Q) : Float := q.toFloat

/-- Alignment reference of block `j` (build order): the nearest earlier block it rests on, or
for a block on the ground the nearest earlier ground block. The builder lines block `j` up
with it — the robustness check (H1/H2) bounds misalignment along these links. -/
def alignRef (arr : Array Pose) (j : Nat) : Option Nat := Id.run do
  let b := arr[j]!
  let mut best : Option (Nat × Q) := none
  for i in [0:j] do
    let a := arr[i]!
    let under := if b.bottomZ = 0 then a.bottomZ = 0 else a.topZ = b.bottomZ
    if under then
      let d := |a.center.x - b.center.x| + |a.center.y - b.center.y|
      match best with
      | some (_, d0) => if d < d0 then best := some (i, d)
      | none => best := some (i, d)
  return best.map (·.1)

/-- Build order and step annotations. -/
def sequence (bs : List Pose) : BuildPlan :=
  let levels := (bs.map (·.bottomZ)).eraseDups.mergeSort (· ≤ ·)
  let sorted := bs.mergeSort fun a b =>
    a.bottomZ < b.bottomZ || (a.bottomZ = b.bottomZ &&
      (a.center.y < b.center.y || (a.center.y = b.center.y && a.center.x ≤ b.center.x)))
  let arr := sorted.toArray
  ⟨(List.range arr.size).map fun j =>
    let b := arr[j]!
    let lvl := levels.idxOf b.bottomZ
    { blocks := [b]
      grip := .longSides
      approach := .fromAbove
      phase := s!"layer {lvl + 1}"
      refs := [alignRef arr j] }⟩

/-- Drop blocks (bottom-up) whose centre is no longer spanned by supports. -/
def pruneUnsupported (bs : List Pose) : List Pose := Id.run do
  let sorted := bs.mergeSort fun a b => a.bottomZ ≤ b.bottomZ
  let mut kept : List Pose := []
  for b in sorted do
    if b.up = .flat && !spanned kept b then continue
    if b.up != .flat && b.bottomZ ≠ 0 &&
        !(kept.any fun a => a.topZ = b.bottomZ && decide (a.InFootprint b.center)) then continue
    kept := kept ++ [b]
  return kept

/-- Ask physics; remove blamed blocks until it accepts (or we give up). -/
def repair (ph : PhysicsEngine) (H : HumanModel) (N : Nat) (bs0 : List Pose)
    (maxIter : Nat := 40) : BuildPlan × PhysicsReport := Id.run do
  let mut bs := (pruneUnsupported bs0).take N
  let mut plan := sequence bs
  let mut rep := ph.check H N plan
  for _ in [0:maxIter] do
    if rep.ok || bs.isEmpty then break
    let blocks := plan.blocks
    -- blame: the block placed at the first failing step (its load breaks the structure),
    -- or the later block of an overlapping pair
    let victim : Option Nat := rep.diagnostics.findSome? fun
      | .unstable s _ => some s
      | .pressTips s _ => some s
      | .overlap _ j => some j
      | .clearance _ j => some j
      | .belowGround b => some b
      | _ => none
    match victim with
    | none => break
    | some v =>
      bs := pruneUnsupported (blocks.eraseIdx v)
      plan := sequence bs
      rep := ph.check H N plan
  return (plan, rep)

def difficultyOf (plan : BuildPlan) : Difficulty :=
  let bs := plan.blocks
  let height : Q := (bs.map (·.topZ)).max?.getD 0
  if bs.any (·.up != .flat) && bs.length > 20 then .medium
  else if height > 400 then .medium
  else .easy

/-- Volume of the bounding box (mm³) of a shape. -/
def bboxVolume (s : Shape) : Q :=
  let (lo, hi) := s.bbox
  (hi.x - lo.x) * (hi.y - lo.y) * (hi.z - lo.z)

/-- Rational approximation with denominator 20 (keeps all coordinates simple). -/
def roundQ (x : Float) : Q := ((x * 20).round.toInt64.toInt : Q) / 20

def scaled (t : TargetSpec) (s : Q) : TargetSpec :=
  { t with shape := .scale s t.shape, unitMM := s }

/-- Blocks the layer planner uses at scale `s` (capped at `cap`). -/
def layerCount (t : TargetSpec) (s : Q) (cap : Nat) : Nat :=
  (layerPlan (scaled t s).shape cap (phases := 1)).flatten.length

/-- Count-driven scale search: iterate `s ← s·(N/count)^(1/3)` so the layer plan just fits
the budget, then propose the largest fitting scale, a slightly smaller one, and the
smallest overflowing one (which gets truncated). -/
def scaleCandidates (t : TargetSpec) (N : Nat) : List Q := Id.run do
  let v := bboxVolume t.shape
  if v ≤ 0 || N = 0 then return [1]
  let cap := 3 * N + 10
  -- beyond this scale the bounding box is 20× the volume of all blocks: hopeless
  let sMax := Float.cbrt (20 * N.toFloat * qf Block.volume / qf v)
  let mut s : Float := Float.cbrt (N.toFloat * qf Block.volume / (0.5 * qf v))
  let mut seen : Array (Q × Nat) := #[]
  for _ in [0:6] do
    let sq := roundQ (min sMax (max (1/20) s))
    if seen.any (·.1 == sq) then break
    let c := layerCount t sq cap
    seen := seen.push (sq, c)
    let ratio := if c = 0 then 2.0 else Float.cbrt (N.toFloat / c.toFloat)
    s := sq.toFloat * (min 2 (max 0.5 ratio))
  let fits := seen.filter fun (_, c) => 0 < c && c ≤ N
  let overflow := seen.filter fun (_, c) => c > N
  let best := (fits.toList.map (·.1)).max?
  let above := (overflow.toList.map (·.1)).min?
  let picks := best.toList ++ best.toList.map (fun b => roundQ (qf b * 0.9)) ++ above.toList
  -- the volume-based guesses keep the special motifs (tree, tower) in play
  let s0 := Float.cbrt (N.toFloat * qf Block.volume / (0.5 * qf v))
  let byVolume := [0.7, 1.0].map fun f => roundQ (min 6 (max (1/20) (s0 * f)))
  let probed := if picks.isEmpty then seen.toList.map (·.1) else []
  return (picks ++ byVolume ++ probed).filter (· > 0) |>.eraseDups

/-- Proposed block sets for one scaled target. -/
def proposals (t : TargetSpec) (N : Nat) : List (String × List Pose) :=
  let s := t.shape
  let (lo, hi) := s.bbox
  let tags := s.tags
  let layered := [0, W / 2].map fun off => ("layers", (layerPlan s N (1/2) off).flatten)
  let sparse := [("layers-sparse", (layerPlan s N (7/10) 0).flatten)]
  let tower :=
    if tags.contains "tower" && hi.x - lo.x ≤ 2 * L && hi.y - lo.y ≤ 2 * L then
      let layers := min (N / 2) ((hi.z / T).floor.toNat)
      [("log-cabin tower", cabinTower ((lo.x + hi.x) / 2) ((lo.y + hi.y) / 2) layers)]
    else []
  let treeM :=
    if tags.contains "trunk" || N ≤ 2 then
      let crown := min (N - 1) ((max 0 ((hi.z - L) / T)).floor.toNat)
      [("tree", tree ((lo.x + hi.x) / 2) ((lo.y + hi.y) / 2) crown)]
    else []
  let roof := (s.taggedParts.filter fun (tg, _) => tg == "roof:gable" || tg == "roof:hip").flatMap
    fun (_, part) =>
      let (rlo, rhi) := part.bbox
      [("layers + stepped roof",
        ((layerPlan (.diff s part) N (1/2) 0).flatten ++
          steppedRoof ((rlo.x + rhi.x) / 2) ((rlo.y + rhi.y) / 2) (rhi.x - rlo.x) (rhi.y - rlo.y)
            rlo.z (W / 2) 40))]
  (layered ++ sparse ++ tower ++ treeM ++ roof).filter fun (_, bs) => !bs.isEmpty

def plan (req : PlanRequest) (ph : PhysicsEngine) (se : SemanticEngine)
    (maxRepairs : Nat := 4) : IO (List Candidate) := do
  -- 1. propose at every scale and pre-rank by the (cheap) score of the unrepaired blocks
  let mut pre : Array (Q × String × TargetSpec × List Pose) := #[]
  for s in scaleCandidates req.target req.blocks do
    let t := scaled req.target s
    for (motif, bs) in proposals t req.blocks do
      let bs := (pruneUnsupported bs).take req.blocks
      if bs.isEmpty then continue
      pre := pre.push ((se.score t bs).score, motif, t, bs)
  let shortlist := (pre.toList.mergeSort fun a b => a.1 ≥ b.1).take maxRepairs
  -- 2. repair only the shortlist with the physics engine
  let mut out : Array Candidate := #[]
  for (_, motif, t, bs) in shortlist do
    let (p, rep) := repair ph req.human req.blocks bs
    if p.blockCount = 0 then continue
    let sc := se.score t p.blocks
    out := out.push { plan := p, motif, target := t, score := sc, physics := rep,
                      difficulty := difficultyOf p }
  let ranked := out.toList.mergeSort fun a b =>
    (a.physics.ok && !b.physics.ok) ||
    (a.physics.ok == b.physics.ok && (a.score.score > b.score.score ||
      (a.score.score = b.score.score && a.plan.blockCount ≤ b.plan.blockCount)))
  return ranked

def planner : Kapla.Planner where
  name := "layers-v1"
  plan := fun r ph se => plan r ph se

end Kapla.Planning
