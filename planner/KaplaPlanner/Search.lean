import KaplaPlanner.PreCheck
import KaplaPlanner.Motifs.Single
import KaplaPlanner.Motifs.Tower
import KaplaPlanner.Motifs.Column

/-! # Search: propose plans, check them, repair them, rank them

Version P1: the whole target is one region, built as a log-cabin tower (hollow), a solid
column, or a single upright block.

1. **Propose**: a few heights per motif (the one that matches the target's shape, the
   tallest the budget allows, and smaller ones), plus the single block.
2. **Pre-check** on the grid.
3. **Physics check**. On a failure at step `k`, **repair**: keep only the steps before
   `k`. Those passed the check, so the shorter plan is a safe fallback. Then check again.
4. **Score** with the semantic engine, and **rank**.

Only plans that passed the physics check and use at most `N` blocks are returned
(`planPure_sound`). -/

namespace KaplaPlanner
open KaplaCore

/-- A proposal: a name and the grid steps. -/
structure Proposal where
  name  : String
  steps : List GridStep

/-- A box around all parts of the target. -/
def targetBox (t : TargetSpec) : Box :=
  (Box.joinAll (t.partsOrWhole.map (·.box))).getD t.shape.bbox

/-- Layer counts to try for a square motif 15 cells wide that costs `perLayer` blocks per
layer. A motif with `15 · h / w` layers has the target's height-to-width ratio. We also try
the tallest the budget allows, and half and a quarter of that. -/
def layerCounts (t : TargetSpec) (n perLayer : Nat) : List Nat :=
  let b := (targetBox t).size
  let w := max b.x b.y
  let maxL := n / perLayer
  let fit : Nat := if w ≤ 0 then maxL else ((15 * b.z / w).ceil).toNat
  ([min fit maxL, maxL, maxL / 2, maxL / 4].filter (· ≥ 1)).eraseDups

/-- Proposals for a square motif with layers. -/
def layered (m : Motif Nat) (perLayer : Nat) (phase : String) (t : TargetSpec) (n : Nat) :
    List Proposal :=
  (layerCounts t n perLayer).map fun l =>
    { name := s!"{m.name}, {l} layers", steps := sequence phase (m.blocks l) }

/-- The plans we try first: log-cabin towers (hollow), solid columns, and one block. -/
def proposals (t : TargetSpec) (n : Nat) : List Proposal :=
  let single : List Proposal :=
    if n ≥ 1 then [{ name := "single block", steps := sequence "trunk" (Motifs.single.blocks ()) }]
    else []
  layered Motifs.tower 2 "tower" t n ++ layered Motifs.column 5 "column" t n ++ single

/-- How hard a plan is to build: two-hand steps or many blocks make it harder. -/
def difficultyOf (p : BuildPlan) : Difficulty :=
  if p.blockCount > 150 then .expert
  else if p.blockCount > 60 || p.steps.any (·.blocks.length > 1) then .medium
  else .easy

/-- 0 for easy, 1 for medium, 2 for expert. -/
def difficultyRank : Difficulty → Nat
  | .easy => 0 | .medium => 1 | .expert => 2

/-- The first step that the physics engine says is unstable, if any. -/
def firstUnstableStep (r : PhysicsReport) : Option Nat :=
  (r.diagnostics.filterMap fun
    | .unstable k _ | .pressTips k _ | .slides k _ | .unreachable k => some k
    | _ => none).min?

/-- Check a plan; on a failure at step `k > 0`, keep only the steps before `k` and check
again. `fuel` limits the number of physics calls. Returns the last plan checked, its
report, and the fuel left. -/
def checkAndRepair (phys : PhysicsEngine) (h : HumanModel) (n : Nat) :
    Nat → List GridStep → Option (List GridStep × PhysicsReport) × Nat
  | 0, _ => (none, 0)
  | fuel + 1, steps =>
    let r := phys.check h n (toBuildPlan steps)
    if r.ok then (some (steps, r), fuel) else
    match firstUnstableStep r with
    | some k =>
      if 0 < k && k < steps.length then checkAndRepair phys h n fuel (steps.take k)
      else (some (steps, r), fuel)
    | none => (some (steps, r), fuel)

/-- Sort key: score in steps of 1/50 (higher first), then easier first, then exact score. -/
def better (a b : Candidate) : Bool :=
  let bucket (c : Candidate) : Int := (c.score.score * 50).floor
  bucket a > bucket b ||
  (bucket a == bucket b && (difficultyRank a.difficulty < difficultyRank b.difficulty ||
    (difficultyRank a.difficulty == difficultyRank b.difficulty && a.score.score ≥ b.score.score)))

/-- A candidate we may return: physics said ok, and it uses at most `n` blocks. -/
def acceptable (n : Nat) (c : Candidate) : Bool := c.physics.ok && c.plan.blockCount ≤ n

/-- Check, repair and score each proposal. -/
def evaluate (req : PlanRequest) (phys : PhysicsEngine) (sem : SemanticEngine) :
    List Proposal → Nat → List Candidate
  | [], _ => []
  | p :: ps, fuel =>
    if !(preCheck req.blocks p.steps).isEmpty then evaluate req phys sem ps fuel else
    match checkAndRepair phys req.human req.blocks (min fuel 8) p.steps with
    | (none, _) => []
    | (some (steps, r), left) =>
      let plan := toBuildPlan steps
      let c : Candidate :=
        { plan, physics := r, score := sem.score req.target plan.blocks,
          difficulty := difficultyOf plan }
      c :: evaluate req phys sem ps (fuel - (min fuel 8 - left))

/-- The planner as a pure function: the best candidates, best first. -/
def planPure (req : PlanRequest) (phys : PhysicsEngine) (sem : SemanticEngine) :
    List Candidate :=
  let all := evaluate req phys sem (proposals req.target req.blocks) req.maxChecks
  ((all.filter (acceptable req.blocks)).mergeSort better).take req.maxCandidates

/-- Every candidate the planner returns passed the physics check and uses at most `N`
blocks. -/
theorem planPure_sound (req : PlanRequest) (phys : PhysicsEngine) (sem : SemanticEngine) :
    ∀ c ∈ planPure req phys sem, c.physics.ok = true ∧ c.plan.blockCount ≤ req.blocks := by
  intro c hc
  simp only [planPure] at hc
  have h := List.mem_of_mem_take hc
  rw [List.mem_mergeSort] at h
  have := (List.mem_filter.mp h).2
  simp only [acceptable, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

end KaplaPlanner
