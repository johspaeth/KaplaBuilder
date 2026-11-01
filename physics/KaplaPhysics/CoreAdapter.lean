import KaplaCore
import KaplaPhysics.Engine

/-! # The physics engine behind KaplaCore's interface

`physicsEngine` is the value of `KaplaCore.PhysicsEngine` that the app passes to the
planner instead of `physicsMock`. A core block is a physics plank, so it runs `checkPlan` on
the blocks of the plan and turns the result into core diagnostics.

How core's plan is read:

* **Blocks per step.** Core lets a step place up to `hands` blocks. The physics rules (K1)
  place one plank per step. We check the build after **every block**, in list order, not
  only after every step. That is cautious: a step whose blocks only stand together (for
  example a counterweight put on at the same time) is refused.
* **Placement error: R1 is the model.** `epsRel` is used as `ε` of rule R1: every block
  may land up to `epsRel` off its own planned spot along `x` and along `y`. The default is
  10/39 (2 mm), as in the rules. Core's `HumanModel` also allows errors that add up from
  level to level (up to `eAbs`); those are not covered. With `ε = eAbs`, no build taller
  than one level would pass, so the team chose R1.
* **Clearance.** `coreCheck` takes the `PlanOptions`; `physicsEngine` uses the default
  (clearance off). When it is on, blocks that touch in the plan are still fine, but two
  blocks with a gap must keep it: the gap must be at least `2 * epsRel`, so no placement
  error can close it. Pairs with a smaller gap get a `clearance` diagnostic.
* **Turns.** Only the turns allowed by B6 (quarter turns, and about 30°, 45°, 60°) pass
  the well-formedness check. A plan with any other turn is not `ok`.
* **Reach (K3)** is a warning: it gives an `unreachable` diagnostic but does not make the
  plan not `ok`.
* **Not modelled:** `eAbs`, `press`, `clear` and `muSafe` are not used, and the engine never
  gives `slides`, `pressTips` or `unevenSupports`.

`coreCheck_ok_sound` (statement in `specs/KaplaSpecs/Physics.lean`) says what `ok` means. -/

namespace KaplaPhysics

open KaplaCore (HumanModel BuildPlan PhysicsReport Diagnostic)

/-- The step number of each block, in build order. -/
def stepOfBlock (plan : BuildPlan) : List Nat :=
  plan.steps.zipIdx.flatMap fun (st, k) => st.blocks.map fun _ => k

/-- Problems with the steps themselves: empty steps, and steps with more blocks than the
builder has hands. -/
def stepDiagnostics (h : HumanModel) (plan : BuildPlan) : List Diagnostic :=
  plan.steps.zipIdx.flatMap fun (st, k) =>
    (if st.blocks.isEmpty then [.emptyStep k] else []) ++
      (if st.blocks.length > h.hands then [.tooManyHands k] else [])

/-- Every pair of blocks `i < j` that seem to share inside space (P1). Only a hint for the
builder: the guarantee comes from `checkPlan`. -/
def overlapPairs (b : Build) : List Diagnostic :=
  (List.range b.length).flatMap fun i =>
    ((List.range b.length).filter fun j => i < j && overlapGuess (b.get i) (b.get j)).map
      fun j => .overlap i j
where
  /-- The heights overlap and the computed point is strictly inside both planks. -/
  overlapGuess (p q : Plank) : Bool :=
    decide (p.bottom < q.top) && decide (q.bottom < p.top) && sharesCheck p q

/-- Every pair of blocks `i < j` with a gap that a placement error up to `ε` could close:
a near miss (`clearPairCheck`). -/
def clearancePairs (ε : Rat) (b : Build) : List Diagnostic :=
  (List.range b.length).flatMap fun i =>
    ((List.range b.length).filter fun j =>
      i < j && !overlapPairs.overlapGuess (b.get i) (b.get j) &&
        !clearPairCheck ε (b.get i) (b.get j)).map fun j => .clearance i j

/-- The first block after which the build is not shown to be well-formed and solid.
(Near misses get their own `clearance` diagnostic.) -/
def firstUnsafeBlock (ε : Rat) (b : Build) : Option Nat :=
  (List.range b.length).find? fun k =>
    !(wellFormedCheck (b.take (k + 1)) && solidAnswer ε (b.take (k + 1)))

/-- `KaplaCore.PhysicsEngine.check`, done by the verified engine.

`ok` is true exactly when every step places 1 to `hands` blocks and `checkPlan opts`
accepts the blocks as a plan of at most `maxBlocks` planks.

If the build after a block is not shown to be well-formed and solid (for example because
the block's turn is not allowed), the report has `unstable step block` for the first such
block. The engine does not say which block would fall, so it names the block whose
placement went wrong. -/
def coreCheck (opts : PlanOptions) (h : HumanModel) (maxBlocks : Nat) (plan : BuildPlan) :
    PhysicsReport :=
  let b : Build := plan.blocks
  let n := plan.blockCount
  let stepOf := fun i => (stepOfBlock plan).getD i 0
  let countDiags : List Diagnostic := if n > maxBlocks then [.tooManyBlocks n maxBlocks] else []
  let stepDiags := stepDiagnostics h plan
  let safe := checkPlan opts h.epsRel maxBlocks b
  let unsafeDiags : List Diagnostic :=
    if safe then [] else
      match firstUnsafeBlock h.epsRel b with
      | some k => [.unstable (stepOf k) k]
      | none => []
  let reachDiags : List Diagnostic :=
    ((hardToReach dropGap b).map stepOf).eraseDups.map .unreachable
  { ok := stepDiags.isEmpty && safe,
    diagnostics := countDiags ++ stepDiags ++ overlapPairs b ++
      (if opts.clearance then clearancePairs h.epsRel b else []) ++
      unsafeDiags ++ reachDiags }

/-- The verified physics engine, for `app/Main.lean` to pass to the planner. Clearance is
off (the default `PlanOptions`). -/
def physicsEngine : KaplaCore.PhysicsEngine := ⟨coreCheck {}⟩

end KaplaPhysics
