import KaplaCore
import KaplaPhysics.Engine
import KaplaSpecs.PhysicsRules.FromCore

/-! # The physics engine behind KaplaCore's interface

`physicsEngine` is the value of `KaplaCore.PhysicsEngine` that the app passes to the
planner instead of `physicsMock`. It turns the core plan into planks (`buildOf`), runs
`checkPlan`, and turns the result into core diagnostics.

How core's plan is read:

* **Blocks per step.** Core lets a step place up to `hands` blocks. The physics rules (K1)
  place one plank per step. We check the build after **every block**, in list order, not
  only after every step. That is cautious: a step whose blocks only stand together (for
  example a counterweight put on at the same time) is refused.
* **Placement error.** `epsRel` is used as `ε` of rule R1: every block may land up to
  `epsRel` off its planned spot along `x` and along `y`. The default is 10/39 (2 mm), as
  in the rules.
* **Turns.** Only quarter turns have a physics pose. A plan with any other turn is not
  `ok`.
* **Reach (K3)** is a warning: it gives an `unreachable` diagnostic but does not make the
  plan not `ok`.
* **Not modelled:** `eAbs`, `press`, `clear` and `muSafe` are not used, and the engine never
  gives `slides`, `pressTips`, `clearance` or `unevenSupports`.

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

/-- Every pair of blocks `i < j` that share inside space (P1). -/
def overlapPairs (b : Build) : List Diagnostic :=
  (List.range b.length).flatMap fun i =>
    ((List.range b.length).filter fun j => i < j && decide (Overlap (b.get i) (b.get j))).map
      fun j => .overlap i j

/-- The first block after which the build is not shown to be well-formed and solid. -/
def firstUnsafeBlock (ε : Rat) (b : Build) : Option Nat :=
  (List.range b.length).find? fun k =>
    !(decide (WellFormed (b.take (k + 1))) && solidAnswer ε (b.take (k + 1)))

/-- `KaplaCore.PhysicsEngine.check`, done by the verified engine.

`ok` is true exactly when every step places 1 to `hands` blocks, every block has a physics
pose, and `checkPlan` accepts the blocks as a plan of at most `maxBlocks` planks.

If a block has no physics pose, or the build after a block is not shown to stand, the
report has `unstable step block` for the first such block. The engine does not say which
block would fall, so it names the block whose placement went wrong. -/
def coreCheck (h : HumanModel) (maxBlocks : Nat) (plan : BuildPlan) : PhysicsReport :=
  let n := plan.blockCount
  let stepOf := fun i => (stepOfBlock plan).getD i 0
  let countDiags : List Diagnostic := if n > maxBlocks then [.tooManyBlocks n maxBlocks] else []
  let stepDiags := stepDiagnostics h plan
  match buildOf plan.blocks with
  | none =>
      let bad := (plan.blocks.findIdx? fun p => (plankOf p).isNone).getD 0
      { ok := false, diagnostics := countDiags ++ stepDiags ++ [.unstable (stepOf bad) bad] }
  | some b =>
      let safe := checkPlan h.epsRel maxBlocks b
      let unsafeDiags : List Diagnostic :=
        if safe then [] else
          match firstUnsafeBlock h.epsRel b with
          | some k => [.unstable (stepOf k) k]
          | none => []
      let reachDiags : List Diagnostic :=
        ((hardToReach dropGap b).map stepOf).eraseDups.map .unreachable
      { ok := stepDiags.isEmpty && safe,
        diagnostics := countDiags ++ stepDiags ++ overlapPairs b ++ unsafeDiags ++ reachDiags }

/-- The verified physics engine, for `app/Main.lean` to pass to the planner. -/
def physicsEngine : KaplaCore.PhysicsEngine := ⟨coreCheck⟩

end KaplaPhysics
