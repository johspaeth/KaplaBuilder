import KaplaCore
import KaplaPhysics.Engine
import KaplaPhysics.Turned
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
* **Placement error: R1 is the model.** `epsRel` is used as `ε` of rule R1: every block
  may land up to `epsRel` off its own planned spot along `x` and along `y`. The default is
  1/2 (3.9 mm), as in the rules. Core's `HumanModel` also allows errors that add up from
  level to level (up to `eAbs`); those are not covered. With `ε = eAbs`, no build taller
  than one level would pass, so the team chose R1.
* **Clearance.** `coreCheck` takes the `PlanOptions`; `physicsEngine` uses the default
  (clearance on). Blocks that touch in the plan are still fine, but two blocks with a gap
  must keep it: the gap must be at least `2 * epsRel`, so no placement error can close it.
  Pairs with a smaller gap get a `clearance` diagnostic. A block that goes into a slot
  exactly its own width, between two blocks placed before it, gets a `tightSlot`
  diagnostic.
* **Turns.** A plan with only quarter turns gets the full check below. A plan with some
  other turn in steps of 15° (B6) is checked at the planned positions only: well-formed
  and stable after every block (`checkTurnedPlan`), without placement errors, gaps or
  reach. A plan with any other turn is not `ok`.
* **Reach (K3)** is a warning: it gives an `unreachable` diagnostic but does not make the
  plan not `ok`.
* **Not modelled:** `eAbs`, `clear` and `muSafe` are not used, and the engine never gives
  `slides` or `unevenSupports`.

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

/-- Every pair of blocks `i < j` with a gap that a placement error up to `ε` could close:
a near miss (`ClearPair`). -/
def clearancePairs (ε : Rat) (b : Build) : List Diagnostic :=
  (List.range b.length).flatMap fun i =>
    ((List.range b.length).filter fun j =>
      i < j && !decide (Overlap (b.get i) (b.get j)) &&
        !decide (ClearPair ε (b.get i) (b.get j))).map fun j => .clearance i j

/-- Every block that goes into a tight slot between blocks placed before it (H6). -/
def tightSlots (b : Build) : List Nat :=
  (List.range b.length).filter fun k => decide (InTightSlot (b.take k) (b.get k))

/-- Every pair of turned blocks `i < j` that share inside space (P1). -/
def tOverlapPairs (b : TBuild) : List Diagnostic :=
  (List.range b.length).flatMap fun i =>
    ((List.range b.length).filter fun j => i < j && decide (TOverlap (b.get i) (b.get j))).map
      fun j => .overlap i j

/-- The first block after which a turned build is not shown to be well-formed and to stand. -/
def firstUnsafeTurned (b : TBuild) : Option Nat :=
  (List.range b.length).find? fun k =>
    !(decide (TWellFormed (b.take (k + 1))) && tStands (b.take (k + 1)))

/-- The first block after which the build is not shown to be well-formed and solid.
(Near misses get their own `clearance` diagnostic.) -/
def firstUnsafeBlock (ε : Rat) (b : Build) : Option Nat :=
  (List.range b.length).find? fun k =>
    !(decide (WellFormed (b.take (k + 1))) && solidAnswer ε (b.take (k + 1)))

/-- `KaplaCore.PhysicsEngine.check`, done by the verified engine.

`ok` is true exactly when every step places 1 to `hands` blocks, every block has a physics
pose, and `checkPlan opts` accepts the blocks as a plan of at most `maxBlocks` planks.

If a block has no physics pose, or the build after a block is not shown to stand, the
report has `unstable step block` for the first such block. The engine does not say which
block would fall, so it names the block whose placement went wrong. -/
def coreCheck (opts : PlanOptions) (h : HumanModel) (maxBlocks : Nat) (plan : BuildPlan) :
    PhysicsReport :=
  let n := plan.blockCount
  let stepOf := fun i => (stepOfBlock plan).getD i 0
  let countDiags : List Diagnostic := if n > maxBlocks then [.tooManyBlocks n maxBlocks] else []
  let stepDiags := stepDiagnostics h plan
  match buildOf plan.blocks with
  | none =>
      match turnedBuildOf plan.blocks with
      | some tb =>
          -- Some block is turned by a 15° step that is not a quarter turn (B6): check at the
          -- planned positions only.
          let safe := checkTurnedPlan maxBlocks tb
          let unsafeDiags : List Diagnostic :=
            if safe then [] else
              match firstUnsafeTurned tb with
              | some k => [.unstable (stepOf k) k]
              | none => []
          { ok := opts.allowNominal && stepDiags.isEmpty && safe,
            diagnostics := countDiags ++ stepDiags ++ tOverlapPairs tb ++ unsafeDiags }
      | none =>
          let bad := (plan.blocks.findIdx? fun p => (turnedOf p).isNone).getD 0
          { ok := false, diagnostics := countDiags ++ stepDiags ++ [.unstable (stepOf bad) bad] }
  | some b =>
      let safe := checkPlan opts h.epsRel maxBlocks b
      let unsafeDiags : List Diagnostic :=
        if safe then [] else
          match firstUnsafeBlock h.epsRel b with
          | some k => [.unstable (stepOf k) k]
          | none => []
      let reachDiags : List Diagnostic :=
        ((hardToReach dropGap b).map stepOf).eraseDups.map .unreachable
      { ok := stepDiags.isEmpty && safe, assurance := .robust,
        diagnostics := countDiags ++ stepDiags ++ overlapPairs b ++
          (if opts.clearance then
            clearancePairs h.epsRel b ++ ((tightSlots b).map stepOf).map .tightSlot
          else []) ++
          unsafeDiags ++ reachDiags }

/-- The verified physics engine, for `app/Main.lean` to pass to the planner. It uses the
default `PlanOptions`: clearance on. -/
def physicsEngine : KaplaCore.PhysicsEngine := ⟨coreCheck {}⟩

end KaplaPhysics
