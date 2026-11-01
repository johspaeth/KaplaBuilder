# KaplaPlanner

Owner: C. Scope: see [docs/WORKSPLIT.md](../docs/WORKSPLIT.md). Design: [DESIGN.md](DESIGN.md)
(§10 says what v1 does, §11 is v2, §11.13 what was built).

- Build: `lake build KaplaPlanner`
- Files: `KaplaPlanner.lean` (root, imports the rest) and `KaplaPlanner/*.lean`.
- May import: `KaplaCore` only.
- Rules and CI: see the [README](../README.md).

## Use

`KaplaPlanner.planner : KaplaCore.Planner`. Give it a `PlanRequest` whose target is a bubble
model (`TargetSpec.ofBubbles`), and the two engines. It searches for **at most 30 seconds**
(branch and cut over courses at several heights, then improving the best plans) and returns up
to `maxCandidates` plans, from different heights first, best first. Every plan uses at most `N`
blocks and passed `PhysicsEngine.check` (theorem `candidatesOf_sound`). Other kinds of target
get no candidates. `plannerWith cfg` sets the time limit and other settings (`PlannerConfig`).
`planPure` is v1, a pure function without a time limit.

The planner sends 2 tiny plans to the physics engine first, to learn whether upright blocks
may stand on or carry other blocks; today they may not, so they are used only on the ground.

`KaplaPlanner.blueprintJson model candidate` writes a candidate in the blueprint format of
`web/README.md`, for `kapla view`.

The planner is not yet called by the `kapla` CLI; that is a change in `app/` (owner D).

## Trying it with the real engines

The planner may not import the physics engine or the scorer, so a test with the real engines
needs a program outside this folder that imports `KaplaPlanner`, `KaplaPhysics` and
`KaplaSemantics`, for example:

```lean
def semantic : KaplaCore.SemanticEngine :=
  { interpret := fun _ => pure default, refine := fun t _ => pure t
    score := fun t f ps => match t.shape with
      | .bubbles m => KaplaSemantics.scoreReport m f.scale ps
      | _ => default }

def main : IO Unit := do
  let cs ← KaplaPlanner.planner.plan { target := .ofBubbles KaplaPlanner.bunnyModel, blocks := 40 }
    KaplaPhysics.physicsEngine semantic
  IO.println (cs.map (·.score.score))
```

Compile it (a `lean_exe`): the search runs thousands of builds in parallel; in the interpreter
it gets far less done in its 30 seconds.
