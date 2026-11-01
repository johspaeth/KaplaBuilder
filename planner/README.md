# KaplaPlanner

Owner: C. Scope: see [docs/WORKSPLIT.md](../docs/WORKSPLIT.md). How it works:
[DESIGN.md](DESIGN.md) (§3 is the algorithm).

- Build: `lake build KaplaPlanner`
- Files: `KaplaPlanner.lean` (root, imports the rest) and `KaplaPlanner/*.lean`.
- May import: `KaplaCore` only.
- Rules and CI: see the [README](../README.md).

## Use

`KaplaPlanner.planner : KaplaCore.Planner`. Give it a `PlanRequest` (`TargetSpec.ofBubbles`)
and the two engines. It searches for **at most 30 seconds** and returns up to
`maxCandidates` plans, from different heights first, best first. Every plan uses at most `N`
blocks and passed `PhysicsEngine.check` (theorem `candidatesOf_sound`).

- `plannerWith cfg` sets the time limit and other settings (`PlannerConfig`).
- `planPure` runs only the greedy sweep with a check-and-repair step, as a pure function with
  no time limit. The tests use it.
- `blueprintJson model candidate` writes a candidate in the blueprint format of
  `web/README.md`, for `kapla view`.

The `kapla` CLI does not call the planner yet; that is a change in `app/` (owner D).

## Trying it with the real engines

The planner may not import the physics engine or the scorer, so a test with the real engines
needs a program outside this folder that imports `KaplaPlanner`, `KaplaPhysics` and
`KaplaSemantics`, for example:

```lean
def semantic : KaplaCore.SemanticEngine :=
  { interpret := fun _ => pure default, refine := fun t _ => pure t
    score := fun t h ps => KaplaSemantics.scoreReport t.model h ps }

def main : IO Unit := do
  let cs ← KaplaPlanner.planner.plan { target := .ofBubbles KaplaPlanner.bunnyModel, blocks := 40 }
    KaplaPhysics.physicsEngine semantic
  IO.println (cs.map (·.score.score))
```

Compile it (a `lean_exe`): the search runs thousands of builds in parallel; in the interpreter
it gets far less done in its 30 seconds.
