# KaplaPlanner

Owner: C. Scope: see [docs/WORKSPLIT.md](../docs/WORKSPLIT.md). Design: [DESIGN.md](DESIGN.md)
(§10 says what v1 does).

- Build: `lake build KaplaPlanner`
- Files: `KaplaPlanner.lean` (root, imports the rest) and `KaplaPlanner/*.lean`.
- May import: `KaplaCore` only.
- Rules and CI: see the [README](../README.md).

## Use

`KaplaPlanner.planner : KaplaCore.Planner`. Give it a `PlanRequest` whose target is a bubble
model (`TargetSpec.ofBubbles`), and the two engines. It returns up to `maxCandidates` plans,
each from a different height, best first. Every plan uses at most `N` blocks and passed
`PhysicsEngine.check` (theorem `planPure_sound`). Other kinds of target get no candidates.

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

#eval (KaplaPlanner.planPure { target := .ofBubbles KaplaPlanner.bunnyModel, blocks := 40 }
  KaplaPhysics.physicsEngine semantic).map (·.score.score)
```

Compile it (a `lean_exe`): the search runs a few hundred builds in parallel, which takes
seconds compiled and minutes in the interpreter.
