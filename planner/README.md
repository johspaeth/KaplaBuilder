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

It is also the strategy `layered-branch-and-bound` (see Strategies below), so `kapla plan` and
the website can run it.

## Trying it with the real engines

```
lake exe kapla plan --strategy layered-branch-and-bound --blocks 40 --target web/examples/bubbles/bunny.json --out bunny.json
lake exe kapla view bunny.json
```

Use the compiled `kapla`: the search runs thousands of builds in parallel; in the interpreter
it gets far less done in its 30 seconds.

## Demos

`KaplaPlanner/Demos.lean` holds the problems the planner is developed against: the ball,
bunny, egg and foot models, each with 10, 40 and 100 blocks (`demos`). Where PR #31's planner
was run on a problem, its result (blocks used, height) is kept as a bar to reach.

- `checkDemo req physics semantic candidates` lists what is wrong with an answer: no
  candidate, too many candidates, too many blocks, a plan physics does not accept, a plan the
  scorer does not accept, or a stored physics report that the engine does not confirm.
- `runDemos planner physics semantic` runs a planner on every demo and prints one line each.

## Strategies

Choose one with `lake exe kapla plan --strategy NAME [--effort LEVEL] [--blocks N] [--target MODEL.json] [--out BLUEPRINT.json]`.

| Name | What it does |
|---|---|
| `empty` | Proposes nothing. |
| `layered-branch-and-bound` | The search of [DESIGN.md](DESIGN.md) §3: course-by-course builds at several heights, branch-and-bound over courses, then local improvement of the best plan. At most 30 seconds, no calls to Claude. Every plan uses at most `N` blocks and passed physics (`candidatesOf_sound`). |
| `ai` | Asks Claude (`claude-opus-5-5`) for 3 designs at the same time. A design passes when the semantic engine accepts it and the verified physics engine says it is safe to build. If none passes, it asks 3 more times, each time with one failed design and its problems. It returns the passing design with the best likeness score, or nothing. |
| `ai-unchecked` | The same, but without the physics check: it trusts Claude. Its candidates have `physics.ok = false` with no diagnostics, which means "not checked". |

The `ai` strategies need `ANTHROPIC_API_KEY` and `curl`. `--effort low|medium|high` (default
`high`; on the website, the "Reasoning" button) sets how much Claude thinks before it answers.
Measured on 2026-11-01 (one call, and how many designs passed the checks):

| Effort | Egg, 20 blocks | Bunny, 40 blocks |
|---|---|---|
| `low` | 4–17 s, 1 of 3 | 25–47 s, 0 of 6 |
| `medium` | 49–80 s, 2 of 3 | 86–110 s, 1 of 3 |
| `high` | 70–111 s, 4 of 4 | 249–469 s, 2 of 3 |

Claude also chooses the height, and may turn blocks by 0, 30, 45, 60 or 90 degrees (rule B6). Each
design is logged to stderr. The prompts are `systemPrompt`, `userPrompt` and `repairPrompt` in
`KaplaPlanner/AiStrategy.lean`. `judge_checked_passed` proves that with the physics check on, a
passing design is physics-ok and within the block budget.
