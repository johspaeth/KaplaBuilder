# KaplaPlanner

Owner: C. Scope: see [docs/WORKSPLIT.md](../docs/WORKSPLIT.md).

- Build: `lake build KaplaPlanner`
- Files: `KaplaPlanner.lean` (root, imports the rest) and `KaplaPlanner/*.lean`.
- May import: `KaplaCore` only.
- Rules and CI: see the [README](../README.md).

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

Claude also chooses the height, and may turn blocks by 0, 30, 45, 60 or 90 degrees
(`allowedTurns`, a subset the planner chose). The physics engine accepts every 15° step
(rule B6); turns other than 0 and 90 are checked at the planned positions only. Each
design is logged to stderr. The prompts are `systemPrompt`, `userPrompt` and `repairPrompt` in
`KaplaPlanner/AiStrategy.lean`. `judge_checked_passed` proves that with the physics check on, a
passing design is physics-ok and within the block budget.
