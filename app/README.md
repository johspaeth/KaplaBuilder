# kapla (CLI)

Owner: D. The only place where the real engines meet. May import every component.

- Build: `lake build kapla`
- Run the website: `make run` (same as `lake exe kapla serve`). `lake exe kapla` with no
  command only lists the components.

## Commands

This list is the one home for the CLI; other docs link here. The source of truth is the
module comment and `main` in `app/Main.lean`.

| Command | What it does | Exit code |
|---|---|---|
| `kapla check BLUEPRINT.json [--max N]` | Runs the verified physics engine (`KaplaPhysics.coreCheck`) on the blueprint, with the default builder and at most `N` blocks (default 200). Prints what it finds. | 0 when the plan is `ok`, 1 when not |
| `kapla view BLUEPRINT.json [--out DIR]` | Writes `DIR/index.html` (default `out/`): 3D view, step cards, and the physics result in the notes. Format: `web/README.md`. | 0 |
| `kapla plan [--blocks N] [--strategy NAME] [--effort LEVEL] [--target MODEL.json] [--out BLUEPRINT.json]` | Runs one planner strategy (`empty` by default, `ai`, `ai-unchecked`) on a bubble model (default: the egg). Then it runs the physics engine and the scorer **again** on each candidate, so what it prints never comes from the planner's own report. `--out` writes a blueprint for `kapla view`. `ai` and `ai-unchecked` ask Claude and need a key; `--effort` is `low`, `medium` or `high` (default `high`). | 0 |
| `kapla serve [--port N]` | Starts the website on this computer only, default port 8000. Run it from the top folder of the repo. | – |
| `kapla gallery-check` | Reads every file in `gallery/` and lists the ones that are not good entries. CI and `make check` run it. | 0 when all are good |

Flags for `check`, `view`, `plan` and `serve`:

- `--no-clearance`: turns off two checks that are on by default: a 3.9 mm error must never
  close a gap between two blocks, and no block goes into a slot exactly its own width.
  Blocks that touch face to face in the plan, like the walls in `web/examples/`, are fine
  either way.
- `--robust-only`: refuses plans with turned blocks (15° steps that are not quarter turns).
  Without it, such a plan can be `ok`, but only at the planned positions: the notes say so.

`serve` and the `ai` planners need an API key (below). With no key, the chat says so and the
rest of the site works.

## The API key

The key lives in one file: `.env` in the top folder of the repo (copy `.env.example`; git ignores
`.env`). Only `main` in `Main.lean` reads it. It puts the key into `ANTHROPIC_API_KEY` and starts
`kapla` again once, so every command (`serve`, and `plan` with the `ai` strategies) gets it from the
environment. With no `.env`, `ANTHROPIC_API_KEY` from the shell is used. The file wins when both are
set.

The blueprint is read twice: as `Float`s for drawing (KaplaWeb), and with exact fractions for
the physics engine (`readBuildPlan`, listed as trusted in the top README).

## Examples

```sh
lake exe kapla check web/examples/house.json
#   web/examples/house.json: 27 steps, 27 blocks
#     Physics (verified): well-formed and solid after every block, for 3.9 mm placement errors
lake exe kapla check web/examples/spiral.json        # turned blocks: ok, but "nominal"
#     Physics (verified): well-formed and stands after every block, at the planned positions only (...)
lake exe kapla check web/examples/duck.json --max 10   # exit 1
#     Physics: not shown to be safe to build
#     uses 15 blocks, at most 10 allowed
lake exe kapla view web/examples/spiral.json --out out/spiral   # then open out/spiral/index.html
lake exe kapla gallery-check
#   gallery/bunny.json: ok
#   gallery/egg.json: ok
```

(Output checked on `main` at `488d22e`.)
