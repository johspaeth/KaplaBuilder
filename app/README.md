# kapla (CLI)

Owner: D. The only place where the real engines meet. May import every component.

- Build: `lake build kapla`
- Run: `make run` (or `lake exe kapla`)

## Commands

- `kapla check BLUEPRINT.json [--max N] [--no-clearance]`: runs the verified physics engine
  (`KaplaPhysics.coreCheck`) on the blueprint, with the default builder and at most `N`
  blocks (default 200). Prints the problems it finds. Exit code 0 when the plan is `ok`.
- `kapla view BLUEPRINT.json [--out DIR] [--no-clearance]`: writes the page
  (`web/README.md`), with the physics result in its notes.
- `kapla serve [--port N]`: starts the website on this computer only, at
  `http://localhost:8000`. Run it from the top folder of the repo. The API key comes from `ANTHROPIC_API_KEY`
  (see below). With no key at all the chat says so and the rest still works. See `web/README.md`.
- `kapla gallery-check`: reads every file in `gallery/` and lists the ones that are not good
  entries (format: `web/README.md`). Exit code 0 when all are good. CI and `make check` run it.

## The API key

The key lives in one file: `.env` in the top folder of the repo (copy `.env.example`; git ignores
`.env`). Only `main` in `Main.lean` reads it. It puts the key into `ANTHROPIC_API_KEY` and starts
`kapla` again once, so every command (`serve`, and `plan` with the `ai` strategies) gets it from the
environment. With no `.env`, `ANTHROPIC_API_KEY` from the shell is used. The file wins when both are
set.

The blueprint is read twice: as `Float`s for drawing (KaplaWeb), and with exact fractions for
the physics engine. By default it also refuses a plan when a 3.9 mm error could close a gap
between two blocks (a near miss), or when a block goes into a slot exactly its own width
between two blocks placed before it. `--no-clearance` turns these two checks off. Blocks that
touch in the plan, like the walls in `web/examples/`, are fine either way.

```sh
lake exe kapla check web/examples/house.json
```
