# kapla (CLI)

Owner: D. The only place where the real engines meet. May import every component.

- Build: `lake build kapla`
- Run: `make run` (or `lake exe kapla`)

## Commands

- `kapla check BLUEPRINT.json [--max N] [--clearance]`: runs the verified physics engine
  (`KaplaPhysics.coreCheck`) on the blueprint, with the default builder and at most `N`
  blocks (default 200). Prints the problems it finds. Exit code 0 when the plan is `ok`.
- `kapla view BLUEPRINT.json [--out DIR] [--clearance]`: writes the page
  (`web/README.md`), with the physics result in its notes.
- `kapla serve [--port N]`: starts the website on this computer only, at
  `http://localhost:8000`. Run it from the top folder of the repo. It reads the API key from `semantics/dev/.env` when it
  starts; with no key the chat says so and the rest still works. See `web/README.md`.

The blueprint is read twice: as `Float`s for drawing (KaplaWeb), and with exact fractions for
the physics engine. `--clearance` also refuses a plan when a 3.9 mm error could close a gap
between two blocks (a near miss). Blocks that touch in the plan, like the walls in
`web/examples/`, are fine with or without it.

```sh
lake exe kapla check web/examples/house.json --clearance
```
