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
- `kapla plan [N] [target ...] [--no-clearance]`: the planner demo (`planner/README.md`).
  Fills the bubble test targets with at most `N` blocks (default 60) and writes blueprints
  to `out/planner-demo/`. The verified physics engine judges every block the search tries
  (`physicsStands`, fast solver only) and then the whole plan, step by step (`coreCheck`).

The blueprint is read twice: as `Float`s for drawing (KaplaWeb), and with exact fractions for
the physics engine. `--no-clearance` allows blocks placed side by side and touching; without
it, a plan is refused if a 2 mm error could push two blocks into each other. Both examples in
`web/examples/` build walls from touching blocks, so they pass only with `--no-clearance`.

```sh
lake exe kapla check web/examples/house.json --no-clearance
```
