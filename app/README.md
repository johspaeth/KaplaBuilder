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

The blueprint is read twice: as `Float`s for drawing (KaplaWeb), and with exact fractions for
the physics engine. `--no-clearance` allows blocks placed side by side and touching; without
it, a plan is refused if a 2 mm error could push two blocks into each other. Both examples in
`web/examples/` build walls from touching blocks, so they pass only with `--no-clearance`.

```sh
lake exe kapla check web/examples/house.json --no-clearance
```
