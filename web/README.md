# KaplaWeb

Owner: D. Scope: see [docs/WORKSPLIT.md](../docs/WORKSPLIT.md).

- Build: `lake build KaplaWeb`
- Files: `KaplaWeb.lean` (root, imports the rest) and `KaplaWeb/*.lean`.
- May import: `KaplaCore` only. (Today it needs only Lean core.)
- Rules and CI: see the [README](../README.md).

## Show a blueprint

```sh
lake exe kapla view web/examples/house.json --out out/house
open out/house/index.html
```

The page has a 3D view with a step slider (drag to turn, scroll to zoom), one card per step
with a top-down plan of the layer (new block in orange, blocks below shaded), and a
"Print booklet" button. It is a single HTML file; only three.js comes from a CDN, and the
step cards work without it.

## Blueprint format

```json
{
  "title": "House",                      // optional
  "subtitle": "60 blocks",               // optional
  "notes": ["stands after every step"],  // optional, shown under the title
  "plan": {                              // or put "steps" at the top level
    "steps": [
      { "blocks": [
          { "up": "flat",                // "flat" | "edge" | "upright"
            "rot": { "c": 1, "s": 0 },   // cos and sin of the turn about the vertical axis
            "center": [0, 0, "1/2"] }    // numbers or exact fractions as strings
        ],
        "phase": "layer 1",              // optional, shown on the card
        "grip": "longSides",             // optional: longSides | shortEnds | topEnd
        "approach": "fromAbove" }        // optional: fromAbove | slideXPos | ...
    ]
  }
}
```

A block is 15 × 3 × 1 (one unit is one block thickness). `flat` lies on its wide face, `edge` on its long narrow
face, `upright` stands on its end. `center` is the centre of the block, so a flat block on
the ground has `z = 1/2`. Steps are shown in order; a step with two blocks is marked
"two hands". Other fields are ignored.

`web/examples/` has a house (27 blocks) and a duck (15 blocks).
