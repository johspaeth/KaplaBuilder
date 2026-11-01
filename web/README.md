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

## Show a bubble model

```sh
web/serve-bubbles.sh        # then open the address it prints
```

Open `http://localhost:8000/?bubbles=egg.json&height=30`. Drag to turn, scroll to zoom. The file
stays at height 1; `height` only sets the numbers on the axes and the sizes in the list. With no
`height`, the numbers are the model's own (0 to 1). `shiftX` and `shiftY` move the model sideways.
The page never rescales a model to fit. A broken model shows an error and no picture; the rules are
the same as `decode` in `semantics/KaplaSemantics/Json.lean`, and Lean stays the final authority.

The chat (step 7) shows a new model with one call, and the picture changes at once:

```js
KaplaViewer.show(model, 30)   // model is the parsed bubble JSON, 30 is the height
```

The served folder holds `semantics/fixtures/targets/` and `web/examples/bubbles/` (`foot.json` is a
half sphere, `bunny.json` has six bubbles, `bad-*.json` must show an error).

## Blueprint format

```json
{
  "title": "House",                      // optional
  "subtitle": "60 blocks",               // optional
  "notes": ["stands after every step"],  // optional, shown under the title
  "bubbles": [                           // optional: the target, drawn see-through
    { "label": "head", "center": [0, 0, 20], "semi": [5, 5, 5] }  // semi = half-widths
  ],
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
the ground has `z = 1/2`. Bubbles are ellipsoids with axes along x, y and z, in the same units, cut off at the ground;
the "Hide bubbles" button turns them off and on. Steps are shown in order; a step with two blocks is marked
"two hands". Other fields are ignored.

`web/examples/` has a house (27 blocks) and a duck (15 blocks).
