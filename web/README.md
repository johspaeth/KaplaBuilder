# KaplaWeb

Owner: D. Scope: see [docs/WORKSPLIT.md](../docs/WORKSPLIT.md).

- Build: `lake build KaplaWeb`
- Files: `KaplaWeb.lean` (root, imports the rest) and `KaplaWeb/*.lean`.
- May import: `KaplaCore` only. (Today it needs only Lean core.)
- Rules and CI: see the [README](../README.md).

## The website

```sh
lake exe kapla serve        # then open http://localhost:8000
```

Run it from the top folder of the repo. `--port N` picks another port. Only this computer can reach
it. The page needs internet once, to load three.js. The page is `KaplaWeb/Site.lean`, the server is
in `app/Main.lean`. CI does not run browser code, so test a change to the page in a browser.

Saved models are plain files in `models/`, always at height 1. The website does not use git: commit
a file to share it. A file name uses only small letters, digits, `-` and `_`; other files in the
folder are not listed. Saving keeps only the fields of the format, so a `comment` is lost.

Requests between the page and the server. Every answer is JSON, and a failure has `{"error": text}`.

| Request | Sends | Answer |
|---|---|---|
| `GET /` | | The page (HTML) |
| `GET /models` | | `{"models": ["bunny", "egg"]}` |
| `GET /models/NAME` | | The model. 404 if there is none, 422 if the file is not a good model |
| `GET /status` | | `{"key": true or false}`: does the server have an API key? |
| `POST /chat` | `{"text": newest message, "messages": [{"role": "user" or "assistant", "text": text}], "model": model on screen or null}` | `{"reply": text, "model": new model, or null if Claude only answered}`. 503 with no key, 502 if Claude failed |
| `GET /planners` | | `{"planners": [names]}`, from `KaplaPlanner.strategies` |
| `POST /plan` | `{"planner": name, "blocks": block limit, "model": model on screen}` | `{"proposal": ...}`, or null if the planner made none. A proposal has `view` (blocks and steps for the viewer), `score` (the score report), `stands` and `physics` (lines of text). 504 if the planner takes over 60 seconds |
| `POST /models` | `{"name": text, "model": model, "overwrite": true or false}` | `{"name": clean name, "model": saved model}`. 409 with `{"name": clean name}` if the name exists and `overwrite` is not true. 400 if the name or the model is bad |

A planner gives one plan. The server runs physics and the scorer on it again, so "Stands" and "Accepted"
do not depend on what a planner says about itself. A new model on screen clears the proposal.

The conversation lives only in the page. It is gone when the page closes. `kapla serve` reads the key
from `semantics/dev/.env` when it starts, and never sends it to the page.

The server cleans the name ("My Bunny!" becomes `my-bunny`) and checks the model with `decode`. It
answers 403 to a request that does not come from its own page, such as one from another website open
in the same browser.

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
`height`, the numbers are the model's own (0 to 1).
The page never rescales a model to fit. A broken model shows an error and no picture; the rules are
the same as `decode` in `semantics/KaplaSemantics/Json.lean`, and Lean stays the final authority.

The chat (step 7) shows a new model with one call, and the picture changes at once:

```js
KaplaViewer.show(model, 30)   // model is the parsed bubble JSON, 30 is the height
KaplaViewer.showPlan(model, 30, plan)   // also the blocks and the slider; plan has blocks and steps
KaplaViewer.clearPlan()
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
