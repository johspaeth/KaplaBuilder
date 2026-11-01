# KaplaSemantics

Owner: B. May import: `KaplaCore` only. Build: `lake build KaplaSemantics`.

It answers two questions:

1. **What should we build?** In the website's chat, you describe a shape ("an egg", "a bunny
   with long ears"). Claude answers with a **bubble model**: a few ellipsoids, each with a
   label. You see it in 3D and change it by chatting. Claude is not trusted: `decode` checks
   every answer, and a person approves the model.
2. **How close is a plan to the model?** Lay a grid of 1 × 1 × 1 cubes over the model at the
   chosen height. Then compute, exactly with fractions:
   - **Within the target**: every block has at least one cube inside some bubble (`WithinTarget`).
   - **Covers the target**: every bubble big enough to hold a cube has a block cube in it
     (`CoversTarget`).
   - **Likeness score** = covered cubes / (target cubes + cubes that stick out). A cube of a
     bubble counts as covered when a block fills it, or when it lies between two filled cubes
     of the same bubble on a straight line, so the hollow middle of a tower counts as built.
     0 = nothing covered, 1 = exact fit.

   A plan is **accepted** when it has at least one block and passes both checks. The score
   does not decide acceptance: a person does.

## Run it

```sh
make run      # open http://localhost:8000, type "an egg" in the chat (needs an API key)
```

Without a key: open **Gallery → egg**, choose the planner "stand-in tower (test only)", and
press **Generate proposal**. The page shows the score and "Accepted". The score report, from the command line:

```sh
lake build KaplaSemantics
lake env lean --run semantics/dev/Score.lean MODEL.json BLOCKS.json HEIGHT
```

## What is proven

**No theorems yet.** The checks and the score are Lean definitions, computed with `Rat` (no
`Float`), and the app runs those definitions. They are tested with `#guard` at build time
(`Grid.lean`, `Check.lean`, `Score.lean`, `Json.lean`, `Engine.lean`). For example:

```lean
#guard score ballModel 2 [flatBlock] == 1 / 52   -- one block touching a small ball
#guard score ballModel 2 [] == 0                  -- nothing built
#guard scoreOf 8 8 0 == 1                         -- a bubble filled exactly
#guard !checkWithin ballModel 2 [farBlock]        -- a block far away is outside
```

The planned theorems (`targetCells_correct`, `blockCells_correct`, `checkWithin_correct`,
`checkCovers_correct`, `score_in_unit_interval`) are in [APPROACH.md §6](APPROACH.md). When one
is proven, it gets a statement in `specs/KaplaSpecs/Semantics.lean` and an entry in
`comparator/semantics.json`, and this section lists it.

## What is trusted

- `decode` (`Json.lean`): reads a model file. `#guard` tests, including round trips and
  refused files; no proof.
- Claude (`Claude.lean`): not trusted. It only proposes models.

## Examples

| File | What it is |
|---|---|
| `fixtures/targets/egg.json` | one ellipsoid, the smallest model |
| `fixtures/targets/bunny.json` | six bubbles: body, head, two ears, tail, paws |
| `fixtures/plans/one-block.json` | one block, for the score report |
| `../gallery/*.json` | the same models as gallery entries (`kapla gallery-check` tests them) |
| `../web/examples/bubbles/bad-*.json` | broken models (floating, underground, bad width) that the viewer must show as errors |

## Known gaps

- No theorems (above).
- "Within" and "covers" ask for **one** cube per block and per bubble, not more.
- No image input yet; text only.

Design and history: [APPROACH.md](APPROACH.md). Team notes: [ROADMAP.md](ROADMAP.md),
[STEP7.md](STEP7.md).
