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

Six theorems. Statements: `specs/KaplaSpecs/Semantics.lean`. Proofs, under the same names:
`KaplaSemantics/Proofs/Semantics.lean`. `comparator/semantics.json` checks that the proofs prove
exactly the statements, with only the standard axioms. The theorems are about the definitions
the app runs, not about a copy. Next to the proofs: an example for each where every condition
holds, and wrong answers each one rules out.

| Theorem | In plain words |
|---|---|
| `targetCells_correct` | The target's cubes are exactly the cubes whose middle is inside some bubble. |
| `blockCells_correct` | The plan's cubes are exactly the cubes whose middle is inside some block, when every block's turn is a real rotation (cos² + sin² = 1). |
| `checkWithin_correct` | With real turns: the checker says yes exactly when every block shares a cube with some bubble (`WithinTarget`). |
| `checkCovers_correct` | With real turns: the checker says yes exactly when every bubble with cubes shares a cube with some block (`CoversTarget`). |
| `score_in_unit_interval` | The score is from 0 to 1. |
| `perBubble_in_unit_interval` | The share of one bubble that is covered is from 0 to 1. |

The score's formula is its definition (`score`, `Score.lean`): there is no separate reference
to compare it with. Build-time tests show what it computes:

```lean
#guard score ballModel 2 [flatBlock] == 1 / 52   -- one block touching a small ball
#guard score ballModel 2 [] == 0                  -- nothing built
#guard scoreOf 8 8 0 == 1                         -- a bubble filled exactly
#guard !checkWithin ballModel 2 [farBlock]        -- a block far away is outside
```

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

- `blockCells_correct`, `checkWithin_correct` and `checkCovers_correct` need real turns.
  `decodeBlocks` refuses other turns, but the blueprint readers in `app/` and `web/` do not
  check them.
- "Within" and "covers" ask for **one** cube per block and per bubble, not more.
- No image input yet; text only.

Design and history: [APPROACH.md](APPROACH.md). Team notes: [ROADMAP.md](ROADMAP.md),
[STEP7.md](STEP7.md).
