# KaplaSemantics: the approach

Owner: person B. Scope: `docs/WORKSPLIT.md` §6B. Status: design reviewed and agreed on
1 Nov 2026, no Lean yet. Open points are collected in §10.

The engine answers two questions. *What should we build?* A bubble model of the target,
proposed by Claude and approved by a person. *How close is a plan to it?* Two yes/no checks
(every block is part of the shape, every part of the shape is built) and a likeness number,
all computed exactly in Lean, with proofs that they mean what the report says.
`docs/DESIGN.md` §5 describes the general idea; this file is the concrete version of it, and
it differs from §5 where it says so.

Words used throughout: a **bubble model** is the target as bubbles (§1); a **placed** model
is a bubble model after the frame (§3) has been applied; **Claude model** means the LLM.
A **cell** is a cube of the grid in §4 (WORKSPLIT calls it a voxel).

## 1. The target is a bubble model

A target is a `BubbleModel`: a name and a list of `Bubble`s. A bubble is an ellipsoid with
its axes parallel to x, y, z. The types are in `core/KaplaCore/Bubble.lean`, shared with the
planner:

```lean
structure Bubble where
  label  : String       -- for people and reports: "head", "left ear", "tower NE"
  tags   : List String  -- hints for the planner, DESIGN.md §5 vocabulary:
                        -- tower, wall, roof:gable, roof:cone, roof:hip, trunk, ...
  center : Q3           -- centre in the unit frame (Q3 = three Rat)
  semi   : Q3           -- semi-axes a, b, c; all > 0

structure BubbleModel where
  name    : String
  bubbles : List Bubble
```

A point is inside a bubble when

    ((x − cx) / a)² + ((y − cy) / b)² + ((z − cz) / c)² ≤ 1.

This is one line of exact `Rat` arithmetic, so `Bubble.contains` is a decidable `Bool`
with no rounding anywhere. Points below the ground (z < 0) are never inside. A bubble with a semi-axis of 0 or less contains nothing. Lean
computes x / 0 as 0, so without this rule it would contain every point.

**The unit frame.** The model is scale-free. Up is +z. The ground is at z = 0, and the highest
point of the model is at z = 1. At least one bubble must reach the ground: a model that floats
is rejected, because its blocks would have to fly. A bubble may go below the ground (a half
sphere with its middle at z = 0 makes a foot), but only the part above counts: `contains` says
no below z = 0, so those cells are in no score. A bubble entirely underground is rejected. x
and y are free; the frame in §3 centres them later. `normalize` only scales, so that the top is
at z = 1 and the ground stays where it is, exactly in `Rat`; `interpret` applies it to
everything Claude returns, and
fixtures are stored normalised. There is no minimum bubble size in the unit model: whether a
bubble is worth having is the person's judgement in the chat (§2); the one mechanical size
rule lives in the scaled model (§4, `CoversTarget`).

**Tags** are advice for the planner, which picks a motif from them (a log-cabin tower for
`tower`, a stepped roof for `roof:gable`, ...). A tag nobody knows is ignored, so the
vocabulary can grow without a contract change. **v1 is axis-aligned.** A yaw rotation per
bubble, as an exact Pythagorean rotation like the blocks have, is a later extension; nothing
below depends on its absence except the "SVG is exact" remark in §2.

A bunny with six bubbles, as Claude would write it:

```json
{
  "name": "bunny",
  "bubbles": [
    {"label": "body",      "tags": ["tower"], "center": [ 0.00,  0.00, 0.28], "semi": [0.30, 0.22, 0.28]},
    {"label": "head",      "tags": ["tower"], "center": [ 0.22,  0.00, 0.60], "semi": [0.17, 0.15, 0.16]},
    {"label": "left ear",  "tags": ["wall"],  "center": [ 0.20, -0.07, 0.86], "semi": [0.05, 0.03, 0.14]},
    {"label": "right ear", "tags": ["wall"],  "center": [ 0.20,  0.07, 0.86], "semi": [0.05, 0.03, 0.14]},
    {"label": "tail",      "tags": [],        "center": [-0.32,  0.00, 0.30], "semi": [0.07, 0.07, 0.07]},
    {"label": "paws",      "tags": ["slab"],  "center": [ 0.30,  0.00, 0.05], "semi": [0.08, 0.14, 0.05]}
  ]
}
```

Body and paws touch z = 0 (0.28 − 0.28 = 0, 0.05 − 0.05 = 0); the ears reach z = 1
(0.86 + 0.14). Decimals in JSON are exact rationals, so decoding loses nothing.

**Why ellipsoids.** An LLM writes them reliably: six numbers and a name per part, no
geometry vocabulary. A person reads them and can say "the ears are too small". The
membership test is one line, so the verified part stays small. Each bubble is a natural
*part*, which gives per-part scores for free ("left ear missing"). And a union of bubbles is
as non-convex as a target needs; a bunny, a castle with four towers and a tree are all unions
of a handful of blobs.

## 2. The interpret loop (untrusted)

**Replaced in part, 1 Nov 2026.** The website is planned in `semantics/STEP7.md`, and that file wins
where they differ. It lives in `app/`, `web/` and `semantics/`, not in `semantics/dev/`. There is no
transcript file and no 3-view SVG page.

Nothing in this section is trusted. It produces a `BubbleModel`; the verified part only ever
sees the model, never the conversation that made it.

- **Call.** Prompt or image → Claude Messages API through `curl` (`IO.Process.output`), key
  from `ANTHROPIC_API_KEY`, as DESIGN.md §6 says. The system prompt asks for JSON only in
  the format above, with the unit-frame convention spelled out, including the ground at z = 0. The Claude model id is one
  constant in `Claude.lean`. Images (B3) go in as base64 image content blocks. *Note for the
  image path:* run the picture through an image segmenter first (Segment Anything, version
  3.1 was recommended to us) and hand Claude the segments, so that each segment becomes a
  candidate bubble instead of Claude guessing parts from the raw picture. Untrusted
  preprocessing, outside Lean; where it lives is decided with the image work.
- **Validate.** The Lean decoder is the validator: JSON schema, every semi-axis > 0, label
  non-empty, at most 32 bubbles. A model that fails to decode is rejected with a message;
  that message goes back to Claude, at most 2 retries. Then `normalize`.
- **Inspect, in a chat page.** For building and testing the engine, a small local web page:
  a text box and the three views (top, front, side) of the current model, redrawn after every
  message. The views are SVG written by `Preview.lean`: an axis-aligned ellipsoid projects
  onto each axis plane as an axis-aligned ellipse with two of its semi-axes, so the picture
  is the exact geometry, and writing the rationals as decimals rounds only the drawing. When
  a plan and a frame are given, the same views draw the blocks as rectangles. The page asks
  for the intended height or block count up front and shows every bubble's size in blocks
  ("tail: 1.1 blocks across"), so a bubble too small to build is dropped or merged *here*,
  by the person. Lean core has no HTTP server, so the page needs a small serving layer under
  `semantics/dev/` that calls the Dev tools below; how exactly is a roadmap item (§10). In
  the finished product the chat lives in the project web UI and the bubbles are drawn as
  ellipsoids in the project's three.js viewer (D's component, §8); the bubble JSON is
  already what such a page consumes.
- **Feedback.** `refine model transcript remark → new model` sends the transcript plus the
  remark and gets a new model, validated the same way. The transcript is a JSON list of
  messages in a file next to the model (`bunny.transcript.json`). Accepted models are copied
  to `semantics/fixtures/targets/<name>.json` and become test inputs.
- **Dev entry points** without touching the shared lakefile: each tool is a module with a
  `main`, run as

      lake build KaplaSemantics
      lake env lean --run semantics/KaplaSemantics/Dev/Preview.lean fixtures/targets/bunny.json out/bunny.svg

  Tools: `Dev/Interpret.lean` (prompt → model + transcript), `Dev/Refine.lean`,
  `Dev/Preview.lean`, `Dev/Score.lean` (target, plan, frame → report JSON). The chat page is
  a thin front on these four. CI builds `Dev/*.lean` like every other module, so they must
  compile with zero warnings.

## 3. Fitting: the scale problem

**Replaced, 1 Nov 2026.** `score` takes a height, not a `Frame`. There is no sideways shift: the
blocks are built to fit the model, and every length of the model is multiplied by the height. If the
blocks are off to one side, the score shows it. `canonicalFrame` and `Frame.lean` are dropped. Read
"frame" below and in §4 to §7 as "height". `Frame` is gone from Core too.

The plan is a pile of real blocks with real sizes. The bubble model is a figurine of height
exactly 1 with no unit attached. Before asking how well the blocks cover the bunny, we have to
decide how big the bunny is and where on the table it stands. That is all §3 does.

**Block units.** Across the whole project every length is in block units: 1 unit = one block
thickness. A block is 15 × 3 × 1 units (length × width × thickness): lying flat it
is a 15 × 3 × 1 brick, on edge 15 × 1 × 3, upright 1 × 3 × 15. Every block dimension is a
whole number and a tower of ten flat blocks is exactly 10 tall. `KaplaCore` uses the same
units, so nothing is converted anywhere. The default grid spacing is 1 unit.

**Frame.** Think of the model as a rubber figurine. Two things may be done to it: blow it up
uniformly by a factor `s : Rat` (s > 0, every direction equally, no stretching), and slide it
across the table by `tx, ty : Rat`. It may not be lifted off the table or pushed into it:
model and plan both stand on the ground, so there is no z offset. A `Frame` is those three
numbers.

    place F b = { b with center := (s·cx + tx, s·cy + ty, s·cz), semi := (s·a, s·b, s·c) }

**The frame is an argument, never a guess.** `score` (§4) takes a `Frame`; there is no code
path that chooses one silently. The reason is the half-built plan: at layer 5 of
an intended 30, a frame fitted to the stump would shrink the bunny to 5 tall and report that
the stump looks like a small bunny. Wrong question. The planner decides once, before placing
anything, how tall the finished bunny will be, builds the frame from that, and passes the
same frame with every call; then the half-built plan is compared with the full-size bunny
and "missing" means "not built yet". This is a contract point, §8 item 3.

**Canonical frame**, for the final report. `canonicalFrame plan model` is a separate
function the orchestrator calls once a plan is finished: `s` = plan height / model height
(the model is 1 tall, so a 30-unit plan gives s = 30 and the bunny becomes 30 units tall, body
about 18 × 13 × 17 units); `tx, ty` make the x/y bounding-box centres of the placed model
and of the plan coincide; an empty plan gets (1, 0, 0). Deterministic, no search.

**The frame travels with the score.** A report says "0.62 at s = 30, offset (7.5, 1.5)", so
anyone can redo the computation and get the same number.

**Not in v1: frame refinement.** A local search over nearby scales and offsets, keeping the
frame with the best verified score, would be sound (every score is exact for its frame, and
the frame used is reported) but it is a planner concern: deciding how big to build is the
planner's scale search (WORKSPLIT §6C). Listed in §10 as a possible later helper.

## 4. Similarity: two checks and a number

**Grid.** Lay a 3D grid of spacing 1 (one block thickness) over the table and look only at
the cell centres, which sit at half-integers (0.5, 1.5, 2.5, ...). A cell is an integer
triple `GridPt = Int × Int × Int` with `(i, j, k).centre = (i + ½, j + ½, k + ½)`.
Everything below is a count of cells; "a cell is inside something" means its centre is.

- **Block cells B.** The cells whose centre lies inside some block. Block containment is
  `lo ≤ t < hi` on each axis (half-open). A flat block on the grid, covering
  [0,15] × [0,3] × [0,1], contains exactly 15 · 3 · 1 = 45 centres, and no centre lies on a
  face. Half-open faces keep every axis-aligned block at exactly 45 cells even when it is
  shifted by a fraction, and two blocks touching face to face never share a cell.
- **Target cells T.** The cells whose centre is inside some placed bubble. `T_b` is the
  same for one bubble b alone.

Both are computed the same way: list the integer ranges of the bounding box (`Rat.floor`,
`Rat.ceil`), keep the cells that pass the exact membership test. There is no tolerance
parameter anywhere: a block touches a bubble when one of its 45 centres is inside, and the
grid itself is the resolution of everything.

**Two acceptance checks.** These are the semantic counterpart of physics' `Valid`. A plan is
accepted when it has at least one block and passes both. The score plays no part: there is no
minimum, and a person gives the final approval.

- **`WithinTarget F m plan`**: every block has at least one of its 45 cells inside some
  bubble. No block floats outside the bunny. (A block partly outside is allowed and costs
  score, below.)
- **`CoversTarget F m plan`**: every bubble that contains at least one grid centre at this
  frame contains at least one block cell. No part of the bunny is left unbuilt. A bubble so
  small at this scale that it contains no centre at all (the tail at s = 8 has radius 0.56,
  less than half a cell) can never be covered; such bubbles are skipped by the rule and
  listed in the report as `tooSmall`. The person can remove them in the UI before accepting
  the design. This changes no result, because they contain no cells. Do not run `normalize`
  after removing one: the model would change size and no longer match the proposal.

"At least one block" closes one gap: if every bubble is too small, both checks pass with no
blocks. Any real block is then fully outside, so such a target has no accepted plan.

Both have decidable checkers (`checkWithin`, `checkCovers`) with the theorem "checker says
yes ⇔ property holds" (§6). There is one call, `score target frame blocks`, for a finished
or partial plan. Its report lists `outside` (blocks fully outside, always a reject) and
`uncovered` (bubbles with no block yet, normal mid-build: at layer 5 the ears are not built
yet), with the similarity number. `ScoreReport.accepted` is worked out from these lists.
Mid-build, the planner's other useful signals are `extra` (is the material placed so far
inside the bubble?) and per-bubble coverage ("paws 90 %, body 20 %, head 0 %"); `missing`
only means something at the end.

**Covered cells and the fill.** Kapla structures are hollow: a log-cabin tower is two
blocks per layer around an empty middle. Comparing block cells against a solid bubble would
call the whole middle "missing", so the empty insides count as built when they are enclosed.
A cell c is **covered** if either

- c is a block cell inside some bubble b, or
- along x, or along y, or along z, there is a block cell of this bubble b on both sides of c
  on the same grid line (c is "between two built cells of b").

The fill is **per bubble**: the two built cells must be inside the *same* bubble. So the
middle of a log-cabin layer fills (left wall, right wall, same tower bubble), the ring of a
round tower and the inside of a four-walled house fill, but the gap between the bunny's
ears does not (left-ear bubble, right-ear bubble), nor the courtyard between two castle
towers. One pass, not iterated: in a Kapla structure an enclosed interior always has walls on
a straight line through it. And because a bubble is convex, every cell on a straight line
between two cells inside it is itself inside it: **covered cells never leave their bubble**
(lemma `fill_subset_target`), which is what makes the score formula below clean.

*Known limitation, accepted:* the rule credits any straight gap between two built cells of
one bubble, however long. A bridge-deck bubble with one block at each end scores the hole
between them as built. Enclosure in two horizontal directions would avoid this at the cost
of a longer definition; revisit if it shows in demos.

**The numbers**, with F = covered cells (all inside T):

| Name | Definition | Meaning for the planner |
|---|---|---|
| `extra` | block cells inside no bubble | "this sticks out" |
| `missing` | `T \ F` | "this part is not built" |
| `score` | `|F| / (|T| + |extra|)`, 0 when the denominator is 0 | the likeness number |
| `perBubble b` | `|F ∩ T_b| / |T_b|` | "left ear 10 % covered" |
| `solid` | `|B ∩ T| / (|T| + |extra|)` | material-only coverage, informational |

In words: covered target over target plus material outside. Covering more of a bubble raises
the numerator; every block cell outside the bubbles adds one to the denominator; material
inside the bubbles beyond what covers them changes nothing (a solid and a hollow tower that
enclose the same cells score the same; block count is the planner's budget problem). The
score is 0 when nothing is covered and 1 exactly when nothing is missing and nothing sticks
out. It is intersection-over-union in disguise: target plus extra is every cell the bunny or
the plan occupies, and F is the plan's overlap with the bunny with enclosed insides credited.

One horizontal slice through a hollow tower compared with a tower bubble (one character per
cell):

```
   . . . o o o o . . .        .  outside the bubble, no block: ignored
   . x # # # # # # x .        o  bubble cell with nothing in it ............ missing
   . o # f f f f # o .        #  block cell inside the bubble ............... covered
   o o # f f f f # o o        f  empty cell between two # of this bubble ... covered (fill)
   o o # f f f f # o o        x  block cell outside the bubble .............. extra
   . o # f f f f # o .
   . x # # # # # # x .
   . . . o o o o . . .
```

T = 20 + 20 + 16 = 56, F = 36, extra = 4, missing = 20, score = 36 / 60 = 0.60 ("coarse").
Without the fill the same tower would score 20 / 60 = 0.33. The `x` cells show a mismatch
built into the bubble model: a square tower in an ellipsoidal bubble always has a little
extra at the corners.

**How it is computed: from the blocks.** The blocks are few and the ellipsoid formula is
the cheap test, so nothing enumerates the target per plan:

```
for every block, for each of its 45 cell centres:          -- 200 blocks → 9000 points
    test the ellipsoid formula against each bubble
    inside some bubble b → covered cell, remembered with b
    inside none         → extra
fill: group the covered cells by bubble and by grid line;
      on each line, the cells between the first and the last covered cell are covered too
score := |covered| / (|T| + extra)
```

`|T|` depends on the target and the frame, not the plan, so it is enumerated once per frame
and reused (it is also what `missing` needs, once, for the final report). The convexity
shortcut makes it cheaper still: if all 8 corners of a block are inside one bubble, all 45
centres are (lemma `corners_in_bubble`), no enumeration needed; only blocks straddling a
surface need the 45 points. The reference definitions in `Score.lean` are written from the
block side too, so the code that runs is the definition a reviewer reads.

A bubble cut by the ground has no dents either, so the fill still stays inside it: a straight
line between two points above the ground stays above the ground.

**Why not a convex hull of the plan.** Targets are not convex (ears, towers), so the hull
would reward empty space; and an exact 3D hull in `Rat` is heavy to write and heavier to
verify. The per-bubble fill is three one-dimensional checks.

**Verdict** from DESIGN.md §5, applied to `score`: ≥ 0.7 good likeness, 0.4–0.7 coarse,
0.15–0.4 abstract, < 0.15 symbolic only. The bands are defaults and can move.

## 5. No verified upper bound

DESIGN.md §5 and the README promise "a proven upper limit shows the best score that N blocks
could reach at all". The argument was a count: a block holds 45 cells, so N blocks cover at
most 45·N target cells. Once the score credits enclosed insides that count says nothing
about the number we report: a hollow tower of 20 blocks has 900 cells of wood and covers
2000. The theorem would prove a true statement about `solid`, a number nobody looks at, and
the explanation it was meant to give is no longer true. So there is **no verified bound**.

What takes its place as the user-facing guarantee is §4: every surviving block is part of
the shape, every part of the shape is built, and the likeness number is computed correctly
(§6). An unverified `suggestScale target N` helper can give the planner a starting height
("don't build a 60-tall bunny from 20 blocks"); a hint needs no proof. The README sentence,
DESIGN.md §5 and the shared interface change accordingly (§8).

## 6. What gets verified

The statements, as they compile against the definitions today. These are for team review before
they go in `specs/KaplaSpecs/Semantics.lean`:

```lean
theorem targetCells_correct (m : BubbleModel) (height : Q) (g : GridPt) :
    g ∈ targetCells m height ↔ ∃ b ∈ m.bubbles, (placeAt height b).contains g.centre = true
theorem blockCells_correct (plan : List Pose) (hrot : ∀ blk ∈ plan, blk.rot.valid = true) (g : GridPt) :
    g ∈ blockCells plan ↔ ∃ blk ∈ plan, blk.contains g.centre = true
theorem checkWithin_correct (m : BubbleModel) (height : Q) (plan : List Pose) :
    checkWithin m height plan = true ↔ WithinTarget m height plan
theorem checkCovers_correct (m : BubbleModel) (height : Q) (plan : List Pose) :
    checkCovers m height plan = true ↔ CoversTarget m height plan
theorem score_in_unit_interval (m : BubbleModel) (height : Q) (plan : List Pose) :
    0 ≤ score m height plan ∧ score m height plan ≤ 1
```

The fill is computed on a bubble's own cells (`coveredOfBubble` filters `bubbleCells`), so covered
cells are inside the bubble by definition and theorem 5 does not need `fill_subset_target`.

Five main theorems. Each is stated once in `specs/KaplaSpecs/Semantics.lean` (unproven
there, human-reviewed) and proved under the same name in `semantics/KaplaSemantics/Proofs/`;
`comparator/semantics.json` ties them together. For each: what it says in words, why it
matters, its **surface** (the definitions a reviewer must read), a concrete **example** with
every hypothesis discharged, and one **bad output** the statement rejects (repo `CLAUDE.md`
§4). Running examples: the bunny of §1; `ball`, one bubble with centre (0, 0, ½) and
semi-axes ½ (with frame s = 2 it is the ball of radius 1 around (0, 0, 1) and contains
exactly the 8 cells with centres (±½, ±½, 1 ± ½); with s = 6, radius 3 around (0, 0, 3), it
contains 136); `flat`, one block covering [0,15] × [0,3] × [0,1].

1. **`targetCells_correct`**: `g ∈ targetCells F m ↔ ∃ b ∈ m.bubbles, (place F b).contains g.centre`.
   The listed target cells are exactly the cells whose centre passes the ellipsoid test.
   Why: the program lists the cells of each bounding box with `floor`/`ceil`; this says no
   cell at a bubble's edge is lost or invented.
   Surface: `GridPt.centre`, `Bubble.contains`, `place`, `Frame`.
   Example: `#guard (targetCells ⟨2, 0, 0⟩ ball).length == 8`; `(-1, -1, 0)` is in the list.
   Rejects: the empty list; any list containing (5, 5, 5).
2. **`blockCells_correct`**: `g ∈ blockCells plan ↔ ∃ blk ∈ plan, blk.contains g.centre`.
   Same for blocks, against `Pose.contains` from `KaplaCore`. It holds when every block has a real
   turn (cos² + sin² = 1, ruled 1 Nov 2026). With made-up turn numbers it is false.
   Surface: `Pose.contains`, `GridPt.centre`.
   Example: `#guard (blockCells [flat]).length == 45`.
   Rejects: a list of 44 cells.
3. **`checkWithin_correct`**: `checkWithin F m plan = true ↔ WithinTarget F m plan`.
   The checker says yes exactly when every block has a cell inside some bubble.
   Why: this is the rejection rule; a wrong `true` lets a floating block through, a wrong
   `false` throws away a good plan.
   Surface: `WithinTarget`, `blockCells`, `Bubble.contains`, `place`.
   Example: `flat` against `ball` at s = 2 passes (the cell (0, 0, 0) is inside); `flat`
   moved to x ∈ [20, 35] fails.
   Rejects: a checker that tests only block centres (it says no to a long block whose end is
   inside and whose centre is out).
4. **`checkCovers_correct`**: `checkCovers F m plan = true ↔ CoversTarget F m plan`.
   The checker says yes exactly when every bubble with at least one grid centre at this
   frame contains a block cell.
   Why: this is the other rejection rule; it is also where "too small at this scale" is
   decided.
   Surface: `CoversTarget`, `targetCells` per bubble, `blockCells`.
   Example: the bunny at s = 30 with one block in each of its six bubbles passes; remove the
   tail's block and it fails.
   Rejects: a checker that looks only at the bubble's centre cell (a hollow tower has no
   block at its centre and would be wrongly rejected).
5. **`score_in_unit_interval`**: `0 ≤ score F m plan ∧ score F m plan ≤ 1`, and the same
   for every `perBubble` value.
   Why: the verdict bands and the web badge assume a ratio.
   Surface: `score`, `covered`, `targetCells`, `blockCells`, `extra`.
   Example: `flat` against `ball` at s = 2: one block cell inside the ball, nothing to fill,
   extra = 44, |T| = 8, so `score = 1 / 52`, `missing = 7`, verdict symbolic (and both checks
   pass: acceptance is not likeness).
   Rejects: block cells over target cells, `45 / 8` on this example.

**The one geometric lemma.** Theorem 5 needs `fill_subset_target`: a cell between two cells
of bubble b on an axis-parallel line is inside b. Theorem 3's fast path needs
`corners_in_bubble`: if all 8 corners of an axis-aligned block are inside b, every point of
the block is. Both are convexity, and both reduce to one one-axis fact, provable with the
`Rat` lemmas core has or a short local lemma: for `lo ≤ t ≤ hi`,
`(t − c)² ≤ max ((lo − c)², (hi − c)²)` (case split on the sign of `t − c`, then squaring is
monotone on non-negatives). The membership expression is a sum of three such terms, one per
axis, so its value anywhere between two inside points (or anywhere in a box whose corners
are inside) is at most the value at an end point or a corner, which is ≤ 1. For yaw-rotated
blocks the corner lemma needs convex-combination algebra instead; not needed for v1.

**Internal lemmas**, no spec entry: `fill_subset_target`, `corners_in_bubble`,
`decode_wellFormed` (whatever decodes has positive semi-axes and at most 32 bubbles), and the
`perBubble` bounds if they are not folded into theorem 5.

**Tested, not proven.** JSON round trip `decode (encode m) = some m`: `#guard` on every
fixture plus one model with a non-decimal rational such as 1/3, which forces the encoder to
write fractions exactly. This follows the project convention (WORKSPLIT §3: codecs "with
round-trip tests"); a codec bug is a wrong input, not a wrong theorem, and the chat preview
is drawn from the decoded model, so the person approves the same value the scorer uses.

**Dropped from the first draft, and why.** `gate_sound` and `extra_eq_zero_iff_gate`: the
planner's gate *is* "extra is empty", there is nothing to relate. `iou_le_bound`: §5.
`scoreImpl_eq_spec`: there is one definition, written from the block side, and no second
implementation. `covered_mono` (adding blocks never reduces coverage) and shift invariance
(moving plan and frame together by whole cells changes nothing): true and pleasant, no
guarantee depends on them; optional if time allows.

The examples in proofs are tiny on purpose: `decide` runs in the kernel and `native_decide`
is forbidden. Big inputs go in `#guard`, which is a build-time test, not a proof.

## 7. Module layout under `semantics/KaplaSemantics/`

| File | Contents |
|---|---|
| `Bubble.lean` | `normalize` (the types, `contains`, `wellFormed`, `Frame` and `place` are in `KaplaCore.Bubble`) |
| `Json.lean` | `encode` / `decode` for models, frames and reports; exact `Rat` codec |
| `Grid.lean` | `GridPt`, `centre`, `targetCells`, `blockCells` (blocks are `Pose` from `KaplaCore`) |
| `Score.lean` | `covered` (with the per-bubble fill), `extra`, `missing`, `score`, `solid`, `perBubble`; block-side definitions that are also the implementation |
| `Check.lean` | `WithinTarget`, `CoversTarget`, `checkWithin`, `checkCovers`, the "too small" list |
| `Engine.lean` | the `SemanticEngine` implementation (`interpret`, `refine`, `score`); **the only file that uses the engine and report types** (`SemanticEngine`, `TargetSpec`, `ScoreReport`). Any file may use `Q3`, `Bubble`, `BubbleModel` and `Pose`. Also hosts `componentName`, which `app/Main.lean` prints |
| `Claude.lean` | Messages API client over `curl`, prompt templates, retries |
| `Preview.lean` | 3-view SVG of a model, optionally with a plan |
| `semantics/dev/*.lean` | the CLI tools of §2, one `main` each, outside the library so they do not clash with `kapla` in `lake check`. `dev/Score.lean` runs `runScore`: model file, blocks file, height |
| `Proofs/*.lean` | one file per spec file, theorem names identical to the specs |

Plus `semantics/fixtures/{targets,plans,score_expected}/` (JSON), and `semantics/dev/`
for shell helpers (§9) and the chat page's serving layer (§2). `Basic.lean` is the current
placeholder and goes away when `Engine.lean` takes over `componentName`. The root
`semantics/KaplaSemantics.lean` imports every module including `Proofs`, so a spec file
imports the definition modules it needs (`KaplaSemantics.Score`, `KaplaSemantics.Check`,
...) and never the root.

## 8. The contract in KaplaCore

Settled and merged in PR #17 (1 Nov 2026). Rulings:

1. **Bubbles in Core.** `Bubble`, `BubbleModel`, `contains`, `wellFormed`, `Frame`, `place`,
   `Frame.ofHeight` and the egg are in `core/KaplaCore/Bubble.lean`, so the planner and the
   engine share one meaning of "inside". `normalize` and the JSON codec stay here.
2. **Targets.** `Shape.bubbles` is the bubble shape; the older shapes stay for now.
   `TargetSpec.ofBubbles` makes one part per bubble. The planner cannot import the codec, so
   it tests with `TargetSpec.egg`. In real runs it gets its target in the `PlanRequest`.
3. **`SemanticEngine`.** `interpret`, `refine : TargetSpec → String → IO TargetSpec`, and
   `score : TargetSpec → Frame → List Pose → ScoreReport`. `bound` and `Bound` are gone (§5).
   There is no separate `check`. The transcript stays on my side (a file next to the model).
4. **`ScoreReport`** adds `frame`, `blockCount`, `outside` (block positions), `uncovered` and
   `tooSmall` (bubble labels), next to `score`, `perPart`, `missing` and `extra`. `iou` stays
   only because `specs/KaplaSpecs/Planner.lean` sets it. `solid` is not in the report.
   `accepted` and `verdict` are functions of the report. Bubbles are named by label, so
   step 7 must reject duplicate labels.
5. **Exact `Rat` in JSON.** A JSON number when the denominator divides a power of ten (every
   decimal Claude writes), else the string `"p/q"`; the decoder accepts both. This stays in
   `Json.lean`, as Core has no JSON code.
6. **Blocks.** Block cells come from `Pose.contains` in Core, with half-open faces, so an
   axis-aligned block has exactly 45 cells at any offset.

Still open:

- **The planner does not filter on `accepted`.** It can return plans these rules reject. On
  the egg with 60 blocks, all three plans it returns have blocks fully outside (its towers
  have a fixed width). `planPure_sound` promises nothing about acceptance yet.
- **The planner chooses a sideways shift** (`frameFor` in `planner/KaplaPlanner/Search.lean`),
  so the egg it builds is not around x = 0, y = 0. This is allowed; the note in `egg.json` says so.
- **Fixtures.** Ask D for the fixture set (WORKSPLIT §5). Until the shared `fixtures/` exists,
  mine live under `semantics/fixtures/`.
- **The end-user experience is a chat box plus the 3D viewer,** built with D on top of
  `interpret` and `refine`. The dev chat page of §2 is my stand-in until then.
- **Batteries** is allowed by the rules but is not in `lake-manifest.json`. I plan to need only
  Lean core; if a `Rat` lemma is missing I prove it locally.

## 9. Dev workflow

- Branch `feature-semantics` only. Never commit to `main`; merge by PR when **CI OK** is
  green (`.github/pull_request_template.md` has the checklist).
- Change files under `semantics/` only. For `core/`, `specs/`, `comparator/`: write the
  proposed text, flag it, let the team review.
- `lake build KaplaSemantics` after every module edit. `make check` before every commit
  (imports, forbidden words, `lake build --fail-level=warning`, `lake build KaplaSpecs`).
  `lake check` and `lake comparator` are Linux-only: they run in CI, and locally in the
  Docker container through `semantics/dev/ci.sh`.
- One `lake` process at a time. No parallel builds, no lake next to a REPL.
- The forbidden words apply to comments and docstrings too. Write "unfinished proof", not
  the tactic's name, when you talk about one.
- Unfinished proofs may live in WIP commits on the branch, never in a PR. `make check` fails
  locally until they are done; that is the point.

**Pre-commit guard.** `semantics/dev/pre-commit`:

```bash
#!/usr/bin/env bash
# On feature-semantics, refuse to commit anything outside semantics/.
[[ "$(git branch --show-current)" == "feature-semantics" ]] || exit 0
bad=$(git diff --cached --name-only | grep -v '^semantics/' || true)
if [[ -n "$bad" ]]; then
  echo "pre-commit: staged paths outside semantics/:"; echo "$bad"; exit 1
fi
```

`semantics/dev/setup.sh` copies it to `.git/hooks/pre-commit` and makes it executable.
Git hooks are not versioned, so every clone runs `semantics/dev/setup.sh` once.

## 10. Milestones and open questions

Mapped onto WORKSPLIT §7 (B1–B3 are the three Semantics bars in the Gantt chart). The
project roadmap itself (steps, order, the first simple website with chat and visualization)
is structured separately; this is only my track.

| | Deliverable | Verified | Due |
|---|---|---|---|
| **B1** | bubble model + JSON, grid, `targetCells`, `blockCells`, covered/fill, score, checkers, `canonicalFrame`, `Dev/Score`, first fixtures | theorems 1–4 | before I1, 20 Nov |
| **B2** | chat page, Claude client, `normalize`, preview SVG, `refine`, `Dev/Interpret` + `Dev/Preview`, `SemanticEngine` wired in `Engine.lean` | — | ~1 Dec |
| **B3** | image input, silhouette IoU against the input mask, per-bubble scores in the report, narration text | theorem 5 if not done in B1 | before I2, 18 Dec |

Yaw-rotated bubbles and the optional lemmas of §6 come after I2 if there is time.

**Open questions**

1. **Serving the website.** Settled: Lean's `Std.Http.Server` works, in `kapla serve`. See `STEP7.md`.
2. **Silhouette for images** (B3): projection along which axis, mask resolution, and whether
   the mask arrives through `TargetSpec.silhouette` as pixels or as a polygon.
3. **Frame refinement.** Worth adding as an untrusted helper the planner can call, or not at
   all (§3).
4. **Defaults:** bubble count limit 32, retries 2, verdict bands. Change if the fixtures say
   so.
5. **Performance** is not expected to matter (§4: 9000 points through a formula per plan),
   but `|T|` per frame should be cached, and if the planner scores thousands of candidates per
   second the per-block check (`extra` for one block) is the inner-loop signal.
