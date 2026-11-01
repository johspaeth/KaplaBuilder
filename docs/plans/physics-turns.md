# Plan: turned blocks (30°, 45°, 60°) in the physics engine

Status: implemented. Owner of the change: A (physics), with spec review by all.

**What the implementation does differently from this plan:**
- `turnedTower r n` (E19) turns the **whole** square tower by one allowed turn `r`,
  instead of turning each level 45° against the one below. Its proof follows from
  `squareTower_safe` by turning (`TurnProofs.lean`), for errors with
  `ε (|cos r| + |sin r|) ≤ 1/2`. A tower with levels turned against each other is left
  for later.
- Rule-side contacts are not polygons: `SharesArea` and `Meets` say "some point is under
  both", `InPatch` says "the point is under both planks". The engine finds the polygon
  (untrusted) and proves each answer with weights on the planks' sides (`Affine.lean`).
- F4 lets a push act anywhere in the patch, not only at its corners (equivalent, because
  the patch is convex). This removed the corner-spreading proofs.
- Property 7 is now two theorems linking the rules to Core's `Pose.contains`
  (`covers_of_contains`, `contains_of_inside`); the `Rect` and `restPatch` theorems and
  `plankOf_box` are gone with `FromCore.lean`.
- `fallCertificate_sound` takes a motion that passes `checkFall` (a `Bool` check), since
  the fall conditions are now checked with weights.
- E14's patch has 4 corners (a slanted four-sided shape), not more.

## 1. What we want

Today a block may only be turned about the vertical axis by 0°, 90°, 180° or 270°. We also
want 30°, 45° and 60°, and so every multiple of 30° or 45° (120°, 135°, 150°, ...).
Blocks are never tilted: their bottom and top stay flat.

## 2. What is there today

- **Core** (`core/KaplaCore/Block.lean`) already allows any turn: `Rot` is an exact
  `(cos, sin)` pair with `cos² + sin² = 1`. `Pose.box` and `Pose.contains` already work for
  any turn. The scorer and the web view (`yaw`) already accept any turn.
- **Physics** only knows six poses with sides along the axes (`Pose` in
  `specs/KaplaSpecs/PhysicsRules/Geometry.lean`, rule B4). A plank is its pose plus its
  lowest corner. `poseOf` in `FromCore.lean` returns `none` for any other turn, and the
  engine refuses the plan.

So the work is almost all in physics: every rule that assumes "sides along the axes".

## 3. Angles in exact fractions

`cos 30°`, `cos 45°` are not fractions. We use turns from Pythagorean triples, which are
exact and within a quarter of a degree of the wanted angle:

| Angle | Triple (cos, sin) | Real angle | Error at the block's end (7.5 units out) |
|---|---|---|---|
| 30° | 209/241, 120/241 | 29.86° | 0.018 units (0.14 mm) |
| 45° | 119/169, 120/169 | 45.24° | 0.031 units (0.24 mm) |
| 60° | 120/241, 209/241 | 60.14° | 0.018 units (0.14 mm) |

These errors are well below the placement error of 2 mm, so a builder cannot tell.

**Which turns the physics accepts (new rule B6, `Rot.Allowed`).** A turn is allowed when
1. it is a real turn: `cos² + sin² = 1` (`Rot.valid`), and
2. `sin²` is exactly 0 or 1 (the quarter turns we have today), or within `1/200` of
   1/4, 1/2 or 3/4 (about ±0.3° around 30°, 45°, 60° and their mirror images).

This test uses only fractions, covers all quadrants at once, and is short to review.
The planner should use only the table above (plus quarter-turn multiples), so its numbers
stay small: the simplex works on exact fractions, and 241 or 169 in every corner
coordinate makes the numbers grow. The physics accepts any turn that passes B6.

## 4. Spec changes (`specs/`, needs human review)

### 4.1 `Geometry.lean`: a plank is Core's block

The physics rules use Core's `Pose` directly (decision Q2):

```lean
abbrev Plank := KaplaCore.Pose   -- up : Upright, rot : Rot, center : Q3
abbrev Build := List Plank
```

- The six-pose `Pose` enum, the lowest-corner position, `x1`, `y1` go away.
- New helpers, each with a docstring and an example:
  - `Plank.bottom`, `Plank.top`: `center.z ∓ height / 2` (height from `Upright.dims`).
  - `Plank.footprint`: the plank seen from above, a **four-corner shape** (`Polygon`: a
    list of corners in counter-clockwise order), computed from `center`, `rot` and
    `Upright.dims`. Not `Pose.box` (that is the axis-aligned box *around* a turned block)
    and not `Pose.contains` (its half-open faces are meant for counting grid cells, not for
    contact).
  - `Plank.moveBy`: moves `center`.
- The six old poses stay as named examples (`Plank.flatX x y z`, ...), so old examples
  E1–E12 read the same.
- **Trusted surface grows by these Core definitions:** `Pose`, `Upright`, `Upright.dims`,
  `Rot`, `Rot.valid`, `Q3`, `blockLength`, `blockWidth`, `blockThickness`. All are short
  and already reviewed as part of Core. From now on a Core change to them is also a physics
  spec change; say so in Core's README.

### 4.2 `Rules.lean`

| Rule | Today | New |
|---|---|---|
| B6 `Rot.Allowed` | – | section 3 |
| P1 `Overlap` | intervals overlap along x, y, z | the two footprints share area **and** the heights overlap. "Share area" is checked by the separating-line test: two four-corner shapes do not share area exactly when, along one of their (at most 4 different) edge directions, there is a gap or a touch between them. Exact in fractions. |
| P2/P3 `WellFormed` | – | add: every plank's turn passes B6 |
| C1–C3 `restPatch` | `Rect.inter`, `HasArea` | the overlap of two footprints is a shape with up to 8 corners (cut one shape by the 4 edges of the other). `HasArea`: its area (shoelace sum) is above 0. |
| F4 `Push.Allowed` | push at one of 4 rectangle corners | push at one of the corners of the patch shape |
| S1 `Balanced` | unchanged | unchanged (it only uses push points and plank centres) |
| R1 `Build.shift` | moves the lowest corner | moves the centre. **Still no turning error** (section 10 "no twisting error" stays). |
| R5 `Meets`, `KeepsGaps` | gaps along x, y, z | a gap between footprints along some edge direction, or a gap in height |
| K3 `StraightPath` | unchanged in words | unchanged in words (it uses `Overlap` and `moveBy`) |
| F3 friction | patch corners | patch-shape corners |

New definitions to review (keep them short): `Rot.Allowed`, `Polygon`, `Polygon.area`,
`Polygon.inter`, `Polygon.Contains`, `Plank.footprint`, the separating-line test.

Each gets a docstring, an example and a `#guard`. Where possible, also check it against a
simple reference: for example `Polygon.Contains` against "the point is on the inner side
of every edge", and `Overlap` against `Pose.contains` on a grid of points.

### 4.3 `Column.lean`, `Tower.lean`: general, not only quarter turns (decision Q4)

- `IsColumn`, `comX`, `comY` stay as they are (they only use `restPatch` and centres).
- `ColumnRule`: "the combined centre of mass lies over the patch" uses
  `Polygon.Contains` instead of `Rect.Contains`. No quarter-turn hypothesis.
  `column_stable_iff` must hold for every column, turned blocks included.
- `squareTower` is rewritten with the new plank helpers; `squareTower_safe` keeps its
  statement.
- **New: a turned tower** (`turnedTower n`, E19): each level is two parallel planks, and
  each level is turned 45° against the one below. Theorem `turnedTower_safe`: safe plan at
  every height `n` for errors up to some stated ε. This shows the general machinery on a
  build with turns at every height, the way `squareTower_safe` does for quarter turns.
  The ε bound comes from the geometry (how far a corner of the patch is from the load
  point); we work it out with the engine on small `n` before stating it.

### 4.4 `FromCore.lean`

Almost all of it goes: core blocks *are* planks. What is left:

- `buildOf ps := if ps.all (·.rot.Allowed) then some ps else none` (or drop it and let
  `WellFormed` carry B6).
- `plankOf`, `poseOf`, `plankOf_box` are removed; `comparator/physics.json` and
  `coreCheck_ok_sound` are updated to match.

### 4.5 `Physics.lean` (theorem statements)

The statements keep their wording; only the definitions they mention change. Add:

- satisfiable-hypotheses examples with turned blocks (E13–E19 below);
- `¬ Spec` examples: an overlapping pair of turned blocks is not well-formed; a 45° block
  resting on a corner touch only is not stable; a 40° turn is not well-formed.

## 5. Engine and proof changes (`physics/`)

| File | Change | Size |
|---|---|---|
| all files | `Plank` fields: `p.x`, `p.pose`, ... → `p.center`, `p.up`, `p.rot` | mechanical, many places |
| `Solver.lean` | push variables at each patch corner instead of 4 rectangle corners; the equations are the same | small |
| `Engine.lean`, `checkPushes` | new `restPatch` and corners | small |
| `Robust.lean` | `Load.InsideOf`: "at least `ε·drift` from each edge" becomes "for each edge with direction `(a, b)`, at least `ε·drift·(|a|+|b|)` inside". Still linear, still exact. | medium |
| `RobustProofs.lean` | spread each load over the patch corners. For a rectangle this was the bilinear split; for a convex shape, split it into triangles from one corner and use the three triangle weights. **Hardest proof.** | large |
| `RobustSolver.lean` | same LP, new inside-the-patch constraints | medium |
| fall certificate (`Motion`) | "lifts no plank into its support" checked at each patch corner | small |
| `Reach.lean` | today: from above and 4 sides along x, y. Add the 4 sides along the block's own axes. Reach is a warning only, so a turned block the simple check cannot clear just gets a warning. | medium |
| `CoreAdapter.lean` | no conversion any more; refuse a plan only when a turn fails B6 | small |
| `ColumnProofs.lean` | redo with patch shapes; both directions use lemmas 2 and 6 below | large |
| `TowerProofs.lean` | redo `squareTower_safe` with new definitions (lemma 5 keeps it close to today's proof); new proof for `turnedTower_safe` | large |
| `Proofs.lean` | `Overlap`, `restPatch_plank_iff` (patch = overlap as sets of points) for shapes | medium |

Lemmas to state first (skeleton, CLAUDE.md §6), then prove one by one:

1. `Polygon.inter_contains`: a point is in the cut shape ⇔ it is in both shapes.
2. `Polygon.convex_combo`: a point inside a convex shape is a weighted sum of its corners,
   with weights ≥ 0 that add up to 1 (from the triangle split).
3. `sepLine_sound`: the separating-line test says "no shared area" ⇒ no point is strictly
   inside both.
4. `insideOf_moves`: a load point at least `ε·drift·(|a|+|b|)` inside every edge stays
   inside for every error up to `ε`.
5. Quarter-turn case: for quarter turns the new `restPatch` has the same corners as the
   old rectangle (keeps old examples and the square-tower proof cheap).
6. `Polygon.combo_contains`: a weighted sum of a convex shape's corners (weights ≥ 0,
   adding up to 1) is inside the shape. (The other direction of lemma 2; needed for
   "stable ⇒ column rule".)
7. `footprint_convex`: every footprint, and every overlap of two footprints, is convex
   with corners in counter-clockwise order.

## 6. Outside physics (other owners)

- **Core (D):** add `Rot.deg30`, `Rot.deg45`, `Rot.deg60` (the table) next to
  `Rot.quarter`, and `Rot.compose` to get 120°, 135°, ... Note in Core's README that `Pose`,
  `Upright`, `Rot` are now part of the physics trusted surface. Small PR, reviewed on its
  own, before the physics work.
- **Planner (C):** may propose turns from the table in section 3. Planner is empty today,
  so this is a note for whoever writes it.
- **Semantics (B):** nothing needed; `Pose.contains` already handles turns. A turned block
  no longer covers exactly 45 grid cells; the scorer counts cells, so that is fine.
- **Web (D):** `yaw` in the blueprint must come from `atan2(sin, cos)`; check that it does
  not assume multiples of 90°.
- **Docs:** `spec/physics-rules.md`: B4 ("sides are always parallel to the axes") and B5
  (lowest corner → centre) change, B6 is new, section 10 keeps "no tilted planks" and "no
  twisting error". `physics/README.md` and the top README: trusted list, main theorems.

## 7. Order of work

1. Core PR: named turns (section 6).
2. Spec PR: B6, `Polygon` and friends, `Plank := KaplaCore.Pose`, new `Overlap` /
   `restPatch` / `Meets` / `ColumnRule`, `turnedTower`, examples E13–E19, all statements in
   `Physics.lean` with `sorry`, updated `comparator/physics.json`. Run `plausible` on
   lemmas 1–7 before proving. **Human review here.**
3. Engine: field renames, solver, checker, adapter, reach. `#guard`s on E1–E19.
4. Proofs, in this order: lemmas 7, 5, 1, 3 → `checkPushes_sound`, `fallCertificate_sound`,
   `stabilityAnswer_*`, `restPatch_*_iff` → lemmas 2, 6, 4 → `solidCertificate_sound`,
   `verdict_*`, `checkPlan_sound` → `column_stable_iff` → `squareTower_safe` →
   `turnedTower_safe` → reach → `coreCheck_ok_sound`.
5. `make check`, axiom audit, CI (`lake check`, `lake comparator`).

Steps 1–3 are about a day or two. Step 4 is most of the work. The risks are lemma 2 with
`solidCertificate_sound`, and `turnedTower_safe` (explicit pushes for every error, at
every height, with 8-corner patches).

## 8. New examples

| # | Build | Expected |
|---|---|---|
| E13 | one flat block turned 45° on the ground | stable, solid |
| E14 | two flat blocks, the upper turned 30° and centred on the lower | stable, solid; the patch is a slanted four-sided shape |
| E15 | upper block turned 45°, centre outside the lower's footprint | falls |
| E16 | two blocks turned 45° and 135° whose footprints cross | overlap ⇒ not well-formed |
| E17 | a block on edge turned 60° on the ground | stable, solid |
| E18 | a turn of 40° (fails B6) | not well-formed, refused by the adapter |
| E19 | `turnedTower .deg45 3`: the square tower of 3 levels, turned as a whole by about 45° | safe plan |

## 9. Decisions

- **Q1.** Vertical blocks: out of scope for this plan.
- **Q2.** The physics rules use Core's block type (`KaplaCore.Pose`) directly.
- **Q3.** Tolerance ±0.3° (`1/200` in `sin²`) is accepted.
- **Q4.** `column_stable_iff` and `squareTower_safe` are **not** limited to quarter turns:
  the column rule must hold for every column, and a turned tower gets its own theorem.
