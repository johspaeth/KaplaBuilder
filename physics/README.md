# KaplaPhysics

Owner: A. Scope: see [docs/WORKSPLIT.md](../docs/WORKSPLIT.md).

- Build: `lake build KaplaPhysics`
- Files: `KaplaPhysics.lean` (root, imports the rest) and `KaplaPhysics/*.lean`.
- May import: `KaplaCore` only.
- Rules and CI: see the [README](../README.md).

## What is here

Rules come from [spec/physics-rules.md](../spec/physics-rules.md). Rule IDs (P1, C3, S2, ...)
appear in the docstrings.

| File | What it does | Trusted? |
|---|---|---|
| `Geometry.lean` | planks, the six poses, rectangles (W1–W3, B1–B5) | yes: read it |
| `Rules.lean` | `WellFormed` (P1–P3), `restPatch` (C1–C4), `Push`, `Balanced`, `Stable` (F1–F4, S1–S4), placement errors and `SolidWithin` (R1–R3), `SafePlan` (K1, K4, K5), `StraightPath` and `Reachable` (K2, K3) | yes: read it |
| `Solver.lean` | exact-fraction simplex; proposes pushes or a fall motion | no: every proposal is checked |
| `Robust.lean` | `SolidCertificate`: loads whose points move with the errors | checked by the proofs |
| `RobustSolver.lean` | proposes a solidity certificate (an LP, then a top-down pass) | no: checked |
| `Column.lean` | the simple centre-of-mass rule for a single column (section 7) | yes: read it |
| `Reach.lean` | K3 checker: tries five straight paths (from above, from each side) plus the drop | checked by the proofs |
| `Engine.lean` | `stabilityAnswer`, `verdict` (solid / risky / falls), `checkPlan` | checked by the proofs |
| `Sums.lean`, `RobustProofs.lean`, `ColumnProofs.lean`, `Proofs.lean` | the proofs (main statements in `specs/KaplaSpecs/Physics.lean`) | checked by Lean |
| `Examples.lean` | worked examples E1–E12 as `#guard`s; concrete instances of the theorems; bad answers the rules reject | tests |

## Main theorems

- `stabilityAnswer_stable_sound`: answer "stable" ⇒ `Stable b` (property 1).
- `stabilityAnswer_falls_sound`: answer "falls" ⇒ `¬ Stable b` (property 2). The solver
  hands over a motion of the planks that lifts no plank into its support yet lowers the
  total weight; the checker confirms it, and the proof shows no balancing pushes can exist.
- `verdict_solid_sound`: verdict "solid" ⇒ stable for **every** combination of placement
  errors up to ε (property 3). The certificate gives each contact a fixed load at a point
  that moves with the errors; the proof spreads each load over the corners of the real
  contact patch (F4) and shows balance for every error.
- `verdict_risky_sound`, `verdict_falls_sound`: "risky" ⇒ stable at the exact positions;
  "falls" ⇒ not stable.
- `checkPlan_sound`: an accepted plan has at most N planks and is well-formed and
  **solid** after every step (property 4, K4).
- `reachDir_sound`, `hardToReach_nil_sound`: a step the checker does not flag can be put
  in place along a straight path from far away plus a drop of `h`, never sharing inside
  space with a placed plank (property 5, K3). Flagged steps are warnings only.
- `column_stable_iff`: for a single column, `Stable` holds exactly when at every level the
  combined centre of mass of everything from that level up is over the patch below it
  (property 6). Both directions are proven, so the definition of `Stable` is checked
  against the simple rule a reviewer can verify by hand.
- `Rect.inter_contains`, `Rect.hasArea_iff`, `restPatch_plank_iff`, `restPatch_ground_iff`:
  the contact patches are exactly the overlaps of C1–C3, as sets of points (property 7).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only. No `opaque` contracts.

The statements mention `verdict` and `checkPlan`, which call the solvers, so the solvers
are in the spec surface. Nothing depends on them being right: a wrong proposal only gives
"risky" or "unknown".

**Cautious, never optimistic (R3).** "Risky" means "not shown to be solid". A solid build
can get "risky" when no certificate of the simple kind exists (fixed loads per contact).
A "solid" verdict is always right.

Placement errors are taken over the whole R1 box (every plank within ε along `x` and `y`).
R5 only removes some of these errors, so "solid" here implies solid under R5.

## Not done yet

- Friction (property 8), square tower for every `n` (property 9; today checked for 8
  levels).
- K3 tries only five directions; a plank reachable only along a slanted line is flagged.
- Speed: the engine first tries fast top-down solvers (one small LP per plank) and uses
  the global LPs only for builds of at most 40 planks. Measured with the interpreter on a
  200-plank square tower: exact check 1.4 s, solid verdict 2.4 s. `checkPlan` checks
  every prefix separately, so a 200-step plan takes minutes; reusing work between steps
  is still to do. Large builds that fall get "unknown" (the fall certificate needs the
  global LP).
- Checking the robust solver's output inside the Lean kernel is slow beyond one plank, so
  the kernel examples for E2 and E6 check a written-out certificate.
