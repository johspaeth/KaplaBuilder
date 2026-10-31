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
| `Rules.lean` | `WellFormed` (P1–P3), `restPatch` (C1–C4), `Push`, `Balanced`, `Stable` (F1–F4, S1–S4), placement errors and `SolidWithin` (R1–R3), `SafePlan` (K1, K4, K5) | yes: read it |
| `Solver.lean` | exact-fraction simplex; proposes pushes or a fall motion | no: every proposal is checked |
| `Robust.lean` | `SolidCertificate`: loads whose points move with the errors | checked by the proofs |
| `RobustSolver.lean` | proposes a solidity certificate (an LP, then a top-down pass) | no: checked |
| `Engine.lean` | `stabilityAnswer`, `verdict` (solid / risky / falls), `checkPlan` | checked by the proofs |
| `Sums.lean`, `RobustProofs.lean`, `Proofs.lean` | the proofs (main statements in `specs/KaplaSpecs/Physics.lean`) | checked by Lean |
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

- Reachability (K3, property 5), single-column rule (property 6), contacts match the
  face overlap as point sets (property 7), friction (property 8), square tower for every
  `n` (property 9; today checked for 8 levels).
- Speed: the engine first tries fast top-down solvers (one small LP per plank) and uses
  the global LPs only for builds of at most 40 planks. Measured with the interpreter on a
  200-plank square tower: exact check 1.4 s, solid verdict 2.4 s. `checkPlan` checks
  every prefix separately, so a 200-step plan takes minutes; reusing work between steps
  is still to do. Large builds that fall get "unknown" (the fall certificate needs the
  global LP).
- Checking the robust solver's output inside the Lean kernel is slow beyond one plank, so
  the kernel examples for E2 and E6 check a written-out certificate.
