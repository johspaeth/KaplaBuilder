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
| `Rules.lean` | `WellFormed` (P1–P3), `restPatch` (C1–C4), `Push`, `Balanced`, `Stable` (F1–F4, S1–S4), `StandsAtEveryStep` (K1, K4, K5) | yes: read it |
| `Solver.lean` | exact-fraction simplex that *proposes* pushes or a fall motion | no: every proposal is checked |
| `Engine.lean` | `FallCertificate`, `checkPushes`, `stabilityAnswer`, `checkPlan` | checked by the proofs |
| `Proofs.lean` | the main theorems (statements in `specs/KaplaSpecs/Physics.lean`) | checked by Lean |
| `Examples.lean` | worked examples E1–E12 as `#guard`s; concrete instances of every theorem; bad answers the rules reject | tests |

## Main theorems

- `stabilityAnswer_stable_sound`: answer "stable" ⇒ `Stable b` (property 1).
- `stabilityAnswer_falls_sound`: answer "falls" ⇒ `¬ Stable b` (property 2). The solver
  hands over a motion of the planks that lifts no plank into its support yet lowers the
  total weight; the checker confirms it, and the proof shows no balancing pushes can exist.
- `checkPlan_sound`: an accepted plan is well-formed and stable after every step, with at
  most N planks (property 4, at the exact positions).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only. No `opaque` contracts.

The statements mention `stabilityAnswer`, which calls the solver, so the solver is in the
spec surface, but nothing depends on it being right: a wrong proposal only gives "unknown".

## Not done yet

- R1–R5 placement errors ("solid" vs "risky", property 3). K4 asks for solid; today
  `checkPlan` checks stability at the exact positions only.
- Reachability (K3, property 5), single-column rule (property 6), contacts match the
  face overlap as point sets (property 7), friction (property 8), square tower for every
  `n` (property 9; today checked for 8 levels).
- Speed: the simplex is dense; large builds (~200 planks) are not yet measured.
