# KaplaSemantics: roadmap for the hackathon session

Agreed 1 Nov 2026. Design: `semantics/APPROACH.md`. Rules for sessions: `semantics/CLAUDE.md`.
Everything here is done in one sitting of a few hours; times are boxes, not estimates.

**Process rule for every step:** the decisions a step involves are listed and ruled on by the
person before anything is written. Contract and viewer changes in particular are never
drafted from an assistant's own idea of what they should be.

**Branches:** `feature-semantics` (only `semantics/`) for steps 2–4 and 7–10;
`web/bubble-viewer` (only `web/`) for step 6; `core/semantics-contract` (only `core/`) for
step 5. Nothing reaches `main` without a PR and a green **CI OK**.

| # | Step | Box | Done when |
|---|---|---|---|
| 1 | **Pull main and read what landed.** Merge `origin/main` into `feature-semantics`. Read the viewer in `web/` (how it takes data, units, what it draws) and the state of `core/`. | 10 min | We know what the viewer needs and which Core types exist. May adjust steps 5–7. |
| 2 | **Docker.** `semantics/dev/Dockerfile` (Ubuntu 24.04 as in CI, elan with the pinned toolchain, bubblewrap), `ci.sh` (the CI checks: `make check`, `lake check`, `lake comparator`), `dev.sh` (repo mounted, `.lake` on a named volume). Editing stays on macOS; no editor in the container. Download runs while step 3 starts. | 30 min | `ci.sh` is green inside the container. |
| 3 | **Bubble model + JSON.** `Bubble.lean`, `Json.lean` (exact `Rat` codec), `normalize`, `wellFormed`, round-trip `#guard`s, the one-ellipsoid fixture `egg.json` (centre (0, 0, ½), semi-axes (0.3, 0.3, 0.5)). | 30 min | `egg` decodes, normalises and round-trips. |
| 4 | **Egg handover to the planner.** `egg.json` (scale-free) plus the placement-and-grid rule written down: scale by the planner's height, grid of spacing 1 with half-step centres, keep centres that pass the ellipsoid test. `Dev/Cells egg.json --height H` only if C would rather call than compute. The height is the planner's. | 10 min | C has the file and the rule and can produce cells for a height of their choosing. |
| 5 | **Core semantics contract.** Design conversation, then the `core/semantics-contract` branch and PR. Three handover points: the bubble format in `TargetSpec`; how bubbles meet the grid when the planner proposes blocks (frame, units, where "inside" is computed: by asking the engine, or from `contains`/`place` in Core); what the checker returns to the planner (accepted or not, which block is outside, which bubble is uncovered, per-bubble coverage, score). Fastest with C reachable. | 45–60 min | Every decision has a ruling; the Core PR compiles. |
| 6 | **Viewer bubbles.** On `web/bubble-viewer`: draw ellipsoids from the bubble JSON, take data by file or URL. Size depends on step 1. | depends | `egg` shows in 3D at a given height. |
| 7 | **Chat loop on the viewer.** `Claude.lean` (interpret, refine, 2 retries, transcript file), placed bubbles sent in block units at the chosen height, the Lean tools under `KaplaSemantics/Dev/`, the chat page with its serving script in `semantics/dev/`. Fallback if the viewer cannot draw ellipsoids in time: a 3-view SVG in the browser. | 1 h | "an egg" → 3D at build size → "make it taller" → change → accept → fixture file. Testing starts here. |
| 8 | **Engine with theorems 1–4.** `Grid`, `Score`, `Check`, `Frame` as the short block-side definitions, matching the contract; theorem statements in the same sitting; proofs; `Dev/Score`; a tower fixture. In Docker. | 2–3 h | Theorems 1–4 pass `lake check` and `lake comparator`; the 1/52 example is a `#guard`. |
| 9 | **Interface for the planner.** `Engine.lean` implements the contract (`interpret`, `refine`, `score`, `check`), wired in `Main.lean`, mock swapped. | 20 min | `kapla build` runs end to end on a tower fixture. |
| 10 | **Theorem 5 and the convexity lemmas.** First thing to cut. | rest | `lake comparator` passes for theorem 5. |

Later, outside the session: image input (segment first, APPROACH.md §2) and silhouette,
narration text, chat inside the project web UI, demo polish.

**Why this order.** The egg and the contract go before the chat because they are what the
planner is waiting for; the chat only needs the model (3) and the viewer (6), not the engine,
so it is not delayed by the proofs; the engine (8) comes after the contract (5) so its
definitions match what the planner holds; theorem statements are written with the
definitions so a proof that will not go through reveals a wrong definition early.
