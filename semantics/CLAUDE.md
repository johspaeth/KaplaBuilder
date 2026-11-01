# CLAUDE.md for `semantics/` (KaplaSemantics, person B)

You act as person B. Read `semantics/APPROACH.md` first (design, file map, open questions).
The repo root `CLAUDE.md` and `README.md` still apply. Ask before deciding anything the file
leaves open; never resolve a design choice on your own.

## Before any edit
- `git branch --show-current` decides what you may touch; any other branch: stop and say so.
  `feature-semantics` → `semantics/` only · `web/bubble-viewer` → `web/` only (draw ellipsoids
  from the bubble JSON, take data by file or URL) · `core/semantics-contract` → `core/` only.
- Contract and viewer changes are designed with the person first: list the decisions, get a
  ruling on each, then write. Never draft them from your own theory of what they should be.
- Lean files only under `semantics/KaplaSemantics/` (lakefile glob `KaplaSemantics.*`); a `.lean`
  anywhere else in `semantics/` is not built. Add each new module to `semantics/KaplaSemantics.lean`.

## Lean rules (CI enforces them; never work around them)
- Lean 4.35.0, pinned. No Mathlib; Lean core only (Batteries is allowed but not in the
  manifest, ask first). Imports: `KaplaCore` and `KaplaSemantics.*` only, never Physics,
  Planner, Web. `Rat` everywhere, never `Float`. `autoImplicit` is off: name every variable.
- Block units everywhere: 1 unit = block thickness, a block is 15 × 3 × 1. No other unit exists
  in the project. `Engine.lean` is the only file that uses `KaplaCore` types.
- Forbidden words, also inside comments and docstrings: sorry, admit, axiom, native_decide,
  implemented_by, extern, unsafe, maxHeartbeats 0, debug.skipKernelTC. Rephrase. Warnings fail
  CI: no unused variables, no deprecated names, no unfinished proofs in a PR (WIP commits may).

## Build and check
- After each module edit: `lake build KaplaSemantics`. Before every commit: `make check`.
  `lake check` / `lake comparator` are Linux-only: run them in the Docker container
  (`semantics/dev/ci.sh`), never two `lake` processes at once.
- Dev tools: `lake env lean --run semantics/KaplaSemantics/Dev/<Tool>.lean <args>`, after
  `lake build KaplaSemantics`. CI builds `Dev/*.lean` too: zero warnings there as well.

## File map (APPROACH.md §7)
`Bubble.lean` types · `Frame.lean` frame, place, canonicalFrame · `Json.lean` codec · `Grid.lean`
cells, targetCells, blockCells · `Score.lean` covered (per-bubble fill), extra, missing, score,
solid, perBubble, verdict · `Check.lean` WithinTarget, CoversTarget, checkers · `Engine.lean`
SemanticEngine, `componentName` · `Claude.lean` API client · `Dev/*.lean` CLI tools
(the chat page's backend) · `Proofs/*.lean` one per spec file, same theorem names ·
`semantics/fixtures/{targets,plans,score_expected}/` · `semantics/dev/` Docker, shell helpers,
chat page. The frame is always an argument; nothing picks one silently.

## Adding a theorem
1. Statement in `specs/KaplaSpecs/Semantics.lean` (unproven there on purpose).
2. Proof under the same name and statement in `semantics/KaplaSemantics/Proofs/<Spec>.lean`,
   a module the spec file does not import; the spec imports definition modules, never the root.
3. Entry in `comparator/semantics.json`. Steps 1 and 3 touch shared files: prepare the text,
   flag it for team review, never commit them alone.
4. Beside the proof: the spec surface, a concrete `example` with every hypothesis discharged,
   and a `¬ Spec … badOutput` example.

## Testing style
- `#guard cond` for unit checks (build-time test); `#eval` while exploring, remove before commit.
  JSON round trip is tested this way (every fixture, plus a 1/3 case), not proven.
- One definition per number, written from the block side so it is both the spec a reviewer
  reads and the code that runs; no separate fast version unless measured to be needed.

## Stuck proofs and commits
Never weaken the spec or change a definition to make a proof go through; report it stuck (goal,
what was tried, missing lemma) and leave it unfinished on the branch. Commit only when asked;
short messages naming the module: `Grid: targetCells and blockCells`.
