# KaplaBuilder

Design: [docs/DESIGN.md](docs/DESIGN.md). Who does what: [docs/WORKSPLIT.md](docs/WORKSPLIT.md).

## Quick start

```sh
make install   # needs elan; builds everything with Lean 4.35 (pinned in lean-toolchain)
make run       # runs the `kapla` CLI
make check     # what CI checks (except `lake check` / `lake comparator`, Linux only)
```

## Layout: one folder per component

| Folder | Lean library | Owner | May import |
|---|---|---|---|
| `core/` | `KaplaCore` | all (stewarded by D) | Lean core, Batteries |
| `physics/` | `KaplaPhysics` | A | `KaplaCore` |
| `semantics/` | `KaplaSemantics` | B | `KaplaCore` |
| `planner/` | `KaplaPlanner` | C | `KaplaCore` |
| `web/` | `KaplaWeb` | D | `KaplaCore` |
| `app/` | `kapla` (exe) | D | everything |
| `specs/` | `KaplaSpecs` | all (humans) | everything |
| `comparator/` | – | all (humans) | – |

Work only in your own folder. Build only your part: `lake build KaplaPhysics`.
Every `.lean` file in your folder is built, even if nothing imports it.

## Rules for `main`

`main` is protected. You can merge only through a pull request, and only when the
**CI OK** check is green. Nobody can bypass this.

CI fails if:

1. **A build fails or warns.** Each library builds with `--fail-level=warning`.
   A `sorry` is a warning, so it fails.
2. **An import breaks the rules.** A component imports another component
   (`scripts/check_imports.sh`).
3. **A forbidden word appears** in code: `sorry`, `admit`, `axiom`, `native_decide`,
   `debug.skipKernelTC`, `maxHeartbeats 0`, `implemented_by`, `extern`, `unsafe`
   (`scripts/check_forbidden.sh`). This also counts words in comments.
4. **`lake check` fails.** The whole project is replayed through the Lean kernel, and only
   the standard axioms (`propext`, `Quot.sound`, `Classical.choice`) are allowed.
5. **`lake comparator` fails** for a file in `comparator/`. This checks that the proofs
   prove exactly the statements in `specs/`.

## How to work

1. Branch from `main`: `git switch -c physics/contacts`.
2. Change files in your folder. Run `lake build <YourLib>` often and `make check` before
   you push.
3. Unfinished proofs: keep the `sorry` on your branch. It cannot reach `main`.
4. Open a PR. Wait for **CI OK**. Merge.

## Specs and the comparator

A spec is a theorem statement that humans wrote and reviewed. It lives in `specs/`, with
`sorry` as its proof. The real proof lives in your folder, with **the same name and the same
statement**. A file in `comparator/` connects the two. Example: `specs/KaplaSpecs/Core.lean`,
`core/KaplaCore/Proofs.lean`, `comparator/core.json`.

To add a spec:

1. Write the statement in `specs/KaplaSpecs/<Component>.lean`. Import only the definitions it
   needs, not the proofs.
2. Prove it in your folder, in a module that the spec does not import.
3. Add `comparator/<component>.json`: challenge module, solution module, theorem names.

Changes to `specs/`, `comparator/` and `core/` change what everyone relies on.
Get a review from the whole team before you merge them.

## What is trusted

- The Lean 4.35 kernel and the statements in `specs/` (and every definition they mention).
- No extra axioms. No `opaque` contracts yet. Add them here when you add them.
