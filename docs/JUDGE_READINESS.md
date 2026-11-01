# Judge readiness checklist

What we check before the judges look at KaplaBuilder. Judges score two things
([rules.md](../rules.md)):

1. **Coolness**: a non-technical person runs `make install && make run` and says "ooh".
2. **Verification**: the proofs are about the code that runs, they say something
   important, and they pass Comparator.

Each item below says **what to check**, **where** (file:line on `main` at `dd69a4c`), and
**done when**. Tick an item only when its "done when" is true on `main`.

Severity: 🔴 a judge will notice and it hurts the score · 🟡 should fix · ⚪ nice to have.

---

## 0. The rule that keeps everything consistent

**One fact, one home.** Every fact lives in one place. Every other place links to it.

| Fact | Its one home | Others link to it |
|---|---|---|
| What is proven, and what is not | `README.md` "What the plan guarantees" | DESIGN.md, component READMEs |
| Physics rules (B, C, F, K, P, R, S, E, H IDs) | `spec/physics-rules.md` + `specs/KaplaSpecs/PhysicsRules/` | physics/README.md, DESIGN.md |
| Main theorem statements | `specs/KaplaSpecs/<Component>.lean` | each component README |
| CLI commands and flags | `app/README.md` (from `app/Main.lean`) | README.md, DESIGN.md, web/README.md |
| File formats (blueprint, model, gallery) | `web/README.md` | app/README.md, semantics/README.md |
| What is trusted | `README.md` "What is trusted" | physics/README.md |

When code changes one of these facts, the same PR updates its home. A doc that repeats a
fact instead of linking to it is a bug.

---

## A. Lean engine

### A1. Every claim in the README has a theorem that passes Comparator

| README claim | Theorem | Spec | Comparator | Status |
|---|---|---|---|---|
| At most N blocks | `checkPlan_sound`, `coreCheck_ok_sound` | `specs/KaplaSpecs/Physics.lean:91,360` | `physics.json` | ✅ |
| Stands after every step | `coreCheck_ok_sound` | `Physics.lean:360` | `physics.json` | ✅ |
| Stands with 3.9 mm placement error | `coreCheck_ok_sound`, `verdict_solid_sound` | `Physics.lean:48,360` | `physics.json` | ✅ |
| Blocks fit; `hands` per step | `coreCheck_ok_sound` (`SafePlan`) | `Physics.lean:360` | `physics.json` | ✅ |
| Turned blocks stand at planned positions | `checkTurnedPlan_sound` | `Physics.lean:341` | `physics.json` | ✅ |
| Every block is part of the target, every part is built | **none** | **none** | **none** | 🔴 |
| Likeness score is computed correctly | **none** | **none** | **none** | 🔴 |

- [ ] 🔴 **Semantics theorems.** `semantics/` has no theorems, no `specs/KaplaSpecs/Semantics.lean`
  and no `comparator/semantics.json`. The five statements exist only as text in
  `semantics/APPROACH.md:341-350`. **Done when:** they are in `specs/`, proved in
  `semantics/`, and listed in `comparator/semantics.json`. **Or:** the README stops
  calling the scorer verified (`README.md:18-19, 44, 82`). Choose one; do not leave both.
- [ ] 🔴 **Make "part of the target" mean what the sentence says.** `WithinTarget` asks
  only that a block has *one* cube in some bubble (`semantics/KaplaSemantics/Check.lean:13-14`).
  `CoversTarget` asks only that each bubble has *one* block cube (`Check.lean:18-20`).
  **Done when:** the README sentence describes exactly these definitions, or the
  definitions are made stronger.
- [ ] 🟡 **Score against a reference.** Today there are only `#guard`s (`Score.lean:69-102`).
  **Done when:** there is a theorem "`score` = this simple function" (CLAUDE.md §4,
  "Compare against a reference") or `score_in_unit_interval` at least.
- [ ] 🟡 **Proven but not compared.** `KaplaPlanner.judge_checked_passed`
  (`planner/KaplaPlanner/AiStrategy.lean:301`) and `ai_passed_safe` (`app/Main.lean:154`)
  have no spec or comparator entry. **Done when:** both are in `specs/` + `comparator/`, or
  the docs stop calling `ai_passed_safe` a main theorem (`physics/README.md:105`).
- [ ] ⚪ **Core spec is trivial.** `Q3.add_comm` (`specs/KaplaSpecs/Core.lean:12`) is the only
  core spec. Keep it as the template example, and say so in `core/README.md`.

### A2. Hypotheses are satisfiable, bad outputs are rejected (CLAUDE.md §4)

For **each** main theorem: one `example` with every hypothesis discharged, and at least one
`example : ¬ Spec input bad`.

- [ ] 🟡 `checkTurnedPlan_sound` has only negative examples (`Physics.lean:345-349`). The
  positive case is a `#guard` (`physics/KaplaPhysics/Turned.lean:128`). **Done when:** a
  positive `example` sits next to the spec.
- [ ] ⚪ `checkPlan_sound`'s positive example is one plank, E1 (`Physics.lean:96`). Add a
  multi-step plan (for example `squareTower`).
- [ ] ⚪ Put a named example next to each definition in `physics/KaplaPhysics/Engine.lean`
  (none today), or link to where they live (`Examples.lean`).
- [ ] 🟡 Run `#audit_axioms` and `#spec_surface` (CLAUDE.md appendix) on each main theorem
  and paste the output into the component README. Judges like to see it, not only
  "CI passes".

**Template for every main theorem** (names in `<>` are placeholders; real cases to copy:
`e1_stable`, `floating_no_push`, `e3_not_solid` in `specs/KaplaSpecs/PhysicsRules/Examples.lean`):

```lean
/-- A two-step plan that the checker accepts: the hypotheses of `checkPlan_sound` hold. -/
example : checkPlan {} placementError <N> <goodPlan> = true := by decide +kernel
/-- The spec says no to a bad output: a plank in mid-air is not stable. -/
example : ¬ Stable <badBuild> := <proof>
```

### A3. The code that runs is the code that is proven

- ✅ Physics: `runPhysics` calls `KaplaPhysics.coreCheck` (`app/Main.lean:228`), the
  function in `coreCheck_ok_sound`. No `partial def` in any library. `Float` only in the
  viewer (`web/KaplaWeb/Blueprint.lean`) and in a drawing check (`app/Main.lean:129`).
- [ ] 🔴 `kapla plan` prints **"physics ok (verified)"** from the report that the planner
  returns (`app/Main.lean:308`). It does not run the check again. A planner can fake that
  report (`planner/KaplaPlanner/Demos.lean:333`). **Done when:** `kapla plan` runs
  `coreCheck` itself, as the website does (`app/Main.lean:516`).
- [ ] 🟡 The website's **"stands"** badge is `physics.ok` (`app/Main.lean:519`). It ignores
  `assurance`, so a turned plan (`.nominal`, no placement-error check) gets the same badge
  as a `.robust` one. `allowNominal` is on by default (`specs/KaplaSpecs/PhysicsRules/Rules.lean:235`).
  **Done when:** the badge shows the two cases differently ("stands, ±3.9 mm" vs.
  "stands as planned").

### A4. No duplicate or conflicting definitions

- [ ] 🟡 `core/KaplaCore/Mocks.lean` has a second scorer and a second physics check
  (`:84`, `:176-184`, `:216`). Its `blockCells`/`bubbleCells` have the same names as in
  semantics but different types (`semantics/KaplaSemantics/Grid.lean:40,52`). Only tests
  use them. **Done when:** they are renamed (`mockBlockCells`, ...) and the file header
  says "tests only".
- [ ] ⚪ `semantics/dev/Score.lean` and `web/dev/BubblePage.lean` match no lakefile glob
  (`lakefile.toml:14-47`), so nothing builds them. **Done when:** they are built in CI or
  deleted.

### A5. The CI gate catches what CLAUDE.md §7 forbids

- ✅ CI builds with `--fail-level=warning`, checks imports and forbidden words, runs
  `lake check` and `lake comparator` (`.github/workflows/ci.yml:25-80`).
- [ ] 🟡 Add to `scripts/check_forbidden.sh:22-28`: `decide +native`, `ofReduceBool`,
  `@[csimp]`, and `maxHeartbeats` above a limit. None are used today; `lake check`
  catches new axioms, but the script is the first, readable line of defense.
- [ ] ⚪ `opaque` is *allowed* (the script's own advice for a function without a body), but
  each one is part of the trusted surface. Make CI print every `opaque` so it cannot be
  added without a matching line in README "What is trusted".
- [ ] ⚪ `scripts/check_imports.sh:20` misses `public import` and two modules on one line.

### A6. Trusted surface is complete and true

- [ ] 🟡 `README.md` "What is trusted" (`:139-151`) misses: the model reader
  `KaplaSemantics.decode`, the viewer (`KaplaWeb.parsePlan`, uses `Float`), the Claude calls
  (`curl`, untrusted by design: say so), and the `kapla serve` HTTP layer.
- [ ] 🔴 `docs/DESIGN.md:40-50` marks **all** of H1–H9 "Rule (verified)". In fact:
  H2 (errors add up) is not covered (`physics/KaplaPhysics/CoreAdapter.lean:20-22`);
  H4 is not modelled; H5 is a warning only; H8 and H9 are never reported
  (`CoreAdapter.lean:37-38`). `README.md:32` says DESIGN shows how *each* is ruled out.
  **Done when:** the table has a "Status" column (proven / warning / not modelled) and the
  README "Not guaranteed" list names H4, H8, H9 too.
- [ ] ⚪ `spec/physics-rules.md:209` (K1) says one plank per step; the app allows `hands`.
  `CoreAdapter.lean:14-17` explains it; put the same sentence in K1.

---

## B. End-to-end flow

### B1. Fresh clone: `make install && make run` just works

Dry run on a clean machine (or `docker run -it ubuntu`), with **no** API key:

```sh
git clone https://github.com/johspaeth/KaplaBuilder && cd KaplaBuilder
make install   # time it; write the time in the README
make run       # open http://localhost:8000
```

- [ ] 🔴 Do the dry run on macOS and on Linux. Write down the build time and any error.
- [ ] 🟡 The README says only "chat needs an API key" (`README.md:72`). The server reads
  **only** `semantics/dev/.env` (`app/Main.lean:428, 626`). If `ANTHROPIC_API_KEY` is set in
  the shell but there is no `.env`, chat gives 503 while the `ai` planners work
  (`planner/KaplaPlanner/Claude.lean:85`). **Done when:** both read the same source, and
  the README Quick start shows `cp semantics/dev/.env.example semantics/dev/.env`.
- [ ] 🟡 List the tools besides elan in Quick start: `curl` (all Claude calls), `git` +
  `gh` (gallery PR button, #47), internet for three.js (`web/KaplaWeb/Page.lean:305-306`).
- [ ] ⚪ `make run PORT=8001`. Today the port is fixed (`Makefile:12`).

### B2. The demo a judge sees first

- [ ] 🟡 The default planner on the page is **"stand-in tower (test only)"**
  (`app/Main.lean:470, 478`). **Done when:** the default is the best real planner when a
  key is present, and a gallery model is pre-loaded when there is not.
- [ ] 🟡 Offline path works: with no key, a judge can open a saved model, see the 3D view,
  move the step slider, and see the "stands" badge and the score.
- [ ] 🟡 Make a 2-minute script: prompt → target → plan → slider → badges → "here is the
  theorem behind this badge". Put it in the README under "Demo".

### B3. Every documented command exists, every command is documented

What `app/Main.lean:658-705` implements:

```
kapla                      # prints the component list
kapla check FILE [--max N]
kapla view  FILE [--out DIR]
kapla plan  [--blocks N] [--strategy empty|ai|ai-unchecked] [--effort low|medium|high]
            [--target FILE] [--out FILE]
kapla serve [--port N]     # default 8000
global: --no-clearance  --robust-only
```

- [ ] 🔴 `README.md:60-62` "Planned usage" shows `kapla build --prompt --image` and
  `serve --port 8080`. `build` does not exist; the port is 8000. Replace with the block
  above (taken from `app/README.md`).
- [ ] 🔴 "Upload a picture" (`README.md:3, 38`) is not built (`semantics/ROADMAP.md:29`).
  Remove it or mark it "later".
- [ ] 🟡 Same stale `build` / `--eps` / 8080 in `docs/DESIGN.md:288-290` and
  `docs/WORKSPLIT.md:25, 324, 363, 409`.
- [ ] 🟡 `app/README.md:8-17` misses `plan` and `--robust-only`; line 6 says `lake exe
  kapla` runs the app (it prints the list). The no-argument help (`Main.lean:695-701`) also
  misses `plan` and still says "scaffold".

### B4. Examples: plenty, and all of them tested

- [ ] 🟡 CI never runs `kapla check` on `web/examples/{house,duck,spiral}.json`. **Done
  when:** a CI step runs `kapla check` on every file in `web/examples/` and `gallery/`
  (good ones must pass, `bad-*` ones must fail).
- [ ] 🟡 One README section "Examples" with a table: file, blocks, what it shows, expected
  verdict, command to run it. Include at least one that **falls** and one that is
  **risky**, so judges see the checker say no.
- [ ] ⚪ `models/{egg,bunny}.json` are byte copies of `semantics/fixtures/targets/`. Keep one
  (#47 moves `models/` to `gallery/`; update `semantics/STEP7.md` and `semantics/CLAUDE.md`).
- [ ] 🟡 Docs point to files that do not exist: top-level `fixtures/physics_expected/`,
  `score_expected/` (`docs/WORKSPLIT.md:292-296`), `semantics/fixtures/score_expected`
  (`semantics/CLAUDE.md:43`, `semantics/APPROACH.md:452`), `semantics/KaplaSemantics/Dev/`
  (`APPROACH.md:129-133`).

### B5. Smoke test of the whole flow in CI

- [ ] 🟡 Add a CI job: start `kapla serve`, `curl` the page, open one gallery model,
  check the JSON has `"stands": true` and a score. No Claude call needed.
- [ ] 🟡 `kapla plan --strategy empty --target semantics/fixtures/targets/egg.json` runs
  and exits 0.

---

## C. Documentation

### C1. What a judge reads, in order

1. `README.md`: what it is, demo, guarantees, how to run, what is trusted.
2. `spec/physics-rules.md` and `specs/`: the rules and the statements.
3. Component READMEs: one page each, same headings (below).

Everything else is team-internal. Move it to `docs/internal/` or say so at the top of each
file: `docs/WORKSPLIT.md` (Gantt chart to 2027-02-05, mocks that do not exist at `:225,
302`), `semantics/STEP7.md`, `semantics/ROADMAP.md`, `semantics/CLAUDE.md` (points to spec
and comparator files that do not exist, `:47-50`), root `CLAUDE.md`.

- [ ] 🟡 Internal docs are moved or marked.

### C2. Same headings in every component README

```markdown
# <Component>
What it does (two sentences).
## Run it        (one command, one example, its output)
## What is proven (theorem names → specs/ file → comparator/ file; or "nothing, untrusted")
## What is trusted
## Examples      (files, with the expected result)
## Known gaps
```

- [ ] 🟡 `semantics/README.md` is 8 lines and does not mention the chat, the scorer or its
  status. Rewrite with the headings above.
- [ ] 🟡 `core/README.md:10, 23` ("v0.1 draft", "Not yet: JSON codecs, tilted poses") is stale.
- [ ] ⚪ `planner/README.md:39`: the turns row breaks the table, and says 0/30/45/60/90
  while physics allows every 15° step. Say why the planner limits itself.
- [ ] ⚪ `web/README.md:71` "The chat (step 7)": drop the internal step number.

### C3. DESIGN.md matches the code

- [ ] 🟡 Module names that do not exist (`Kapla.Geometry`, ..., `docs/DESIGN.md:272-284`);
  theorems that do not exist (`certify_sound`, `robust_sound`, `:206, 306`; `Valid`,
  `:324`); the Shape DSL and voxelizer (§5), replaced by bubbles; the score is called IoU
  (`:252-255, 279`) but the code is covered / (target + extra) (`Score.lean:52`);
  M3 "tilted blocks ✅" (`:307`) and "any rotation" (`:165-168, 323`) while the code allows
  15° steps only. **Done when:** every name in DESIGN.md resolves to a file or theorem
  (a `grep` per name), or the section is marked "original design, not built".
- [ ] ⚪ `README.md:40` "Planner + LP → certificates": the live planner is Claude; the LP is
  in physics. Fix the diagram.

### C4. Style (CLAUDE.md §4)

- [ ] Short sentences, simple words, no unexplained jargon (Simplified Technical English).
- [ ] The numbers are the same everywhere: block 15 × 3 × 1, ε = 1/2 unit = 3.9 mm, turns
  in 15° steps, default `hands` = 1, port 8000. (Checked: they agree today, except the
  8080 lines in B3.)

---

## D. Last check, on the day

```sh
make check                                  # green
gh pr checks <PR>                           # CI OK + Comparator green on main
grep -rn "kapla build\|8080\|upload a picture" --include=*.md .   # no hits
lake exe kapla check web/examples/house.json  # accepted
```

- [ ] Fresh-clone dry run (B1) done after the last merge.
- [ ] Every 🔴 item is ticked.
- [ ] The README "What the plan guarantees" table (A1) has no row without a theorem.
