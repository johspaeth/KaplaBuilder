# Step 7: the website. Start here.

Rulings from 1 Nov 2026. Read this first in a new chat, then `semantics/CLAUDE.md`. Do not reopen
what is ruled here. The person wants short answers without jargon, and decisions listed and ruled
on before anything new is written.

## What we are building

One local website. You run `kapla serve` and open one address on your own computer.

1. A chat window. You describe a model ("an egg"). Claude makes the bubbles and the 3D view shows them.
2. You change it in the chat ("make the ears longer") and the view changes by itself.
3. You save models, open saved ones, change them and save again.
4. You choose a planner, give a block limit and press "Generate proposal". The planner gives one plan.
5. The page then shows its blocks with the bubbles, and a slider that adds the blocks one step at a
   time.
6. The plan shows two separate badges and its scores. "Stands" comes from physics, which runs by
   itself on each plan. "Accepted" comes from the scorer.

## Where the code goes

| Folder | What goes there |
|---|---|
| `web/` | The chat window, model list, planner choice, score panel, badges, slider |
| `semantics/` | `Claude.lean` (`interpret`, `refine`, retries) and the real `SemanticEngine` in `Engine.lean` |
| `app/` | `kapla serve`: the server, the list of planners, reading the key, saving models |
| `models/` | Saved models, as files on your computer. New, at the top of the repo |
| `planner/`, `core/` | No change. No new Core contract is needed |

Branch: a new branch `app/chat-ui`, from the latest `main` merged with `feature-semantics` if these
notes have not reached `main` yet. It may change `app/`, `web/`, `semantics/` and `models/` (ruled).
The person owns `app/` and `web/` for this work.

## How it connects to what exists

- Make and change a model: `SemanticEngine.interpret` and `refine`.
- Show bubbles: `KaplaViewer.show(model, height)` in `web/KaplaWeb/Page.lean`. It does not yet accept
  blocks: today the blocks and the slider are fixed when the page is made. This is the main gap.
- Save and open: `encode` and `decode` in `semantics/KaplaSemantics/Json.lean`.
- Plan: `Planner.plan` with a `PlanRequest` from `TargetSpec.ofBubbles`.
- Physics: `runPhysics` and `physicsLines` in `app/Main.lean`.
- Scores: `scoreReport` and `reportToJson` in `semantics/KaplaSemantics/Engine.lean`.
- A `Candidate` holds the blocks, the physics report and the score report. `ScoreReport.height` says
  which height the planner chose, so the page draws the bubbles at that height for that plan.
- New: a small set of requests between the page and the server, written in `web/README.md`. Roughly
  `POST /chat`, `GET /models`, `POST /models`, `POST /plan`, `POST /check`.

## Rulings

- **Server:** Lean's `Std.Http.Server`, no Python. See the test results below.
- **Height:** you never type one. The planner chooses it. Before planning, the bubbles show at
  height 1 with axes from 0 to 1. The model file stays at height 1.
- **Updates:** the chat tells the picture to redraw when a new model arrives. No polling and no
  buttons to load a model.
- **Chat memory:** Claude remembers the conversation while the page is open. It is not saved to disk.
- **API key:** `kapla serve` reads `semantics/dev/.env` at startup. With no key the site still runs
  and the chat says the key is missing. Never print the key or ask for it in the chat.
- **Too-small bubbles:** listed next to each plan, because they depend on the height, with an action
  to remove one. Never run `normalize` after removing one.
- **One plan (replaces "several plans", 1 Nov 2026):** the planner's output is one plan, shown as soon
  as it is ready. The website asks for it with `maxCandidates := 1` and uses only the first. There is
  no list and no `POST /check`.
- **Planner list (1 Nov 2026):** the website uses `KaplaPlanner.strategies`. Johannes writes the planners
  `ai` and `ai-unchecked`. Until they merge, `app/Main.lean` adds `standInTower`, website only. Remove it then.
- **Clearing:** a new model on screen (opened, from the chat, or a bubble removed) clears the proposal.
- **Gaps:** the website uses the physics engine's default setting.
- **Block limit:** a number box, starting at 40.
- **Bad answers from Claude:** retry twice, then show the error in the chat and keep the current
  model on screen. The prompt gives the vertical reference in ROADMAP step 7.
- **JSON:** reject duplicate labels. Keep ignoring unknown fields (`egg.json` has `comment`). Reject
  huge exponents like `1e999999` before computing.
- **Saved models:** plain files in `models/`. The website does not use git; the person commits a file
  to share it. Copy the egg and the bunny there to start. `semantics/fixtures/` stays for tests.
  Ask before overwriting a name. Clean the file name so saving stays inside `models/`.
- **Badges must be honest:** "stands" means it passes the verified physics rules. Say that gaps are
  not checked when clearance is off.
- **Planner:** do not wait for PR #31. Build against the `Planner` contract with a stand-in, and
  connect the real one when it merges. Johannes owns the planner.
- **`FastScore` in PR #31:** no test comparing it with the real scorer, because planners will differ.
  No review needed from the person.
- **Fill rule:** not changing it now. The person's view is that physics stops a floor and a lid from
  existing. Johannes's PR #31 notes (`planner/DESIGN.md` §8) report plans of this kind, so look at
  real plans on the page. A lid can stand on a few thin supports.
- **Theorem statements** go in `specs/` when the proofs are done. Johannes runs Comparator.

## Build order

1. Server, page requests and saved models, with bubbles only. Needs no key and no planner.
2. Chat with Claude (`interpret`, `refine`). Tell the person to add the key first.
3. Generate proposal button, blocks, slider, scores and badges, with a stand-in planner.
4. Connect the real planners when Johannes merges them.

Done when: "an egg" shows in 3D, "make it taller" changes it, you save it, open it again, plan it,
slide through the blocks, and see the badges and scores.

## Lean server: what was tested (Lean 4.35, compiled, 1 Nov 2026)

HTML and JSON replies with the right content type, a 300 KB POST body, a call to `curl` from inside a
request, and quick replies while slow or heavy requests ran, including 20 heavy ones at once. A
browser was not tried against it.

The docs in `Std/Http.lean` are wrong in one place: use `req.line.uri`, not `req.head.uri`. A minimal
handler:

```lean
import Std.Http
open Std Async
open Std Http Server

structure H

instance : Handler H where
  onRequest _ req := do
    let path := toString req.line.uri
    let body : String ← req.body.readAll
    Response.ok |>.text s!"{path} {body.utf8ByteSize}"

def main : IO Unit := Async.block do
  let addr : Net.SocketAddress := .v4 ⟨.ofParts 127 0 0 1, 8000⟩
  let server ← Server.serve addr H.mk
  server.waitShutdown
```

## Traps

- A second `main` inside a library breaks `lake check`. Tools with a `main` go outside the library
  (`semantics/dev/`, `web/dev/`) and call a library function.
- Before a PR, run `semantics/dev/ci.sh` (Docker) as well as `make check`. It catches what macOS cannot.
- PR #31 says a physics check still running at the time limit keeps the process alive. This matters
  in a server that runs for a long time. Planning takes up to 30 seconds, so the page needs a
  "working" state.
- CI does not run browser code. Test the page in a real browser and say so in the PR.
