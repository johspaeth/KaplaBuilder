# KaplaPhysics

Owner: A. Scope: see [docs/WORKSPLIT.md](../docs/WORKSPLIT.md).

- Build: `lake build KaplaPhysics`
- Files: `KaplaPhysics.lean` (root, imports the rest) and `KaplaPhysics/*.lean`.
- May import: `KaplaCore`, and the physics rules in `specs/KaplaSpecs/PhysicsRules/`.
- Rules and CI: see the [README](../README.md).

## What is here

Rules come from [spec/physics-rules.md](../spec/physics-rules.md). Rule IDs (P1, C3, S2, ...)
appear in the docstrings.

The rules in Lean are human-owned, so they are not in this folder. They are in
[specs/KaplaSpecs/PhysicsRules/](../specs/KaplaSpecs/PhysicsRules/), next to the theorem
statements in [specs/KaplaSpecs/Physics.lean](../specs/KaplaSpecs/Physics.lean). To change
what a theorem means, you must change `specs/`, which needs a spec review.

| File in `specs/KaplaSpecs/PhysicsRules/` | What it says | Trusted? |
|---|---|---|
| `Geometry.lean` | a plank is Core's block (`KaplaCore.Pose`: upright, turn, centre); allowed turns (`Rot.Allowed`, B6); what a plank covers seen from above; `Plank.at` for the six axis poses (W1–W3, B1–B6) | yes: read it |
| `Rules.lean` | `SharesArea`, `Overlap`, `WellFormed` (P1–P3, B6), `RestsOn` and `InPatch` (C1–C4), `Push`, `Balanced`, `Stable` (F1–F4, S1–S4), placement errors, `SolidWithin`, `Meets` and `KeepsGaps` (R1–R3, R5), `PlanOptions` and `SafePlan` (K1, K4, K5), `StraightPath` and `Reachable` (K2, K3), `StableWithFriction` (F3) | yes: read it |
| `Tower.lean` | the square tower of example E8, and `turnedTower` (E19) | yes: read it |
| `Column.lean` | the simple centre-of-mass rule for a single column (section 7) | yes: read it |
| `Examples.lean` | builds E1–E19; proofs from the rules alone that E1 stands, that E4 falls, that E3 is not solid, that E16 and E18 are not well-formed, and a few more | checked by Lean |

Core's `KaplaCore.Pose`, `Rot`, `Rot.comp` and `Rot.apply` (in `core/KaplaCore/Block.lean`)
are part of this trusted surface: a plank **is** a core block.

| File in this folder | What it does | Trusted? |
|---|---|---|
| `Affine.lean` | sides of a plank as expressions `a x + b y + c`; weighted sums of sides (`Cert`, `Sep`) that show two planks share no area, or that an expression is at least zero on a patch; untrusted helpers that cut out the patch polygon | the checks are proven |
| `Contacts.lean` | checks for `SharesArea`, `RestsOn`, `Overlap`, `WellFormed`, `Meets`, each with a soundness proof | checked by the proofs |
| `Solver.lean` | exact-fraction simplex; proposes pushes or a fall motion | no: every proposal is checked |
| `Robust.lean` | `SolidCertificate`: loads whose points move with the errors | checked by the proofs |
| `RobustSolver.lean` | proposes a solidity certificate (an LP, then a top-down pass) | no: checked |
| `Reach.lean` | K3 checker: tries nine straight paths (from above; along `x` and `y`; along the plank's own length and width) plus the drop | checked by the proofs |
| `Engine.lean` | `stabilityAnswer`, `checkFall`, `verdict` (solid / risky / falls), `checkPlan`, column checks | checked by the proofs |
| `CoreAdapter.lean` | `coreCheck` and `physicsEngine`: the engine behind `KaplaCore.PhysicsEngine` | checked by the proofs |
| `Sums.lean`, `RobustProofs.lean`, `ColumnProofs.lean`, `TowerProofs.lean`, `TurnProofs.lean`, `Proofs.lean` | the proofs (main statements in `specs/KaplaSpecs/Physics.lean`) | checked by Lean |
| `Examples.lean` | the engine on E1–E19 as `#guard`s; more instances of the theorems; bad answers the rules reject | tests |

## Main theorems

- `stabilityAnswer_stable_sound`: answer "stable" ⇒ `Stable b` (property 1).
- `stabilityAnswer_falls_sound`: answer "falls" ⇒ `¬ Stable b` (property 2). The solver
  hands over a motion of the planks that lifts no plank into its support yet lowers the
  total weight; the checker confirms it, and the proof shows no balancing pushes can exist.
- `verdict_solid_sound`: verdict "solid" ⇒ stable for **every** combination of placement
  errors up to ε (property 3). The certificate gives each contact a fixed load at a point
  that moves with the errors; the proof shows that point stays in the real contact patch
  (F4) and that the loads balance every plank for every error. "Solid" includes `0 ≤ ε`: the
  engine never answers "solid" for a negative error, and `verdict_solid_stable` shows a
  solid build also stands at the exact positions.
- `verdict_risky_sound`, `verdict_falls_sound`: "risky" ⇒ stable at the exact positions;
  "falls" ⇒ not stable.
- `checkPlan_sound`: an accepted plan has at most N planks, and after every step it is
  well-formed at the planned positions and **solid** (property 4, K4). With the clearance
  check on (`PlanOptions.clearance := true`; off by default) it also **keeps its gaps**
  (`KeepsGaps`): two planks that do not touch in the plan are never pushed into each other
  by errors up to ε. The checker (`clearCheck`) asks for weights on the planks' sides that
  show a gap no error up to ε per plank can close. Planks that touch in the plan (`Meets`: side by side, end to end, one on
  another) are left out, as R5 says: a plank pushed against its neighbour moves with it.
  So walls of touching planks pass; only near misses (a gap above 0 and below 2ε) fail.
- `reachDir_sound`, `hardToReach_nil_sound`: a step the checker does not flag can be put
  in place along a straight path from far away plus a drop of `h > 0`, never sharing inside
  space with a placed plank (property 5, K3). Touching a placed plank on the way (sliding
  along a face, brushing an edge) is allowed, as K3 now says. A gap `h ≤ 0` flags every step. Flagged
  steps are warnings only.
- `column_stable_iff`: for a single column, `Stable` holds exactly when at every level the
  combined centre of mass of everything from that level up is over the patch below it
  (property 6). Both directions are proven, so the definition of `Stable` is checked
  against the simple rule a reviewer can verify by hand.
- `stable_withFriction`: a build that is stable without friction is stable with any
  friction coefficient μ ≥ 0, in a model with sideways contact pushes and all six balance
  conditions (property 8, F3).
- `squareTower_safe`: building the square tower (E8) level by level is safe at **every**
  height `n`: well-formed, still well-formed with errors, and solid after every step, for
  placement errors up to any ε from 0 to 1/2 (3.9 mm) (property 9). The proof gives explicit pushes for every error: each
  corner of the tower carries its loads straight down, and every load point stays in a
  small core square at its corner that every contact patch there contains.
- `turnedTower_safe`: the same for the square tower turned as a whole by any allowed turn
  `r` (B6: about 30°, 45°, 60°, ...), for errors up to ε with `ε (|cos r| + |sin r|) ≤ 1/2`
  (for 45°: ε up to about 0.35, 2.8 mm). The proof turns the square tower: turning a whole
  build keeps contacts and balance, and an error of ε along `x` and `y` in the turned
  build is an error of at most `ε (|cos| + |sin|)` in the unturned one.
- `checkPushes_sound`, `fallCertificate_sound` (a motion that passes `checkFall`),
  `solidCertificate_sound`: the checkers are right on their own, for a certificate from
  any source. `not_stands_and_falls`: no build gets both a passing push set and a motion
  that passes the fall check.
- `covers_of_contains`, `contains_of_inside`: what the physics rules call "under the plank"
  agrees with Core's `Pose.contains` (property 7). Core leaves out some faces of a block so
  that touching blocks share no point; the two theorems show the difference is only on
  the faces.
- `coreCheck_ok_sound`: when `coreCheck opts` says a core plan is `ok`, every step places 1 to
  `hands` blocks, and the blocks, one after the other, are a safe plan (with `opts`) for
  placement errors up to `epsRel` (K4, K5). So every turn in it is allowed (B6). With the planner's
  `planPure_sound` (its candidates are `ok`), every candidate is a safe plan.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only. No `opaque` contracts.

The statements mention `verdict` and `checkPlan`, which call the solvers, so the solvers
are in the spec surface. Nothing depends on them being right: a wrong proposal only gives
"risky" or "unknown".

**Cautious, never optimistic (R3).** "Risky" means "not shown to be solid". A solid build
can get "risky" when no certificate of the simple kind exists (fixed loads per contact).
A "solid" verdict is always right. For the "risky" examples E3, E7 and E9 we also prove
that they are not solid, each with an explicit error of at most 2 mm that makes it fall
(`e3_not_solid`, `e7_not_solid`, `e9_not_solid`).

Placement errors are taken over the whole R1 box (every plank within ε along `x` and `y`).
R5 only removes some of these errors, so "solid" here implies solid under R5.

## Differences from KaplaCore, and how the adapter settles them

`KaplaPhysics.physicsEngine : KaplaCore.PhysicsEngine` (`CoreAdapter.lean`) replaces
`physicsMock`; `app/Main.lean` (owner D) has to pass it to the planner.
`coreCheck_ok_sound` says what its `ok` means.

- **Steps.** Core places 1–2 blocks per step (`hands`); K1 places one plank per step. The
  adapter checks the build after every block, in list order. This is cautious: a step
  whose blocks stand only together is refused.
- **Blocks are planks.** The physics rules use Core's `Pose` directly, so there is no
  conversion. `Plank.at` (place by the lowest corner) is only a helper for examples.
- **Turns.** Core's `Rot` allows any exact turn; B6 allows quarter turns and turns within
  about 0.3° of 30°, 45° and 60° (and their multiples). Any other turn makes the plan not
  `ok` (it is not well-formed). Core's `Rot.deg30`, `Rot.deg45`, `Rot.deg60` are allowed.
  Blocks always lie with a face down (B5); a block standing on a corner or an edge is not
  modelled.
- **Placement error: R1 is the model (team decision).** The two models measure error
  differently, even though both defaults are 10/39 (2 mm):
  - physics (R1, `SmallShift ε`): every plank lands within ε of its own planned spot,
    along `x` and along `y`;
  - Core (`HumanModel`): `epsRel` is the error against the block(s) a block rests on, and
    `eAbs` (default 50/39 = 5ε) caps the total drift from the plan. Errors can add up from
    level to level (docs/DESIGN.md §2.2).

  The adapter uses ε = `epsRel` with R1. So `ok` does **not** cover all of Core's errors.
  Example: three planks stacked straight up, shifted along `x` by 0, ε and 2ε. Core allows
  this, but the top plank is 2ε from its own spot, so R1 excludes it.

  The other choices were tried and refused: with ε = `eAbs` (or ε growing with the number of
  levels, which would cover Core's model), the solid check passes E2 and the square tower
  only up to one level (measured: ε = 30/39 already fails both), so the planner could build
  almost nothing. Core's `HumanModel` docs should be brought in line with R1 (a change to
  `core/`, for the team).
- **Clearance.** `physicsEngine` uses the default `PlanOptions` (clearance off).
  `kapla check --clearance` uses `coreCheck { clearance := true }`: blocks that touch in
  the plan are fine, and blocks with a gap below 2ε get a `clearance` diagnostic. Core's
  `clear` is not used.
- **Reach.** K3 gives `unreachable` warnings, which do not change `ok`.
- **Not used:** `eAbs`, `press`, `clear`, `muSafe`. The engine never reports `slides`,
  `pressTips` or `unevenSupports`, and `slackPerBlock` is `none`. Core has no diagnostic for
  "risky" or "this turn is not allowed", so both are reported as `unstable step block`
  for the block where things first go wrong.

## Not done yet

- K3 tries only nine directions; a plank reachable only along another slanted line is
  flagged.
- F4 now lets a push act anywhere in the contact patch, not only at its corners. For a
  patch without holes (all patches here: the overlap of two rectangles) the two are the
  same: a push inside the patch equals pushes at its corners that add up to it.
- Speed: the engine first tries fast top-down solvers (one small LP per plank) and uses
  the global LPs only for builds of at most 40 planks. Measured with the interpreter on a
  200-plank square tower: exact check 1.4 s, solid verdict 2.4 s. `checkPlan` checks
  every prefix separately, so a 200-step plan takes minutes; reusing work between steps
  is still to do. For large builds that fall, the engine looks for a fall certificate that
  moves only the planks at and above the place where the top-down solver got stuck (the
  rest stay still, like the ground); it can still answer "unknown" if that is not enough.
- Checking the robust solver's output inside the Lean kernel is slow beyond one plank, so
  the kernel examples for E2 and E6 check a written-out certificate.
