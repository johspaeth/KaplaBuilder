# KaplaBuilder: Component Split for a Team of Four

This document splits the system described in [DESIGN.md](DESIGN.md) into **four independent
components**, one per person. They share **one small contract package**, `KaplaCore`. Every
team codes only against `KaplaCore` (types, JSON formats, interfaces, mocks), so nobody is
ever blocked waiting for another team's engine.

| | Component | Owner | One-line responsibility |
|---|---|---|---|
| **A** | Physics Engine | Person A | *"Does it stand, and can a human build it?"* Verified. |
| **B** | Semantic Engine | Person B | *"What should we build, and how close are we?"* Verified score. |
| **C** | Construction Planner | Person C | *"Which blocks go where, and in what order?"* Search; untrusted. |
| **D** | Web & Integration | Person D | *"Wire it up and show it."* CLI, webpage, fixtures, CI. |
| ⚙ | `KaplaCore` (shared contract) | all four, stewarded by D | data types, JSON, basic geometry, engine interfaces, mocks |

---

## 1. System overview

```mermaid
flowchart LR
  user(["User<br/>prompt / image · N blocks · profile"])

  subgraph D["D · Web & Integration"]
    orch["Orchestrator<br/>(kapla build / serve)"]
    web["Webpage Renderer"]
  end

  subgraph B["B · Semantic Engine"]
    interp["interpret<br/>prompt/image → TargetSpec<br/>(Claude)"]
    score["score · bound · verdict<br/>(verified)"]
  end

  subgraph C["C · Construction Planner"]
    plan["search · motifs · roofs<br/>sequencing · repair"]
  end

  subgraph A["A · Physics Engine"]
    check["check / certify<br/>stability + Human Model<br/>(verified)"]
  end

  user --> orch
  orch -- "Request" --> interp
  interp -- "TargetSpec" --> orch
  orch -- "PlanRequest + engine handles" --> plan
  plan -- "BuildPlan" --> check
  check -- "PhysicsReport<br/>(ok | diagnostics)" --> plan
  plan -- "Structure" --> score
  score -- "ScoreReport" --> plan
  plan -- "ranked candidates" --> orch
  orch -- "certify best" --> check
  orch -- "RenderInput" --> web
  web --> out(["index.html"])

  classDef a fill:#fde2e2,stroke:#c0392b;
  classDef b fill:#e2f0fd,stroke:#2471a3;
  classDef c fill:#e8f8e2,stroke:#239b56;
  classDef d fill:#fdf5e2,stroke:#b9770e;
  class check a; class interp,score b; class plan c; class orch,web d;
```

**Key rule:** the Planner never imports the Physics or Semantic packages. It receives them
as **interface values** (`PhysicsEngine`, `SemanticEngine`) defined in `KaplaCore`. During
development, C plugs in the mocks; in production, D plugs in the real engines.

---

## 2. Package dependencies

Each component is its own Lake library. Arrows mean "imports". The graph has no cycles,
and the only shared node is `KaplaCore`.

```mermaid
flowchart TB
  core["⚙ KaplaCore<br/>types · JSON codecs · rational geometry basics<br/>engine interfaces · mocks"]

  phys["A · KaplaPhysics<br/>contacts · LP · certificates<br/>Human Model rules · proofs"]
  sem["B · KaplaSemantics<br/>Shape DSL · voxelizer · IoU · bound<br/>Claude client · image silhouette"]
  plan["C · KaplaPlanner<br/>motifs · roofs · layer planner<br/>sequencer · repair · scale search"]
  web["D · KaplaWeb<br/>HTML builder · SVG · three.js page<br/>report · HTTP server"]

  app["D · kapla (executable)<br/>Main.lean — the only place<br/>where real engines meet"]

  phys --> core
  sem --> core
  plan --> core
  web --> core
  app --> phys
  app --> sem
  app --> plan
  app --> web
```

| Library | May import | Must **not** import |
|---|---|---|
| `KaplaCore` | Lean core, Batteries | anything else in this repo |
| `KaplaPhysics` (A) | `KaplaCore`, the physics rules `KaplaSpecs.PhysicsRules.*` | Semantics, Planner, Web, the rest of `KaplaSpecs` |
| `KaplaSemantics` (B) | `KaplaCore` | Physics, Planner, Web |
| `KaplaPlanner` (C) | `KaplaCore` | Physics, Semantics, Web |
| `KaplaWeb` (D) | `KaplaCore` | Physics, Semantics, Planner |
| `kapla` exe (D) | everything | — |

D enforces this with a CI script that greps the imports.

The physics rules (what "stable", "solid" and "safe plan" mean) are human-owned, so
they live in `specs/KaplaSpecs/PhysicsRules/`. Physics imports them; the rules import only
`KaplaCore` and each other, never the engine or its proofs.

---

## 3. The contract: `KaplaCore`

This is the only thing all four people must agree on. It is frozen as **v0.1 in week 1**.
After that, changes go through a PR reviewed by all four, and additive changes are
preferred.

```mermaid
classDiagram
  direction LR

  class Pose {
    +Upright up
    +Rot rot
    +Q3 center
    +corners() List~Q3~
    +contains(Q3) Bool
  }
  class Step {
    +List~Pose~ blocks
    +Grip grip
    +Approach approach
    +String phase
  }
  class BuildPlan {
    +List~Step~ steps
    +blockCount() Nat
  }
  class HumanModel {
    +Q epsRel
    +Q eAbs
    +Q press
    +Nat hands
    +Q clear
    +Q muSafe
    +GripModel grip
  }
  class TargetSpec {
    +Shape shape
    +Option~Mask~ silhouette
    +List~PartTag~ parts
  }
  class PhysicsReport {
    +Bool ok
    +List~Diagnostic~ diagnostics
    +Option~List Q~ slackPerBlock
  }
  class Diagnostic {
    <<enumeration>>
    Unstable(step, block)
    Slides(step, contact)
    PressTips(step, corner)
    Unreachable(step)
    Overlap(i, j)
    Clearance(i, j)
    UnevenSupports(block)
    TooManyHands(step)
  }
  class ScoreReport {
    +Q score
    +Q iou
    +Option~Q~ silhouetteIoU
    +List~PartScore~ perPart
    +VoxelDiff missingAndExtra
  }
  class Bound {
    +Q maxScore
    +Verdict verdict
  }

  class PhysicsEngine {
    <<interface>>
    +check(HumanModel, Nat, BuildPlan) PhysicsReport
  }
  class SemanticEngine {
    <<interface>>
    +interpret(Request) IO TargetSpec
    +score(TargetSpec, List~Pose~) ScoreReport
    +bound(TargetSpec, Nat) Bound
  }
  class Planner {
    <<interface>>
    +plan(PlanRequest, PhysicsEngine, SemanticEngine) IO List~Candidate~
  }
  class Renderer {
    <<interface>>
    +render(RenderInput) Html
  }

  BuildPlan *-- Step
  Step *-- Pose
  PhysicsReport *-- Diagnostic
  PhysicsEngine ..> BuildPlan
  PhysicsEngine ..> HumanModel
  PhysicsEngine ..> PhysicsReport
  SemanticEngine ..> TargetSpec
  SemanticEngine ..> ScoreReport
  SemanticEngine ..> Bound
  Planner ..> PhysicsEngine
  Planner ..> SemanticEngine
  Planner ..> BuildPlan
  Renderer ..> BuildPlan
  Renderer ..> ScoreReport
  Renderer ..> PhysicsReport
```

Contents of `KaplaCore`:
- **Data**: `Q` (= `Rat`), `Q3`, `Rot` (Pythagorean rotation, exact), `Upright`, `Pose`,
  `Grip`, `Approach`, `Step`, `BuildPlan`, `HumanModel` + profiles, `Shape` (DSL AST),
  `TargetSpec`, `Diagnostic`, `PhysicsReport`, `ScoreReport`, `Bound`, `Verdict`,
  `Request`, `PlanRequest`, `Candidate`, `RenderInput`.
- **JSON codecs** for all of the above, with round-trip tests. JSON is the format of the
  fixtures, the webpage data and the Claude output.
- **Basic geometry** that everyone needs: rational rotations, `Pose.corners`,
  `Pose.contains`, block dimensions. Physics-specific geometry (contacts, clipping,
  separating-axis tests) stays in A's package.
- **Engine interfaces** (Lean `structure`s of functions), as in the diagram.
- **Mocks**: `PhysicsMock`, `SemanticMock`, `PlannerMock`, `RendererMock` (see §5).

### Verified vs. data across the boundary

Proof-carrying types do not cross the `KaplaCore` interfaces. Only plain data does, which
keeps the components independent. The proofs come back together in exactly one place:

```mermaid
flowchart LR
  subgraph A["A · KaplaPhysics"]
    valid["def Valid H N plan : Prop"]
    cert["certify : H → N → BuildPlan →<br/>Except (List Diagnostic) {p // Valid H N p}"]
    sound["theorem certify_sound"]
    chk["check := report of certify<br/>(implements PhysicsEngine)"]
  end
  subgraph B["B · KaplaSemantics"]
    iou["def iou spec + scoreImpl<br/>theorem scoreImpl_eq_spec"]
    bnd["theorem iou_le_bound"]
  end
  subgraph D["D · kapla Main.lean"]
    final["Final output type:<br/>{p // Valid H N p} × verified score × proven bound"]
  end
  cert --> final
  iou --> final
  bnd --> final
  chk -. "data only" .-> core["KaplaCore.PhysicsEngine"]
```

---

## 4. One run, end to end

```mermaid
sequenceDiagram
  autonumber
  actor U as User
  participant O as Orchestrator (D)
  participant S as Semantic Engine (B)
  participant P as Planner (C)
  participant Ph as Physics Engine (A)
  participant R as Renderer (D)

  U->>O: prompt / image, N, profile
  O->>S: interpret(request)
  S-->>O: TargetSpec
  O->>S: bound(target, N)
  S-->>O: Bound (proven ceiling + verdict)
  O->>P: plan(PlanRequest, physics, semantics)
  loop search & repair (untrusted)
    P->>Ph: check(H, N, BuildPlan)
    Ph-->>P: PhysicsReport (ok or diagnostics)
    P->>S: score(target, blocks)
    S-->>P: ScoreReport (+ per-part / voxel diff)
  end
  P-->>O: ranked candidates
  O->>Ph: certify(H, N, best)
  Ph-->>O: {p // Valid H N p}
  O->>S: score(target, p)
  S-->>O: verified ScoreReport
  O->>R: render(RenderInput)
  R-->>U: index.html (3D view, step cards, report)
```

---

## 5. How each person works independently: mocks and golden fixtures

```mermaid
flowchart TB
  subgraph F["fixtures/ — shared golden JSON (part of the contract)"]
    fbp["plans/*.json<br/>tree_1block · tower_10 · overhang_bad<br/>rotated_stack · aframe_2hands · bridge_uneven"]
    ftg["targets/*.json<br/>tree · duck · house · gable_roof · castle"]
    fpr["physics_expected/*.json<br/>ok / diagnostics per plan"]
    fsr["score_expected/*.json<br/>score + bound per (plan, target)"]
  end

  subgraph mocks["KaplaCore.Mocks"]
    pm["PhysicsMock<br/>simple centre-of-mass rule, unverified"]
    sm["SemanticMock<br/>returns fixture target · bounding-box IoU"]
    plm["PlannerMock<br/>returns fixture plans"]
  end

  A["A · Physics"] -- "must reproduce" --> fpr
  fbp --> A
  B["B · Semantics"] -- "must reproduce" --> fsr
  ftg --> B
  fbp --> B
  C["C · Planner"] -- "develops against" --> pm
  C -- "develops against" --> sm
  ftg --> C
  D["D · Web"] -- "develops against" --> plm
  fbp --> D
  fpr --> D
  fsr --> D
```

| Person | Develops against | Proves it works by |
|---|---|---|
| A | fixture plans | reproducing `physics_expected/`, plus proofs compiling with no `sorry` |
| B | fixture targets and plans | reproducing `score_expected/`, plus proofs compiling |
| C | `PhysicsMock` + `SemanticMock` | producing plans for every fixture target that the mock accepts. Later the real engines are swapped in with zero code change. |
| D | `PlannerMock` + fixture reports | rendering a webpage for every fixture. `kapla build` runs end to end on mocks from week 3. |

Whoever finds a new interesting case adds a fixture. Fixtures are the shared language
between the teams.

---

## 6. Work packages per person

### A: Physics Engine (`KaplaPhysics`)
- **Owns**: contact detection (polygons, segments, points), polygon clipping and shrinking,
  3D separating-axis tests, the LP solver that generates force certificates, the robust
  certificates (margins, shift budgets), the friction pyramid for tilted blocks, and the
  Human Model rules H1–H9 (`Reachable`, `Clearance`, `ParallelSupportsOK`, press load
  cases).
- **Delivers**: `PhysicsEngine` implementation, `certify`, `Valid`, `certify_sound`,
  `robust_sound`.
- **Does not care about**: what the structure is supposed to look like.
- **Heaviest proof load.** A's scope is bounded by DESIGN.md §2–3.

### B: Semantic Engine (`KaplaSemantics`)
- **Owns**: the Shape DSL semantics, the voxelizer with its correctness proof, IoU,
  silhouette projection, the upper bound `iou_le_bound`, verdict bands, per-part scores
  (so the planner gets a feedback signal such as "tower missing"), the Claude client
  (text/image → `TargetSpec`, validation, retries), image decoding and silhouette mask, and
  the narration text for the report.
- **Delivers**: `SemanticEngine` implementation, proven score and bound.
- **Does not care about**: gravity.

### C: Construction Planner (`KaplaPlanner`)
- **Owns**: scale search, exhaustive search for N ≤ 4, motif library (log-cabin tower,
  round tower, spiral, wall, slab, arch, tree, **roofs**: stepped, leaning-rafter gable,
  A-frame, tipi, hip), layer planner, block-budget knapsack, the repair loop driven by
  `Diagnostic`, the sequencer (build order, 1–2-block steps, grip/approach choice, phase
  labels), and the difficulty rating.
- **Delivers**: a `Planner` implementation.
- **Does not care about**: why something is unstable. It only reads `Diagnostic`. It never
  needs to be proven correct.

### D: Web & Integration (`KaplaWeb` + `kapla`)
- **Owns**: stewardship of `KaplaCore` and the fixtures; `Main.lean` (CLI: `build`,
  `check`, `serve`); the HTML builder in Lean; three.js 3D view with step slider; step-card
  SVGs (offsets, angles, grip hints, two-hand badge); feasibility, difficulty and
  verified badges; print booklet; local HTTP server and input form; CI (build, axiom
  audit, import rules, fixture contract tests).
- **Delivers**: the webpage and the end-to-end pipeline.
- **Does not care about**: how any engine works inside.

---

## 7. Timeline with integration points

```mermaid
gantt
  title KaplaBuilder — four parallel tracks
  dateFormat YYYY-MM-DD

  section All
  Freeze KaplaCore v0.1 + fixtures v0      :crit, core, 2026-11-02, 5d
  I1 · end-to-end on mocks                  :milestone, i1, 2026-11-20, 0d
  I2 · real physics + semantics, simple plans :milestone, i2, 2026-12-18, 0d
  I3 · roofs, Neuschwanstein@200            :milestone, i3, 2027-02-05, 0d

  section A · Physics
  M1 yaw geometry + nominal checker + proof :a1, after core, 15d
  M2 robust certificates + Human Model      :a2, after a1, 25d
  M3 tilted blocks + friction (roofs)       :a3, after a2, 25d

  section B · Semantics
  Shape DSL + voxelizer + IoU + bound       :b1, after core, 15d
  Claude text frontend                      :b2, after b1, 10d
  Image + silhouette + per-part scores      :b3, after b2, 20d

  section C · Planner
  Tiny-N + towers + walls (on mocks)        :c1, after core, 15d
  Layer planner + scale search + sequencer  :c2, after c1, 20d
  Roof motifs + repair loop + knapsack      :c3, after c2, 25d

  section D · Web
  CLI + mocks wiring + CI                   :d1, after core, 10d
  Webpage 3D + step cards                   :d2, after d1, 15d
  serve + report + print booklet            :d3, after d2, 20d
```

| Integration point | What must work | Who is on the critical path |
|---|---|---|
| **I1** | `kapla build` → webpage, using all mocks | D (C delivers early plans) |
| **I2** | Real `check`/`certify` (yaw-only, robust) + real score/bound; planner builds towers and walls; 1-block tree/duck case | A, B |
| **I3** | Tilted blocks + friction; roof motifs; Neuschwanstein@200 with conical tower roofs | A (M3), C (roofs) |

Real-world calibration of the HumanModel (DESIGN M10) is a shared activity after I2.
Everyone builds generated blueprints by hand.
