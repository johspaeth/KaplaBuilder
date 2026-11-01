# KaplaBuilder: Design Plan

Goal: take a description or picture plus a block count N, and produce a **verified** Kapla
blueprint that **a real person can actually build**. Such a blueprint uses at most N blocks.
It stays standing after every build step, **even when the builder's hands are imprecise**.
Every block can be put in place by hand. It looks as much like the target as possible. It
comes with a 3D view and step-by-step instructions on a webpage. Everything is written in
Lean 4.

---

## 1. Core idea: untrusted generator, verified checker

```
 description / image ──► [Frontend: Claude] ──► TargetShape                 (untrusted)
                                                   │
 N blocks, HumanModel ──► [Planner + LP]   ──► Blueprint + certificates     (untrusted)
                                                   │
                          [Checker]        ──► { bp // Valid H N bp }       (VERIFIED)
                                                   │
                          [Scorer]         ──► score + fits the target      (VERIFIED)
                                                   │
                          [Render]         ──► Lean-generated webpage
```

Everything that searches is untrusted: the planner, the LP solver, the build-order
sequencer and Claude. Each one only *proposes* a blueprint together with **certificates**,
which are concrete numbers such as contact forces. A small checker with a **soundness proof**
accepts or rejects the proposal. The pipeline can only output a value of type
`{bp // Valid H N bp}`. Bugs in the untrusted parts can make results worse. They cannot
produce a blueprint that collapses, or one that a human cannot build.

---

## 2. Physical feasibility is not enough: the Human Model

Many structures stand in theory but cannot be built in practice. Each failure below gets
an explicit rule in the verified spec:

| # | Failure in real life | Example | Rule (verified) |
|---|---|---|---|
| H1 | **Knife-edge balance**: works only when placed perfectly | an overhang exactly at the tipping point | robust equilibrium under placement error ε (§2.2) |
| H2 | **Accumulated drift**: errors add up over many layers | a 60-layer tower whose top is more than one block thickness off, or a bridge between two tall pillars that no longer line up | per-contact relative error + absolute drift cap (§2.2) |
| H3 | **Order-dependent stability** | a cantilever that only stands once its counterweight is on | every build step is checked, never only the final state |
| H4 | **The press of placing** | the hand presses the new block down and the overhang below tips | an extra load case: press force P at any point of the new block (§2.3) |
| H5 | **Unreachable placement** | a block that must go into a closed pocket, or under an overhang | hand access check: the block plus fingers can be lowered or slid into place (§2.4) |
| H6 | **Tight fits** | a gap that is exactly one block wide | no near-misses: gaps are either 0 (blocks touch by design) or at least the clearance c |
| H7 | **Needs more hands than a person has** | A-frame rafters that only stand as a pair | a step places at most `hands` blocks at once (default 2) |
| H8 | **Uneven parallel supports**: a block resting on two separate stacks rocks if their real heights differ | a bridge over pillars built from different block mixes | equal-composition rule for parallel support paths (§2.5) |
| H9 | **Leaning blocks slide** | roof rafters that slip on smooth wood | friction with a safety margin (μ_safe < μ_real), plus margin on the friction cone (§3) |

### 2.1 HumanModel parameters

```lean
structure HumanModel where
  εrel   : ℚ    -- max error of any corner of a block, measured against the block(s) it rests on
  eabs   : ℚ    -- max drift from the plan (the builder corrects anything larger by eye)
  θtilt  : ℚ    -- max angular error of a leaning block (as a rational tangent)
  press  : ℚ    -- downward press while placing, in block weights
  hands  : Nat  -- max blocks placed in one step
  clear  : ℚ    -- minimum gap between blocks that don't touch by design
  μsafe  : ℚ    -- friction coefficient assumed (wood on wood is about 0.4–0.5 in reality)
  grip   : GripModel
```

| εrel | eabs | press | hands | μsafe |
|---|---|---|---|---|
| 10/39 | 50/39 | 0.5 | 2 | 0.3 |

The defaults are educated guesses. Milestone M10 **calibrates them on real builds**: build
test structures, measure the actual placement errors, and see what collapses.

### 2.2 Robust stability (H1, H2)

The perturbation model works as follows. The builder places each block `b` so that every
point of it lands within **εrel of its intended position relative to its supports**, and
also within **eabs of its absolute planned position**. Two blocks `i` and `j` that touch
can therefore be misaligned against each other by at most

  `r_ij = εrel` if `j` rests only on `i`,
  otherwise `min(εrel + ρ(supports of j), 2·eabs)`,

where `ρ` is the largest relative offset between the separate supports, computed along the
support graph. Measuring error relative to the block below is the crucial choice. A naive
absolute-margin rule would be either unsound, because drift accumulates with height, or
hopelessly strict, because 60 layers × 10/39 is more than 15 block thicknesses.

The checker cannot test infinitely many perturbations. The planner therefore supplies a
**robust certificate** for the planned (unperturbed) structure, consisting of:
- non-negative contact forces that put every block in equilibrium;
- for each contact `c` between a lower block `i` and an upper block `j`, a margin `m_c`.
  Every point where a force acts must lie inside the contact polygon *shrunk by `m_c`*;
- **shift budgets** `σ_c`, computed from the top down. They bound how far the forces under
  block `j` must move to make up for the tipping effect of its misaligned loads above:

  `σ_below(j) = ( Σ_{c' above j} F_c' · (r_c' + σ_c') ) / W_j`  (W_j = total load carried by j)

The checker verifies `m_c ≥ r_c + σ_c` exactly, in ℚ. The main theorem is
**`robust_sound`**: if this check passes, then **every** perturbation the HumanModel allows
still has an equilibrium. The proof sketch has three parts:
1. A rigid motion moves each point of a contact by at most `r`. The contact polygon shrunk
   by `r` therefore stays inside the real contact. (For any point `x`, the disc of radius
   `r` around `x` maps to a disc that still contains `x`.)
2. The forces keep their size. Each force moves with the block above it and then shifts by
   `σ`.
3. Force balance is unchanged. A block's own rotation drops out of its moment balance,
   because its own forces and its own centre of mass turn with it. The only moment left
   over comes from the relative misalignment of the blocks resting on it, and the shift
   budget absorbs it.

This holds for horizontal contacts with any rotation about the vertical axis. For tilted
contacts, an extended version (M9) adds friction-cone margins.

The shift budgets also show how drift is damped. The leftover moment is divided by the
total load `W_j` and weighted by how much load sits above. Tall stacks therefore need
margins of about εrel, not about `height × εrel`. This matches the experience that a
careful builder can stack Kapla very high.

**Backup**: the web page also runs a **perturbation test**. It samples random admissible
perturbations and re-checks each one exactly. This test is not part of the proof. It catches
mistakes in the spec and supports the calibration in M10.

### 2.3 Placement press (H4)

At each step k, the structure must stay robustly stable with an extra downward load
`press` acting anywhere on the top of the newly placed block(s). For each prefix, the set
of loads that still allow equilibrium is convex. Checking the **corners of the top face**
therefore covers every point in between (a lemma: the loads that work form a convex set).
That is about 4 extra certificates per step.

### 2.4 Hand access (H5, H6, H7)

- **GripModel**: two finger pads, each about 2.3 × 2.6, on opposite faces of the block. The
  allowed grips are the long sides, the short ends, or the top end of an upright block.
- **Approach**: the block is lowered straight down from above, or slid in horizontally
  along one axis. The space swept by the block and the fingers, from outside the structure
  to the final position, must not hit any block already placed. The check is decidable: a
  separating-axis test on the swept prisms, done exactly in ℚ.
- The **certificate** names the grip and the approach direction for every step. The web page
  uses them for the hand hint ("hold at the ends, lower from above").
- **Clearance**: any two blocks that don't touch in the plan are at least `clear` apart. This
  rules out slots exactly one block wide.
- **Hands**: a step places 1 to `hands` blocks at once. The structure only has to be stable
  after the step, not halfway through it. A two-block step is how real builders set up an
  A-frame.

### 2.5 Parallel supports (H8)

Suppose a block rests on two or more support paths that don't share a block, apart from
the ground. Then the blocks in those paths must stack to the same height **in the same way**:
the same number of flat, on-edge and upright layers. Their manufacturing errors are then
equal on average, and wood's give absorbs the remaining tiny fraction of a block thickness. This is a
decidable rule and an explicit modelling assumption. It is the honest alternative to
pretending that heights are exact.

---

## 3. Physical model (the trusted spec)

- **Block**: a rigid, uniform-density cuboid of 15 × 3 × 1, with
  weight 1. All lengths are exact ℚ, and one unit is one block thickness.
- **Pose**: a rotation matrix `R` that is a **product of Pythagorean rotations**, so every
  entry is rational and the matrix is exactly orthogonal, plus a centre in ℚ³.
  - **v1 (M1–M2)**: rotation about the vertical axis only, at any angle, combined with
    lying flat, standing on edge or standing upright.
  - **v2 (M3, roofs)**: tilted poses. The tilt is a rotation about a horizontal axis by a
    Pythagorean angle, such as 3-4-5 → 36.87° or 20-21-29 → 46.4°, and these angles are
    dense.
  - With rational rotations, everything stays in ℚ: corners, face normals, contact
    polygons, shrunk polygons (convex polygons whose sides point in rational unit
    directions) and the separating-axis tests (cross products of rational vectors).
- **Contacts**: a face of one block, or the ground, touching a face, edge or corner of
  another block. Accordingly a contact is a convex polygon, a segment or a single point,
  each computed exactly. Contacts between side faces are counted only if the certificate
  uses them. Ignoring a contact is always sound.
- **Forces**: at each contact corner, a normal force `n ≥ 0`. For a non-horizontal contact
  there is also friction, modelled by a k-sided pyramid lying **inside** the friction cone
  with coefficient μsafe. Using an inner approximation is conservative, so it is sound. The
  result is still a linear program over ℚ.
- **Stability ⇔ equilibrium exists** (Heyman's safe theorem). This assumes that contacts
  can only push, never pull, that blocks never crush, and that no friction beyond μsafe is
  needed. With horizontal contacts and gravity only, friction is never needed.
- **Equilibrium per block** consists of 3 force equations and 3 moment equations. The
  checker verifies them exactly with the rational forces from the certificate.

```lean
def Equilibrium (s : Structure) (loads : List Load) : Prop :=
  ∃ f : ContactForces s, f.admissible μsafe ∧ ∀ b ∈ s.blocks, balance s loads f b

def RobustStable (H : HumanModel) (s : Structure) (loads) : Prop :=
  ∀ g, Admissible H s g → Equilibrium (s.perturb g) loads

def Step := List Pose            -- 1 ≤ length ≤ H.hands

def Valid (H : HumanModel) (N : Nat) (steps : List Step) : Prop :=
  (steps.join.length ≤ N) ∧ NonOverlap steps.join ∧ Clearance H steps.join ∧
  ParallelSupportsOK steps.join ∧
  ∀ k < steps.length,
    let pre := (steps.take (k+1)).join
    RobustStable H pre [] ∧
    (∀ p ∈ topCorners steps[k], RobustStable H pre [press H p]) ∧
    Reachable H (steps.take k).join steps[k]

theorem certify_sound : certify H N steps certs = some bp → Valid H N bp.val
```

The proofs must not use `native_decide`, and CI must run `#print axioms` on the
soundness path.

---

## 4. Roofs (requested by Christian)

Roofs are the main reason for allowing tilted blocks. The tilt support (M3) is therefore
now **core** rather than a stretch goal. The roof motifs are:

| Roof | Construction | Needs | Build-ability notes |
|---|---|---|---|
| **Stepped roof** (gable, hip, cone) | flat courses stepping inward by ≤ safe overhang | v1 only | works with few blocks; looks stepped |
| **Leaning-rafter gable** | 2 upright gable posts + a ridge beam; rafters lean from a **stopper ledge** on the wall top to the ridge | tilt, friction | ridge built first, then rafters one by one, one hand |
| **A-frame pairs** (no ridge) | rafters lean on each other in pairs | tilt, friction | **two-hand steps**; the first pair is the hardest |
| **Conical "tipi" roof** (round towers, e.g. Neuschwanstein) | central **king post** (stacked upright blocks); rafters in a ring lean on it, feet on a ring-shaped stopper | tilt, friction, rotation about vertical | the king post makes it buildable one block at a time |
| **Shingled roof** | flat blocks laid on rafters, overlapping like tiles | tilt, friction | top layer, mostly for looks |
| **Hip roof** | leaning rafters on 4 sides around a short ridge | tilt, friction | combines the gable and tipi patterns |

How the motifs are used:
- Each motif is parametric: span, pitch (a Pythagorean angle), overhang and number of
  rafters.
- The planner chooses the pitch from a small table of rational angles near the target
  slope. It then solves exactly for the touching positions of the rafter ends, which are
  rational.
- Every roof is passed through the full checker: robustness, press load cases, hand access,
  and friction with μsafe.
- The checker's diagnostics feed back to the planner, for example "rafter 7 slides: add a
  stopper / steepen the pitch / add a collar block".

The DSL `tagged "roof"` hint (with `gable`, `cone` or `hip`) tells the planner which motif to
use. Claude's shape output already distinguishes roofs from walls.

---

## 5. Target and similarity metric

- **Shape DSL** (JSON, produced by Claude or written by hand). It offers box, cylinder,
  cone, pyramid, wedge and prism shapes. They can be combined with union and difference,
  moved and scaled, and labelled with semantic tags (tower, wall, roof:gable/cone/hip,
  trunk, …).
- **Voxelizer** (verified against the meaning of the DSL): it samples the shape at grid
  centres with spacing h (default 1) and produces a finite set `T_s` of integer grid points (a sorted, duplicate-free list with a proven membership test).
- **Score**: volumetric IoU, the share of grid points shared by the blocks and the target
  `|V(bp) ∩ T_s| / |V(bp) ∪ T_s|`. For image input it is combined with **silhouette IoU**
  against the input mask. The score is maximized over the scale s.
- **No upper bound**: there is no proven limit on the score. The score credits hollow insides,
  so counting a block's cells says nothing about it (`semantics/APPROACH.md` §5). Instead, an
  accepted plan has at least one block, no block fully outside the target, and a block in every
  part of the target that is big enough to hold one.
- **Verdict bands**: ≥ 0.7 good likeness, 0.4–0.7 coarse, 0.15–0.4 abstract, < 0.15
  symbolic only. For example, 1 block → "stand it upright as a tree trunk". This is still a
  valid, buildable blueprint.
- **Difficulty rating** (reported, not a validity condition): the smallest robustness
  slack, the number of two-hand steps, and the number of leaning blocks. The rating is
  easy, medium or expert, and the planner prefers easier designs when scores are similar.

---

## 6. Components

> Team split, interfaces and Mermaid diagrams: see [WORKSPLIT.md](WORKSPLIT.md).

| Module | Trust | Contents |
|---|---|---|
| `Kapla.Geometry` | ✅ verified | rational unit vectors, Pythagorean rotations (2D yaw, then 3D), convex polygons, clipping, shrinking, 3D separating-axis test, swept prisms, contact detection, centre of mass, voxel cap K_h. Untrusted helper: Stern–Brocot search for the closest Pythagorean angle. |
| `Kapla.Physics` | ✅ verified | contacts, friction pyramid, `Equilibrium`, `RobustStable`, the press load cases, and the robust-certificate checker with `robust_sound` |
| `Kapla.Human` | ✅ verified | `HumanModel`, `Admissible` perturbations, `Reachable` (grip and approach), `Clearance`, `ParallelSupportsOK` |
| `Kapla.Blueprint` | ✅ verified | `Step`, `Valid`, `certify`, `certify_sound` |
| `Kapla.Target` | ✅ core / untrusted JSON | Shape DSL, its meaning, voxelizer and correctness proof |
| `Kapla.Score` | ✅ verified | IoU, silhouette, acceptance checks, verdict |
| `Kapla.LP` | untrusted | Float solve → rationalize → exact check, with an exact rational simplex as fallback. Warm-started across steps. Also produces margins and shift budgets. |
| `Kapla.Planner` | untrusted | scale search; motifs (log-cabin tower, round-tower ring, spiral, wall, slab, arch, tree, **roofs §4**); layer planner; budget knapsack; repair loop driven by diagnostics; exhaustive search for N ≤ 4 |
| `Kapla.Sequencer` | untrusted | build order, grouping into steps (1–2 blocks), grip and approach choice, grouping steps into phases |
| `Kapla.Frontend` | untrusted | Claude Messages API through `curl` (`ANTHROPIC_API_KEY`): text or image → Shape DSL, with validation and at most 2 retries; prose narration of the verified report |
| `Kapla.Render` | untrusted | **Lean-generated webpage**: a three.js 3D view (pinned CDN version) with a step slider; step cards with top-down SVG, offsets, angles, **grip and approach hints**, and a "two hands" badge; feasibility, difficulty and verified badges; a print-ready booklet; `kapla serve` |

CLI:
```
kapla build --blocks 200 --prompt "Neuschwanstein" [--image ref.png] [--eps 10/39] [--out out/]
kapla check blueprint.json
kapla serve --port 8080
```

Trusted base: the Lean kernel, Lean core (and Batteries, if used), the **spec files** (`Physics/Spec`, `Human/Spec`,
`Geometry` definitions, `Score` definitions), and the Lean compiler. The parameters of
the HumanModel are *assumptions about people*. They are validated empirically (M10), not
proven.

---

## 7. Milestones

| # | Deliverable | Verified |
|---|---|---|
| M0 | Lake project on Lean 4.35 (core only, **no Mathlib**), CI (`lake build`, axiom audit, no `sorry`) | — |
| M1 | Yaw-only geometry, nominal equilibrium checker with `checkEquilibrium_sound`; examples include a stack, a rotated stack and a rejected overhang | ✅ |
| M2 | **Human Model I**: robust certificates (relative error, drift cap, shift budgets) with `robust_sound`; press load cases; build steps; hand access; clearance; parallel supports | ✅ |
| M3 | **Tilted blocks + friction** in the nominal checker; roof motifs (stepped, leaning-rafter gable, tipi); two-hand steps | ✅ (nominal + margins enforced) |
| M4 | Shape DSL, voxelizer, IoU, acceptance checks, verdict, difficulty rating | ✅ |
| M5 | Planner v1 (exhaustive search for small N, towers, walls, layers, scale search) + LP certificate generation | output ✅ |
| M6 | Lean-generated webpage + `kapla check` + perturbation test | — |
| M7 | Claude frontend (text, then image + silhouette); `kapla serve` | — |
| M8 | Remaining motifs, repair loop and knapsack → **Neuschwanstein@200 with conical tower roofs** | output ✅ |
| M9 | `robust_sound` extended to tilted contacts (friction-cone and angle margins) | ✅ |
| M10 | **Real-world calibration**: build about 20 generated blueprints by hand, record collapses and measured errors, and tune the HumanModel defaults | empirical |

## 8. Decisions

| Topic | Decision |
|---|---|
| LLM frontend | ✅ Claude, outside the trusted base |
| Viewer | ✅ webpage generated by Lean |
| Tolerance | ✅ HumanModel: εrel = 10/39 relative to supports, eabs = 50/39 drift cap |
| Rotations | ✅ any rotation about the vertical axis from M1; tilted blocks for roofs in M3 (core) |
| Real-world buildability | ✅ H1–H9 are part of the verified `Valid` spec |
| Toolchain | ✅ Lean 4.35, pinned. **No Mathlib**: core Lean (which includes `Rat`) plus Batteries if needed. Proofs must pass `lake comparator` (Linux CI). |
