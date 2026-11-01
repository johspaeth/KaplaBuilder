# Physics rules for Kapla building

Status: draft for review. Owner: the team (humans own this spec, see CLAUDE.md §8).

This document says, in plain English, what our physics engine must decide and
which rules a Kapla build must follow. The Lean spec files will follow this
document rule by rule. Each rule has an ID (for example `S2`). Lean definitions
and theorems should name the rule they implement.

## 1. The one question

A user designs a build in the app. Then a **person builds it for real**, with
real Kapla planks, by following the app's step-by-step plan.

So the engine answers this question: **"If a person places these planks in this
order, a little bit off each time, does the build stand after every step?"**

It does not simulate motion. It does not say how a build falls, only whether it
stands. This is called a *static* check. We choose this because:

- A static check uses exact numbers (fractions), so we can prove things about it.
- It is what the builder needs to know before they start: will this work on
  my table?

The app may still show a falling animation. That animation is for show only
and is not part of what we verify.

## 2. The world

- **W1. Units.** One unit is the thickness of a Kapla plank (7.8 mm).
  All positions and sizes are exact fractions, never floating-point numbers.
- **W2. Axes.** `x` and `y` are horizontal. `z` points up.
- **W3. Ground.** The ground is the flat, level table at `z = 0`. It is large
  enough and strong enough. Nothing may go below it.
- **W4. Gravity.** Gravity pulls every plank straight down (towards lower `z`).
  Once a plank is let go, gravity is the only outside force. There is no wind
  and no bump to the table.

## 3. Planks

- **B1. Size.** Every plank is a solid box of the same size:
  length 15, width 3, thickness 1 (117 mm × 23.4 mm × 7.8 mm, a real Kapla
  plank). Five planks side by side are exactly as wide as one plank is long.
- **B2. Weight.** Every plank weighs the same. The weight is spread evenly
  through the plank, so its balance point (centre of mass) is its exact centre.
- **B3. Rigid.** Planks never bend, squash or break.
- **B4. Orientation.** A plank's sides are always parallel to the axes. That
  leaves six ways to place it:

  | Pose | Size along `x` × `y` × `z` |
  |------|----------------------------|
  | Flat, along `x` | 15 × 3 × 1 |
  | Flat, along `y` | 3 × 15 × 1 |
  | On edge, along `x` | 15 × 1 × 3 |
  | On edge, along `y` | 1 × 15 × 3 |
  | Standing, wide side facing `y` | 3 × 1 × 15 |
  | Standing, wide side facing `x` | 1 × 3 × 15 |

  No tilted or leaning planks.
- **B5. Position.** A plank's position is the corner with the smallest
  `x`, `y` and `z`. Any fraction is allowed. (The app may snap to a grid; the
  engine does not need one.)
- **B6. Turned planks.** A plank may also be turned about the vertical axis in steps of
  15° (15°, 30°, 45°, 60°, 75°, and so on all the way round). It is still never tilted:
  its top and bottom faces stay horizontal, so every contact is still a flat, horizontal
  patch and F3 still holds. 15° and its multiples have no exact fraction for their cosine,
  so the engine uses the closest exact turns (15.19°, 29.86°, 45.24°, 60.14°, 74.81°).
  For now a plan with a turned plank is checked only at the planned positions (P1–P3 and
  S2 after every step); R1, R5, gaps and K3 are not checked for it. The engine's report
  says so (*nominal*, not *robust*), and the app can be told to refuse such plans.

*Why B4:* if every plank is parallel to the axes, every contact between planks
is a flat, horizontal patch. That makes the physics much simpler (see F3).

## 4. Legal placement

A build is a list of planks. It must be *well-formed*:

- **P1. No overlap.** No two planks share any inside space. Planks may touch
  at faces, edges or corners.
- **P2. Above ground.** Every plank has its bottom at `z ≥ 0`.
- **P3. Resting.** Every plank's bottom face touches either the ground or the
  top face of at least one other plank, over an area bigger than zero.

## 5. Contacts

- **C1. What a contact is.** Plank A rests on plank B when A's bottom is at
  the same height as B's top, and the two faces overlap in a patch of area
  bigger than zero. A plank rests on the ground when its bottom is at `z = 0`.
- **C2. Contact patch.** The patch is the rectangle where the two faces
  overlap. For the ground it is the whole bottom face of the plank.
- **C3. Edge and corner touches do not count.** If two faces meet only along a
  line or at a point, there is no contact.
- **C4. Side touches do not count.** When two planks touch side by side
  (vertical faces), we treat them as not touching.

*Why C3 and C4:* ignoring a contact can only make a build look *less* stable,
never more. So if the engine says "stands" with fewer contacts, the build also
stands with all of them. We accept that, in rare cases, a build that is held
up by sideways friction is reported as falling.

## 6. Forces

- **F1. Weight.** Each plank's weight acts at its centre (B2).
- **F2. Push only.** A contact can only push the upper plank up and the lower
  plank down, with equal strength (Newton's third law). It can never pull.
  There is no glue.
- **F3. We never rely on friction.** Real planks have friction. The engine
  does not use it to hold anything up. Gravity is straight down and every
  contact is horizontal, so nothing tries to slide and friction has nothing to
  do. Friction can resist motion but can never start it, so a build we call
  stable is stable with or without friction.
- **F4. Corner forces are enough.** Any way of spreading a push over a
  rectangle patch has the same effect as four pushes, one at each corner of
  the patch, each zero or more. So the engine only uses corner pushes.

*Why F4 is true:* a spread-out push acts like one push at its "centre of
pressure". That point is always inside the patch, and any point inside a
rectangle is a weighted average of its four corners. (This is a lemma we
should prove, or list as a trusted modelling fact.)

## 7. Stability at the exact positions

- **S1. Balanced plank.** A plank is balanced when:
  1. the pushes up on it equal its weight plus the pushes down on it, and
  2. the pushes do not turn it about the `x` axis, and
  3. the pushes do not turn it about the `y` axis.

  (Turning is measured about any fixed point; we use the plank's centre.
  Full balance has three more conditions: no push along `x`, no push along
  `y`, no turning about `z`. All forces are vertical, so those three are
  always true.)
- **S2. Stable build.** A build is stable when there is **at least one**
  choice of contact pushes that follows F2 and F4 and makes **every** plank
  balanced at the same time.
- **S3. Unstable build.** A build is unstable when no such choice exists.
- **S4. Exactly on the edge counts as stable.** If a balance point sits exactly
  above the edge of its support, a push of size zero on the far side is
  allowed, so the build counts as stable at the exact positions. A real build
  needs more than this: see section 8.

*Simple case to check S2 against:* in a single column of planks, the build is
stable exactly when, at every level, the combined centre of mass of everything
above that level is over the contact patch below it. The engine must agree with
this simple rule for single columns.

*What S2 does not claim:* it does not say which pushes really happen (in
general there are many valid choices). It says that a valid choice exists.

## 8. Stability in real life

A real person never puts a plank exactly where the plan says. These rules make
sure a build still stands when every plank is a little off.

- **R1. Placement error.** When the builder places a plank, it ends up within
  `ε` of its planned position along `x` and within `ε` along `y`. Each plank's
  error is separate from every other plank's, except as in R5. We use
  **ε = 1/2 unit**, which is 3.9 mm.
- **R2. Height follows.** A plank's height is not an error: it sits on whatever
  it rests on, so its height is the same as planned.
- **R3. Solid build.** A build is *solid* when it is stable (S2) for **every**
  combination of placement errors allowed by R1.
- **R4. Three answers.** For each build the engine reports one of:
  - **Solid**: stands even with real placement errors.
  - **Risky**: stands at the exact positions, but some small misplacement
    could make it fall. The app warns the builder.
  - **Falls**: does not stand even at the exact positions.

*Why "Solid" needs its own check:* in a contact between two planks, both planks
can be off, in opposite directions. So the contact patch can shrink and the
centre of mass of the upper plank can move by up to `2ε` (1 unit, 7.8 mm) relative
to the plank below. For thin faces (a plank on edge or standing is only 7.8 mm
thick) that is a lot.

*How the engine checks R3:* this is an engineering question, not part of the
spec. The rule for the method is: **it may be cautious, never optimistic.** It
may report "Risky" for a build that is really solid. It must never report
"Solid" for a build that some misplacement makes fall.

- **R5. Pushed against a neighbour.** If the plan puts a plank touching an
  already-placed plank side by side, the builder pushes it gently up against
  that neighbour. In that direction the new plank has no error of its own: it
  is exactly against its neighbour, so it moves with the neighbour's error.
  In the other direction R1 still applies. Pushing it into place does not move
  the neighbour.

*Why R5:* a real builder lines planks up by feel, against each other. Treating
a touching pair as exact is closer to reality than giving each its own 3.9 mm,
and it removes the case where a 3.9 mm error would make two planks overlap.
Side contacts still carry no force (C4); R5 is only about where planks end up.

- **R6. Gaps stay open.** If two planks are not face to face in the plan, no combination
  of placement errors allowed by R1 may make them share inside space. *Face to face* means
  side by side or end to end, flush, over a face of area bigger than zero. Those pairs are
  left out, because of R5. Planks that touch only at an edge or a corner are not left out:
  R5 does not line them up. In Lean: `FaceToFace`, `KeepsGaps`. The engine asks for a gap
  of at least `2ε`, or no shared height (`Clear`).
- **R7. No tight slots.** A plank must not go into a slot exactly its own width, between
  two planks placed before it. Each wall can land `ε` towards the other, so the slot can
  end up too narrow. In Lean: `InTightSlot`.

R6 and R7 are checked when the clearance option is on (the default; `PlanOptions`).
They are H6 in docs/DESIGN.md.

## 9. The build plan

The app turns a design into a list of steps. A person follows the steps.

- **K1. One plank per step.** Each step places one plank, in one of the six
  poses (B4), at one position.
- **K2. Set it down, don't slide it.** The builder may carry the plank to its
  spot along any path: from above, from the side, at an angle. The last
  movement is a short drop straight down onto its supports. They do not
  slide it across the planks below, so friction does not push those planks
  (F3).
- **K3. Reachable (a warning, not a rule).** The plank must be able to reach
  its spot without passing through any plank already placed. It may touch them
  on the way: slide along a face, or brush an edge or a corner (for example,
  slide under a roof whose underside is exactly at the plank's top). The app checks one
  simple kind of path: the plank stays flat in its final pose, moves in a
  straight line from far away to a point a small gap `h` above its spot, then
  drops `h`. The straight line may go in any direction. If such a path
  exists, the step is *reachable*. If not, the app warns "this step may be
  hard to reach". It does not forbid the step, because a person can use
  curved paths, tilt the plank, or reach between planks.

*Why only a warning:* if the check fails, a build does not fall. At worst the
builder needs a trickier move. A perfect check would mean planning every
possible hand movement, which is much harder than this project needs.

*One case is a real problem:* if the new plank must fit into a slot with no
gap above it (a plank already placed sits right on top of the spot), there is
no room for the drop in K2. The builder would have to slide it in, rubbing
both planks. The app should suggest a different order for that step.
- **K4. Every step stands.** After every step, the build so far must be
  well-formed (P1–P3) and **solid** (R3), not only the finished build. With the clearance
  option on (the default), R6 and R7 must also hold after every step.
- **K5. Plank count.** A plan uses at most 200 planks (one Kapla box).

*Why K4:* a design can stand when finished but fall halfway. A plank that is
held down by a counterweight falls if it is placed before the counterweight
(example E12). The app must find an order where every step is solid, or tell
the user that no such order exists.

## 10. What we do not model

Say these out loud in the demo and the README:

- No motion, speed, or falling sequence (section 1).
- No placement error bigger than 3.9 mm (R1).
- No twisting error: we assume the builder lines each plank up square with
  the others.
- No difference between planks: all have exactly the same size and weight
  (B1–B2). Real Kapla planks are very even, but a plank resting on two
  supports can rock if one support is a hair taller.
- No help from friction or side contacts (F3, C4). This can only make us
  cautious.
- No bumps, shaking, or dropping a plank from a height (K2, W4).
- No pressing: the builder sets each plank down and lets go, without pushing on it.
- No hands or fingers: the reachability check (K3) looks at the plank only,
  and only at straight paths.
- No tilted or leaning planks (B4).

## 11. Properties to prove

These are the main theorems. Each one points to the rules it depends on.

1. **"Stands" is right.** If the engine says *stable*, then forces exist that
   meet S2. The engine gives those forces, and the Lean checker confirms them.
2. **"Falls" is right.** If the engine says *falls*, then no forces meet S2.
   The engine gives a certificate (a "reason it must fall"), and the Lean
   checker confirms it.
3. **"Solid" is right.** If the engine says *solid*, then the build is stable
   for every placement error allowed by R1. (The cautious-never-optimistic rule
   in section 8.)
4. **The plan is safe.** If the engine accepts a plan, then after every step
   the build is well-formed and solid (K4).
5. **"Reachable" is right.** If the app says a step is reachable, then on the
   straight path in K3 the plank shares no inside space with any plank already
   placed, at any point along the way. Touching them is allowed (K3).
6. **Matches the simple rule.** For a single column of planks, the engine
   agrees with the centre-of-mass rule in section 7.
7. **Contacts are right.** The contact patches the engine finds are exactly
   the overlaps described in C1–C3.
8. **Friction cannot hurt.** If a build is stable without friction, it is
   stable with any amount of friction (F3).
9. **Square towers are safe to build, at any height.** For every `n`, building
   the square tower (example E8) level by level is a safe plan.

As CLAUDE.md asks, each theorem also gets a concrete example with every
hypothesis met, and a few known-bad outputs that the spec rejects.

## 12. Worked examples

Positions are `(x, y, z)` of the plank's low corner. ε = 1/2 unit (3.9 mm),
so two planks can end up `2ε` = 1 unit (7.8 mm) off from each other.

| # | Build | Exact (S2) | Real (R4) | Why |
|---|-------|------------|-----------|-----|
| E1 | One flat plank on the ground | Stable | Solid | It rests on its own bottom face, which moves with it. |
| E2 | Flat plank on flat plank, top shifted 5 along its length | Stable | Solid | Top centre at 12.5, 2.5 units from the edge. 1 unit of error cannot push it past. |
| E3 | Same, shifted exactly 7.5 | Stable | Risky | Centre exactly over the edge (S4). Any error the wrong way tips it. |
| E4 | Same, shifted 8 | Falls | Falls | Top centre at 15.5, past the edge at 15. |
| E5 | A plank resting only on an edge line of another | Not well-formed | — | Edge touch is not a contact (C3), so P3 fails. |
| E6 | One plank standing on the ground (3 × 1 footprint, 15 tall) | Stable | Solid | It rests on its own footprint, which moves with it. |
| E7 | Staircase: 3 flat planks along `x`, middle shifted 3.75 from the bottom, top shifted 7.5 from the middle | Stable | Risky | Two centres sit exactly over edges. Beautiful on paper, falls in real life. |
| E8 | Square tower, `n` levels, built level by level: level `k` at `z = k`. Even levels: flat along `x` at `y = 0` and `y = 12`. Odd levels: flat along `y` at `x = 0` and `x = 12`. | Stable | Solid at every step | Every centre is at least 1.5 units inside its support, more than 1. |
| E9 | Bridge: two standing planks (3 × 1 footprint) at `(0, 1, 0)` and `(12, 1, 0)`, one flat plank along `x` at `(0, 0, 15)` | Stable | Risky | The top plank's centre is at `y = 1.5`, only 0.5 from the edge of the 1-unit-thick supports. A 1-unit error can put it past the edge. |
| E10 | Same bridge, but the standing planks at `y = 0` | Falls | Falls | Supports cover `y` from 0 to 1. The top plank's centre is at `y = 1.5`. |
| E11 | Square tower (E8) with one plank of a middle level left out | Falls | Falls | The planks above rest on one end only. |
| E12 | Counterweight: plank A flat along `x` at `(0, 0, 0)`; B flat along `x` at `(9, 0, 1)`; C flat along `y` at `(9, -6, 2)` | Stable | Solid (finished build) | Finished, B and C together have their centre at `x = 13.5`, over A. But B alone has its centre at 16.5, past A's edge at 15, so B falls before C can be placed. No order works: **not buildable** (K4). |

## 13. Open questions

None at the moment.

Decided:

- Checking method for R3: a certificate with a fixed load per contact, at a point that
  moves with the placement errors (`SolidCertificate` in `physics/KaplaPhysics/Robust.lean`).
  It calls E1, E6 and E8 solid.
- Final drop gap for K3: `h` = 1 unit, about 8 mm (`dropGap`).

- 3D from the start, no 2D version.
- Side-by-side planks: the builder pushes them together (R5).
- No room for fingers in the reachability check, for now.
- No twisting error, for now (section 10).
