import KaplaPhysics.Engine
import KaplaPhysics.CoreAdapter
import KaplaSpecs.PhysicsRules.Examples

/-! # Spec for KaplaPhysics (human-owned)

Rules: `spec/physics-rules.md`. What "well-formed", "stable", "solid" and "safe plan"
mean is in `specs/KaplaSpecs/PhysicsRules/` (human-owned, like this file); the engine is
in `physics/KaplaPhysics/Engine.lean`. Proofs live in `physics/KaplaPhysics/Proofs.lean`.
`sorry` is expected in this file only.

After each theorem:
* an example where every hypothesis holds, on a concrete build, so the theorem is not
  empty;
* an example of a wrong answer that the theorem rules out.
The builds (E1–E12 of the rules) and the facts about them are in
`specs/KaplaSpecs/PhysicsRules/Examples.lean`. -/

namespace KaplaPhysics

open Solver (Motion)
open Examples

/-- Property 1 ("stands" is right): when the engine answers "stable", there are allowed
pushes that balance every plank (S2). -/
theorem stabilityAnswer_stable_sound (b : Build) (h : stabilityAnswer b = .stable) :
    Stable b := by
  sorry

-- The engine answers "stable" for E2.
example : stabilityAnswer e2 = .stable := by decide +kernel
-- Ruled out: "stable" for E4, which falls.
example : ¬ Stable e4 := e4_not_stable

/-- Property 2 ("falls" is right): when the engine answers "falls", no allowed pushes
balance every plank (S3). -/
theorem stabilityAnswer_falls_sound (b : Build) (h : stabilityAnswer b = .falls) :
    ¬ Stable b := by
  sorry

-- The engine answers "falls" for E4.
example : stabilityAnswer e4 = .falls := by decide +kernel
-- Ruled out: "falls" for E1, which stands.
example : ¬ ¬ Stable e1 := fun h => h e1_stable

/-- Property 3 ("solid" is right): when the verdict is "solid", the build is stable for
every combination of placement errors up to `ε` (R3). -/
theorem verdict_solid_sound (ε : Rat) (b : Build) (h : verdict ε b = .solid) :
    SolidWithin ε b := by
  sorry

-- The verdict for E1 with 3.9 mm of error is "solid".
example : verdict placementError e1 = .solid := by decide +kernel
-- Ruled out: "solid" for E3, which falls if its top plank lands 3.9 mm too far.
example : ¬ SolidWithin placementError e3 := e3_not_solid

/-- A "solid" verdict is only given for an error `ε` not below zero, and then the build
also stands at the exact positions. -/
theorem verdict_solid_stable (ε : Rat) (b : Build) (h : verdict ε b = .solid) :
    0 ≤ ε ∧ Stable b := by
  sorry

-- The verdict for E1 with 3.9 mm of error is "solid".
example : verdict placementError e1 = .solid := by decide +kernel
-- Ruled out: "solid" for E4 with a negative error. E4 falls at the exact positions.
example : ¬ (0 ≤ (-1 : Rat) ∧ Stable e4) := fun h => e4_not_stable h.2

/-- When the verdict is "risky", the build is stable at the exact positions (R4). -/
theorem verdict_risky_sound (ε : Rat) (b : Build) (h : verdict ε b = .risky) : Stable b := by
  sorry

-- The verdict for E3 with 3.9 mm of error is "risky".
example : verdict placementError e3 = .risky := by decide +kernel
-- Ruled out: "risky" for E4, which does not stand even at the exact positions.
example : ¬ Stable e4 := e4_not_stable

/-- When the verdict is "falls", the build is not stable (R4). -/
theorem verdict_falls_sound (ε : Rat) (b : Build) (h : verdict ε b = .falls) : ¬ Stable b := by
  sorry

-- The verdict for E4 with 3.9 mm of error is "falls".
example : verdict placementError e4 = .falls := by decide +kernel
-- Ruled out: "falls" for E1, which stands.
example : ¬ ¬ Stable e1 := fun h => h e1_stable

/-- Property 4 ("the plan is safe"): when the engine accepts a plan, it uses at most
`maxPlanks` planks, and after every step the build so far is well-formed, is solid for
placement errors up to `ε`, and (only when `opts.clearance` is on) keeps its gaps for those
errors: planks that do not touch in the plan are not pushed into each other (K4, K5). -/
theorem checkPlan_sound (opts : PlanOptions) (ε : Rat) (maxPlanks : Nat) (steps : Build)
    (h : checkPlan opts ε maxPlanks steps = true) : SafePlan opts ε maxPlanks steps := by
  sorry

-- The engine accepts the one-step plan E1.
example : checkPlan {} placementError 200 e1 = true := by decide +kernel
-- Ruled out: accepting E12 in its given order. After step 2, plank B sticks out past A's
-- end with nothing on it yet, and falls.
example : ¬ SafePlan {} placementError 200 e12 := fun h =>
  not_solid_of_not_stable _ _
    (show ¬ Stable (e12.take 2) from overhang_not_stable 9 (by decide +kernel))
    (h.2 2 (by decide) (by decide)).2.2
-- Ruled out: accepting a plan with more planks than allowed.
example : ¬ SafePlan {} placementError 1 e2 := fun h => absurd h.1 (by decide)
-- Ruled out: accepting a plan with a plank that rests on nothing (E5: an edge touch, P3).
example : ¬ SafePlan {} placementError 200 e5 := fun h =>
  absurd (h.2 2 (by decide) (by decide)).1 (by decide +kernel)
-- Ruled out (clearance on): two planks 1/4 apart. Moving each 1/4 towards the other is
-- within the 3.9 mm error and makes them share inside space (P1).
example : ¬ SafePlan { clearance := true } placementError 200
    [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 0, 13 / 4, 0⟩] := fun h =>
  (h.2 2 (by decide) (by decide)).2.1 rfl
    (fun i => if i = 0 then (0, 1 / 4) else (0, -1 / 4)) (by unfold SmallShift; decide +kernel)
    0 (by decide) 1 (by decide) (by decide +kernel) (by decide +kernel)

/-- Property 5 ("reachable" is right): when the checker finds a direction, the drop gap
`h` is above zero, and the plank can come in along it in a straight line from far away and
drop into place without sharing inside space with any plank already placed (K3). -/
theorem reachDir_sound (placed : Build) (p : Plank) (h : Rat) (d : Dir)
    (hd : reachDir? placed p h = some d) : StraightPath placed p h d.vec := by
  sorry

-- The checker finds a way to slide a plank under a roof from the open side.
example : reachDir? underRoof ⟨.flatY, 6, 0, 0⟩ dropGap = some .fromPlusY := by decide +kernel
-- Ruled out: coming straight down into a slot that has a plank right above it.
example : ¬ StraightPath slotPlaced slotPlank dropGap Dir.fromAbove.vec := by
  intro ⟨_, _, _, hpath, _⟩
  apply hpath 0 (by decide) ⟨.flatX, 0, 0, 1⟩ (by decide)
  decide +kernel
-- Ruled out: a path whose final drop has a gap of zero.
example (v : Rat × Rat × Rat) : ¬ StraightPath slotPlaced slotPlank 0 v :=
  fun h => absurd h.1 (by decide)

/-- Property 5 for a plan: when no step is listed as hard to reach, every step can be put
in place by a straight path and a drop. -/
theorem hardToReach_nil_sound (h : Rat) (steps : Build) (hn : hardToReach h steps = []) :
    EveryStepReachable h steps := by
  sorry

-- No step of the two-level square tower is hard to reach.
example : hardToReach dropGap (squareTower 2) = [] := by decide +kernel
-- Ruled out: calling the slot plan reachable. (The checker does list its step 1.)
example : ¬ EveryStepReachable dropGap (slotPlaced ++ [slotPlank]) := slot_not_reachable
example : hardToReach dropGap (slotPlaced ++ [slotPlank]) = [1] := by decide +kernel

/-- Property 6 (matches the simple rule): for a single column of planks, "stable" means
exactly that at every level the combined centre of mass of everything from that level up
is over the patch below that level. -/
theorem column_stable_iff (b : Build) (hc : IsColumn b) : Stable b ↔ ColumnRule b := by
  sorry

-- E2 and E4 are columns; a bridge (E9) is not.
example : IsColumn e2 ∧ IsColumn e4 ∧ ¬ IsColumn e9 := by decide +kernel
-- Both sides agree on E1 (stands) and E4 (falls), each shown on its own.
example : Stable e1 ∧ ColumnRule e1 := ⟨e1_stable, by decide +kernel⟩
example : ¬ Stable e4 ∧ ¬ ColumnRule e4 := ⟨e4_not_stable, by decide +kernel⟩

/-- Property 8 (friction cannot hurt): a build that is stable without friction is stable
with any friction coefficient `μ ≥ 0` (F3). -/
theorem stable_withFriction (μ : Rat) (hμ : 0 ≤ μ) (b : Build) (h : Stable b) :
    StableWithFriction μ b := by
  sorry

-- Wood on wood (μ = 0.4), and E1, which stands.
example : (0 : Rat) ≤ 2 / 5 ∧ Stable e1 := ⟨by decide +kernel, e1_stable⟩
-- Ruled out: a plank in the air standing with the help of friction.
example : ¬ StableWithFriction (2 / 5) floating := floating_not_stableWithFriction _

/-- Property 9 (square towers are safe to build, at any height): building the square tower
(example E8) level by level is a safe plan for every height `n`: after every step it is
well-formed, keeps its gaps with placement errors up to `ε`, and is solid for those
errors, for any `ε` from 0 to 1/2 (3.9 mm), with the clearance check on or off. -/
theorem squareTower_safe (opts : PlanOptions) (ε : Rat) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (n : Nat) : SafePlan opts ε (2 * n) (squareTower n) := by
  sorry

-- The default error, 3.9 mm, is within the limits.
example : 0 ≤ placementError ∧ placementError ≤ 1 / 2 := by decide +kernel
-- Ruled out: building a tower of `n` levels with fewer than `2 * n` planks.
example : ¬ SafePlan {} placementError 1 (squareTower 1) := fun h => absurd h.1 (by decide +kernel)

/-- Property 7 (contacts are right): the overlap of two rectangles holds exactly the points
that lie in both. -/
theorem Rect.inter_contains (r s : Rect) (x y : Rat) :
    (r.inter s).Contains x y ↔ r.Contains x y ∧ s.Contains x y := by
  sorry

-- The planks of E2 overlap from `x = 5` to `x = 15`: the point (10, 1) is in both and in
-- the overlap; the point (2, 1) is only in the bottom plank, and not in the overlap.
example : (e2.get 0).footprint.Contains 10 1 ∧ (e2.get 1).footprint.Contains 10 1 ∧
    ((e2.get 0).footprint.inter (e2.get 1).footprint).Contains 10 1 := by
  unfold Rect.Contains; decide +kernel
example : (e2.get 0).footprint.Contains 2 1 ∧
    ¬ ((e2.get 0).footprint.inter (e2.get 1).footprint).Contains 2 1 := by
  unfold Rect.Contains; decide +kernel

/-- Property 7: a rectangle has an area bigger than zero exactly when some point lies
strictly inside it (C3). -/
theorem Rect.hasArea_iff (r : Rect) :
    r.HasArea ↔ ∃ x y, r.x0 < x ∧ x < r.x1 ∧ r.y0 < y ∧ y < r.y1 := by
  sorry

-- The overlap of E2's planks has an area; the overlap of E5's planks (an edge) has none.
example : ((e2.get 0).footprint.inter (e2.get 1).footprint).HasArea := by decide +kernel
example : ¬ ((e5.get 0).footprint.inter (e5.get 1).footprint).HasArea := by decide +kernel

/-- Property 7: plank `i` rests on plank `j` over `r` exactly when `i`'s bottom is at the
height of `j`'s top, `r` is the overlap of their footprints, and `r` has an area (C1, C2). -/
theorem restPatch_plank_iff (b : Build) (i j : Nat) (r : Rect) :
    restPatch b i (.plank j) = some r ↔
      (b.get i).z = (b.get j).top ∧ r = (b.get i).footprint.inter (b.get j).footprint ∧
        r.HasArea := by
  sorry

-- E2's top plank rests on the bottom one over the 10 × 3 patch they share.
example : restPatch e2 1 (.plank 0) = some ⟨5, 15, 0, 3⟩ := by decide +kernel
-- Ruled out: a contact along an edge only (E5, C3).
example : restPatch e5 1 (.plank 0) = none := by decide +kernel

/-- Property 7: plank `i` rests on the ground over `r` exactly when its bottom is at `z = 0`
and `r` is its whole footprint (C1, C2). -/
theorem restPatch_ground_iff (b : Build) (i : Nat) (r : Rect) :
    restPatch b i .ground = some r ↔ (b.get i).z = 0 ∧ r = (b.get i).footprint := by
  sorry

-- E1 rests on the ground over its whole footprint.
example : restPatch e1 0 .ground = some ⟨0, 15, 0, 3⟩ := by decide +kernel
-- Ruled out: a plank in the air resting on the ground.
example : restPatch floating 0 .ground = none := by decide +kernel

/-! ## Certificates

A planner (or anyone) holding its own certificate can check it directly. These say the
checkers are right on their own, whatever produced the certificate. -/

/-- If the push check passes, the build is stable (S2). -/
theorem checkPushes_sound (b : Build) (ps : List Push) (h : checkPushes b ps = true) :
    Stable b := by
  sorry

-- A quarter of E1's weight at each corner passes the check.
example : checkPushes e1 e1Pushes = true := by decide +kernel
-- Ruled out: holding up E4's top plank at `x = 16`, past the end of its support.
example : checkPushes e4 [⟨0, .ground, 0, 0, 1⟩, ⟨1, .plank 0, 16, 0, 1⟩] = false := by
  decide +kernel

/-- A motion that tips E4's top plank over the end of the bottom plank: its centre goes
down by 1/2, and it turns so that every point it rests on goes up. -/
def e4Motion : List Motion := [{}, ⟨-1 / 2, -2, 0⟩]

/-- A fall certificate shows that the build is not stable (S3). -/
theorem fallCertificate_sound (b : Build) (ms : List Motion) (hc : FallCertificate b ms) :
    ¬ Stable b := by
  sorry

-- The tipping motion is a fall certificate for E4.
example : FallCertificate e4 e4Motion := by decide +kernel
-- Ruled out: a fall certificate for E1, which stands. (Lowering it would push it into the
-- ground, so this motion is not one.)
example : ¬ FallCertificate e1 [⟨-1, 0, 0⟩] := by decide +kernel
example : ¬ ¬ Stable e1 := fun h => h e1_stable

/-- A passing solidity certificate makes the build solid (R3). -/
theorem solidCertificate_sound (ε : Rat) (b : Build) (ls : List Load)
    (hc : SolidCertificate ε b ls) : SolidWithin ε b := by
  sorry

-- E6 (one standing plank): the ground carries its weight at its centre, which moves with
-- the plank's error.
example : SolidCertificate placementError e6 [⟨0, .ground, 1, 3 / 2, 1 / 2, #[1]⟩] := by
  decide +kernel
-- Ruled out: a certificate for E3, which is not solid.
example : ¬ SolidWithin placementError e3 := e3_not_solid

/-- No build gets both answers: a push set that passes the check and a fall certificate
cannot exist for the same build. -/
theorem not_stands_and_falls (b : Build) (ps : List Push) (ms : List Motion)
    (h1 : checkPushes b ps = true) (h2 : FallCertificate b ms) : False := by
  sorry

-- The two hypotheses cannot hold together (that is the point of the theorem), but each
-- one can hold on its own, so neither is impossible by itself.
example : checkPushes e1 e1Pushes = true := by decide +kernel
example : FallCertificate e4 e4Motion := by decide +kernel

/-! ## The engine behind KaplaCore's interface

The planner and the app see the engine through `KaplaCore.PhysicsEngine`, which works on
core blocks (centre, any turn, 1 or 2 blocks per step). `plankOf` and `buildOf`
(`specs/KaplaSpecs/PhysicsRules/FromCore.lean`) turn core blocks into planks. -/

/-- The conversion keeps each block where it is: for a block with a physics pose, core's box
for it and the plank's box are the same. -/
theorem plankOf_box (p : KaplaCore.Pose) (q : Plank) (h : plankOf p = some q) :
    p.box = q.toBox := by
  sorry

-- Core's example block (flat, centre at height 1/2) is a flat plank on the ground.
example : plankOf KaplaCore.Pose.example = some ⟨.flatX, -15 / 2, -3 / 2, 0⟩ := by
  decide +kernel
-- Ruled out: reading core's centre as the plank's corner puts the block somewhere else.
example : KaplaCore.Pose.example.box ≠ (⟨.flatX, 0, 0, 1 / 2⟩ : Plank).toBox := fun h =>
  absurd (congrArg (·.lo.z) h) (by decide +kernel)

/-- When the engine says a core plan is `ok`: every step places 1 to `hands` blocks, every
block has a physics pose, and the blocks, placed one after the other in plan order, are a
safe plan with options `opts`: at most `maxBlocks` of them, and after every block
well-formed, solid for every placement error up to `epsRel`, and (if `opts.clearance` is on)
keeping its gaps for every such error (R1, K4, K5). `physicsEngine` uses the default
options. Core's errors that add up from level to level are not covered (R1 is the model). -/
theorem coreCheck_ok_sound (opts : PlanOptions) (h : KaplaCore.HumanModel) (maxBlocks : Nat)
    (plan : KaplaCore.BuildPlan) (hok : (coreCheck opts h maxBlocks plan).ok = true) :
    (∀ st ∈ plan.steps, 1 ≤ st.blocks.length ∧ st.blocks.length ≤ h.hands) ∧
      ∃ b, buildOf plan.blocks = some b ∧ SafePlan opts h.epsRel maxBlocks b := by
  sorry

-- One flat block on the ground, with the default builder: the engine says `ok`.
example : (coreCheck {} .default 200 ⟨[{ blocks := [KaplaCore.Pose.example] }]⟩).ok = true := by
  decide +kernel
-- Ruled out: `ok` for a block that floats one unit above the ground (P3).
example : (coreCheck {} .default 200
    ⟨[{ blocks := [⟨.flat, .id, ⟨15 / 2, 3 / 2, 3 / 2⟩⟩] }]⟩).ok ≠ true := fun hok => by
  obtain ⟨_, b, hb, hs⟩ := coreCheck_ok_sound _ _ _ _ hok
  have hf : buildOf [⟨.flat, .id, ⟨15 / 2, 3 / 2, 3 / 2⟩⟩] = some floating := by decide +kernel
  obtain rfl : b = floating := Option.some.inj (hb.symm.trans hf)
  exact absurd (hs.2 1 (by decide) (by decide)).1 (by decide +kernel)
-- Ruled out: `ok` for a step with two blocks when the builder has one hand.
example : (coreCheck {} { KaplaCore.HumanModel.default with hands := 1 } 200
    ⟨[{ blocks := [KaplaCore.Pose.example, ⟨.flat, .id, ⟨0, 0, 3 / 2⟩⟩] }]⟩).ok ≠ true :=
  fun hok => absurd ((coreCheck_ok_sound _ _ _ _ hok).1 _ (List.mem_singleton_self _)).2
    (by decide)

end KaplaPhysics
