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
The builds (E1–E19 of the rules) and the facts about them are in
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

-- The verdict for E1 with 2 mm of error is "solid".
example : verdict placementError e1 = .solid := by decide +kernel
-- Ruled out: "solid" for E3, which falls if its top plank lands 2 mm too far.
example : ¬ SolidWithin placementError e3 := e3_not_solid

/-- A "solid" verdict is only given for an error `ε` not below zero, and then the build
also stands at the exact positions. -/
theorem verdict_solid_stable (ε : Rat) (b : Build) (h : verdict ε b = .solid) :
    0 ≤ ε ∧ Stable b := by
  sorry

-- The verdict for E1 with 2 mm of error is "solid".
example : verdict placementError e1 = .solid := by decide +kernel
-- Ruled out: "solid" for E4 with a negative error. E4 falls at the exact positions.
example : ¬ (0 ≤ (-1 : Rat) ∧ Stable e4) := fun h => e4_not_stable h.2

/-- When the verdict is "risky", the build is stable at the exact positions (R4). -/
theorem verdict_risky_sound (ε : Rat) (b : Build) (h : verdict ε b = .risky) : Stable b := by
  sorry

-- The verdict for E3 with 2 mm of error is "risky".
example : verdict placementError e3 = .risky := by decide +kernel
-- Ruled out: "risky" for E4, which does not stand even at the exact positions.
example : ¬ Stable e4 := e4_not_stable

/-- When the verdict is "falls", the build is not stable (R4). -/
theorem verdict_falls_sound (ε : Rat) (b : Build) (h : verdict ε b = .falls) : ¬ Stable b := by
  sorry

-- The verdict for E4 with 2 mm of error is "falls".
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
  not_wellFormed_of_floats _ 1 (by decide) (by decide +kernel) (h.2 2 (by decide) (by decide)).1
-- Ruled out: accepting a plan with a turn that B6 does not allow (E18, about 53°).
example : ¬ SafePlan {} placementError 200 e18 := fun h =>
  e18_not_wellFormed (h.2 1 (by decide) (by decide)).1
-- Ruled out (clearance on): two planks 1/4 apart. Moving each 1/4 towards the other is
-- within the 2 mm error and makes them share inside space (P1).
example : ¬ SafePlan { clearance := true } placementError 200
    [Plank.at .flatX 0 0 0, Plank.at .flatX 0 (13 / 4) 0] := fun h =>
  (h.2 2 (by decide) (by decide)).2.1 rfl
    (fun i => if i = 0 then (0, 1 / 4) else (0, -1 / 4)) (by unfold SmallShift; decide +kernel)
    0 (by decide) 1 (by decide)
    (by
      rintro ⟨-, x, y, h1, h2⟩
      simp only [List.take, Build.get, List.getD_cons_zero, List.getD_cons_succ] at h1 h2
      rw [Plank.at_covers] at h1 h2
      simp only [AxisPose.size] at h1 h2
      grind)
    ⟨by decide +kernel, 1, 31 / 10, by decide +kernel, by decide +kernel⟩

/-- Property 5 ("reachable" is right): when the checker finds a direction, the drop gap
`h` is above zero, and the plank can come in along it in a straight line from far away and
drop into place without sharing inside space with any plank already placed (K3). -/
theorem reachDir_sound (placed : Build) (p : Plank) (h : Rat) (d : Dir)
    (hd : reachDir? placed p h = some d) : StraightPath placed p h d.vec := by
  sorry

-- The checker finds a way to slide a plank under a roof from the open side.
example : reachDir? underRoof (Plank.at .flatY 6 0 0) dropGap = some (.side 0 1) := by
  decide +kernel
-- Ruled out: coming straight down into a slot that has a plank right above it.
example : ¬ StraightPath slotPlaced slotPlank dropGap Dir.fromAbove.vec := by
  intro ⟨_, _, _, hpath, _⟩
  apply hpath 0 (by decide) (Plank.at .flatX 0 0 1) (by simp [slotPlaced])
  exact ⟨by decide +kernel, 1, 1, by decide +kernel, by decide +kernel⟩
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

-- E2 and E4 are columns; a bridge (E9) is not: its second standing plank rests on the
-- ground, not on the plank before it.
example : IsColumn e2 ∧ IsColumn e4 ∧ ¬ IsColumn e9 :=
  ⟨columnCheck_sound _ (by decide +kernel), columnCheck_sound _ (by decide +kernel),
   fun h => absurd ((h 1 (by decide) .ground trivial).mp (by decide +kernel)) (by decide)⟩
-- Both sides agree on E1 (stands) and E4 (falls), each shown on its own.
example : Stable e1 ∧ ColumnRule e1 := ⟨e1_stable, columnRuleCheck_sound _ (by decide +kernel)⟩
example : ¬ Stable e4 ∧ ¬ ColumnRule e4 :=
  ⟨e4_not_stable, fun h => absurd (h 1 (by decide)).2 (by decide +kernel)⟩

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

-- The default error, 2 mm, is within the limits.
example : 0 ≤ placementError ∧ placementError ≤ 1 / 2 := by decide +kernel
-- Ruled out: building a tower of `n` levels with fewer than `2 * n` planks.
example : ¬ SafePlan {} placementError 1 (squareTower 1) := fun h => absurd h.1 (by decide +kernel)

/-- Property 9 for turned towers: the square tower turned as a whole by an allowed turn
`r` (B6; for example about 30°, 45° or 60°) is a safe plan at every height `n`, for
placement errors up to `ε`. Seen along the turned planks, an error of `ε` along `x` and
along `y` can be up to `ε * (|cos| + |sin|)`, so that must be at most 1/2. -/
theorem turnedTower_safe (opts : PlanOptions) (r : KaplaCore.Rot) (hr : r.Allowed) (ε : Rat)
    (hε0 : 0 ≤ ε) (hε : ε * (max r.cos (-r.cos) + max r.sin (-r.sin)) ≤ 1 / 2) (n : Nat) :
    SafePlan opts ε (2 * n) (turnedTower r n) := by
  sorry

-- About 45° with the default error of 2 mm: the turn is allowed and the error is small
-- enough.
example : KaplaCore.Rot.deg45.Allowed ∧ 0 ≤ placementError ∧
    placementError * (max KaplaCore.Rot.deg45.cos (-KaplaCore.Rot.deg45.cos) +
      max KaplaCore.Rot.deg45.sin (-KaplaCore.Rot.deg45.sin)) ≤ 1 / 2 := by decide +kernel
-- Ruled out: a tower turned by about 53°, which B6 does not allow.
example : ¬ SafePlan {} placementError 2 (turnedTower (.ofTriple 3 4 5) 1) := fun h =>
  absurd ((h.2 1 (by decide) (by decide)).1.turnsAllowed 0 (by decide)) (by decide +kernel)

/-- Property 7 (planks are Core's blocks): a point that Core counts as inside a block
(`KaplaCore.Pose.contains`) is under the plank seen from above, edges included, and
between its bottom and its top. -/
theorem covers_of_contains (p : Plank) (q : KaplaCore.Q3) (h : p.contains q = true) :
    p.Covers q.x q.y ∧ p.bottom ≤ q.z ∧ q.z < p.top := by
  sorry

-- The middle of a block turned about 45° is inside it for Core.
example : (e13.get 0).contains ⟨0, 0, 1 / 2⟩ = true := by decide +kernel
-- Ruled out: a point 2 along the width of that block is not under it.
example : ¬ (e13.get 0).Covers (-2 * 120 / 169) (2 * 119 / 169) := by decide +kernel

/-- Property 7: a point strictly inside the plank (seen from above, and in height) is
inside the block for Core. -/
theorem contains_of_inside (p : Plank) (q : KaplaCore.Q3) (hxy : p.CoversInside q.x q.y)
    (hb : p.bottom < q.z) (ht : q.z < p.top) : p.contains q = true := by
  sorry

-- The middle of E13's block is strictly inside it.
example : (e13.get 0).CoversInside 0 0 ∧ (e13.get 0).bottom < 1 / 2 ∧
    1 / 2 < (e13.get 0).top := by decide +kernel
-- Ruled out: a point above the block is not inside it for Core.
example : (e13.get 0).contains ⟨0, 0, 2⟩ = false := by decide +kernel

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

/-- A motion that passes the fall check shows that the build is not stable (S3). -/
theorem fallCertificate_sound (b : Build) (ms : List Motion) (hc : checkFall b ms = true) :
    ¬ Stable b := by
  sorry

-- The tipping motion passes the fall check for E4.
example : checkFall e4 e4Motion = true := by decide +kernel
-- Ruled out: a fall certificate for E1, which stands. (Lowering it would push it into the
-- ground, so this motion does not pass.)
example : checkFall e1 [⟨-1, 0, 0⟩] = false := by decide +kernel
example : ¬ ¬ Stable e1 := fun h => h e1_stable

/-- A passing solidity certificate makes the build solid (R3). -/
theorem solidCertificate_sound (ε : Rat) (b : Build) (ls : List Load)
    (hc : SolidCertificate ε b ls) : SolidWithin ε b := by
  sorry

-- E6 (one standing plank): the ground carries its weight at its centre, which moves with
-- the plank's error.
example : SolidCertificate placementError e6 [⟨0, .ground, 1, 3 / 2, 1 / 2, #[1], 0, 0⟩] := by
  decide +kernel
-- Ruled out: a certificate for E3, which is not solid.
example : ¬ SolidWithin placementError e3 := e3_not_solid

/-- No build gets both answers: a push set that passes the check and a fall certificate
cannot exist for the same build. -/
theorem not_stands_and_falls (b : Build) (ps : List Push) (ms : List Motion)
    (h1 : checkPushes b ps = true) (h2 : checkFall b ms = true) : False := by
  sorry

-- The two hypotheses cannot hold together (that is the point of the theorem), but each
-- one can hold on its own, so neither is impossible by itself.
example : checkPushes e1 e1Pushes = true := by decide +kernel
example : checkFall e4 e4Motion = true := by decide +kernel

/-! ## The engine behind KaplaCore's interface

The planner and the app see the engine through `KaplaCore.PhysicsEngine`, which works on
core blocks (`KaplaCore.Pose`: centre, upright, turn; 1 or 2 blocks per step). A core block
is a physics plank, so the engine checks the blocks as they are. -/

/-- When the engine says a core plan is `ok`: every step places 1 to `hands` blocks, and the
blocks, placed one after the other in plan order, are a safe plan with options `opts`: at
most `maxBlocks` of them, and after every block well-formed (so every turn is allowed by
B6), solid for every placement error up to `epsRel`, and (if `opts.clearance` is on)
keeping its gaps for every such error (R1, K4, K5). `physicsEngine` uses the default
options. Core's errors that add up from level to level are not covered (R1 is the model). -/
theorem coreCheck_ok_sound (opts : PlanOptions) (h : KaplaCore.HumanModel) (maxBlocks : Nat)
    (plan : KaplaCore.BuildPlan) (hok : (coreCheck opts h maxBlocks plan).ok = true) :
    (∀ st ∈ plan.steps, 1 ≤ st.blocks.length ∧ st.blocks.length ≤ h.hands) ∧
      SafePlan opts h.epsRel maxBlocks plan.blocks := by
  sorry

-- One flat block on the ground, with the default builder: the engine says `ok`.
example : (coreCheck {} .default 200 ⟨[{ blocks := [KaplaCore.Pose.example] }]⟩).ok = true := by
  decide +kernel
-- A block turned by about 45°, too.
example : (coreCheck {} .default 200 ⟨[{ blocks := e13 }]⟩).ok = true := by decide +kernel
-- Ruled out: `ok` for a block that floats one unit above the ground (P3).
example : (coreCheck {} .default 200 ⟨[{ blocks := floating }]⟩).ok ≠ true := fun hok =>
  not_wellFormed_of_floats _ 0 (by decide) (by decide +kernel)
    ((coreCheck_ok_sound _ _ _ _ hok).2.2 1 (by decide) (by decide)).1
-- Ruled out: `ok` for a block turned by about 53°, which B6 does not allow.
example : (coreCheck {} .default 200 ⟨[{ blocks := e18 }]⟩).ok ≠ true := fun hok =>
  e18_not_wellFormed ((coreCheck_ok_sound _ _ _ _ hok).2.2 1 (by decide) (by decide)).1
-- Ruled out: `ok` for a step with two blocks when the builder has one hand.
example : (coreCheck {} { KaplaCore.HumanModel.default with hands := 1 } 200
    ⟨[{ blocks := [KaplaCore.Pose.example, ⟨.flat, .id, ⟨0, 0, 3 / 2⟩⟩] }]⟩).ok ≠ true :=
  fun hok => absurd ((coreCheck_ok_sound _ _ _ _ hok).1 _ (List.mem_singleton_self _)).2
    (by decide)

end KaplaPhysics
