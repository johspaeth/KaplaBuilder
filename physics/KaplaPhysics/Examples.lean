import KaplaPhysics.Proofs
import KaplaPhysics.CoreAdapter
import KaplaSpecs.PhysicsRules.Examples

/-! # Worked examples (section 12 of `spec/physics-rules.md`)

Each `#guard` fails the build if the engine disagrees with the table in the spec: the
"Exact (S2)" column, the "Real (R4)" column (with ε = 2 mm), and buildability (K4).
The builds themselves (`e1` ... `e12`, `slotPlaced`, `underRoof`) are in
`specs/KaplaSpecs/PhysicsRules/Examples.lean`, shared with the spec. -/

namespace KaplaPhysics.Examples

#guard [e1, e2, e3, e4, e6, e7, e9, e10, e11, e12].all fun b => decide (WellFormed b)
#guard !decide (WellFormed e5)

#guard stabilityAnswer e1 == .stable
#guard stabilityAnswer e2 == .stable
#guard stabilityAnswer e3 == .stable
#guard stabilityAnswer e4 == .falls
#guard stabilityAnswer e6 == .stable
#guard stabilityAnswer e7 == .stable
#guard stabilityAnswer (squareTower 8) == .stable
#guard stabilityAnswer e9 == .stable
#guard stabilityAnswer e10 == .falls
#guard stabilityAnswer e11 == .falls
#guard stabilityAnswer e12 == .stable

-- A large build that falls (51 planks, above the global-LP limit): a 25-level tower with
-- an overhanging plank on top. The fall certificate moves only the top plank.
#guard stabilityAnswer (squareTower 25 ++ [⟨.flatX, 8, 0, 25⟩]) == .falls

-- Placement errors (R4), with ε = 2 mm.
#guard verdict placementError e1 == .solid
#guard verdict placementError e2 == .solid
#guard verdict placementError e3 == .risky
#guard verdict placementError e4 == .falls
#guard verdict placementError e6 == .solid
#guard verdict placementError e7 == .risky
#guard verdict placementError (squareTower 8) == .solid
#guard verdict placementError e9 == .risky
#guard verdict placementError e10 == .falls
#guard verdict placementError e11 == .falls

-- Buildability, every step (K4, K5).
#guard checkPlan {} placementError 200 (squareTower 8)
#guard !checkPlan {} placementError 200 e7     -- stands on paper, but risky
#guard !checkPlan {} placementError 200 e12    -- B falls before C can hold it down
#guard !checkPlan {} placementError 1 e2       -- more planks than allowed
#guard stabilityAnswer (e12.take 2) == .falls

-- The simple rule for columns (section 7): the engine agrees with it on E2, E3, E4, E7.
#guard [e1, e2, e3, e4, e7].all fun b => decide (IsColumn b)
#guard !decide (IsColumn e9)                       -- a bridge is not a column
#guard [e1, e2, e3, e7].all fun b => decide (ColumnRule b) && stabilityAnswer b == .stable
#guard !decide (ColumnRule e4) && stabilityAnswer e4 == .falls

-- Step-by-step report: E12's second step falls, the third would be solid again.
#guard (planReport placementError dropGap e12).map (·.verdict) == [.solid, .falls, .solid]
#guard (planReport placementError dropGap e7).map (·.verdict) == [.solid, .solid, .risky]

-- Reaching the spot (K3), with a drop gap of 1 unit.
#guard hardToReach dropGap (squareTower 8) == []
#guard hardToReach dropGap e9 == []
#guard reachDir? [] ⟨.flatX, 0, 0, 0⟩ dropGap == some .fromAbove

#guard reachDir? slotPlaced slotPlank dropGap == none

#guard reachDir? underRoof ⟨.flatY, 6, 0, 0⟩ dropGap == some .fromPlusY

/-! ## The main theorems apply to real inputs (their hypotheses can be met) -/

example : Stable e2 := stabilityAnswer_stable_sound e2 (by decide +kernel)
example : Stable e3 := stabilityAnswer_stable_sound e3 (by decide +kernel)
example : ¬ Stable e4 := stabilityAnswer_falls_sound e4 (by decide +kernel)
example : ¬ Stable e10 := stabilityAnswer_falls_sound e10 (by decide +kernel)
example : ¬ Stable (e12.take 2) := stabilityAnswer_falls_sound _ (by decide +kernel)
example : Solid e1 := verdict_solid_sound placementError e1 (by decide +kernel)
example : SafePlan {} placementError 200 e1 := checkPlan_sound {} placementError 200 e1 (by decide +kernel)

/-! Running the robust solver inside the kernel is slow for more than one plank, so for E2
and E6 we write out the certificate the solver finds (the `#guard`s above run the solver
itself) and let the kernel check it. -/

/-- E2: the bottom plank carries 2 to the ground at its middle, which moves with the
average of both planks' errors; the top plank carries 1 at its own centre. -/
def e2Certificate : List Load :=
  [⟨0, .ground, 2, 10, 3 / 2, #[1 / 2, 1 / 2]⟩, ⟨1, .plank 0, 1, 25 / 2, 3 / 2, #[0, 1]⟩]

example : Solid e2 := solidCertificate_sound _ _ e2Certificate (by decide +kernel)
example : Solid e6 := solidCertificate_sound _ _ [⟨0, .ground, 1, 3 / 2, 1 / 2, #[1]⟩]
  (by decide +kernel)

example : StraightPath underRoof ⟨.flatY, 6, 0, 0⟩ dropGap Dir.fromPlusY.vec :=
  reachDir_sound _ _ _ _ (by decide +kernel)
example : EveryStepReachable dropGap (squareTower 2) :=
  hardToReach_nil_sound _ _ (by decide +kernel)

/-- E3 is stable by the simple column rule alone, with no solver involved. -/
example : Stable e3 := (column_stable_iff e3 (by decide +kernel)).mpr (by decide +kernel)
/-- E4 falls by the simple column rule: the top plank's centre is past the edge. -/
example : ¬ Stable e4 := fun h =>
  absurd ((column_stable_iff e4 (by decide +kernel)).mp h) (by decide +kernel)

/-- E2 stands with wood-on-wood friction too (μ = 0.4). -/
example : StableWithFriction (2 / 5) e2 :=
  stable_withFriction _ (by decide +kernel) e2 (stabilityAnswer_stable_sound e2 (by decide +kernel))

/-- E8 for every height, with the default 2 mm error: a 100-level tower (200 planks, a full
Kapla box) is safe to build level by level. -/
example : SafePlan {} placementError 200 (squareTower 100) :=
  squareTower_safe {} placementError (by decide +kernel) (by decide +kernel) 100

/-! ## "Risky" builds really are not solid (R3)

"Risky" only means the engine could not show the build solid. For E3, E7 and E9 we show
more: a placement error of at most 2 mm per plank that makes the build fall. E3 is
`e3_not_solid` (in `KaplaSpecs.PhysicsRules.Examples`, from the rules alone). For E7 and
E9, the solver's fall certificate for the shifted build is written out here and checked by
the kernel. -/

/-- E7's errors: the top plank lands 2 mm further out along `x`. Its centre then lies past
the end of the middle plank. -/
def e7Shift (i : Nat) : Rat × Rat := if i = 2 then (placementError, 0) else (0, 0)

/-- How the shifted E7 falls: the top plank tips over the end of the middle plank. -/
def e7Fall : List Solver.Motion := [{}, ⟨29 / 39, -116 / 585, 0⟩, ⟨-1, -1, 0⟩]

/-- E7 is not solid (R3): the 2 mm error `e7Shift` makes it fall. -/
theorem e7_not_solid : ¬ Solid e7 := fun h =>
  fallCertificate_sound _ e7Fall (by decide +kernel)
    (h.2 e7Shift (by unfold SmallShift; decide +kernel))

/-- E9's errors: both standing planks land 2 mm towards `-y`, the top plank 2 mm towards
`+y`. The top plank's centre is then 1/78 past the far side of its supports. -/
def e9Shift (i : Nat) : Rat × Rat := if i = 2 then (0, placementError) else (0, -placementError)

/-- How the shifted E9 falls: the top plank tips over the far side of its supports. -/
def e9Fall : List Solver.Motion := [{}, {}, ⟨-1 / 78, 0, -1⟩]

/-- E9 is not solid (R3): the 2 mm errors `e9Shift` make it fall. -/
theorem e9_not_solid : ¬ Solid e9 := fun h =>
  fallCertificate_sound _ e9Fall (by decide +kernel)
    (h.2 e9Shift (by unfold SmallShift; decide +kernel))

/-- The engine's "risky" for E3, E7 and E9 is right in the strong sense: each stands at
the exact positions but is not solid. -/
example : (Stable e3 ∧ ¬ Solid e3) ∧ (Stable e7 ∧ ¬ Solid e7) ∧ (Stable e9 ∧ ¬ Solid e9) :=
  ⟨⟨stabilityAnswer_stable_sound _ (by decide +kernel), e3_not_solid⟩,
   ⟨stabilityAnswer_stable_sound _ (by decide +kernel), e7_not_solid⟩,
   ⟨stabilityAnswer_stable_sound _ (by decide +kernel), e9_not_solid⟩⟩

/-! ## The rules reject bad answers -/

/-- A pull (negative push) is not allowed (F2). -/
example : ¬ (Push.mk 1 (.plank 0) 5 0 (-1)).Allowed e2 := by decide +kernel

/-- A push that is not at a corner of a contact patch is not allowed (F4). -/
example : ¬ (Push.mk 1 (.plank 0) 10 0 1).Allowed e2 := by decide +kernel

/-- A push between planks that do not touch is not allowed (C1). -/
example : ¬ (Push.mk 1 .ground 5 0 1).Allowed e2 := by decide +kernel

/-- Holding up E4's top plank at its far end is not allowed: the support stops at 15. -/
example : checkPushes e4
    [⟨0, .ground, 0, 0, 1⟩, ⟨1, .plank 0, 16, 0, 1⟩] = false := by decide +kernel

/-- Pushes that only carry the weight but let the plank turn do not balance it (S1). -/
example : ¬ Balanced e2 [⟨1, .plank 0, 15, 0, 1⟩] 1 := by decide +kernel

/-- E2's certificate does not fit E3: the top load is too close to the edge of the plank
below, so it could leave the patch. -/
example : ¬ SolidCertificate placementError e3
    [⟨0, .ground, 2, 45 / 4, 3 / 2, #[1 / 2, 1 / 2]⟩, ⟨1, .plank 0, 1, 15, 3 / 2, #[0, 1]⟩] := by
  decide +kernel

/-- An unstable build is not called stable: E4 is not stable, so no answer "stable". -/
example : stabilityAnswer e4 ≠ .stable := by decide +kernel

/-- A plan whose middle step falls is not safe. -/
example : ¬ SafePlan {} placementError 200 e12 := fun h =>
  stabilityAnswer_falls_sound (e12.take 2) (by decide +kernel)
    (solid_stable _ _ (h.2 2 (by decide) (by decide)).2.2)

/-- E12 cannot be built in any order (K4). Orders that start with B or C, or that put C
right after A, leave a plank in the air after step 1 or 2 (P3). The order A, B, C falls
after step 2, as above. -/
example : ∀ plan ∈ [[e12A, e12B, e12C], [e12A, e12C, e12B], [e12B, e12A, e12C],
    [e12B, e12C, e12A], [e12C, e12A, e12B], [e12C, e12B, e12A]],
    ¬ SafePlan {} placementError 200 plan := by
  intro plan hplan
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hplan
  rcases hplan with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun h => stabilityAnswer_falls_sound _ (by decide +kernel)
      (solid_stable _ _ (h.2 2 (by decide) (by decide)).2.2)
  all_goals first
    | exact fun h => absurd (h.2 1 (by decide) (by decide)).1 (by decide +kernel)
    | exact fun h => absurd (h.2 2 (by decide) (by decide)).1 (by decide +kernel)

/-- Coming straight down into the slot is not a valid path: the plank above is in the way. -/
example : ¬ StraightPath slotPlaced slotPlank dropGap Dir.fromAbove.vec := by
  intro ⟨_, _, _, _, hdrop⟩
  exact hdrop 1 (by decide +kernel) (by decide +kernel) ⟨.flatX, 0, 0, 1⟩ (by simp [slotPlaced])
    (by decide +kernel)

/-! ## Review regressions (PR #14) -/

/-- Two planks side by side with a gap of 1/4. Each is stable and well-formed where it is
planned, but moving them 1/4 towards each other (within the 10/39 error) makes them share
a strip of inside space. -/
def nearlyTouching : Build := [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 0, 13 / 4, 0⟩]

/-- The errors that push the two planks of `nearlyTouching` into each other. -/
def towardsEachOther (i : Nat) : Rat × Rat := if i = 0 then (0, 1 / 4) else (0, -1 / 4)

#guard decide (WellFormed nearlyTouching)
#guard !checkPlan {} placementError 200 nearlyTouching
#guard !decide (WellFormed (nearlyTouching.shift towardsEachOther))

/-- The plan is not safe: the errors `towardsEachOther` are allowed and break P1. -/
example : ¬ SafePlan {} placementError 200 nearlyTouching := fun h =>
  absurd ((h.2 2 (by decide) (by decide)).2.1 rfl towardsEachOther
    (by unfold SmallShift; decide +kernel))
    (by decide +kernel)

-- With the clearance check switched off, the plan is accepted: each step is well-formed
-- at the planned positions and solid.
#guard checkPlan { clearance := false } placementError 200 nearlyTouching

-- Switching the check off never lets through a plan that falls or is risky.
#guard !checkPlan { clearance := false } placementError 200 e7
#guard !checkPlan { clearance := false } placementError 200 e12

-- With a gap of 1 (more than twice the error) the same plan is accepted.
#guard checkPlan {} placementError 200 [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 0, 4, 0⟩]

-- A negative error is never "solid": E4 falls at the exact positions.
#guard verdict (-1) e4 == .falls
#guard verdict (-1) e1 == .risky
#guard !checkPlan {} (-1) 200 e4
#guard !checkPlan {} (-1) 200 e1

/-- "Solid" with a negative error does not hold, whatever the build. -/
example : ¬ SolidWithin (-1) e4 := fun h => absurd h.1 (by decide)

/-- E4 is not solid for any error: it already falls with none. -/
example (ε : Rat) : ¬ SolidWithin ε e4 := fun h =>
  stabilityAnswer_falls_sound e4 (by decide +kernel) (solid_stable ε e4 h)

-- A drop gap of zero or below gives no path (K2, K3 ask for a real drop).
#guard reachDir? slotPlaced slotPlank 0 == none
#guard reachDir? [⟨.flatX, 0, 0, 0⟩] ⟨.flatX, 0, 0, 0⟩ (-2) == none
#guard hardToReach 0 e1 == [0]

/-- No straight path has a gap of zero. -/
example (v : Rat × Rat × Rat) : ¬ StraightPath slotPlaced slotPlank 0 v :=
  fun h => absurd h.1 (by decide)

/-- No straight path has a negative gap, even for a plank put exactly onto itself. -/
example (v : Rat × Rat × Rat) :
    ¬ StraightPath [⟨.flatX, 0, 0, 0⟩] ⟨.flatX, 0, 0, 0⟩ (-2) v :=
  fun h => absurd h.1 (by decide)

/-- A sideways push bigger than `μ` times the up-push is not allowed. -/
example : ¬ (FrictionPush.mk ⟨1, .plank 0, 5, 0, 1⟩ 1 0).Allowed (2 / 5) e2 :=
  fun h => absurd h.2.2.1 (by decide +kernel)

/-! ## Through KaplaCore's interface (`coreCheck`)

The same builds written as core plans: blocks given by their centre, `flatAt` for flat
blocks, one block per step unless said otherwise. -/

section Core
open KaplaCore (HumanModel BuildPlan flatAt physicsMock)

/-- A block on its long edge, along `x`, with its lowest corner at `(x, y, z)`. -/
def coreEdgeAt (x y z : Rat) : KaplaCore.Pose := ⟨.onEdge, .id, ⟨x + 15 / 2, y + 1 / 2, z + 3 / 2⟩⟩

/-- E2 as a core plan. -/
def coreE2 : BuildPlan := .ofBlocks [flatAt 0 0 0, flatAt 5 0 1]
/-- E7 as a core plan. -/
def coreE7 : BuildPlan := .ofBlocks [flatAt 0 0 0, flatAt (15 / 4) 0 1, flatAt (45 / 4) 0 2]
/-- E12 as a core plan. -/
def coreE12 : BuildPlan := .ofBlocks [flatAt 0 0 0, flatAt 9 0 1, flatAt 9 (-6) 2 (turned := true)]
/-- E12 with B and C put on in the same step, one in each hand. -/
def coreE12TwoHands : BuildPlan :=
  ⟨[{ blocks := [flatAt 0 0 0] }, { blocks := [flatAt 9 0 1, flatAt 9 (-6) 2 (turned := true)] }]⟩
/-- E8 with two levels as a core plan. -/
def coreTower : BuildPlan :=
  .ofBlocks [flatAt 0 0 0, flatAt 0 12 0, flatAt 0 0 1 true, flatAt 12 0 1 true]
/-- A block between two walls, under a roof, with a block across each open end (1 unit
away, so placement errors cannot push them together): it stands, but no straight path
reaches it. -/
def coreBoxedIn : BuildPlan := .ofBlocks
  [flatAt 0 0 0 true, flatAt 0 0 1 true, flatAt 0 0 2 true,
   flatAt 12 0 0 true, flatAt 12 0 1 true, flatAt 12 0 2 true,
   flatAt 0 0 3, coreEdgeAt 0 16 0, coreEdgeAt 0 (-2) 0, flatAt 6 0 0 true]

-- The conversion gives the same planks as the physics examples.
#guard buildOf coreE7.blocks == some e7
#guard buildOf coreE12.blocks == some e12
#guard buildOf coreTower.blocks == some (squareTower 2)

#guard coreCheck {} .default 200 coreE2 == { ok := true }
#guard coreCheck {} .default 200 coreTower == { ok := true }
-- E7 stands on paper but is risky: block 2 (step 2) is where it goes wrong.
#guard coreCheck {} .default 200 coreE7 == { ok := false, diagnostics := [.unstable 2 2] }
-- E12: B falls before C can hold it down.
#guard coreCheck {} .default 200 coreE12 == { ok := false, diagnostics := [.unstable 1 1] }
-- Blocks of one step are checked one after the other, so two hands do not save E12.
#guard coreCheck {} .default 200 coreE12TwoHands == { ok := false, diagnostics := [.unstable 1 1] }
-- A block turned by the 3-4-5 angle has no physics pose.
#guard coreCheck {} .default 200 (.ofBlocks [⟨.flat, .ofTriple 3 4 5, ⟨0, 0, 1 / 2⟩⟩]) ==
  { ok := false, diagnostics := [.unstable 0 0] }
#guard coreCheck {} .default 200 (.ofBlocks [flatAt 0 0 0, flatAt 1 0 0]) ==
  { ok := false, diagnostics := [.overlap 0 1, .unstable 1 1, .unreachable 1] }
-- Two blocks side by side, touching: a placement error could push one into the other.
#guard coreCheck {} .default 200 (.ofBlocks [flatAt 0 0 0, flatAt 0 3 0]) ==
  { ok := false, diagnostics := [.clearance 0 1] }
-- With clearance off, the same plan is `ok`.
#guard coreCheck { clearance := false } .default 200 (.ofBlocks [flatAt 0 0 0, flatAt 0 3 0]) ==
  { ok := true }
#guard coreCheck {} .default 3 coreTower == { ok := false, diagnostics := [.tooManyBlocks 4 3] }
#guard coreCheck {} .default 200 ⟨[{ blocks := [] }]⟩ ==
  { ok := false, diagnostics := [.emptyStep 0] }
#guard coreCheck {} { HumanModel.default with hands := 1 } 200 coreE12TwoHands ==
  { ok := false, diagnostics := [.tooManyHands 1, .unstable 1 1] }
-- Hard to reach is a warning only (K3): the plan is still `ok`.
#guard coreCheck {} .default 200 coreBoxedIn == { ok := true, diagnostics := [.unreachable 9] }

-- Where the mock is too kind: it ignores placement error and lets two blocks of a step hold
-- each other up.
#guard (physicsMock.check .default 200 coreE7).ok
#guard (physicsMock.check .default 200 coreE12TwoHands).ok

end Core

end KaplaPhysics.Examples
