import KaplaPhysics.Proofs

/-! # Worked examples (section 12 of `spec/physics-rules.md`)

Each `#guard` fails the build if the engine disagrees with the table in the spec. The
"Real (R4)" column (solid or risky) needs the placement-error check, which is not built
yet; here we check the "Exact (S2)" column and buildability (K4 at exact positions). -/

namespace KaplaPhysics.Examples

/-- E1. One flat plank on the ground. -/
def e1 : Build := [⟨.flatX, 0, 0, 0⟩]
/-- E2. Flat plank on flat plank, top shifted 5 along its length. -/
def e2 : Build := [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 5, 0, 1⟩]
/-- E3. Same, shifted exactly 7.5: the top centre is exactly over the edge (S4). -/
def e3 : Build := [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 15 / 2, 0, 1⟩]
/-- E4. Same, shifted 8: the top centre is past the edge. -/
def e4 : Build := [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 8, 0, 1⟩]
/-- E5. A plank resting only on an edge line of another. -/
def e5 : Build := [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 15, 0, 1⟩]
/-- E6. One plank standing on the ground. -/
def e6 : Build := [⟨.standFacingY, 0, 0, 0⟩]
/-- E7. Staircase: middle shifted 3.75, top shifted 7.5 from the middle. -/
def e7 : Build := [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 15 / 4, 0, 1⟩, ⟨.flatX, 45 / 4, 0, 2⟩]

/-- One level of the square tower (E8): level `k` sits at height `k`. -/
def towerLevel (k : Nat) : Build :=
  if k % 2 = 0 then [⟨.flatX, 0, 0, k⟩, ⟨.flatX, 0, 12, k⟩]
  else [⟨.flatY, 0, 0, k⟩, ⟨.flatY, 12, 0, k⟩]

/-- E8. Square tower with `n` levels, built level by level. -/
def squareTower (n : Nat) : Build := (List.range n).flatMap towerLevel

/-- E9. Bridge on two standing planks at `y = 1`. -/
def e9 : Build := [⟨.standFacingY, 0, 1, 0⟩, ⟨.standFacingY, 12, 1, 0⟩, ⟨.flatX, 0, 0, 15⟩]
/-- E10. Same bridge with the standing planks at `y = 0`. -/
def e10 : Build := [⟨.standFacingY, 0, 0, 0⟩, ⟨.standFacingY, 12, 0, 0⟩, ⟨.flatX, 0, 0, 15⟩]
/-- E11. Square tower of 5 levels with the second plank of level 2 left out. -/
def e11 : Build := (squareTower 5).eraseIdx 5
/-- E12. Counterweight: B only stands once C is on it. -/
def e12 : Build := [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 9, 0, 1⟩, ⟨.flatY, 9, -6, 2⟩]

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

-- Buildability, every step (K4 at exact positions, K5).
#guard checkPlan 200 (squareTower 8)
#guard checkPlan 200 e7
#guard !checkPlan 200 e12          -- B falls before C can hold it down
#guard !checkPlan 1 e2             -- more planks than allowed
#guard stabilityAnswer (e12.take 2) == .falls

/-! ## The main theorems apply to real inputs (their hypotheses can be met) -/

example : Stable e2 := stabilityAnswer_stable_sound e2 (by decide +kernel)
example : Stable e3 := stabilityAnswer_stable_sound e3 (by decide +kernel)
example : ¬ Stable e4 := stabilityAnswer_falls_sound e4 (by decide +kernel)
example : ¬ Stable e10 := stabilityAnswer_falls_sound e10 (by decide +kernel)
example : ¬ Stable (e12.take 2) := stabilityAnswer_falls_sound _ (by decide +kernel)
example : StandsAtEveryStep 200 e7 := checkPlan_sound 200 e7 (by decide +kernel)

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

/-- An unstable build is not called stable: E4 is not stable, so no answer "stable". -/
example : stabilityAnswer e4 ≠ .stable := by decide +kernel

/-- A plan whose middle step falls is rejected, and it really does not stand at every step. -/
example : ¬ StandsAtEveryStep 200 e12 := fun h =>
  stabilityAnswer_falls_sound (e12.take 2) (by decide +kernel) (h.2 2 (by decide) (by decide)).2

end KaplaPhysics.Examples
