import KaplaSpecs.PhysicsRules.Tower

/-! # Worked examples (section 12 of `spec/physics-rules.md`)

The builds E1–E12, written once here so the spec and the engine's tests use the same ones.
A few facts follow from the rules alone, with no engine: E1 stands, and a flat plank whose
centre is past the end of the plank below it falls (E4). The spec uses them to show that
its theorems rule out wrong answers. -/

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

/-- E8 is `squareTower n` (in `Tower.lean`). -/
example : squareTower 1 = [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 0, 12, 0⟩] := by decide +kernel

/-- E9. Bridge on two standing planks at `y = 1`. -/
def e9 : Build := [⟨.standFacingY, 0, 1, 0⟩, ⟨.standFacingY, 12, 1, 0⟩, ⟨.flatX, 0, 0, 15⟩]
/-- E10. Same bridge with the standing planks at `y = 0`. -/
def e10 : Build := [⟨.standFacingY, 0, 0, 0⟩, ⟨.standFacingY, 12, 0, 0⟩, ⟨.flatX, 0, 0, 15⟩]
/-- E11. Square tower of 5 levels with the second plank of level 2 left out. -/
def e11 : Build := (squareTower 5).eraseIdx 5

/-- E12's plank A: flat on the ground. -/
def e12A : Plank := ⟨.flatX, 0, 0, 0⟩
/-- E12's plank B: on A, sticking out past A's end. -/
def e12B : Plank := ⟨.flatX, 9, 0, 1⟩
/-- E12's plank C: across B, as a counterweight. -/
def e12C : Plank := ⟨.flatY, 9, -6, 2⟩
/-- E12. Counterweight: B only stands once C is on it. -/
def e12 : Build := [e12A, e12B, e12C]

/-- A slot with no gap above: a plank already sits right where the new plank must be
lifted to before its drop (the "real problem" case of K3). -/
def slotPlaced : Build := [⟨.flatX, 0, 0, 1⟩]
/-- The plank that should go into the slot under `slotPlaced`. -/
def slotPlank : Plank := ⟨.flatX, 0, 0, 0⟩

/-- A plank under a roof on two walls: it can still slide in from the open side. -/
def underRoof : Build := [⟨.edgeY, 0, 0, 0⟩, ⟨.edgeY, 14, 0, 0⟩, ⟨.flatX, 0, 0, 3⟩]

/-! ## E1 stands

The ground pushes up with 1/4 at each corner of the plank. -/

/-- Pushes that hold up E1: a quarter of its weight at each corner. -/
def e1Pushes : List Push :=
  [⟨0, .ground, 0, 0, 1 / 4⟩, ⟨0, .ground, 15, 0, 1 / 4⟩,
   ⟨0, .ground, 0, 3, 1 / 4⟩, ⟨0, .ground, 15, 3, 1 / 4⟩]

/-- E1 is stable (S2). -/
theorem e1_stable : Stable e1 := ⟨e1Pushes, by decide +kernel⟩

/-! ## A plank past the edge falls

Plank 1 lies flat on plank 0, shifted `a` along `x`. When `a > 7.5`, its centre
(`a + 7.5`) is past the end of plank 0 (at 15). Every push on plank 1 is at a corner of the
patch they share, so at `x ≤ 15`: all pushes are on one side of the centre, and they turn
the plank. No choice of pushes balances it. This covers E4 (`a = 8`), E3 moved by the
placement error, and the first two planks of E12 (`a = 9`). -/

/-- Two flat planks along `x`; the top one shifted `a` along `x`. -/
def overhang (a : Rat) : Build := [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, a, 0, 1⟩]

example : overhang 8 = e4 := rfl

/-- Each allowed push lifts plank 1 at a point at least `a - 7.5` before its centre. -/
theorem overhang_push (a : Rat) (p : Push) (hp : p.Allowed (overhang a)) :
    p.upOn 1 * (p.x - ((overhang a).get 1).centerX) ≤ -(a - 15 / 2) * p.upOn 1 := by
  obtain ⟨hf, hu, hl, hm⟩ := hp
  rcases p with ⟨upper, lower, x, y, force⟩
  simp only [overhang, List.length_cons, List.length_nil] at hu hl
  have hu' : upper = 0 ∨ upper = 1 := by omega
  have get0 : (overhang a).get 0 = ⟨.flatX, 0, 0, 0⟩ := rfl
  have get1 : (overhang a).get 1 = ⟨.flatX, a, 0, 1⟩ := rfl
  cases lower with
  | ground =>
    rcases hu' with rfl | rfl
    -- A push under plank 0 does not lift plank 1.
    · simp [Push.upOn] <;> grind
    -- Plank 1 is not on the ground.
    · simp [restPatch, get1] at hm
  | plank j =>
    have hj : j = 0 ∨ j = 1 := by simp [Support.InBuild] at hl; omega
    rcases hu' with rfl | rfl <;> rcases hj with rfl | rfl
    -- Plank 0 on itself: does not lift plank 1.
    · simp [Push.upOn] <;> grind
    -- Nothing rests on plank 1: its top is at 2, and no plank has its bottom there.
    · simp only [restPatch, get0, get1, Plank.top, Pose.size] at hm
      split at hm <;> grind
    -- Plank 1 on plank 0: the push is at a corner of the patch, so `x ≤ 15`.
    · simp only [restPatch, get0, get1] at hm
      split at hm
      next h =>
        simp only [Rect.corners, Rect.inter, Rect.HasArea, Plank.footprint, Plank.x1,
          Plank.y1, Pose.size, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq,
          or_false] at hm h
        have hx : x - (a + 15 / 2) ≤ -(a - 15 / 2) := by
          rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> grind
        have := Rat.mul_le_mul_of_nonneg_left hx hf
        simp [Push.upOn, get1, Plank.centerX, Pose.size]
        grind
      next => exact hm.elim
    · simp only [restPatch, get1, Plank.top, Pose.size] at hm
      split at hm <;> grind

/-- Summed over all pushes: the turning on plank 1 is at most `-(a - 7.5)` times its net
lift. -/
theorem overhang_sum (a : Rat) (ps : List Push) (hall : ∀ p ∈ ps, p.Allowed (overhang a)) :
    (ps.map fun p => p.upOn 1 * (p.x - ((overhang a).get 1).centerX)).sum ≤
      -(a - 15 / 2) * (ps.map fun p => p.upOn 1).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := overhang_push a p (hall p (by simp))
    have h2 := ih fun q hq => hall q (by simp [hq])
    grind

/-- A flat plank whose centre is past the end of the plank below falls (S3). -/
theorem overhang_not_stable (a : Rat) (ha : 15 / 2 < a) : ¬ Stable (overhang a) := by
  intro ⟨ps, hall, hbal⟩
  obtain ⟨hlift, hturn, -⟩ := hbal 1 (by simp [overhang])
  have := overhang_sum a ps hall
  rw [hturn, hlift] at this
  grind

/-- E4 falls (S3). -/
theorem e4_not_stable : ¬ Stable e4 := overhang_not_stable 8 (by decide +kernel)

/-- With no placement error, the build stays where it is. -/
theorem shift_zero (b : Build) : b.shift (fun _ => (0, 0)) = b := by
  apply List.ext_getElem <;> simp [Build.shift, Rat.add_zero]

/-- A build that is not stable is not solid either, for any error `ε`: "solid" asks
`ε ≥ 0`, so "no error" is one of the errors allowed. -/
theorem not_solid_of_not_stable (ε : Rat) (b : Build) (h : ¬ Stable b) :
    ¬ SolidWithin ε b := fun ⟨hε, hs⟩ =>
  h (shift_zero b ▸ hs _ fun _ _ => ⟨by grind, hε, by grind, hε⟩)

/-- E3 is not solid: moving its top plank 2 mm towards the open end makes it fall (R3). -/
theorem e3_not_solid : ¬ SolidWithin placementError e3 := fun h => by
  have hshift : e3.shift (fun i => if i = 1 then (placementError, 0) else (0, 0)) =
      overhang (15 / 2 + placementError) := by decide +kernel
  have hsmall : SmallShift placementError e3.length
      (fun i => if i = 1 then (placementError, 0) else (0, 0)) := by
    intro i _; dsimp only; split <;> simp [placementError] <;> grind
  exact overhang_not_stable _ (by decide +kernel) (hshift ▸ h.2 _ hsmall)

/-! ## A plank in the air does not stand, even with friction -/

/-- One flat plank at height 1, with nothing under it. -/
def floating : Build := [⟨.flatX, 0, 0, 1⟩]

/-- No push touches the floating plank: it does not rest on anything (P3). -/
theorem floating_no_push (p : Push) (hp : p.Allowed floating) : False := by
  obtain ⟨-, hu, hl, hm⟩ := hp
  rcases p with ⟨upper, lower, x, y, force⟩
  simp only [floating, List.length_cons, List.length_nil] at hu hl
  obtain rfl : upper = 0 := by omega
  have get0 : floating.get 0 = ⟨.flatX, 0, 0, 1⟩ := rfl
  cases lower with
  | ground => simp only [restPatch, get0] at hm; split at hm <;> grind
  | plank j =>
    obtain rfl : j = 0 := by simp [Support.InBuild] at hl; omega
    simp only [restPatch, get0, Plank.top, Pose.size] at hm; split at hm <;> grind

/-- The floating plank is not stable with friction, for any friction coefficient (F3). -/
theorem floating_not_stableWithFriction (μ : Rat) : ¬ StableWithFriction μ floating := by
  intro ⟨ps, hall, hbal⟩
  have h := (hbal 0 (by decide)).1
  cases ps with
  | nil => simp at h
  | cons p _ => exact floating_no_push p.push (hall p (by simp)).1

/-! ## A slot with no room above cannot be reached (K3) -/

/-- Placing `slotPlank` after `slotPlaced` cannot be done by any straight path: the very
first point of every path, `dropGap` above the spot, is where the placed plank already is. -/
theorem slot_not_reachable : ¬ EveryStepReachable dropGap (slotPlaced ++ [slotPlank]) := by
  intro h
  obtain ⟨v, -, -, -, hpath, -⟩ := h 1 (by decide)
  apply hpath 0 (by decide) ⟨.flatX, 0, 0, 1⟩ (by decide)
  simp only [Rat.zero_mul, Rat.add_zero]
  decide +kernel

end KaplaPhysics.Examples
