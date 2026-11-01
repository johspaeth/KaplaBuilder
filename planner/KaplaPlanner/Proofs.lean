import KaplaPlanner.Search

/-! # What we prove about the planner

The planner is not trusted: the physics engine and the scorer check every plan. These short
theorems make it more reliable (`planner/DESIGN.md` §7):

1. `planPure_sound` (v1) and `candidatesOf_sound` (v2, the end of `planner`): every candidate
   uses at most `N` blocks, and the physics engine said `ok` for it.
2. `planPure_length`, `candidatesOf_length`: there are at most `maxCandidates` candidates.
3. `toPlan_hands`: every step places exactly one block, so it never needs more hands than the
   builder has (at least one).
4. `toPlan_blockCount`: the plan has exactly the blocks it was made from.

They are about the planner's own code. A statement in `specs/` and a `comparator/` entry
would make them part of the reviewed surface; that is a shared change, not made here. -/

namespace KaplaPlanner

open KaplaCore

/-- Every candidate `finalize` keeps is within the block limit and was accepted by physics. -/
theorem finalize_sound (n k : Nat) (cs : List Candidate) :
    ∀ c ∈ finalize n k cs, c.plan.blockCount ≤ n ∧ c.physics.ok = true := by
  intro c hc
  unfold finalize at hc
  have h := List.mem_of_mem_take hc
  rw [List.mem_mergeSort] at h
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- `finalize` keeps at most `k` candidates. -/
theorem finalize_length (n k : Nat) (cs : List Candidate) : (finalize n k cs).length ≤ k := by
  unfold finalize
  exact List.length_take_le _ _

/-- Every candidate of the planner uses at most `N` blocks, and the physics engine said `ok`
for it. -/
theorem planPure_sound (req : PlanRequest) (ph : PhysicsEngine) (sem : SemanticEngine) :
    ∀ c ∈ planPure req ph sem, c.plan.blockCount ≤ req.blocks ∧ c.physics.ok = true := by
  intro c hc
  exact finalize_sound _ _ _ c hc

/-- The planner returns at most `maxCandidates` candidates. -/
theorem planPure_length (req : PlanRequest) (ph : PhysicsEngine) (sem : SemanticEngine) :
    (planPure req ph sem).length ≤ req.maxCandidates := by
  exact finalize_length _ _ _

/-- Every candidate `pick` keeps is within the block limit and was accepted by physics. -/
theorem pick_sound (n k : Nat) (a b : List Candidate) :
    ∀ c ∈ pick n k a b, c.plan.blockCount ≤ n ∧ c.physics.ok = true := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact finalize_sound _ _ _ c h
  · exact finalize_sound _ _ _ c h

/-- `pick` keeps at most `k` candidates. -/
theorem pick_length (n k : Nat) (a b : List Candidate) : (pick n k a b).length ≤ k := by
  unfold pick
  rw [List.length_append]
  have h1 := finalize_length n k a
  have h2 := finalize_length n (k - (finalize n k a).length) b
  omega

/-- Every candidate the v2 planner returns (`candidatesOf`, the last step of `plannerWith`)
uses at most `N` blocks, and the physics engine said `ok` for it. -/
theorem candidatesOf_sound (req : PlanRequest) (sem : SemanticEngine) (trees : List Tree) :
    ∀ c ∈ candidatesOf req sem trees, c.plan.blockCount ≤ req.blocks ∧ c.physics.ok = true :=
  pick_sound _ _ _ _

/-- The v2 planner returns at most `maxCandidates` candidates. -/
theorem candidatesOf_length (req : PlanRequest) (sem : SemanticEngine) (trees : List Tree) :
    (candidatesOf req sem trees).length ≤ req.maxCandidates :=
  pick_length _ _ _ _

/-- Every step of a plan made by `toPlan` places exactly one block. -/
theorem toPlan_hands (bs : List GBlock) : ∀ s ∈ (toPlan bs).steps, s.blocks.length = 1 := by
  intro s hs
  simp only [toPlan, List.mem_map] at hs
  obtain ⟨b, _, rfl⟩ := hs
  rfl

/-- The plan made by `toPlan` has one block per grid block. -/
theorem toPlan_blockCount (bs : List GBlock) : (toPlan bs).blockCount = bs.length := by
  unfold toPlan BuildPlan.blockCount BuildPlan.blocks
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.flatMap_cons, List.length_append, List.length_cons] at *
    rw [ih]
    simp only [List.length_nil]
    omega

/-! ## The statements are not empty -/

/-- Example: a candidate the physics engine accepted, with one block. -/
private def goodCandidate : Candidate :=
  { plan := toPlan [⟨.flatX, 0, 0, 0⟩], physics := { ok := true }, score := { score := 1 / 2 },
    difficulty := .easy }

/-- Example: the same plan, rejected by physics. -/
private def rejected : Candidate := { goodCandidate with physics := { ok := false } }

-- A good candidate is kept, so `finalize_sound` is about a list that can be non-empty.
#guard (finalize 1 3 [goodCandidate]).length == 1
-- A plan that physics rejected is dropped, and so is one with too many blocks.
#guard (finalize 1 3 [rejected]).isEmpty
#guard (finalize 0 3 [goodCandidate]).isEmpty
-- At most `k` are kept.
#guard (finalize 1 1 [goodCandidate, goodCandidate]).length == 1
-- The step count of an example plan.
example : (toPlan [⟨.flatX, 0, 0, 0⟩, ⟨.flatY, 0, 0, 1⟩]).blockCount = 2 := toPlan_blockCount _

end KaplaPlanner
