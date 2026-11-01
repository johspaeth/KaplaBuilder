import KaplaSpecs.PhysicsRules.Rules

/-! # The simple rule for a single column (section 7, property 6)

In a single column of planks, the build is stable exactly when, at every level, the
combined centre of mass of everything from that level up is over the contact patch below
that level. `column_stable_iff` (stated in `KaplaSpecs/Physics.lean`) proves that `Stable` agrees with this
rule for every column. -/

namespace KaplaPhysics

/-- What plank `i` rests on in a single column: the ground for the bottom plank, the plank
just below it otherwise. -/
def below : Nat → Support
  | 0 => .ground
  | i + 1 => .plank i

/-- The build is a single column: each plank rests on the plank just below it (the bottom
plank on the ground), and on nothing else. -/
def IsColumn (b : Build) : Prop :=
  ∀ i < b.length, ∀ s, s.InBuild b.length → ((restPatch b i s).isSome ↔ s = below i)

instance (b : Build) : Decidable (IsColumn b) := by
  unfold IsColumn
  refine @Nat.decidableBallLT _ _ fun i _ => ?_
  -- Only the ground and planks `0 .. n-1` are in the build.
  exact decidable_of_iff (∀ s ∈ Support.ground :: (List.range b.length).map Support.plank,
      ((restPatch b i s).isSome ↔ s = below i)) (by
    constructor
    · intro h s hs
      cases s with
      | ground => exact h _ (by simp)
      | plank j => exact h _ (by simp [Support.InBuild] at hs ⊢; exact hs)
    · intro h s hs
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hs
      rcases hs with rfl | ⟨j, hj, rfl⟩
      · exact h _ trivial
      · exact h _ hj)

/-- The planks from level `k` to the top: `k, k+1, ..., n-1`. -/
def fromLevel (b : Build) (k : Nat) : List Nat := List.range' k (b.length - k)

/-- `x` of the combined centre of mass of the planks from level `k` up. All planks weigh
the same, so it is the average of their centres. -/
def comX (b : Build) (k : Nat) : Rat :=
  ((fromLevel b k).map fun m => (b.get m).centerX).sum / ((fromLevel b k).length : Rat)

/-- `y` of the combined centre of mass of the planks from level `k` up. -/
def comY (b : Build) (k : Nat) : Rat :=
  ((fromLevel b k).map fun m => (b.get m).centerY).sum / ((fromLevel b k).length : Rat)

/-- The simple rule for a column: at every level `k`, the combined centre of mass of
plank `k` and everything above it lies over the patch where plank `k` rests (its edges
count, S4). -/
def ColumnRule (b : Build) : Prop :=
  ∀ k < b.length,
    match restPatch b k (below k) with
    | some r => r.Contains (comX b k) (comY b k)
    | none => False

instance (b : Build) : Decidable (ColumnRule b) := by
  unfold ColumnRule
  refine @Nat.decidableBallLT _ _ fun k _ => ?_
  cases restPatch b k (below k) <;> unfold Rect.Contains <;> infer_instance

/-- Example (E2): the top plank's centre (12.5) is over the patch [5, 15]; the two planks
together have their centre at 10, over the bottom plank's footprint [0, 15]. -/
example : ColumnRule [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 5, 0, 1⟩] := by decide +kernel

end KaplaPhysics
