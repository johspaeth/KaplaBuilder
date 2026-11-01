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
  ∀ i < b.length, ∀ s, s.InBuild b.length → (RestsOn b i s ↔ s = below i)

/-- The planks from level `k` to the top: `k, k+1, ..., n-1`. -/
def fromLevel (b : Build) (k : Nat) : List Nat := List.range' k (b.length - k)

/-- `x` of the combined centre of mass of the planks from level `k` up. All planks weigh
the same, so it is the average of their centres. -/
def comX (b : Build) (k : Nat) : Rat :=
  ((fromLevel b k).map fun m => (b.get m).centerX).sum / ((fromLevel b k).length : Rat)

/-- `y` of the combined centre of mass of the planks from level `k` up. -/
def comY (b : Build) (k : Nat) : Rat :=
  ((fromLevel b k).map fun m => (b.get m).centerY).sum / ((fromLevel b k).length : Rat)

/-- The simple rule for a column: at every level `k`, plank `k` rests on what is below it,
and the combined centre of mass of plank `k` and everything above it lies over the patch
where plank `k` rests (its edges count, S4). -/
def ColumnRule (b : Build) : Prop :=
  ∀ k < b.length, RestsOn b k (below k) ∧ InPatch b k (below k) (comX b k) (comY b k)

/-- Example (E2): the top plank's centre (12.5) is over the patch [5, 15]; the two planks
together have their centre at 10, over the bottom plank's footprint [0, 15]. -/
example : ColumnRule [Plank.at .flatX 0 0 0, Plank.at .flatX 5 0 1] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  have : k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl
  · exact ⟨show (Build.get _ 0).bottom = 0 by decide +kernel, by decide +kernel⟩
  · exact ⟨⟨by decide +kernel, 10, 1, by decide +kernel, by decide +kernel⟩, by decide +kernel⟩

end KaplaPhysics
