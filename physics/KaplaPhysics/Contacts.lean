import KaplaPhysics.Affine

/-! # Checking contacts and placement (C1–C4, P1–P3)

The rules say "some point is strictly inside both planks" (`SharesArea`). The engine
checks this with a point it computes (the average of the corners of the clipped patch),
and the opposite with weights on the sides (`sepCheck`). Each check is followed by a
proof that it is right; the points and weights themselves are not trusted. -/

namespace KaplaPhysics

open KaplaCore (Pose)

/-- A point that is probably strictly inside both planks, if they share some area. -/
def innerPoint (p q : Plank) : Option (Rat × Rat) := average (patchPoly p q)

/-- The two planks share some area: the computed point is strictly inside both. -/
def sharesCheck (p q : Plank) : Bool :=
  match innerPoint p q with
  | some (x, y) => decide (p.CoversInside x y) && decide (q.CoversInside x y)
  | none => false

theorem sharesCheck_sound (p q : Plank) (h : sharesCheck p q = true) : SharesArea p q := by
  unfold sharesCheck at h
  split at h
  · rename_i x y _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨x, y, h.1, h.2⟩
  · cases h

/-- C1–C3, checked: plank `i` rests on `s`. -/
def restsCheck (b : Build) (i : Nat) : Support → Bool
  | .ground => decide ((b.get i).bottom = 0)
  | .plank j => decide ((b.get i).bottom = (b.get j).top) && sharesCheck (b.get i) (b.get j)

theorem restsCheck_sound (b : Build) (i : Nat) (s : Support) (h : restsCheck b i s = true) :
    RestsOn b i s := by
  cases s with
  | ground => simpa [restsCheck, RestsOn] using h
  | plank j =>
    simp only [restsCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, sharesCheck_sound _ _ h.2⟩

/-- The sides of the contact patch where plank `i` rests on `s`: `i`'s, and `j`'s for a
plank `j`. -/
def contactForms (b : Build) (i : Nat) : Support → List Aff
  | .ground => (b.get i).sides
  | .plank j => (b.get i).sides ++ (b.get j).sides

/-- A point is in the patch exactly when every side of the patch is at least zero there. -/
theorem inPatch_iff (b : Build) (i : Nat) (s : Support) (x y : Rat) :
    InPatch b i s x y ↔ ∀ g ∈ contactForms b i s, 0 ≤ g.eval x y := by
  cases s with
  | ground => simp [InPatch, contactForms, covers_iff_sides]
  | plank j =>
    simp only [InPatch, contactForms, covers_iff_sides, List.mem_append]
    constructor
    · rintro ⟨h1, h2⟩ g (hg | hg)
      · exact h1 g hg
      · exact h2 g hg
    · intro h; exact ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩

/-- The corners of the contact patch (untrusted: used to propose pushes). -/
def patchCorners (b : Build) (i : Nat) : Support → List (Rat × Rat)
  | .ground => (b.get i).corners2
  | .plank j => patchPoly (b.get i) (b.get j)

/-- One plank is completely above the other. -/
def heightsApart (p q : Plank) : Bool := decide (p.top ≤ q.bottom) || decide (q.top ≤ p.bottom)

/-- P1, checked: the planks share no inside space. -/
def noOverlapCheck (p q : Plank) : Bool := heightsApart p q || sepCheck 0 p q

theorem noOverlapCheck_sound (p q : Plank) (h : noOverlapCheck p q = true) : ¬ Overlap p q := by
  rintro ⟨hz, hs⟩
  simp only [noOverlapCheck, heightsApart, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · grind
  · grind
  · obtain ⟨s, hf, hv⟩ := sepCheck_sound 0 p q h
    exact s.no_share p q hf (by grind) hs

/-- P1–P3 and B6, checked: the build is well-formed. -/
def wellFormedCheck (b : Build) : Bool :=
  (List.range b.length).all fun i =>
    decide ((b.get i).rot.Allowed) && decide (0 ≤ (b.get i).bottom) &&
      (List.range b.length).all (fun j => i == j || noOverlapCheck (b.get i) (b.get j)) &&
      (restsCheck b i .ground || (List.range b.length).any fun j => restsCheck b i (.plank j))

theorem wellFormedCheck_sound (b : Build) (h : wellFormedCheck b = true) : WellFormed b := by
  simp only [wellFormedCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
  refine ⟨fun i hi => (h i hi).1.1.1, fun i hi j hj hij => ?_, fun i hi => (h i hi).1.1.2,
    fun i hi => ?_⟩
  · rcases (h i hi).1.2 j hj with h' | h'
    · exact absurd h' hij
    · exact noOverlapCheck_sound _ _ h'
  · rcases (h i hi).2 with h' | ⟨j, hj, h'⟩
    · exact Or.inl (restsCheck_sound _ _ _ h')
    · exact Or.inr ⟨j, hj, restsCheck_sound _ _ _ h'⟩

/-- R5, checked: the planks meet (touch or share inside space). -/
def meetsCheck (p q : Plank) : Bool :=
  decide (p.bottom ≤ q.top) && decide (q.bottom ≤ p.top) &&
    match average (patchPoly p q) with
    | some (x, y) => decide (p.Covers x y) && decide (q.Covers x y)
    | none => false

theorem meetsCheck_sound (p q : Plank) (h : meetsCheck p q = true) : Meets p q := by
  unfold meetsCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨h1, h2⟩, ?_⟩
  split at h3
  · rename_i x y _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
    exact ⟨x, y, h3.1, h3.2⟩
  · cases h3

end KaplaPhysics
