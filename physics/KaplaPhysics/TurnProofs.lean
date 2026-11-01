import KaplaPhysics.TowerProofs

/-! # Turning a whole build (property 9 for turned towers)

Turning every plank of a build by the same real turn `r` about the vertical line through
the origin changes nothing about how it stands: the planks touch in the same way, and
pushes turned along balance them. Only the placement errors change: an error of at most
`ε` along `x` and along `y` in the turned build is, seen from the unturned build, an error
of at most `ε * (|cos| + |sin|)` along each axis.

So a safe plan for errors up to `ε * (|cos| + |sin|)` is still safe after turning, for
errors up to `ε` (`safePlan_turn`). `Proofs.lean` uses this for the turned square tower. -/

namespace KaplaPhysics

open KaplaCore (Pose Rot Q3)

/-! ## Turning points -/

/-- `x` of the point `(x, y)` turned by `r`. -/
def turnX (r : Rot) (x y : Rat) : Rat := r.cos * x - r.sin * y
/-- `y` of the point `(x, y)` turned by `r`. -/
def turnY (r : Rot) (x y : Rat) : Rat := r.sin * x + r.cos * y

/-- The turn back, for a real turn. -/
def unturn (r : Rot) : Rot := ⟨r.cos, -r.sin⟩

/-- A real turn: `cos² + sin² = 1`. -/
def IsTurn (r : Rot) : Prop := r.cos * r.cos + r.sin * r.sin = 1

theorem turn_unturn (r : Rot) (hr : IsTurn r) (x y : Rat) :
    turnX r (turnX (unturn r) x y) (turnY (unturn r) x y) = x ∧
      turnY r (turnX (unturn r) x y) (turnY (unturn r) x y) = y := by
  simp only [IsTurn] at hr
  simp only [turnX, turnY, unturn]
  constructor
  · have : r.cos * (r.cos * x - -r.sin * y) - r.sin * (-r.sin * x + r.cos * y)
        = (r.cos * r.cos + r.sin * r.sin) * x := by grind
    rw [this, hr]; grind
  · have : r.sin * (r.cos * x - -r.sin * y) + r.cos * (-r.sin * x + r.cos * y)
        = (r.cos * r.cos + r.sin * r.sin) * y := by grind
    rw [this, hr]; grind

/-! ## One plank -/

theorem turn_center (r : Rot) (p : Plank) :
    (p.turn r).center = ⟨turnX r p.center.x p.center.y, turnY r p.center.x p.center.y, p.center.z⟩ :=
  rfl

theorem turn_size (r : Rot) (p : Plank) : (p.turn r).size = p.size := rfl

theorem turn_bottom (r : Rot) (p : Plank) : (p.turn r).bottom = p.bottom := rfl

theorem turn_top (r : Rot) (p : Plank) : (p.turn r).top = p.top := rfl

theorem along_turn (r : Rot) (hr : IsTurn r) (p : Plank) (x y : Rat) :
    (p.turn r).alongLength (turnX r x y) (turnY r x y) = p.alongLength x y ∧
      (p.turn r).alongWidth (turnX r x y) (turnY r x y) = p.alongWidth x y := by
  simp only [IsTurn] at hr
  simp only [Pose.alongLength, Pose.alongWidth, Pose.turn, Rot.comp, Rot.apply, turnX, turnY]
  constructor
  · have : (r.cos * p.rot.cos - r.sin * p.rot.sin) *
          (r.cos * x - r.sin * y - (r.cos * p.center.x - r.sin * p.center.y)) +
        (r.sin * p.rot.cos + r.cos * p.rot.sin) *
          (r.sin * x + r.cos * y - (r.sin * p.center.x + r.cos * p.center.y))
        = (r.cos * r.cos + r.sin * r.sin) *
          (p.rot.cos * (x - p.center.x) + p.rot.sin * (y - p.center.y)) := by grind
    rw [this, hr]; grind
  · have : -(r.sin * p.rot.cos + r.cos * p.rot.sin) *
          (r.cos * x - r.sin * y - (r.cos * p.center.x - r.sin * p.center.y)) +
        (r.cos * p.rot.cos - r.sin * p.rot.sin) *
          (r.sin * x + r.cos * y - (r.sin * p.center.x + r.cos * p.center.y))
        = (r.cos * r.cos + r.sin * r.sin) *
          (-p.rot.sin * (x - p.center.x) + p.rot.cos * (y - p.center.y)) := by grind
    rw [this, hr]; grind

theorem covers_turn (r : Rot) (hr : IsTurn r) (p : Plank) (x y : Rat) :
    (p.turn r).Covers (turnX r x y) (turnY r x y) ↔ p.Covers x y := by
  obtain ⟨h1, h2⟩ := along_turn r hr p x y
  simp only [Pose.Covers, turn_size, h1, h2]

theorem coversInside_turn (r : Rot) (hr : IsTurn r) (p : Plank) (x y : Rat) :
    (p.turn r).CoversInside (turnX r x y) (turnY r x y) ↔ p.CoversInside x y := by
  obtain ⟨h1, h2⟩ := along_turn r hr p x y
  simp only [Pose.CoversInside, turn_size, h1, h2]

theorem sharesArea_turn (r : Rot) (hr : IsTurn r) (p q : Plank) :
    SharesArea (p.turn r) (q.turn r) ↔ SharesArea p q := by
  constructor
  · rintro ⟨X, Y, h1, h2⟩
    obtain ⟨ex, ey⟩ := turn_unturn r hr X Y
    refine ⟨turnX (unturn r) X Y, turnY (unturn r) X Y, ?_, ?_⟩
    · rw [← coversInside_turn r hr, ex, ey]; exact h1
    · rw [← coversInside_turn r hr, ex, ey]; exact h2
  · rintro ⟨x, y, h1, h2⟩
    exact ⟨turnX r x y, turnY r x y, (coversInside_turn r hr p x y).mpr h1,
      (coversInside_turn r hr q x y).mpr h2⟩

theorem overlap_turn (r : Rot) (hr : IsTurn r) (p q : Plank) :
    Overlap (p.turn r) (q.turn r) ↔ Overlap p q := by
  simp only [Overlap, turn_bottom, turn_top, sharesArea_turn r hr]

theorem meets_turn (r : Rot) (hr : IsTurn r) (p q : Plank) :
    Meets (p.turn r) (q.turn r) ↔ Meets p q := by
  simp only [Meets, turn_bottom, turn_top]
  constructor
  · rintro ⟨hz, X, Y, h1, h2⟩
    obtain ⟨ex, ey⟩ := turn_unturn r hr X Y
    refine ⟨hz, turnX (unturn r) X Y, turnY (unturn r) X Y, ?_, ?_⟩
    · rw [← covers_turn r hr, ex, ey]; exact h1
    · rw [← covers_turn r hr, ex, ey]; exact h2
  · rintro ⟨hz, x, y, h1, h2⟩
    exact ⟨hz, turnX r x y, turnY r x y, (covers_turn r hr p x y).mpr h1,
      (covers_turn r hr q x y).mpr h2⟩

/-! ## A whole build -/

/-- The build with every plank turned by `r`. -/
def Build.turn (r : Rot) (b : Build) : Build := b.map (·.turn r)

@[simp] theorem turn_length (r : Rot) (b : Build) : (b.turn r).length = b.length := by
  simp [Build.turn]

theorem turn_get (r : Rot) (b : Build) (i : Nat) (h : i < b.length) :
    (b.turn r).get i = (b.get i).turn r := by
  simp [Build.turn, Build.get, List.getD_eq_getElem?_getD, h]

theorem restsOn_turn (r : Rot) (hr : IsTurn r) (b : Build) (i : Nat) (s : Support)
    (hi : i < b.length) (hs : s.InBuild b.length) :
    RestsOn (b.turn r) i s ↔ RestsOn b i s := by
  cases s with
  | ground => simp only [RestsOn, turn_get r b i hi, turn_bottom]
  | plank j =>
    have hj : j < b.length := hs
    simp only [RestsOn, turn_get r b i hi, turn_get r b j hj, turn_bottom, turn_top,
      sharesArea_turn r hr]

theorem inPatch_turn (r : Rot) (hr : IsTurn r) (b : Build) (i : Nat) (s : Support)
    (hi : i < b.length) (hs : s.InBuild b.length) (x y : Rat) :
    InPatch (b.turn r) i s (turnX r x y) (turnY r x y) ↔ InPatch b i s x y := by
  cases s with
  | ground => simp only [InPatch, turn_get r b i hi, covers_turn r hr]
  | plank j =>
    have hj : j < b.length := hs
    simp only [InPatch, turn_get r b i hi, turn_get r b j hj, covers_turn r hr]

/-- The push turned along with the build. -/
def Push.turn (r : Rot) (p : Push) : Push :=
  { p with x := turnX r p.x p.y, y := turnY r p.x p.y }

/-- A stable build stays stable when turned: the turned pushes balance it. -/
theorem stable_turn (r : Rot) (hr : IsTurn r) (b : Build) (h : Stable b) : Stable (b.turn r) := by
  obtain ⟨ps, hall, hbal⟩ := h
  refine ⟨ps.map (Push.turn r), ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hf, hu, hl, hrest, hin⟩ := hall p hp
    refine ⟨hf, by simpa [Push.turn] using hu, by simpa [Push.turn] using hl, ?_, ?_⟩
    · exact (restsOn_turn r hr b p.upper p.lower hu hl).mpr hrest
    · exact (inPatch_turn r hr b p.upper p.lower hu hl p.x p.y).mpr hin
  · intro i hi
    rw [turn_length] at hi
    obtain ⟨h1, h2, h3⟩ := hbal i hi
    have hupOn : ∀ p : Push, (p.turn r).upOn i = p.upOn i := fun _ => rfl
    have cx : ((b.turn r).get i).centerX = turnX r (b.get i).centerX (b.get i).centerY := by
      rw [turn_get r b i hi]; rfl
    have cy : ((b.turn r).get i).centerY = turnY r (b.get i).centerX (b.get i).centerY := by
      rw [turn_get r b i hi]; rfl
    unfold Balanced
    simp only [List.map_map, Function.comp_def, hupOn, cx, cy]
    refine ⟨h1, ?_, ?_⟩
    · rw [sum_map_congr _ _ (fun p => r.cos * (p.upOn i * (p.x - (b.get i).centerX))
          - r.sin * (p.upOn i * (p.y - (b.get i).centerY)))
          (fun p _ => by simp only [Push.turn, turnX]; grind),
        sum_map_sub, sum_map_mul_left, sum_map_mul_left, h2, h3]
      grind
    · rw [sum_map_congr _ _ (fun p => r.sin * (p.upOn i * (p.x - (b.get i).centerX))
          + r.cos * (p.upOn i * (p.y - (b.get i).centerY)))
          (fun p _ => by simp only [Push.turn, turnY]; grind),
        sum_map_add, sum_map_mul_left, sum_map_mul_left, h2, h3]
      grind

theorem wellFormed_turn (r : Rot) (hr : IsTurn r) (b : Build)
    (hallowed : ∀ i < b.length, (r.comp (b.get i).rot).Allowed) (h : WellFormed b) :
    WellFormed (b.turn r) := by
  obtain ⟨_, hno, hab, hrest⟩ := h
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [turn_length] at hi
    rw [turn_get r b i hi]; exact hallowed i hi
  · rw [turn_length] at hi hj
    rw [turn_get r b i hi, turn_get r b j hj, overlap_turn r hr]; exact hno i hi j hj hij
  · rw [turn_length] at hi
    rw [turn_get r b i hi, turn_bottom]; exact hab i hi
  · rw [turn_length] at hi ⊢
    rcases hrest i hi with h | ⟨j, hj, h⟩
    · exact Or.inl ((restsOn_turn r hr b i .ground hi trivial).mpr h)
    · exact Or.inr ⟨j, hj, (restsOn_turn r hr b i (.plank j) hi hj).mpr h⟩

/-! ## Placement errors -/

/-- An error `e` in the turned build, seen from the unturned build. -/
def unturnError (r : Rot) (e : Rat × Rat) : Rat × Rat :=
  (turnX (unturn r) e.1 e.2, turnY (unturn r) e.1 e.2)

/-- `|cos| + |sin|`: how much bigger an error can look after turning. -/
def spread (r : Rot) : Rat := max r.cos (-r.cos) + max r.sin (-r.sin)

theorem turn_moveBy (r : Rot) (hr : IsTurn r) (p : Plank) (e : Rat × Rat) :
    (p.moveBy (unturnError r e).1 (unturnError r e).2 0).turn r = (p.turn r).moveBy e.1 e.2 0 := by
  obtain ⟨ex, ey⟩ := turn_unturn r hr e.1 e.2
  simp only [Pose.turn, Pose.moveBy, Rot.apply, unturnError, KaplaCore.Pose.mk.injEq,
    KaplaCore.Q3.mk.injEq, true_and, turnX, turnY]
  simp only [turnX, turnY] at ex ey
  refine ⟨?_, ?_, ?_⟩ <;> grind

theorem shift_turn (r : Rot) (hr : IsTurn r) (b : Build) (d : Nat → Rat × Rat) :
    (b.turn r).shift d = (b.shift fun i => unturnError r (d i)).turn r := by
  apply List.ext_getElem
  · simp [Build.shift, Build.turn]
  · intro i h1 h2
    simp only [Build.shift, Build.turn, List.getElem_mapIdx, List.getElem_map]
    exact (turn_moveBy r hr _ (d i)).symm

theorem smallShift_unturn (r : Rot) (ε ε' : Rat) (hle : ε * spread r ≤ ε') (n : Nat)
    (d : Nat → Rat × Rat) (hd : SmallShift ε n d) :
    SmallShift ε' n fun i => unturnError r (d i) := by
  intro i hi
  obtain ⟨h1, h2, h3, h4⟩ := hd i hi
  have a := Aff.lin_le ⟨r.cos, r.sin, 0⟩ ε (d i).1 (d i).2 ⟨h1, h2⟩ ⟨h3, h4⟩
  have c := Aff.lin_le ⟨-r.sin, r.cos, 0⟩ ε (d i).1 (d i).2 ⟨h1, h2⟩ ⟨h3, h4⟩
  have hs : (⟨-r.sin, r.cos, 0⟩ : Aff).slope = (⟨r.cos, r.sin, 0⟩ : Aff).slope := by
    simp only [Aff.slope]; grind
  rw [hs] at c
  have hS : ε * (⟨r.cos, r.sin, 0⟩ : Aff).slope ≤ ε' := hle
  generalize ε * (⟨r.cos, r.sin, 0⟩ : Aff).slope = S at a c hS
  simp only [unturnError, turnX, turnY, unturn]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem solid_turn (r : Rot) (hr : IsTurn r) (ε ε' : Rat) (hε : 0 ≤ ε)
    (hle : ε * spread r ≤ ε') (b : Build) (h : SolidWithin ε' b) : SolidWithin ε (b.turn r) := by
  refine ⟨hε, fun d hd => ?_⟩
  rw [turn_length] at hd
  rw [shift_turn r hr]
  exact stable_turn r hr _ (h.2 _ (smallShift_unturn r ε ε' hle _ d hd))

theorem keepsGaps_turn (r : Rot) (hr : IsTurn r) (ε ε' : Rat) (hle : ε * spread r ≤ ε')
    (b : Build) (h : KeepsGaps ε' b) : KeepsGaps ε (b.turn r) := by
  intro d hd i hi j hj hm
  rw [turn_length] at hd hi hj
  rw [turn_get r b i hi, turn_get r b j hj, meets_turn r hr] at hm
  rw [shift_turn r hr, turn_get r _ i (by simpa using hi), turn_get r _ j (by simpa using hj),
    overlap_turn r hr]
  exact h _ (smallShift_unturn r ε ε' hle _ d hd) i hi j hj hm

theorem turn_take (r : Rot) (b : Build) (k : Nat) :
    (b.turn r).take k = Build.turn r (b.take k) := by
  simp [Build.turn]

/-- A safe plan stays safe when turned by a real turn whose turned planks are allowed, for
placement errors up to `ε` when it was safe for errors up to `ε * (|cos| + |sin|)`. -/
theorem safePlan_turn (r : Rot) (hr : IsTurn r) (opts : PlanOptions) (ε ε' : Rat) (hε : 0 ≤ ε)
    (hle : ε * spread r ≤ ε') (maxPlanks : Nat) (steps : Build)
    (hallowed : ∀ i < steps.length, (r.comp (steps.get i).rot).Allowed)
    (h : SafePlan opts ε' maxPlanks steps) : SafePlan opts ε maxPlanks (steps.turn r) := by
  refine ⟨by simpa using h.1, fun k hk1 hk2 => ?_⟩
  rw [turn_length] at hk2
  obtain ⟨hw, hg, hs⟩ := h.2 k hk1 hk2
  rw [turn_take]
  have hall : ∀ i < (steps.take k).length,
      (r.comp (Build.get (steps.take k) i).rot).Allowed := by
    intro i hi
    simp only [List.length_take] at hi
    have : Build.get (steps.take k) i = steps.get i := by
      simp [Build.get, List.getD_eq_getElem?_getD, show i < k by omega]
    rw [this]; exact hallowed i (by omega)
  exact ⟨wellFormed_turn r hr _ hall hw, fun ho => keepsGaps_turn r hr ε ε' hle _ (hg ho),
    solid_turn r hr ε ε' hε hle _ hs⟩

/-! ## Allowed turns stay allowed -/

/-- Turning an allowed turn by a quarter turn gives an allowed turn. -/
theorem allowed_comp_quarter (r : Rot) (hr : r.Allowed) : (r.comp .quarter).Allowed := by
  obtain ⟨h1, h2⟩ := hr
  simp only [Rot.comp, Rot.quarter]
  simp only [Rot.Allowed, Rot.Allowed.near]
  simp only [Rot.Allowed.near] at h2
  constructor
  · grind
  · have e : (r.sin * 0 + r.cos * 1) * (r.sin * 0 + r.cos * 1) = 1 - r.sin * r.sin := by grind
    rw [e]; grind

theorem allowed_comp_id (r : Rot) (hr : r.Allowed) : (r.comp .id).Allowed := by
  have : r.comp .id = r := by
    obtain ⟨c, s⟩ := r
    simp only [Rot.comp, Rot.id, Rot.mk.injEq]; constructor <;> grind
  rwa [this]

end KaplaPhysics
