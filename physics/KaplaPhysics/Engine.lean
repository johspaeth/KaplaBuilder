import KaplaPhysics.RobustSolver
import KaplaPhysics.Reach
import KaplaSpecs.PhysicsRules.Column
import KaplaSpecs.PhysicsRules.Tower

/-! # The physics engine: untrusted solver, checked answers

`stabilityAnswer` asks the untrusted solver for a proposal and then checks it:

* "stable": the proposed pushes are allowed and balance every plank. Then the build is
  stable by definition (`Proofs.lean`: `stabilityAnswer_stable_sound`).
* "falls": the proposed motion passes `checkFall` (below). Then no allowed pushes can
  balance the build (`Proofs.lean`: `stabilityAnswer_falls_sound`).
* "unknown": the proposal did not pass the check. This should not happen; it is never
  reported as stable.

`verdict` adds placement errors (R4): "solid" when a solidity certificate passes
(`Robust.lean`), "risky" when the build only stands at the exact positions. -/

namespace KaplaPhysics

open Solver (Motion allSupports)

/-- How much the point `(x, y)` of support `s` rises under the motion `ms` (one entry per
plank, missing entries mean "does not move"). The ground does not move. -/
def rise (b : Build) (ms : List Motion) (s : Support) (x y : Rat) : Rat :=
  match s with
  | .ground => 0
  | .plank j =>
      let m := ms.getD j default
      m.lift + m.tiltX * (x - (b.get j).centerX) + m.tiltY * (y - (b.get j).centerY)

/-- The rise of support `s` under the motion, as an expression in the point. -/
def riseForm (b : Build) (ms : List Motion) : Support → Aff
  | .ground => ⟨0, 0, 0⟩
  | .plank j =>
      let m := ms.getD j default
      ⟨m.tiltX, m.tiltY, m.lift - m.tiltX * (b.get j).centerX - m.tiltY * (b.get j).centerY⟩

/-- `f - g`, as one expression. -/
def Aff.sub (f g : Aff) : Aff := ⟨f.a - g.a, f.b - g.b, f.c - g.c⟩

/-- Candidate weights that might show `f ≥ 0` wherever all of `gs` are: no side, one side,
or two sides (the sides that meet at the patch's lowest corner). Untrusted. -/
def nonnegCandidates (gs : List Aff) (f : Aff) : List Cert :=
  let single := gs.map fun g =>
    [((if g.a != 0 then f.a / g.a else if g.b != 0 then f.b / g.b else 0), g)]
  let pairs := gs.flatMap fun g => gs.filterMap fun h =>
    let det := g.a * h.b - h.a * g.b
    if det == 0 then none
    else some [((f.a * h.b - h.a * f.b) / det, g), ((g.a * f.b - f.a * g.b) / det, h)]
  [] :: single ++ pairs

/-- The weights `C` show that `f` is at least zero wherever all of `gs` are. -/
def nonnegOk (gs : List Aff) (f : Aff) (C : Cert) : Bool :=
  decide (C.Uses gs) && decide (f.a = C.combo.a) && decide (f.b = C.combo.b) &&
    decide (C.combo.c ≤ f.c)

/-- Some candidate shows that `f` is at least zero wherever all of `gs` are. -/
def nonnegCheck (gs : List Aff) (f : Aff) : Bool := (nonnegCandidates gs f).any (nonnegOk gs f)

/-- Plank `i` does not rest on `s`: the heights do not match, or weights on the sides show
that the two share no area. -/
def notRestsCheck (b : Build) (i : Nat) : Support → Bool
  | .ground => decide ((b.get i).bottom ≠ 0)
  | .plank j => decide ((b.get i).bottom ≠ (b.get j).top) || sepCheck 0 (b.get i) (b.get j)

theorem notRestsCheck_sound (b : Build) (i : Nat) (s : Support) (h : notRestsCheck b i s = true) :
    ¬ RestsOn b i s := by
  cases s with
  | ground => simpa [notRestsCheck, RestsOn] using h
  | plank j =>
    simp only [notRestsCheck, Bool.or_eq_true, decide_eq_true_eq] at h
    rintro ⟨hz, ha⟩
    rcases h with h | h
    · exact h hz
    · obtain ⟨c, hf, hv⟩ := sepCheck_sound 0 _ _ h
      exact c.no_share _ _ hf (by grind) ha

/-- Plank `i` rests on nothing: not on the ground, and not on any plank of the build. -/
def floatsCheck (b : Build) (i : Nat) : Bool := (allSupports b.length).all (notRestsCheck b i)

/-- A build with a plank that rests on nothing is not well-formed (P3). -/
theorem not_wellFormed_of_floats (b : Build) (i : Nat) (hi : i < b.length)
    (h : floatsCheck b i = true) : ¬ WellFormed b := by
  intro hw
  simp only [floatsCheck, List.all_eq_true] at h
  rcases hw.resting i hi with hr | ⟨j, hj, hr⟩
  · exact notRestsCheck_sound b i _ (h _ (by simp [allSupports])) hr
  · exact notRestsCheck_sound b i _ (h _ (by simp [allSupports]; exact hj)) hr

/-- Where plank `i` rests on `s` (if it does), plank `i` rises at least as much as `s`
under the motion `ms`, at every point of the patch. Checked by: it does not rest on `s`, or
weights on the patch's sides. -/
def noPushCheck (b : Build) (ms : List Motion) (i : Nat) (s : Support) : Bool :=
  notRestsCheck b i s ||
    nonnegCheck (contactForms b i s) ((riseForm b ms (.plank i)).sub (riseForm b ms s))

/-- Check that the build is a single column (`IsColumn`): each plank rests on what is just
below it, and on nothing else. -/
def columnCheck (b : Build) : Bool :=
  (List.range b.length).all fun i => (allSupports b.length).all fun s =>
    if s = below i then restsCheck b i s else notRestsCheck b i s

theorem columnCheck_sound (b : Build) (h : columnCheck b = true) : IsColumn b := by
  intro i hi s hs
  simp only [columnCheck, List.all_eq_true, List.mem_range] at h
  have hs' : s ∈ allSupports b.length := by
    cases s with
    | ground => simp [allSupports]
    | plank j => simp [allSupports, Support.InBuild] at hs ⊢; exact hs
  have := h i hi s hs'
  split at this
  · rename_i e; exact ⟨fun _ => e, fun _ => restsCheck_sound b i s this⟩
  · rename_i e; exact ⟨fun hr => absurd hr (notRestsCheck_sound b i s this), fun h' => absurd h' e⟩

/-- Check the simple rule for a column (`ColumnRule`). -/
def columnRuleCheck (b : Build) : Bool :=
  (List.range b.length).all fun k =>
    restsCheck b k (below k) && decide (InPatch b k (below k) (comX b k) (comY b k))

theorem columnRuleCheck_sound (b : Build) (h : columnRuleCheck b = true) : ColumnRule b := by
  intro k hk
  simp only [columnRuleCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact ⟨restsCheck_sound b k _ (h k hk).1, (h k hk).2⟩

/-- A reason the build must fall: a small motion of the planks such that
1. at every point of every contact patch, the upper plank rises at least as much as its
   support (no plank moves into what holds it up), and
2. the sum of the planks' centre lifts is below zero (the total weight goes down).

If balancing pushes existed, they would do work on this motion that is at least zero, while
the weight does work below zero; the two must be equal. So no such pushes exist. -/
def checkFall (b : Build) (ms : List Motion) : Bool :=
  (List.range b.length).all (fun i => (allSupports b.length).all fun s => noPushCheck b ms i s) &&
    decide (((List.range b.length).map fun i => (ms.getD i default).lift).sum < 0)

/-- The engine's answer to "does the build stand at the exact positions?" -/
inductive Answer where
  | stable
  | falls
  | unknown
  deriving Repr, DecidableEq

/-- Check that a push is allowed (F2, F4). -/
def pushCheck (b : Build) (p : Push) : Bool :=
  decide (0 ≤ p.force) && decide (p.upper < b.length) && decide (p.lower.InBuild b.length) &&
    restsCheck b p.upper p.lower && decide (InPatch b p.upper p.lower p.x p.y)

/-- Check that the pushes are allowed and balance every plank (S2). -/
def checkPushes (b : Build) (ps : List Push) : Bool :=
  ps.all (pushCheck b) && decide (∀ i < b.length, Balanced b ps i)

/-- Builds up to this many planks also get the global LPs, which are slow but find more
answers than the top-down solvers. -/
def globalLimit : Nat := 40

/-- Ask the global solver, then check what it proposes. -/
def globalAnswer (b : Build) : Answer :=
  match Solver.solve b with
  | .stands ps => if checkPushes b ps then .stable else .unknown
  | .falls ms => if checkFall b ms then .falls else .unknown
  | .gaveUp => .unknown

/-- For a large build where the top-down solver got stuck at plank `i`: look for a fall
certificate that moves only `i` and the planks above it, and check it. -/
def fallAboveAnswer (b : Build) (i : Nat) : Answer :=
  match Solver.solveAbove b i with
  | some ms => if checkFall b ms then .falls else .unknown
  | none => .unknown

/-- The global answer for small builds; for large ones, a fall check around plank `i`. -/
def fallbackAnswer (b : Build) (i : Nat) : Answer :=
  if b.length ≤ globalLimit then globalAnswer b else fallAboveAnswer b i

/-- Ask the fast top-down solver; if it finds no pushes that pass the check, ask the global
solver (small builds) or look for a fall certificate where it got stuck (large builds). -/
def stabilityAnswer (b : Build) : Answer :=
  match Solver.solveLocal b with
  | .ok ps => if checkPushes b ps then .stable else fallbackAnswer b 0
  | .error i => fallbackAnswer b i

/-- Is the build solid for placement errors up to `ε`? Ask the untrusted solver for a
certificate, then check it. "No" can mean "not solid" or "the cautious check could not
show it". -/
def solidAnswer (ε : Rat) (b : Build) : Bool :=
  decide (0 ≤ ε) &&
    (passes (RobustSolver.proposeLoadsLocal ε b) ||
      (b.length ≤ globalLimit && passes (RobustSolver.proposeLoads ε b)))
where
  /-- The proposed certificate exists and passes the check. -/
  passes : Option (List Load) → Bool
    | some ls => decide (SolidCertificate ε b ls)
    | none => false

/-- R4. The three answers, plus "unknown" if a check fails. -/
inductive Verdict where
  /-- Stands even with placement errors up to `ε`. -/
  | solid
  /-- Stands at the exact positions; not shown to stand with errors. -/
  | risky
  /-- Does not stand even at the exact positions. -/
  | falls
  | unknown
  deriving Repr, DecidableEq

/-- The engine's verdict for a build, for placement errors up to `ε`. -/
def verdict (ε : Rat) (b : Build) : Verdict :=
  if solidAnswer ε b then .solid
  else match stabilityAnswer b with
    | .stable => .risky
    | .falls => .falls
    | .unknown => .unknown

/-- Planks `p` and `q` are fine for placement errors up to `ε`: they touch by design
(`Meets`), or they do not share any height, or weights on their sides show a gap that an
error of `ε` per plank cannot close. Only a near miss fails. -/
def clearPairCheck (ε : Rat) (p q : Plank) : Bool :=
  meetsCheck p q || heightsApart p q || sepCheck ε p q

/-- No placement error up to `ε` can close a gap between two planks of the build. -/
def clearCheck (ε : Rat) (b : Build) : Bool :=
  (List.range b.length).all fun i => (List.range b.length).all fun j =>
    i == j || clearPairCheck ε (b.get i) (b.get j)

/-- Check a build plan (K4, K5): at most `maxPlanks` planks, and after every step the
build so far is well-formed, keeps its gaps for placement errors up to `ε` (only if
`opts.clearance` is on), and is solid for those errors. -/
def checkPlan (opts : PlanOptions) (ε : Rat) (maxPlanks : Nat) (steps : Build) : Bool :=
  decide (steps.length ≤ maxPlanks) &&
    (List.range steps.length).all fun k =>
      wellFormedCheck (steps.take (k + 1)) &&
        (!opts.clearance || clearCheck ε (steps.take (k + 1))) &&
        solidAnswer ε (steps.take (k + 1))

/-- What the engine says about one step of a plan, for the planner and the web page. -/
structure StepReport where
  /-- Step number, from 0. -/
  step : Nat
  /-- The plank this step places. -/
  plank : Plank
  /-- The build after this step is well-formed (P1–P3). -/
  wellFormed : Bool
  /-- Solid, risky or falls, for the build after this step (R4). -/
  verdict : Verdict
  /-- A straight path that puts the plank in place, or `none`: "may be hard to reach" (K3). -/
  reach : Option Dir
  deriving Repr

/-- A report for every step of a plan. The guarantees come from `checkPlan` and
`hardToReach`; this report only explains them, step by step. -/
def planReport (ε h : Rat) (steps : Build) : List StepReport :=
  (List.range steps.length).map fun k =>
    let b := steps.take (k + 1)
    { step := k, plank := steps.get k, wellFormed := wellFormedCheck b,
      verdict := verdict ε b, reach := reachDir? (steps.take k) (steps.get k) h }

end KaplaPhysics
