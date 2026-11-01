import KaplaCore

/-! # Planner strategies

A strategy is one way to search for plans. Each strategy is a pure function and carries a
proof that its output is acceptable (`CandidatesOk`). `portfolio` runs several strategies
and keeps the best candidates; it is acceptable because each of its strategies is. -/

namespace KaplaPlanner

open KaplaCore

/-- The output of a planner is acceptable: the physics engine accepts every plan, and no
plan uses more blocks than the request allows. -/
def CandidatesOk (req : PlanRequest) (ph : PhysicsEngine) (out : List Candidate) : Prop :=
  ∀ c ∈ out, (ph.check req.human req.blocks c.plan).ok = true ∧ c.plan.blockCount ≤ req.blocks

/-- One planner strategy: a name, a pure search, and a proof that its output is acceptable. -/
structure Strategy where
  name : String
  run  : PlanRequest → PhysicsEngine → SemanticEngine → List Candidate
  ok   : ∀ req ph sem, CandidatesOk req ph (run req ph sem)

/-- Use a strategy where Core expects a `Planner`. -/
def Strategy.toPlanner (s : Strategy) : Planner := ⟨fun req ph sem => pure (s.run req ph sem)⟩

/-- The empty strategy: proposes no plan. -/
def empty : Strategy where
  name := "empty"
  run := fun _ _ _ => []
  ok := by intro _ _ _ c h; cases h

/-- Keep the first candidate for each plan; drop later candidates with the same plan. -/
def dedupPlans : List Candidate → List Candidate
  | [] => []
  | c :: cs => c :: (dedupPlans cs).filter (fun d => d.plan != c.plan)

theorem mem_of_mem_dedupPlans {c : Candidate} : ∀ {l : List Candidate}, c ∈ dedupPlans l → c ∈ l
  | [], h => by simp [dedupPlans] at h
  | d :: ds, h => by
    simp only [dedupPlans, List.mem_cons, List.mem_filter] at h
    rcases h with h | ⟨h, _⟩
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_mem_dedupPlans h)

/-- Join the candidates, drop repeated plans, sort best score first (ties keep the order),
and keep at most `n`. -/
def mergeCandidates (n : Nat) (l : List Candidate) : List Candidate :=
  ((dedupPlans l).mergeSort (fun a b => decide (b.score.score ≤ a.score.score))).take n

theorem mem_of_mem_mergeCandidates {n : Nat} {l : List Candidate} {c : Candidate}
    (h : c ∈ mergeCandidates n l) : c ∈ l :=
  mem_of_mem_dedupPlans ((List.mem_mergeSort).1 (List.mem_of_mem_take h))

/-- Run every strategy (each with the full check budget) and merge their candidates. -/
def portfolio (ss : List Strategy) : Strategy where
  name := "portfolio"
  run := fun req ph sem => mergeCandidates req.maxCandidates (ss.flatMap (·.run req ph sem))
  ok := by
    intro req ph sem c hc
    obtain ⟨s, _, hs⟩ := List.mem_flatMap.1 (mem_of_mem_mergeCandidates hc)
    exact s.ok req ph sem c hs

/-- The basic strategies, in tie-break order. -/
def baseStrategies : List Strategy := [empty]

/-- Every strategy that can be chosen by name, including the portfolio of the basic ones. -/
def strategies : List Strategy := baseStrategies ++ [portfolio baseStrategies]

/-- The strategy with this name, if there is one. -/
def strategyByName? (name : String) : Option Strategy := strategies.find? (·.name == name)

/-- The default planner: the portfolio of all basic strategies. -/
def planner : Planner := (portfolio baseStrategies).toPlanner

#guard strategies.map (·.name) == ["empty", "portfolio"]
#guard (strategyByName? "portfolio").isSome
#guard (strategyByName? "nope").isNone
#guard ((portfolio baseStrategies).run default physicsMock semanticMock).isEmpty

end KaplaPlanner
