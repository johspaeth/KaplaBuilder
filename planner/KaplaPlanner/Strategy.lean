import KaplaCore

/-! # Planner strategies

A strategy is one way to search for plans. Strategies can be swapped and compared by name.
The list of strategies is in `KaplaPlanner.Registry`. -/

namespace KaplaPlanner

open KaplaCore

/-- One planner strategy: a name and a search. The search is in `IO`, so a strategy may call
Claude. -/
structure Strategy where
  name : String
  run  : PlanRequest → PhysicsEngine → SemanticEngine → IO (List Candidate)

/-- Use a strategy where Core expects a `Planner`. -/
def Strategy.toPlanner (s : Strategy) : Planner := ⟨s.run⟩

/-- The empty strategy: proposes no plan. -/
def empty : Strategy := ⟨"empty", fun _ _ _ => pure []⟩

end KaplaPlanner
