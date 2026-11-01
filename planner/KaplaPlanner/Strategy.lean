import KaplaCore

/-! # Planner strategies

A strategy is one way to search for plans. Strategies can be swapped and compared by name. -/

namespace KaplaPlanner

open KaplaCore

/-- One planner strategy: a name and a pure search. -/
structure Strategy where
  name : String
  run  : PlanRequest → PhysicsEngine → SemanticEngine → List Candidate

/-- Use a strategy where Core expects a `Planner`. -/
def Strategy.toPlanner (s : Strategy) : Planner := ⟨fun req ph sem => pure (s.run req ph sem)⟩

/-- The empty strategy: proposes no plan. -/
def empty : Strategy := ⟨"empty", fun _ _ _ => []⟩

/-- Every strategy that can be chosen by name. -/
def strategies : List Strategy := [empty]

/-- The strategy with this name, if there is one. -/
def strategyByName? (name : String) : Option Strategy := strategies.find? (·.name == name)

#guard (strategyByName? "empty").isSome
#guard (strategyByName? "nope").isNone

end KaplaPlanner
