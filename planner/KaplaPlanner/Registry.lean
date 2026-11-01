import KaplaPlanner.Strategy
import KaplaPlanner.AiStrategy

/-! # All strategies, by name -/

namespace KaplaPlanner

/-- Every strategy that can be chosen by name. -/
def strategies : List Strategy := [empty, ai, aiUnchecked]

/-- The strategy with this name, if there is one. -/
def strategyByName? (name : String) : Option Strategy := strategies.find? (·.name == name)

#guard (strategyByName? "empty").isSome
#guard (strategyByName? "ai").isSome
#guard (strategyByName? "ai-unchecked").isSome
#guard (strategyByName? "nope").isNone

end KaplaPlanner
