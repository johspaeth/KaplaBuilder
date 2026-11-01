import KaplaPlanner.Strategy
import KaplaPlanner.AiStrategy
import KaplaPlanner.Search

/-! # All strategies, by name -/

namespace KaplaPlanner

/-- Layered branch-and-bound (`planner`, `planner/DESIGN.md` §3): build course by course at
several heights, search the tree of partial builds and skip branches that cannot beat the best
plan so far, then improve the best plan. At most 30 seconds. No calls to Claude. Every plan it
returns uses at most `N` blocks and passed physics (theorem `candidatesOf_sound`). -/
def layeredBranchAndBound : Strategy := ⟨"layered-branch-and-bound", planner.plan⟩

/-- Every strategy that can be chosen by name. -/
def strategies : List Strategy := [empty, layeredBranchAndBound, ai, aiUnchecked]

/-- The strategies that ask Claude, and so have an effort. -/
def usesClaude (name : String) : Bool := name == "ai" || name == "ai-unchecked"

/-- The strategy with this name, if there is one. -/
def strategyByName? (name : String) : Option Strategy := strategies.find? (·.name == name)

/-- The strategy with this name, asking Claude with this effort. Strategies that do not ask
Claude are the same at every effort. -/
def strategyWithEffort? (name : String) (effort : Claude.Effort) : Option Strategy :=
  match name with
  | "ai" => some (ai effort)
  | "ai-unchecked" => some (aiUnchecked effort)
  | _ => strategyByName? name

#guard (strategyByName? "empty").isSome
#guard (strategyByName? "ai").isSome
#guard (strategyByName? "ai-unchecked").isSome
#guard (strategyByName? "layered-branch-and-bound").isSome
#guard (strategyByName? "nope").isNone
#guard (strategyWithEffort? "ai" .low).isSome && (strategyWithEffort? "empty" .low).isSome
#guard (strategyWithEffort? "nope" .low).isNone
#guard usesClaude "ai" && !usesClaude "empty"

end KaplaPlanner
