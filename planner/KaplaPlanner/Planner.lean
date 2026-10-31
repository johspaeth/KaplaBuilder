import KaplaPlanner.Search

/-! # The planner as a `KaplaCore.Planner` value

`app/Main.lean` passes the real engines; tests pass `physicsMock` and `semanticMock`. -/

namespace KaplaPlanner
open KaplaCore

/-- The construction planner. -/
def planner : Planner := ⟨fun req phys sem => pure (planPure req phys sem)⟩

end KaplaPlanner
