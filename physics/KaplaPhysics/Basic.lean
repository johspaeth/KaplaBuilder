import KaplaCore

/-! The component name, shown by `kapla`. The engine itself is in `Engine.lean`. -/

namespace KaplaPhysics

/-- Name of this component, shown by `kapla`. -/
def componentName : String := "Physics engine"

#guard componentName.length > 0

end KaplaPhysics
