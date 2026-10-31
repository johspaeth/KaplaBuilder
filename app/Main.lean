import KaplaCore
import KaplaPhysics
import KaplaSemantics
import KaplaPlanner
import KaplaWeb

/-! The `kapla` CLI. The only place where the real engines meet. -/

def main : IO Unit := do
  IO.println "KaplaBuilder scaffold. Components:"
  for name in [KaplaPhysics.componentName, KaplaSemantics.componentName,
               KaplaPlanner.componentName, KaplaWeb.componentName] do
    IO.println s!"  - {name}"
