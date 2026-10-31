import KaplaCore.Types

/-!
# KaplaCore.ShapeMem — the meaning of the Shape DSL

Exact point membership over ℚ (closed sets). Part of the contract: the semantic engine
voxelizes it (and will prove the voxelizer against it), the planner uses it to fill layers.
-/

namespace Kapla.Shape

open Kapla

/-- Exact point membership (closed sets). -/
def mem : Shape → Q3 → Bool
  | .box sx sy sz, p => |p.x| ≤ sx / 2 && |p.y| ≤ sy / 2 && 0 ≤ p.z && p.z ≤ sz
  | .cylinder r h, p => p.x * p.x + p.y * p.y ≤ r * r && 0 ≤ p.z && p.z ≤ h
  | .cone r h, p =>
    let f := r * (1 - p.z / h)
    0 ≤ p.z && p.z ≤ h && p.x * p.x + p.y * p.y ≤ f * f
  | .pyramid sx sy h, p =>
    let f := 1 - p.z / h
    0 ≤ p.z && p.z ≤ h && |p.x| ≤ sx / 2 * f && |p.y| ≤ sy / 2 * f
  | .wedge sx sy h, p =>
    0 ≤ p.z && p.z ≤ h && |p.x| ≤ sx / 2 && |p.y| ≤ sy / 2 * (1 - p.z / h)
  | .union ps, p => ps.attach.any fun ⟨s, _⟩ => mem s p
  | .diff a b, p => mem a p && !mem b p
  | .translate v s, p => mem s (p - v)
  | .scale k s, p => k ≠ 0 && mem s ((1 / k) * p)
  | .tag _ s, p => mem s p

/-- Tagged sub-shapes, in the coordinates of the whole shape. -/
partial def taggedParts : Shape → List (String × Shape)
  | .union ps => ps.flatMap taggedParts
  | .diff a b => (taggedParts a).map fun (t, s) => (t, .diff s b)
  | .translate v s => (taggedParts s).map fun (t, x) => (t, .translate v x)
  | .scale k s => (taggedParts s).map fun (t, x) => (t, .scale k x)
  | .tag t s => (t, s) :: taggedParts s
  | _ => []

end Kapla.Shape
