import KaplaSemantics.Library

/-!
# KaplaSemantics.Engine — `SemanticEngine` implementation
-/

namespace Kapla.Semantics

open Kapla Lean

/-- Load a target from JSON: either a full `TargetSpec` or a bare `Shape`. -/
def loadTarget (path : System.FilePath) : IO TargetSpec := do
  let txt ← IO.FS.readFile path
  let j ← IO.ofExcept (Json.parse txt)
  match fromJson? j with
  | .ok (t : TargetSpec) => return t
  | .error e1 =>
    match fromJson? j with
    | .ok (s : Shape) => return { name := path.fileStem.getD "target", shape := s }
    | .error e2 => throw <| IO.userError s!"{path}: not a TargetSpec ({e1}) nor a Shape ({e2})"

def interpret (r : Request) : IO TargetSpec := do
  if r.prompt.endsWith ".json" then return ← loadTarget r.prompt
  if r.image.isSome then
    IO.eprintln "note: image input needs the Claude frontend (M7); using the prompt only"
  match lookupTarget r.prompt with
  | some t => return t
  | none =>
    IO.eprintln s!"note: no built-in target matches '{r.prompt}' (Claude frontend is M7); \
      building a tower"
    return (lookupTarget "tower").get!

def engine : SemanticEngine where
  name := "voxel-iou"
  interpret := interpret
  score t bs := scoreBlocks t bs
  bound t n := boundFor t n

end Kapla.Semantics
