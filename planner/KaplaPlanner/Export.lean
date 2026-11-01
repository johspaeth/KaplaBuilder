import KaplaPlanner.Sequencer

/-! # Write a plan in the blueprint format of the web viewer (`web/README.md`)

`lake exe kapla view FILE.json` turns the file into a web page with a 3D view and step
cards. -/

namespace KaplaPlanner
open KaplaCore

/-- A number as JSON: a whole number as is, a fraction as the string "num/den". -/
def ratJson (q : Q) : String :=
  if q.den == 1 then toString q.num else s!"\"{q.num}/{q.den}\""

/-- A string as JSON (quotes and backslashes escaped). -/
def strJson (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

def uprightJson : Upright → String
  | .flat => "\"flat\"" | .onEdge => "\"edge\"" | .standing => "\"upright\""

def gripJson : Grip → String
  | .longSides => "\"longSides\"" | .shortEnds => "\"shortEnds\"" | .topEnd => "\"topEnd\""

def poseJson (p : Pose) : String :=
  s!"\{\"up\": {uprightJson p.up}, \"rot\": \{\"c\": {ratJson p.rot.cos}, \"s\": {ratJson p.rot.sin}}, " ++
  s!"\"center\": [{ratJson p.center.x}, {ratJson p.center.y}, {ratJson p.center.z}]}"

def stepJson (s : Step) : String :=
  let blocks := ", ".intercalate (s.blocks.map poseJson)
  s!"\{\"blocks\": [{blocks}], \"phase\": {strJson s.phase}, \"grip\": {gripJson s.grip}, " ++
  "\"approach\": \"fromAbove\"}"

/-- The whole blueprint file. -/
def blueprintJson (title subtitle : String) (notes : List String) (plan : BuildPlan) : String :=
  let steps := ",\n    ".intercalate (plan.steps.map stepJson)
  let notesJ := ", ".intercalate (notes.map strJson)
  s!"\{\n  \"title\": {strJson title},\n  \"subtitle\": {strJson subtitle},\n" ++
  s!"  \"notes\": [{notesJ}],\n  \"plan\": \{\"steps\": [\n    {steps}\n  ]}\n}\n"

#guard ratJson (39 / 10) == "\"39/10\"" && ratJson 3 == "3"

end KaplaPlanner
