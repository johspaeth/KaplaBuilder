import Lean.Data.Json

/-! # Reading a blueprint for display

The viewer reads a blueprint from JSON and turns it into plain display data. It needs no
other component: anything that writes this format can be shown (the planner, a test, a
file written by hand). The format is described in `web/README.md`.

Display only: numbers become `Float` here. The exact plan stays in the JSON file.
-/

namespace KaplaWeb

open Lean

/-- Block size: length, width, thickness. -/
def blockL : Float := 15
def blockW : Float := 3
def blockT : Float := 1

/-- Read a number written as a JSON number (`3`, `2.5`) or as an exact fraction in a
string (`"-169/10"`, `"7"`). -/
def readNum (j : Json) : Except String Float :=
  match j with
  | .num n => .ok n.toFloat
  | .str s =>
    let int (t : String) : Except String Float :=
      let t := t.trimAscii.toString
      match t.toInt? with
      | some i => .ok (Float.ofInt i)
      | none => .error s!"not a number: \"{s}\""
    match s.splitOn "/" with
    | [a] => int a
    | [a, b] => do
      let d ← int b
      if d == 0 then throw s!"zero denominator: \"{s}\""
      return (← int a) / d
    | _ => .error s!"not a number: \"{s}\""
  | _ => .error s!"expected a number, got {j.compress}"

/-- One block as it is drawn. -/
structure ViewBlock where
  /-- `"flat"`, `"edge"` or `"upright"`. -/
  up : String
  /-- Centre. -/
  x : Float
  y : Float
  z : Float
  /-- Turn about the vertical axis: cosine and sine. -/
  c : Float := 1
  s : Float := 0
  deriving Repr, Inhabited

/-- Size along the block's own axes (x, y, z) for each way of laying it. -/
def ViewBlock.size (b : ViewBlock) : Float × Float × Float :=
  match b.up with
  | "edge" => (blockL, blockT, blockW)
  | "upright" => (blockW, blockT, blockL)
  | _ => (blockL, blockW, blockT)

/-- Turn in degrees. -/
def ViewBlock.yawDeg (b : ViewBlock) : Float := Float.atan2 b.s b.c * 180 / 3.141592653589793

/-- Height of the bottom face. -/
def ViewBlock.bottom (b : ViewBlock) : Float := b.z - b.size.2.2 / 2

/-- The four corners of the block seen from above. -/
def ViewBlock.footprint (b : ViewBlock) : List (Float × Float) :=
  let (sx, sy, _) := b.size
  [(-1, -1), (1, -1), (1, 1), (-1, 1)].map fun ((u, v) : Float × Float) =>
    let lx := u * sx / 2
    let ly := v * sy / 2
    (b.x + lx * b.c - ly * b.s, b.y + lx * b.s + ly * b.c)

/-- One build step: the blocks placed together, and hints for the builder. -/
structure ViewStep where
  blocks : List ViewBlock
  phase : String := ""
  grip : String := ""
  approach : String := ""
  deriving Repr, Inhabited

/-- One bubble of the target, as it is drawn: an ellipsoid with axes along x, y and z. -/
structure ViewBubble where
  label : String := ""
  /-- Centre. -/
  x : Float
  y : Float
  z : Float
  /-- Half-widths along x, y and z. -/
  rx : Float
  ry : Float
  rz : Float
  deriving Repr, Inhabited

/-- A whole blueprint plus optional texts for the page. -/
structure ViewPlan where
  title : String := "Kapla blueprint"
  subtitle : String := ""
  /-- Lines shown above the 3D view (for example what was checked). -/
  notes : List String := []
  steps : List ViewStep
  /-- The target's bubbles, if the file has them (drawn see-through, can be hidden). -/
  bubbles : List ViewBubble := []
  deriving Repr, Inhabited

private def optStr (j : Json) (k : String) (d : String := "") : String :=
  (j.getObjValAs? String k).toOption.getD d

def readBlock (j : Json) : Except String ViewBlock := do
  let up := (j.getObjValAs? String "up").toOption.getD "flat"
  let center ← j.getObjValAs? (Array Json) "center"
  unless center.size == 3 do throw "\"center\" needs three numbers"
  let rot := (j.getObjVal? "rot").toOption
  let c ← match rot.bind (·.getObjVal? "c" |>.toOption) with
    | some v => readNum v
    | none => pure 1
  let s ← match rot.bind (·.getObjVal? "s" |>.toOption) with
    | some v => readNum v
    | none => pure 0
  return { up, x := ← readNum center[0]!, y := ← readNum center[1]!, z := ← readNum center[2]!, c, s }

/-- Read one bubble: `label` (optional), `center` and `semi` (half-widths). -/
def readBubble (j : Json) : Except String ViewBubble := do
  let c ← j.getObjValAs? (Array Json) "center"
  let r ← j.getObjValAs? (Array Json) "semi"
  unless c.size == 3 && r.size == 3 do throw "\"center\" and \"semi\" need three numbers"
  return { label := optStr j "label", x := ← readNum c[0]!, y := ← readNum c[1]!,
           z := ← readNum c[2]!, rx := ← readNum r[0]!, ry := ← readNum r[1]!, rz := ← readNum r[2]! }

def readStep (j : Json) : Except String ViewStep := do
  let bs ← j.getObjValAs? (Array Json) "blocks"
  return { blocks := (← bs.toList.mapM readBlock), phase := optStr j "phase",
           grip := optStr j "grip", approach := optStr j "approach" }

/-- Read a blueprint: either `{"steps": [...]}` or `{"plan": {"steps": [...]}, "title": ...,
"subtitle": ..., "notes": [...], "bubbles": [...]}`. -/
def readPlan (j : Json) : Except String ViewPlan := do
  let planJ := (j.getObjVal? "plan").toOption.getD j
  let steps ← planJ.getObjValAs? (Array Json) "steps"
  let bubbles := (j.getObjValAs? (Array Json) "bubbles").toOption.getD #[]
  return { steps := (← steps.toList.mapM readStep), bubbles := (← bubbles.toList.mapM readBubble),
           title := optStr j "title" "Kapla blueprint", subtitle := optStr j "subtitle",
           notes := (j.getObjValAs? (List String) "notes").toOption.getD [] }

/-- Parse and read in one go. -/
def parsePlan (txt : String) : Except String ViewPlan := do
  readPlan (← Json.parse txt)

/-! ## Examples -/

/-- A two-block stack, the second block turned a quarter turn. -/
def exampleJson : String :=
  "{\"title\": \"Two blocks\", \"steps\": [
     {\"blocks\": [{\"up\": \"flat\", \"rot\": {\"c\": 1, \"s\": 0}, \"center\": [0, 0, \"1/2\"]}]},
     {\"blocks\": [{\"up\": \"flat\", \"rot\": {\"c\": 0, \"s\": 1}, \"center\": [0, 0, \"3/2\"]}],
      \"phase\": \"layer 2\"}]}"

#guard (readNum (.str "-169/10")).toOption == some (-16.9)
#guard (readNum (.str "7")).toOption == some 7
#guard (readNum (.str "1/0")) matches .error _
#guard (readNum (.str "abc")) matches .error _
#guard ((parsePlan exampleJson).map (·.steps.length)).toOption == some 2
#guard ((parsePlan exampleJson).map (·.title)).toOption == some "Two blocks"
-- a flat block's bottom face is half a thickness below its centre
#guard ((parsePlan exampleJson).map fun p => (p.steps[0]!.blocks[0]!).bottom).toOption == some 0
-- a quarter turn swaps the footprint's extent in x and y
#guard ((parsePlan exampleJson).map fun p =>
  ((p.steps[1]!.blocks[0]!).footprint.map (·.1)).foldl max (-1000)).toOption == some 1.5
#guard (parsePlan "{\"steps\": [{}]}") matches .error _
-- bubbles are optional; when given, they are read
#guard ((parsePlan exampleJson).map (·.bubbles.length)).toOption == some 0
#guard ((parsePlan "{\"steps\": [], \"bubbles\": [{\"label\": \"head\",
  \"center\": [0, 0, \"5/2\"], \"semi\": [2, 2, 3]}]}").map fun p =>
  p.bubbles.map (fun b => (b.label, b.z, b.rz))).toOption == some [("head", 2.5, 3)]

end KaplaWeb
