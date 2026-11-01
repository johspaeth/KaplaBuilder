import Lean.Data.Json
import KaplaPlanner.Search

/-! # A candidate as a blueprint file

Writes a candidate in the blueprint format of `web/README.md`, so `kapla view` can show it:
the steps, the bubbles at the candidate's height (drawn see-through), and the score and physics
result as notes. Numbers are exact: whole numbers as JSON numbers, fractions as strings such
as `"15/2"`. -/

namespace KaplaPlanner

open Lean (Json)
open KaplaCore

/-- An exact number: a JSON number when it is whole, else a string `"num/den"`. -/
def ratJson (q : Q) : Json :=
  if q.den == 1 then Json.num q.num else Json.str s!"{q.num}/{q.den}"

/-- A point as a list of three exact numbers. -/
def q3Json (p : Q3) : Json := Json.arr #[ratJson p.x, ratJson p.y, ratJson p.z]

/-- One block. -/
def poseJson (p : Pose) : Json :=
  let up := match p.up with
    | .flat => "flat"
    | .onEdge => "edge"
    | .standing => "upright"
  Json.mkObj [("up", Json.str up), ("rot", Json.mkObj [("c", ratJson p.rot.cos), ("s", ratJson p.rot.sin)]),
    ("center", q3Json p.center)]

/-- One build step. -/
def stepJson (s : Step) : Json :=
  Json.mkObj [("blocks", Json.arr (s.blocks.map poseJson).toArray), ("phase", Json.str s.phase)]

/-- A number rounded down to three decimals, as text, for people to read. -/
def decimals (q : Q) : String :=
  let k := (q * 1000).floor
  let whole := k / 1000
  let frac := (k % 1000).toNat
  let pad := if frac < 10 then "00" else if frac < 100 then "0" else ""
  s!"{whole}.{pad}{frac}"

/-- The blueprint of a candidate for a bubble model. The bubbles are drawn at the candidate's
height (`ScoreReport.height`). -/
def blueprintJson (m : BubbleModel) (c : Candidate) : Json :=
  let h := c.score.height
  let bubbles := m.bubbles.map fun b =>
    let p := b.place h
    Json.mkObj [("label", Json.str b.label), ("center", q3Json p.center), ("semi", q3Json p.semi)]
  let notes : List String :=
    [s!"likeness score {decimals c.score.score} ({repr c.score.verdict}), height {decimals h}",
     s!"physics engine: {if c.physics.ok then "stands after every step" else "rejected"}",
     s!"scorer: {if c.score.accepted then "every block is part of the target, every part is built" else "not accepted"}"]
  Json.mkObj
    [ ("title", Json.str m.name)
    , ("subtitle", Json.str s!"{c.plan.blockCount} blocks")
    , ("notes", Json.arr (notes.map Json.str).toArray)
    , ("bubbles", Json.arr bubbles.toArray)
    , ("plan", Json.mkObj [("steps", Json.arr (c.plan.steps.map stepJson).toArray)]) ]

#guard ratJson (15 / 2) == Json.str "15/2" && ratJson 3 == Json.num 3
#guard decimals (1 / 52) == "0.019" && decimals 1 == "1.000" && decimals (7 / 10) == "0.700"

end KaplaPlanner
