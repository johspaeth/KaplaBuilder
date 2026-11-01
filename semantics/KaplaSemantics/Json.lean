import Lean.Data.Json
import KaplaSemantics.Bubble

/-! # Bubble models as JSON

Numbers stay exact. A number that is an exact decimal is written as a JSON number (`0.3`). Any
other number is written as a string (`"1/3"`). The decoder accepts both. See
`semantics/APPROACH.md` §8 item 5. -/

namespace KaplaSemantics

open Lean KaplaCore

/-- Write an exact number as JSON. `e` is the count of decimal places. If `q` has a finite
decimal form, it needs at most `log2` of its denominator places. -/
def ratToJson (q : Rat) : Json :=
  match (List.range (q.den.log2 + 1)).find? (fun e => 10 ^ e % q.den == 0) with
  | some e => Json.num ⟨q.num * ((10 ^ e / q.den : Nat) : Int), e⟩
  | none => Json.str s!"{q.num}/{q.den}"

/-- Read an exact number from JSON: a JSON number, or a string `"p/q"` with `q` above 0. -/
def ratFromJson : Json → Except String Rat
  | .num n => .ok ((n.mantissa : Rat) / ((10 ^ n.exponent : Nat) : Rat))
  | .str s =>
    match s.splitOn "/" with
    | [p, q] =>
      match p.toInt?, q.toNat? with
      | some p', some q' =>
        if q' == 0 then .error s!"zero denominator: {s}"
        else .ok ((p' : Rat) / (q' : Rat))
      | _, _ => .error s!"not a fraction: {s}"
    | _ => .error s!"not a fraction: {s}"
  | j => .error s!"not a number: {j.compress}"

/-- Write three numbers as a JSON list. -/
def q3ToJson (v : Q3) : Json :=
  Json.arr #[ratToJson v.x, ratToJson v.y, ratToJson v.z]

/-- Read three numbers from a JSON list. -/
def q3FromJson (j : Json) : Except String Q3 := do
  match (← j.getArr?).toList with
  | [x, y, z] => return ⟨← ratFromJson x, ← ratFromJson y, ← ratFromJson z⟩
  | _ => throw s!"expected three numbers: {j.compress}"

/-- Write one bubble as JSON. -/
def bubbleToJson (b : Bubble) : Json :=
  Json.mkObj
    [ ("label", Json.str b.label)
    , ("tags", Json.arr (b.tags.map Json.str).toArray)
    , ("center", q3ToJson b.center)
    , ("semi", q3ToJson b.semi) ]

/-- Read one bubble from JSON. -/
def bubbleFromJson (j : Json) : Except String Bubble := do
  let label ← (← j.getObjVal? "label").getStr?
  let tags ← (← (← j.getObjVal? "tags").getArr?).toList.mapM Json.getStr?
  let center ← q3FromJson (← j.getObjVal? "center")
  let semi ← q3FromJson (← j.getObjVal? "semi")
  return { label, tags, center, semi }

/-- Write a model as JSON text. -/
def encode (m : BubbleModel) : String :=
  (Json.mkObj
    [ ("name", Json.str m.name)
    , ("bubbles", Json.arr (m.bubbles.map bubbleToJson).toArray) ]).compress

/-- Read a model from JSON text. Text that does not follow the format, or a model that is not
well formed, gives an error message. -/
def decode (text : String) : Except String BubbleModel := do
  let j ← Json.parse text
  let name ← (← j.getObjVal? "name").getStr?
  let bubbles ← (← (← j.getObjVal? "bubbles").getArr?).toList.mapM bubbleFromJson
  let m : BubbleModel := { name, bubbles }
  if m.wellFormed then return m
  else throw "bad model: every bubble needs a label and half-widths above 0, at most 32 bubbles"

/-- Does `text` decode to exactly this model? -/
def decodesTo (text : String) (m : BubbleModel) : Bool :=
  match decode text with
  | .ok m' => m' == m
  | .error _ => false

/-- Does text fail to decode? -/
def decodeFails (text : String) : Bool :=
  match decode text with
  | .ok _ => false
  | .error _ => true

/-- The egg fixture, read from the real file when this module is built. -/
def eggFixtureText : String := include_str "../fixtures/targets/egg.json"

-- The fixture is the same egg as the one in Core, and survives a round trip.
#guard decodesTo eggFixtureText BubbleModel.egg
#guard decodesTo (encode BubbleModel.egg) BubbleModel.egg

/-- A model with a number that has no finite decimal form. -/
def thirdExample : BubbleModel :=
  { name := "third"
    bubbles := [{ label := "a", tags := [], center := ⟨-1 / 3, 1 / 8, 1 / 3⟩
                  semi := ⟨1 / 3, 1 / 7, 1 / 3⟩ }] }

#guard decodesTo (encode thirdExample) thirdExample
#guard (ratToJson (3 / 10)).compress == "0.3"
#guard (ratToJson (-1 / 3)).compress == "\"-1/3\""
#guard (ratToJson 2).compress == "2"

-- Bad input is rejected: a half-width of 0, a zero denominator, a missing field, a list of two.
#guard decodeFails "{\"name\":\"x\",\"bubbles\":[{\"label\":\"a\",\"tags\":[],\"center\":[0,0,0],\"semi\":[0,1,1]}]}"
#guard decodeFails "{\"name\":\"x\",\"bubbles\":[{\"label\":\"a\",\"tags\":[],\"center\":[0,0,0],\"semi\":[\"1/0\",1,1]}]}"
#guard decodeFails "{\"name\":\"x\",\"bubbles\":[{\"label\":\"a\",\"center\":[0,0,0],\"semi\":[1,1,1]}]}"
#guard decodeFails "{\"name\":\"x\",\"bubbles\":[{\"label\":\"a\",\"tags\":[],\"center\":[0,0],\"semi\":[1,1,1]}]}"

end KaplaSemantics
