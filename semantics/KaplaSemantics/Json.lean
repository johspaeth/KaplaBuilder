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

/-- A model as JSON. -/
def modelToJson (m : BubbleModel) : Json :=
  Json.mkObj
    [ ("name", Json.str m.name)
    , ("bubbles", Json.arr (m.bubbles.map bubbleToJson).toArray) ]

/-- Write a model as JSON text on one line. -/
def encode (m : BubbleModel) : String := (modelToJson m).compress

/-- Write a model as JSON text with line breaks, for a file that people read. -/
def encodePretty (m : BubbleModel) : String := (modelToJson m).pretty

/-- The largest exponent a number in JSON text may have (`1e100` is the limit). -/
def maxJsonExponent : Nat := 100

/-- Does the text have a number with an exponent above `maxJsonExponent`? This looks only at the
text, so it stays fast on `1e999999`, which is very slow to compute. Text inside strings is skipped. -/
def hasHugeExponent (text : String) : Bool :=
  let rec go (inString escaped : Bool) : List Char → Bool
    | [] => false
    | c :: rest =>
      if inString then
        if escaped then go true false rest
        else go (c != '"') (c == '\\') rest
      else if c == '"' then go true false rest
      else if c == 'e' || c == 'E' then
        let unsigned := match rest with
          | '+' :: r | '-' :: r => r
          | r => r
        let digits := unsigned.takeWhile Char.isDigit
        -- Zeros at the front do not make a number bigger, but nobody needs to write them.
        if digits.length > 3 then true
        else if (String.ofList digits).toNat?.getD 0 > maxJsonExponent then true
        else go false false rest
      else go false false rest
  go false false text.toList

#guard hasHugeExponent "[1e999999]"
#guard hasHugeExponent "[1E-999999]"
#guard hasHugeExponent "[1e+101]"
#guard !hasHugeExponent "[1e100, true, false]"
#guard !hasHugeExponent "{\"a\":\"1e999999\"}"
#guard hasHugeExponent "{\"a\\\"\":1e999999}"

/-- Read JSON text, and refuse huge exponents before any number is computed. -/
def parseJson (text : String) : Except String Json :=
  if hasHugeExponent text then
    .error s!"a number has an exponent above {maxJsonExponent}"
  else
    Json.parse text

/-- Read a model from JSON text. Text that does not follow the format, or a model that is not
well formed, gives an error message. -/
def decode (text : String) : Except String BubbleModel := do
  let j ← parseJson text
  let name ← (← j.getObjVal? "name").getStr?
  let bubbles ← (← (← j.getObjVal? "bubbles").getArr?).toList.mapM bubbleFromJson
  let m : BubbleModel := { name, bubbles }
  let labels := bubbles.map (·.label)
  if labels.eraseDups.length != labels.length then
    throw "bad model: two bubbles have the same label"
  if m.wellFormed then return m
  else throw "bad model: every bubble needs a label, half-widths above 0 and some part above the ground (z = 0); at least one bubble must reach the ground; at most 32 bubbles"

/-- Does `text` decode to exactly this model? -/
def decodesTo (text : String) (m : BubbleModel) : Bool :=
  match decode text with
  | .ok m' => m' == m
  | .error _ => false

/-- Read a number in a blocks file: as `ratFromJson`, and also a whole number in a string. -/
private def blockNumber : Json → Except String Rat
  | .str s =>
    match s.toInt? with
    | some i => .ok (i : Rat)
    | none => ratFromJson (.str s)
  | j => ratFromJson j

/-- Read one block: `up` (`"flat"`, `"edge"` or `"upright"`), `rot` (`c`, `s`) and `center`.
This is the block format of `web/README.md`. -/
def poseFromJson (j : Json) : Except String Pose := do
  let up ← match (j.getObjValAs? String "up").toOption.getD "flat" with
    | "flat" => pure Upright.flat
    | "edge" => pure Upright.onEdge
    | "upright" => pure Upright.standing
    | u => throw s!"unknown \"up\": {u}"
  let part (key : String) (default : Rat) : Except String Rat :=
    match j.getObjVal? "rot" |>.toOption |>.bind (·.getObjVal? key |>.toOption) with
    | some v => blockNumber v
    | none => .ok default
  match (← (← j.getObjVal? "center").getArr?).toList with
  | [x, y, z] =>
    return ⟨up, ⟨← part "c" 1, ← part "s" 0⟩, ⟨← blockNumber x, ← blockNumber y, ← blockNumber z⟩⟩
  | _ => throw s!"\"center\" needs three numbers: {j.compress}"

/-- Read a blocks file: a blueprint (`{"steps": ...}` or `{"plan": {"steps": ...}}`), or a plain
`{"blocks": [...]}`. -/
def decodeBlocks (text : String) : Except String (List Pose) := do
  let j ← Json.parse text
  match j.getObjVal? "blocks" with
  | .ok blocks => (← blocks.getArr?).toList.mapM poseFromJson
  | .error _ =>
    let planJ := (j.getObjVal? "plan").toOption.getD j
    let steps ← (← planJ.getObjVal? "steps").getArr?
    let perStep ← steps.toList.mapM fun st => do
      (← (← st.getObjVal? "blocks").getArr?).toList.mapM poseFromJson
    return perStep.flatten

-- Blocks can come in any of the three forms, in the same order.
#guard (decodeBlocks "{\"blocks\":[{\"center\":[\"15/2\",\"3/2\",0.5]}]}").toOption ==
  some [⟨.flat, ⟨1, 0⟩, ⟨15 / 2, 3 / 2, 1 / 2⟩⟩]
#guard ((decodeBlocks "{\"steps\":[{\"blocks\":[{\"up\":\"upright\",\"center\":[0,0,\"7\"]}]}]}").toOption.map
  (·.map (·.center.z))) == some [7]
#guard ((decodeBlocks "{\"plan\":{\"steps\":[{\"blocks\":[{\"center\":[0,0,1]},{\"center\":[0,0,2]}]}]}}").toOption.map
  (·.length)) == some 2
#guard (decodeBlocks "{\"blocks\":[{\"up\":\"sideways\",\"center\":[0,0,0]}]}") matches .error _
#guard (decodeBlocks "{\"blocks\":[{\"center\":[0,0]}]}") matches .error _
#guard (decodeBlocks "{}") matches .error _

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

-- Two bubbles with one label, and a huge exponent, are refused. An unknown field is ignored.
#guard decodeFails "{\"name\":\"a\",\"bubbles\":[{\"label\":\"x\",\"tags\":[],\"center\":[0,0,0.5],\"semi\":[1,1,1]},{\"label\":\"x\",\"tags\":[],\"center\":[0,0,1],\"semi\":[1,1,1]}]}"
#guard decodeFails "{\"name\":\"a\",\"bubbles\":[{\"label\":\"x\",\"tags\":[],\"center\":[0,0,1e999999],\"semi\":[1,1,1]}]}"
#guard !decodeFails "{\"comment\":\"hi\",\"name\":\"a\",\"bubbles\":[{\"label\":\"x\",\"tags\":[],\"center\":[0,0,0.5],\"semi\":[1,1,1]}]}"
-- The form with line breaks reads back the same.
#guard decodesTo (encodePretty BubbleModel.egg) BubbleModel.egg

/-- A model with a number that has no finite decimal form. -/
def thirdExample : BubbleModel :=
  { name := "third"
    bubbles := [{ label := "a", tags := [], center := ⟨-1 / 3, 1 / 8, 1 / 3⟩
                  semi := ⟨1 / 3, 1 / 7, 1 / 3⟩ }] }

/-- The bunny fixture, read from the real file when this module is built. -/
def bunnyFixtureText : String := include_str "../fixtures/targets/bunny.json"

-- The bunny decodes, has six bubbles and survives a round trip.
#guard (decode bunnyFixtureText).toOption.map (·.bubbles.length) == some 6
#guard match decode bunnyFixtureText with
  | .ok m => decodesTo (encode m) m
  | .error _ => false

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
