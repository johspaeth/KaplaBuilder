import KaplaSemantics.Check
import KaplaSemantics.Json
import KaplaSemantics.Claude

/-! # The score report

`scoreReport model height blocks` is the whole answer: the similarity number and the lists that
decide acceptance. `runScore` does the same from file contents. This file is the only one that
uses the report type from Core. -/

namespace KaplaSemantics

open Lean KaplaCore

/-- Compare blocks with a model at a height. The caller chooses the height. The blocks must be
built to fit the model: the model is not moved to fit the blocks. -/
def scoreReport (m : BubbleModel) (height : Q) (plan : List Pose) : ScoreReport :=
  let placed := m.bubbles.map (placeAt height)
  let built := blockCells plan
  let target := (targetCells m height).length
  let covered := (coveredCells placed built).length
  let extra := (extraCells placed built).length
  { score := scoreOf target covered extra
    perPart := (placed.filter fun b => !(bubbleCells b).isEmpty).map fun b =>
      (b.label, perBubble built b)
    missing := target - covered
    extra
    height
    blockCount := plan.length
    outside := outsideBlocks placed plan
    uncovered := uncoveredBubbles placed built
    tooSmall := tooSmallBubbles placed }

/-- A target from one message to Claude, with no earlier conversation. -/
private def askClaude (key : Option String) (current : Option BubbleModel) (text : String) :
    IO TargetSpec := do
  let some key := key
    | throw (IO.userError "no API key: put it in .env in the top folder of the repo")
  match ← chat key [] current text with
  | .error e => throw (IO.userError e)
  | .ok { model := some m, .. } => return .ofBubbles m
  | .ok { reply, .. } => throw (IO.userError s!"Claude gave no model: {reply}")

/-- The real semantic engine, with this API key. The website calls `chat` directly, because it also
sends the earlier conversation, which this contract has no place for. -/
def engineWithKey (key : Option String) : SemanticEngine :=
  { interpret := fun req => askClaude key none req.prompt
    refine := fun t remark => askClaude key (some t.model) remark
    score := fun t height blocks => scoreReport t.model height blocks }

/-- The semantic engine for planners. They only need `score`, which needs no key. -/
def semanticEngine : SemanticEngine := engineWithKey none

/-- The verdict as a word. -/
def verdictName : Verdict → String
  | .good => "good"
  | .coarse => "coarse"
  | .abstract => "abstract"
  | .symbolic => "symbolic"

/-- A number rounded down to three decimals, for people to read. -/
private def rounded (q : Q) : Json := ratToJson (((q * 1000).floor : Q) / 1000)

/-- The report as JSON. Numbers are exact, and `scoreRounded` is there for reading. -/
def reportToJson (r : ScoreReport) : Json :=
  Json.mkObj
    [ ("height", ratToJson r.height)
    , ("accepted", Json.bool r.accepted)
    , ("score", ratToJson r.score)
    , ("scoreRounded", rounded r.score)
    , ("verdict", Json.str (verdictName r.verdict))
    , ("blockCount", (r.blockCount : Nat))
    , ("outside", Json.arr (r.outside.map fun (n : Nat) => (n : Json)).toArray)
    , ("uncovered", Json.arr (r.uncovered.map Json.str).toArray)
    , ("tooSmall", Json.arr (r.tooSmall.map Json.str).toArray)
    , ("missing", (r.missing : Nat))
    , ("extra", (r.extra : Nat))
    , ("perBubble", Json.mkObj (r.perPart.map fun (label, q) => (label, rounded q))) ]

/-- Read a height written as `30`, `1.5` or `3/2`. It must be above 0. -/
def parseHeight (text : String) : Except String Q := do
  let h ← match Json.parse text with
    | .ok j => ratFromJson j
    | .error _ => ratFromJson (.str text)
  if 0 < h then return h else throw s!"the height must be above 0: {text}"

/-- From the text of a model file, the text of a blocks file and a height, to the report as JSON
text. -/
def runScore (modelText blocksText heightText : String) : Except String String := do
  let m ← decode modelText
  let plan ← decodeBlocks blocksText
  let height ← parseHeight heightText
  return (reportToJson (scoreReport m height plan)).pretty

#guard (parseHeight "30").toOption == some 30
#guard (parseHeight "1.5").toOption == some (3 / 2)
#guard (parseHeight "3/2").toOption == some (3 / 2)
#guard (parseHeight "0") matches .error _
#guard (parseHeight "abc") matches .error _

-- The example of APPROACH.md §6: one block touching the ball. Accepted, with a low score.
#guard
  let r := scoreReport ballModel 2 [flatBlock]
  r.score == 1 / 52 && r.missing == 7 && r.extra == 44 && r.accepted && r.verdict == .symbolic &&
    r.perPart == [("ball", 1 / 8)]

/-- Example: a block far from the ball. -/
private def farBlock : Pose := ⟨.flat, .id, ⟨100, 3 / 2, 1 / 2⟩⟩

-- A block far away is rejected, and it is named.
#guard
  let r := scoreReport ballModel 2 [flatBlock, farBlock]
  r.outside == [1] && r.uncovered == [] && !r.accepted
#guard
  let r := scoreReport ballModel 2 [farBlock]
  r.outside == [0] && r.uncovered == ["ball"] && !r.accepted

/-- Example: two balls apart. -/
private def twoBalls : BubbleModel :=
  { name := "two"
    bubbles := [{ label := "a", tags := [], center := ⟨0, 0, 1 / 2⟩, semi := ⟨1 / 2, 1 / 2, 1 / 2⟩ },
                { label := "b", tags := [], center := ⟨20, 0, 1 / 2⟩, semi := ⟨1 / 2, 1 / 2, 1 / 2⟩ }] }

-- A partial plan: a bubble with no block yet stops acceptance, and it is not a block outside.
#guard
  let r := scoreReport twoBalls 2 [flatBlock]
  r.outside == [] && r.uncovered == ["b"] && !r.accepted

-- A bubble too small to hold a cube is listed and needs no block.
#guard
  let r := scoreReport ballModel (1 / 2) []
  r.tooSmall == ["ball"] && r.uncovered == [] && r.perPart == [] && !r.accepted
-- With every bubble too small, any block is outside, so no plan is accepted.
#guard
  let r := scoreReport ballModel (1 / 2) [flatBlock]
  r.outside == [0] && !r.accepted

/-- Example: two walls with a gap between them, inside the egg at height 30. -/
private def eggWalls : List Pose :=
  [⟨.flat, .id, ⟨0, -9 / 2, 31 / 2⟩⟩, ⟨.flat, .id, ⟨0, 9 / 2, 31 / 2⟩⟩]

-- The engine gives the same answer as `scoreReport`.
#guard semanticEngine.score .egg 30 eggWalls == scoreReport .egg 30 eggWalls
-- It credits the hollow middle, so it scores higher than the stand-in in Core.
#guard (semanticEngine.score .egg 30 eggWalls).score > (semanticMock.score .egg 30 eggWalls).score

/-- The block files in `fixtures/plans/`, read from the real files when this module is built. -/
def oneBlockText : String := include_str "../fixtures/plans/one-block.json"

-- The same answer from file text. A bad file gives an error.
#guard
  match runScore (encode ballModel) oneBlockText "2" with
  | .ok text => (text.splitOn "\"accepted\": true").length == 2
  | .error _ => false
#guard (runScore "{}" oneBlockText "2") matches .error _
#guard (runScore (encode ballModel) "{}" "2") matches .error _
#guard (runScore (encode ballModel) oneBlockText "0") matches .error _

end KaplaSemantics
