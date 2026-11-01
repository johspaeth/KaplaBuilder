import Lean.Data.Json
import KaplaCore
import KaplaPlanner.Strategy
import KaplaPlanner.Claude

/-! # Strategies that ask Claude for a design

Claude proposes blocks for the target's bubbles. The engines then judge each proposal:

* round 1: three independent proposals (three calls, run at the same time);
* if none passes, round 2: three more calls, each one repairing one failed proposal, with
  its problems listed;
* the result is the passing proposal with the best likeness score, or nothing.

A proposal passes when the semantic engine accepts it (`ScoreReport.accepted`: no block outside
every bubble, every bubble has a block) and, for `ai`, the physics engine says it is safe to
build. `ai-unchecked` does not ask the physics engine: it trusts Claude. Its candidates say
`physics.ok = false` with no diagnostics, which means "not checked".

Claude is not trusted. A proposal is used only after the engines have looked at it. -/

namespace KaplaPlanner

open Lean KaplaCore

/-! ## Numbers as text -/

/-- A number as exact text: `7`, `-15/2`. -/
def showQ (q : Q) : String := if q.den == 1 then s!"{q.num}" else s!"{q.num}/{q.den}"

#guard showQ (15 / 2) == "15/2" && showQ (-3) == "-3"

/-- A score from 0 to 1, rounded down to three decimals: `0.423`. -/
def showScore (q : Q) : String :=
  let n := (q * 1000).floor
  let f := toString (n % 1000).toNat
  s!"{n / 1000}." ++ "".pushn '0' (3 - f.length) ++ f

#guard showScore (1 / 3) == "0.333" && showScore 1 == "1.000" && showScore (1 / 20) == "0.050"

/-- Read a number written as `7`, `-2.5` or `15/2`, without rounding. -/
def parseQ (s : String) : Except String Q := do
  let t := s.trimAscii.toString
  let (neg, body) := if t.startsWith "-" then (true, String.ofList (t.toList.drop 1)) else (false, t)
  let nat (u : String) : Except String Nat :=
    match u.toNat? with
    | some n => .ok n
    | none => .error s!"not a number: \"{s}\""
  let v : Q ← match body.splitOn "/", body.splitOn "." with
    | [a, b], _ => do
      let d ← nat b
      if d == 0 then throw s!"zero denominator: \"{s}\""
      pure ((← nat a : Q) / (d : Q))
    | _, [a, b] => do
      let whole ← if a.isEmpty then pure 0 else nat a
      let frac ← nat b
      pure ((whole : Q) + (frac : Q) / ((10 ^ b.length : Nat) : Q))
    | _, _ => do pure ((← nat body : Nat) : Q)
  return if neg then -v else v

#guard (parseQ "7").toOption == some 7
#guard (parseQ "-2.5").toOption == some (-5 / 2)
#guard (parseQ " 15/2 ").toOption == some (15 / 2)
#guard (parseQ "-0.25").toOption == some (-1 / 4)
#guard parseQ "abc" matches .error _
#guard parseQ "1/0" matches .error _

/-- A number in an answer: a JSON number or a string as in `parseQ`. -/
def readQ (j : Json) : Except String Q :=
  match j with
  | .num n => .ok ((n.mantissa : Q) / ((10 ^ n.exponent : Nat) : Q))
  | .str s => parseQ s
  | _ => .error s!"expected a number, got {j.compress}"

/-! ## The answer Claude gives -/

/-- The turns about the vertical axis a block may have, in degrees. They are steps of 15°, so
the physics engine can check them (rule B6). -/
def allowedTurns : List Nat := [0, 30, 45, 60, 90]

/-- The turn for a number of degrees, if it is allowed. -/
def turnOf (degrees : Nat) : Option Rot :=
  if allowedTurns.contains degrees then some (Rot.step15 (degrees / 15)) else none

#guard turnOf 0 == some .id && turnOf 90 == some .quarter
#guard turnOf 45 == some (Rot.ofTriple 119 120 169) && turnOf 20 == none
#guard allowedTurns.all fun d => (turnOf d).isSome

/-- The JSON schema of an answer. Numbers are strings, so they stay exact. -/
def answerSchema : Json :=
  let str : Json := Json.mkObj [("type", "string")]
  let block := Json.mkObj
    [ ("type", "object")
    , ("properties", Json.mkObj
        [ ("up", Json.mkObj [("type", "string"), ("enum", Json.arr #["flat", "edge", "upright"])])
        , ("turn", Json.mkObj [("type", "integer"),
            ("enum", Json.arr (allowedTurns.map fun (d : Nat) => (d : Json)).toArray)])
        , ("x", str), ("y", str), ("z", str) ])
    , ("required", Json.arr #["up", "turn", "x", "y", "z"])
    , ("additionalProperties", false) ]
  Json.mkObj
    [ ("type", "object")
    , ("properties", Json.mkObj
        [ ("height", str)
        , ("blocks", Json.mkObj [("type", "array"), ("items", block)]) ])
    , ("required", Json.arr #["height", "blocks"])
    , ("additionalProperties", false) ]

/-- Read one block of an answer. -/
def readBlock (j : Json) : Except String Pose := do
  let up ← match ← j.getObjValAs? String "up" with
    | "flat" => pure Upright.flat
    | "edge" => pure .onEdge
    | "upright" => pure .standing
    | u => throw s!"unknown \"up\": \"{u}\""
  let degrees ← j.getObjValAs? Nat "turn"
  let some rot := turnOf degrees
    | throw s!"turn {degrees}° is not allowed; use one of {allowedTurns}"
  let x ← readQ (← j.getObjVal? "x")
  let y ← readQ (← j.getObjVal? "y")
  let z ← readQ (← j.getObjVal? "z")
  return ⟨up, rot, ⟨x, y, z⟩⟩

/-- Read an answer: the height and the blocks, in build order. The height must be above 0. -/
def parseAnswer (text : String) : Except String (Q × List Pose) := do
  let j ← Json.parse text
  let height ← readQ (← j.getObjVal? "height")
  unless 0 < height do throw s!"the height must be above 0, got {showQ height}"
  let bs ← j.getObjValAs? (Array Json) "blocks"
  let blocks ← bs.toList.zipIdx.mapM fun (b, i) =>
    (readBlock b).mapError (s!"block {i + 1}: " ++ ·)
  return (height, blocks)

#guard (parseAnswer "{\"height\":\"30\",\"blocks\":[{\"up\":\"flat\",\"turn\":0,\"x\":\"0\",\"y\":\"0\",\"z\":\"1/2\"}]}").toOption
  == some (30, [⟨.flat, .id, ⟨0, 0, 1 / 2⟩⟩])
#guard parseAnswer "{\"height\":\"30\",\"blocks\":[{\"up\":\"flat\",\"turn\":90,\"x\":\"one\",\"y\":\"0\",\"z\":\"1/2\"}]}"
  matches .error _
#guard parseAnswer "{\"height\":\"-1\",\"blocks\":[]}" matches .error _
#guard (parseAnswer "{\"height\":\"30\",\"blocks\":[{\"up\":\"edge\",\"turn\":45,\"x\":\"0\",\"y\":\"0\",\"z\":\"3/2\"}]}").toOption
  == some (30, [⟨.onEdge, .ofTriple 119 120 169, ⟨0, 0, 3 / 2⟩⟩])
#guard parseAnswer "{\"height\":\"30\",\"blocks\":[{\"up\":\"flat\",\"turn\":20,\"x\":\"0\",\"y\":\"0\",\"z\":\"1/2\"}]}"
  matches .error _
#guard parseAnswer "not json" matches .error _

/-! ## The prompts -/

/-- The fixed instructions: what a block is, the rules, and the goal. -/
def systemPrompt : String :=
"You design structures built from Kapla blocks. A Kapla block is a wooden block of
15 × 3 × 1 units (length × width × thickness). You answer with JSON only, in the
given schema.

Coordinates: x and y are horizontal, z points up. The ground is the plane z = 0.
Each block is given by:
- \"up\": which face is down.
    \"flat\":    lies on its 15×3 face; it covers 15 along x, 3 along y, 1 along z.
    \"edge\":    lies on its 15×1 face; it covers 15 along x, 1 along y, 3 along z.
    \"upright\": stands on its 3×1 end; it covers 3 along x, 1 along y, 15 along z.
  These sizes are before the turn.
- \"turn\": how far the block is turned about the vertical axis through its centre,
  counter-clockwise seen from above, in degrees: 0, 30, 45, 60 or 90. At 90 the
  x and y sizes swap. The top and bottom faces always stay horizontal.
- \"x\", \"y\", \"z\": the centre of the block. Write numbers as strings, exactly:
  \"7\", \"-2.5\", \"15/2\". A flat block on the ground has z = \"1/2\".

A person, possibly a child, builds your design by hand, one block at a time, in
the order you list the blocks. Hard rules. An answer that breaks any of them is
rejected:
1. No overlap. Two blocks may touch (share a face) but must not overlap anywhere.
   Mind the turned blocks: a turned block covers more of the floor plan than its
   x and y sizes. The engine uses angles a tiny bit off (29.86° for 30°, 45.24°
   for 45°, 60.14° for 60°), so leave a small gap next to turned blocks.
2. Gravity. Nothing floats. The bottom of every block is on the ground (z = 0)
   or rests on the top of blocks directly under it. The structure has to stand
   under gravity after every single block, not only when it is finished. For each
   block, and for each group of blocks on top of a block, the centre of mass has to
   be above the area that supports it, with margin: hands can place a block up to
   0.5 units off in x and in y. Overhangs are allowed only when they stay balanced.
3. Buildable by hand, step by step. List the blocks in build order: a block may
   only rest on blocks that come earlier in the list. Each block must be placeable
   by lowering it from above with one hand: no block may go into a closed pocket,
   under a block that is already placed, or into a gap exactly as wide as the
   block. No step may need a second hand to hold something up.
4. Use at most the given number of blocks.
5. Every block must have part of its volume inside at least one bubble of the
   target shape, and every bubble must contain part of at least one block.

Goal: within these rules, make the blocks fill the bubbles as closely as you can:
cover as much of the bubbles' volume as possible, and put as little block volume
outside them as you can.

Also make the structure look interesting, like a real Kapla sculpture and not a
stack of identical flat layers:
- Use all three poses. Stand blocks on their edge (\"edge\") or on their end
  (\"upright\") for walls, fins, posts, legs, ears and other thin parts. Do not
  lay most of the blocks flat.
- Use the turns. Let blocks point in different directions, for example layers
  that cross, or rings and spirals of blocks turned 30°, 45° or 60° to follow a
  round outline.
- Make the parts of the target easy to recognise.

You also choose \"height\": the scale of the target. Every bubble's centre and
half-widths are multiplied by height, so a model whose top is at z = 1 is then
height units tall. Choose a height that the block budget can fill well."

/-- The question for round 1: the target's bubbles and the block budget. -/
def userPrompt (m : BubbleModel) (budget : Nat) : String :=
  let line (b : Bubble) : String :=
    s!"- \"{b.label}\": centre ({showQ b.center.x}, {showQ b.center.y}, {showQ b.center.z}), " ++
    s!"half-widths ({showQ b.semi.x}, {showQ b.semi.y}, {showQ b.semi.z})"
  s!"Target \"{m.name}\", made of these bubbles (ellipsoids with axes along x, y, z,\n" ++
  "in model units, before scaling by height). Only the part above z = 0 counts:\n" ++
  "\n".intercalate (m.bubbles.map line) ++
  s!"\nBlock budget: at most {budget} blocks."

#guard
  let p := userPrompt BubbleModel.egg 20
  (p.splitOn "\"egg\": centre (0, 0, 1/2), half-widths (3/10, 3/10, 1/2)").length == 2 &&
    (p.splitOn "at most 20 blocks").length == 2

/-! ## Judging one answer -/

/-- A physics problem in words. Steps and blocks count from 1. The same wording as
`kapla check`. -/
def describe : Diagnostic → String
  | .unstable s b => s!"step {s + 1}: not shown to stand after block {b + 1} (falls, risky, or a turn the engine cannot check)"
  | .slides s c => s!"step {s + 1}: slides at contact {c + 1}"
  | .unreachable s => s!"step {s + 1}: may be hard to reach"
  | .overlap i j => s!"blocks {i + 1} and {j + 1} overlap"
  | .clearance i j => s!"blocks {i + 1} and {j + 1} have a small gap: a 3.9 mm error could close it"
  | .tightSlot s => s!"step {s + 1}: the block goes into a slot exactly its own width; a 3.9 mm error could close it"
  | .unevenSupports b => s!"block {b + 1} rests on supports built differently"
  | .tooManyHands s => s!"step {s + 1}: more blocks than the builder has hands"
  | .emptyStep s => s!"step {s + 1}: places no block"
  | .tooManyBlocks used limit => s!"uses {used} blocks, at most {limit} allowed"

/-- One answer and what the engines said about it. -/
structure Design where
  /-- Claude's answer, or `""` if the call failed. -/
  answer    : String
  /-- The plan with its reports, if the answer could be read and is within the budget. -/
  candidate : Option Candidate := none
  /-- True if the semantic engine accepts it and, when asked, the physics engine too. -/
  passed    : Bool := false
  /-- What is wrong, in words, for the repair prompt and the log. -/
  problems  : List String := []

/-- What the score report says, in words. -/
def scoreProblems (r : ScoreReport) : List String :=
  [s!"at height {showQ r.height}, likeness score {showScore r.score} (0 to 1, higher is better)"] ++
  (if r.blockCount == 0 then ["the design has no blocks"] else []) ++
  (if r.outside.isEmpty then [] else
    [s!"blocks outside every bubble: {", ".intercalate (r.outside.map fun i => toString (i + 1))}"]) ++
  (if r.uncovered.isEmpty then [] else
    [s!"bubbles with no block: {", ".intercalate r.uncovered}"])

/-- Judge one reply. `ph = none` means: do not check physics. The order: read the answer, keep
to the budget, score it, then (if asked) check physics. A design over the budget is not scored
or checked. -/
def judge (req : PlanRequest) (ph : Option PhysicsEngine) (sem : SemanticEngine)
    (reply : Except String String) : Design :=
  match reply with
  | .error e => { answer := "", problems := [e] }
  | .ok text =>
    match parseAnswer text with
    | .error e => { answer := text, problems := [s!"the answer could not be read: {e}"] }
    | .ok (height, blocks) =>
      if req.blocks < blocks.length then
        { answer := text
          problems := [s!"uses {blocks.length} blocks, more than the budget of {req.blocks}"] }
      else
        let plan := BuildPlan.ofBlocks blocks
        let score := sem.score req.target height blocks
        match ph with
        | some ph =>
          let physics := ph.check req.human req.blocks plan
          { answer := text
            candidate := some { plan, physics, score, difficulty := .medium }
            passed := score.accepted && physics.ok
            problems := scoreProblems score ++
              (if physics.ok then [] else physics.diagnostics.map (s!"physics: " ++ describe ·)) }
        | none =>
          { answer := text
            candidate := some { plan, physics := { ok := false }, score, difficulty := .medium }
            passed := score.accepted
            problems := scoreProblems score }

/-- One block per step keeps the block count. -/
theorem ofBlocks_blockCount (bs : List Pose) : (BuildPlan.ofBlocks bs).blockCount = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [BuildPlan.blockCount, BuildPlan.blocks, BuildPlan.ofBlocks, List.map_cons,
      List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

/-- With the physics check on, a design that passes has a plan the physics engine accepted, and
it uses at most the allowed number of blocks. The candidate's physics report is the engine's
answer for the candidate's own plan, so the engine's soundness theorem applies to it (for the
real engine: `KaplaPhysics.coreCheck_ok_sound`). -/
theorem judge_checked_passed (req : PlanRequest) (ph : PhysicsEngine) (sem : SemanticEngine)
    (reply : Except String String) (c : Candidate)
    (hpass : (judge req (some ph) sem reply).passed = true)
    (hcand : (judge req (some ph) sem reply).candidate = some c) :
    c.physics = ph.check req.human req.blocks c.plan ∧
      c.physics.ok = true ∧ c.plan.blockCount ≤ req.blocks := by
  unfold judge at hpass hcand
  split at hpass <;> simp_all
  rename_i text
  split at hpass <;> simp_all
  rename_i height blocks _
  split at hpass <;> simp_all
  obtain ⟨-, hok⟩ := hpass
  subst hcand
  exact ⟨rfl, hok, by rw [ofBlocks_blockCount]; omega⟩

/-- An example request: the egg, at most 4 blocks. -/
private def eggRequest : PlanRequest := { target := .egg, blocks := 4 }

/-- An answer with these blocks, at height 30. -/
private def answerWith (blocks : List String) : Except String String :=
  .ok s!"\{\"height\":\"30\",\"blocks\":[{",".intercalate blocks}]}"

/-- A flat block on the ground in the middle of the egg. -/
private def groundBlock : String := "{\"up\":\"flat\",\"turn\":0,\"x\":\"0\",\"y\":\"0\",\"z\":\"1/2\"}"
/-- A flat block in the air, inside the egg. -/
private def floatingBlock : String := "{\"up\":\"flat\",\"turn\":0,\"x\":\"0\",\"y\":\"0\",\"z\":\"10\"}"
/-- A flat block far away from the egg. -/
private def farBlock : String := "{\"up\":\"flat\",\"turn\":0,\"x\":\"100\",\"y\":\"0\",\"z\":\"1/2\"}"

-- every hypothesis of `judge_checked_passed` can hold: one block on the ground passes and has a
-- candidate. (A `#guard`, not an `example`: the kernel cannot evaluate JSON reading or the mock
-- engines, and compiled evaluation in proofs is not allowed here.)
#guard
  let d := judge eggRequest (some physicsMock) semanticMock (answerWith [groundBlock])
  d.passed && d.candidate.isSome
-- over the budget: rejected, and not scored
#guard
  let d := judge eggRequest (some physicsMock) semanticMock (answerWith (List.replicate 5 groundBlock))
  !d.passed && d.candidate.isNone
-- a floating block fails the physics check, and passes without it
#guard !(judge eggRequest (some physicsMock) semanticMock (answerWith [floatingBlock])).passed
#guard (judge eggRequest none semanticMock (answerWith [floatingBlock])).passed
-- unchecked candidates say "physics not ok", with no diagnostics
#guard
  match (judge eggRequest none semanticMock (answerWith [floatingBlock])).candidate with
  | some c => !c.physics.ok && c.physics.diagnostics.isEmpty
  | none => false
-- a block outside the egg is rejected by the semantic engine, also without physics
#guard !(judge eggRequest none semanticMock (answerWith [groundBlock, farBlock])).passed
-- an unreadable answer and a failed call are rejected
#guard !(judge eggRequest none semanticMock (.ok "nonsense")).passed
#guard !(judge eggRequest none semanticMock (.error "no key")).passed

/-! ## The search -/

/-- Proposals asked for in each round. -/
def designsPerRound : Nat := 3

/-- The question for round 2: repair one failed design. A failed call has no design, so it is
asked again with the round-1 question. -/
def repairPrompt (first : String) (budget : Nat) (d : Design) : String :=
  if d.answer.isEmpty then first else
  first ++ "\n\nA previous design for this target was rejected:\n" ++ d.answer ++
  "\nProblems:\n" ++ "\n".intercalate (d.problems.map ("- " ++ ·)) ++
  s!"\nFix these problems and answer with a complete new design, with at most {budget} blocks."

/-- The passing design with the best score. -/
def bestOf (ds : List Design) : Option Candidate :=
  ((ds.filter (·.passed)).filterMap (·.candidate)).foldl
    (fun best c => match best with
      | some b => if b.score.score < c.score.score then some c else some b
      | none => some c) none

/-- One line for the log. -/
def Design.summary (d : Design) (checked : Bool) : String :=
  match d.candidate with
  | none => s!"rejected: {d.problems.headD "?"}"
  | some c =>
    let shape := if c.score.accepted then "shape accepted" else "shape rejected"
    let phys :=
      if !checked then "physics not checked"
      else if c.physics.ok then "physics ok"
      else s!"physics rejected ({c.physics.diagnostics.length} problems)"
    s!"{c.plan.blockCount} blocks, height {showQ c.score.height}, score {showScore c.score.score}, {shape}, {phys}"

/-- Ask Claude these questions at the same time. -/
def askAll (effort : Claude.Effort) (prompts : List String) : IO (List (Except String String)) := do
  let tasks ← prompts.mapM fun p =>
    IO.asTask (prio := .dedicated) (Claude.ask effort systemPrompt p answerSchema)
  tasks.mapM fun t => do
    match ← IO.wait t with
    | .ok r => pure r
    | .error e => pure (.error s!"{e}")

/-- Log the designs of one round to stderr. -/
def logRound (round : Nat) (checked : Bool) (ds : List Design) : IO Unit :=
  for (d, i) in ds.zipIdx do
    IO.eprintln s!"round {round}, design {i + 1}: {d.summary checked}"

/-- The search: round 1 with independent proposals; round 2 repairs them if none passed. -/
def aiRun (effort : Claude.Effort) (checkPhysics : Bool) (req : PlanRequest) (ph : PhysicsEngine) (sem : SemanticEngine) :
    IO (List Candidate) := do
  let phOpt := if checkPhysics then some ph else none
  let first := userPrompt req.target.model req.blocks
  let replies ← askAll effort (List.replicate designsPerRound first)
  let round1 := replies.map (judge req phOpt sem)
  logRound 1 checkPhysics round1
  if let some c := bestOf round1 then return [c]
  if replies.all (·.toOption.isNone) then
    IO.eprintln "no answer from Claude; stopping"
    return []
  let round2 := (← askAll effort (round1.map (repairPrompt first req.blocks))).map (judge req phOpt sem)
  logRound 2 checkPhysics round2
  match bestOf round2 with
  | some c => return [c]
  | none =>
    IO.eprintln "no design passed after 2 rounds"
    return []

/-- Claude proposes; the semantic and physics engines judge. -/
def ai (effort : Claude.Effort := .high) : Strategy := ⟨"ai", aiRun effort true⟩

/-- Claude proposes; only the semantic engine judges. Physics is not checked. -/
def aiUnchecked (effort : Claude.Effort := .high) : Strategy := ⟨"ai-unchecked", aiRun effort false⟩

end KaplaPlanner
