import KaplaSemantics.Bubble
import KaplaSemantics.Json

/-! # Talking to Claude

Turns a conversation into a bubble model, through the Messages API and `curl`. Nothing here is
trusted: only `decode` decides what a good model is, and the verified part only sees the model.
See `semantics/APPROACH.md` §2. The website holds the conversation and sends it with each message. -/

namespace KaplaSemantics

open Lean KaplaCore

/-- The Claude model the chat uses. -/
def claudeModelId : String := "claude-opus-5-5"

/-- How many times a bad answer is sent back to Claude. -/
def maxRetries : Nat := 2

/-- What the chat tells Claude. It gives the vertical reference of `semantics/ROADMAP.md` step 7. -/
def systemPrompt : String :=
  "You turn a person's description into a 3D shape for KaplaBuilder. The shape is later built from \
wooden planks. It is made of bubbles: each bubble is an ellipsoid with its axes along x, y and z.

Coordinates: z is up. z = 0 is the ground. The whole model is 1 tall above the ground, so its highest \
point is at z = 1. x and y are free; keep the model near x = 0, y = 0.

Rules for every bubble:
- label: a short name for the part, such as \"head\" or \"left ear\". Each label is used only once.
- tags: hints for the builder, such as \"tower\", \"wall\" or \"trunk\". The list may be empty.
- center: [x, y, z], the middle of the bubble.
- semi: [a, b, c], half of its width along x, y and z. All three are above 0.

Rules for the model:
- At least one bubble must reach the ground: its lowest point, center z minus c, is at z = 0 or below. \
A model that floats is rejected.
- A bubble may go below the ground, such as a half sphere with its middle at z = 0 for a foot. Only the \
part above the ground counts. A bubble entirely under the ground is rejected.
- At most 32 bubbles. Use as few as show the shape well. Parts should touch or overlap.

Answer with the fields reply, name and bubbles:
- reply: one or two plain sentences for the person.
- name: a short name for the model.
- bubbles: every bubble of the whole model, not only the ones that changed.

The last message may give the model now on screen. Change that model when the person asks for a \
change, and keep the parts they did not mention. To answer or ask a question without changing \
anything, send an empty list of bubbles."

/-- The form of Claude's answer. `decode` still checks everything. -/
def answerSchemaText : String :=
  "{\"type\":\"object\",\"additionalProperties\":false,\"required\":[\"reply\",\"name\",\"bubbles\"],\
\"properties\":{\"reply\":{\"type\":\"string\"},\"name\":{\"type\":\"string\"},\"bubbles\":{\"type\":\"array\",\
\"items\":{\"type\":\"object\",\"additionalProperties\":false,\"required\":[\"label\",\"tags\",\"center\",\"semi\"],\
\"properties\":{\"label\":{\"type\":\"string\"},\"tags\":{\"type\":\"array\",\"items\":{\"type\":\"string\"}},\
\"center\":{\"type\":\"array\",\"items\":{\"type\":\"number\"}},\"semi\":{\"type\":\"array\",\"items\":{\"type\":\"number\"}}}}}}}"

#guard (Json.parse answerSchemaText).toOption.isSome

/-- One message of a conversation. `role` is `user` or `assistant`. -/
structure ChatMessage where
  role : String
  text : String
  deriving BEq, Repr, Inhabited

/-- What the person's newest message becomes, with the model on screen if there is one. -/
def withCurrentModel (current : Option BubbleModel) (text : String) : String :=
  match current with
  | some m => s!"The model now on screen:\n{encode m}\n\nThe person says:\n{text}"
  | none => s!"There is no model on screen yet.\n\nThe person says:\n{text}"

/-- The JSON sent to the Messages API. -/
def requestJson (messages : List ChatMessage) : Json :=
  let schema := (Json.parse answerSchemaText).toOption.getD .null
  Json.mkObj
    [ ("model", Json.str claudeModelId)
    , ("max_tokens", (16000 : Nat))
    , ("fallbacks", Json.str "default")
    , ("system", Json.str systemPrompt)
    , ("output_config", Json.mkObj
        [ ("effort", Json.str "medium")
        , ("format", Json.mkObj [("type", Json.str "json_schema"), ("schema", schema)]) ])
    , ("messages", Json.arr (messages.map fun m =>
        Json.mkObj [("role", Json.str m.role), ("content", Json.str m.text)]).toArray) ]

/-- What came back from one call. -/
inductive ClaudeReply where
  /-- The text of Claude's answer. -/
  | text (text : String)
  /-- Claude or the API said no. Asking again does not help. -/
  | failed (message : String)
  deriving BEq, Repr

/-- Read the reply of the Messages API. The key is never in it. -/
def readApiReply (reply : String) : ClaudeReply :=
  match Json.parse reply with
  | .error _ => .failed "Claude's service sent something that could not be read."
  | .ok j =>
    if (j.getObjValAs? String "type").toOption == some "error" then
      let kind := (j.getObjVal? "error" >>= (·.getObjValAs? String "type")).toOption.getD ""
      let message := (j.getObjVal? "error" >>= (·.getObjValAs? String "message")).toOption.getD ""
      match kind with
      | "authentication_error" =>
        .failed "Claude's service refused the API key in semantics/dev/.env."
      | _ => .failed s!"Claude's service gave an error: {message}"
    else if (j.getObjValAs? String "stop_reason").toOption == some "refusal" then
      .failed "Claude declined this request."
    else
      let blocks := (j.getObjValAs? (Array Json) "content").toOption.getD #[]
      let texts := blocks.toList.filterMap fun b =>
        if (b.getObjValAs? String "type").toOption == some "text" then
          (b.getObjValAs? String "text").toOption
        else none
      .text (String.join texts)

#guard readApiReply "{\"type\":\"message\",\"stop_reason\":\"end_turn\",\"content\":[{\"type\":\"thinking\",\"thinking\":\"\"},{\"type\":\"text\",\"text\":\"hi\"}]}" == .text "hi"
#guard readApiReply "{\"type\":\"message\",\"stop_reason\":\"refusal\",\"content\":[]}" == .failed "Claude declined this request."
#guard readApiReply "{\"type\":\"error\",\"error\":{\"type\":\"authentication_error\",\"message\":\"x\"}}" == .failed "Claude's service refused the API key in semantics/dev/.env."
#guard readApiReply "not json" matches .failed _

/-- A good answer: words for the person, and a new model unless Claude only answered. -/
structure ChatAnswer where
  reply : String
  model : Option BubbleModel
  deriving BEq, Repr

/-- Read Claude's answer. An error here is a message that goes back to Claude. The model is made
exactly 1 tall with `normalize`, so it does not matter if Claude's top is not quite at 1. -/
def readAnswer (text : String) : Except String ChatAnswer := do
  let j ← parseJson text
  let reply ← (← j.getObjVal? "reply").getStr?
  let bubbles ← (← j.getObjVal? "bubbles").getArr?
  if bubbles.isEmpty then return { reply, model := none }
  let m ← decode text
  return { reply, model := some (normalize m) }

-- An answer with a good model, scaled to height 1.
#guard (readAnswer "{\"reply\":\"ok\",\"name\":\"egg\",\"bubbles\":[{\"label\":\"egg\",\"tags\":[\"tower\"],\"center\":[0,0,2],\"semi\":[1.2,1.2,2]}]}").toOption ==
  some { reply := "ok", model := some BubbleModel.egg }
-- An answer with words only keeps the model.
#guard (readAnswer "{\"reply\":\"Which one?\",\"name\":\"\",\"bubbles\":[]}").toOption ==
  some { reply := "Which one?", model := none }
-- A model that floats goes back to Claude.
#guard (readAnswer "{\"reply\":\"ok\",\"name\":\"a\",\"bubbles\":[{\"label\":\"a\",\"tags\":[],\"center\":[0,0,5],\"semi\":[1,1,1]}]}") matches .error _
#guard (readAnswer "no json") matches .error _

/-- Read the key from the text of a `.env` file. -/
def keyFromEnvText (text : String) : Option String :=
  (text.splitOn "\n").findSome? fun line =>
    let t := line.trimAscii.toString
    let t := if t.startsWith "export " then (t.drop 7).trimAscii.toString else t
    if t.startsWith "ANTHROPIC_API_KEY=" then
      let v := (t.drop "ANTHROPIC_API_KEY=".length).trimAscii.toString
      let v := if v.length ≥ 2 && (v.startsWith "\"" || v.startsWith "'") then
        ((v.drop 1).dropEnd 1).toString else v
      if v.isEmpty then none else some v
    else none

#guard keyFromEnvText "# note\nANTHROPIC_API_KEY=abc\n" == some "abc"
#guard keyFromEnvText "export ANTHROPIC_API_KEY=\"abc\"" == some "abc"
#guard keyFromEnvText "ANTHROPIC_API_KEY=\n" == none
#guard keyFromEnvText "# ANTHROPIC_API_KEY=abc" == none

/-- Read the key from a file. No file or no key gives `none`. -/
def loadApiKey (path : System.FilePath) : IO (Option String) := do
  if ← path.pathExists then return keyFromEnvText (← IO.FS.readFile path)
  else return none

/-- A value for a `curl` settings file. -/
private def curlQuote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

#guard curlQuote "a\"b\\c" == "\"a\\\"b\\\\c\""

/-- The settings for `curl`. They go through its standard input, so that the key is not in the list
of running programs, where any program on this computer could read it. -/
private def curlSettings (key body : String) : String :=
  String.intercalate "\n"
    [ "url = \"https://api.anthropic.com/v1/messages\""
    , "silent", "show-error", "max-time = 180"
    , "header = \"content-type: application/json\""
    , "header = \"anthropic-version: 2026-10-21\""
    , "header = \"anthropic-beta: server-side-fallback-2026-07-01\""
    , s!"header = {curlQuote s!"x-api-key: {key}"}"
    , s!"data-binary = {curlQuote body}"
    , "" ]

/-- Make one call. -/
def callClaude (key : String) (messages : List ChatMessage) : IO ClaudeReply := do
  let child ← IO.Process.spawn
    { cmd := "curl", args := #["--config", "-"]
      stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr (curlSettings key (requestJson messages).compress)
  stdin.flush
  let out ← IO.asTask child.stdout.readToEnd .dedicated
  let err ← IO.asTask child.stderr.readToEnd .dedicated
  let code ← child.wait
  let reply ← IO.ofExcept out.get
  let _ ← IO.ofExcept err.get
  if code != 0 then
    return .failed s!"Could not reach Claude's service (curl stopped with code {code}). Check the internet connection."
  return readApiReply reply

/-- Send a conversation to Claude. A bad answer goes back to Claude with the reason, at most
`maxRetries` times; then the error is the result. `history` is the earlier conversation in plain
words; `text` is the newest message; `current` is the model on screen. -/
def chat (key : String) (history : List ChatMessage) (current : Option BubbleModel)
    (text : String) : IO (Except String ChatAnswer) :=
  let first := history ++ [⟨"user", withCurrentModel current text⟩]
  let rec attempt (retriesLeft : Nat) (messages : List ChatMessage) : IO (Except String ChatAnswer) := do
    match ← callClaude key messages with
    | .failed message => return .error message
    | .text answer =>
      match readAnswer answer with
      | .ok good => return .ok good
      | .error why =>
        match retriesLeft with
        | 0 => return .error s!"Claude did not give a good model after {maxRetries + 1} tries. The last problem: {why}"
        | n + 1 =>
          attempt n (messages ++
            [⟨"assistant", answer⟩,
             ⟨"user", s!"That answer was rejected: {why}\nSend the whole answer again, fixed."⟩])
  attempt maxRetries first

end KaplaSemantics
