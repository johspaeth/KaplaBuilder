import Lean.Data.Json

/-! # A small client for the Claude Messages API

Untrusted: whatever Claude answers is checked by the engines afterwards. The call goes through
`curl`. The key comes from the environment variable `ANTHROPIC_API_KEY`; it is written to a
temporary header file, so it does not show up in the process list. -/

namespace KaplaPlanner.Claude

open Lean

/-- The Claude model the planner asks. -/
def model : String := "claude-opus-5-5"

/-- The Messages API endpoint. -/
def endpoint : String := "https://api.anthropic.com/v1/messages"

/-- The request body: one user message, an answer that must follow `schema`. -/
def requestBody (system user : String) (schema : Json) : Json :=
  Json.mkObj
    [ ("model", model)
    , ("max_tokens", (100000 : Nat))
    , ("system", system)
    , ("thinking", Json.mkObj [("type", "adaptive")])
    , ("output_config", Json.mkObj
        [ ("effort", "high")
        , ("format", Json.mkObj [("type", "json_schema"), ("schema", schema)]) ])
    -- if a safety check declines the request, the API retries it on another model
    , ("fallbacks", "default")
    , ("messages", Json.arr #[Json.mkObj [("role", "user"), ("content", user)]]) ]

/-- The text of the answer, from the API's JSON reply. An error reply, a refused request and a
cut-off answer are errors. -/
def answerText (reply : String) : Except String String := do
  let j ← Json.parse reply
  if (j.getObjValAs? String "type").toOption == some "error" then
    let msg := (j.getObjVal? "error" >>= (·.getObjValAs? String "message")).toOption.getD reply
    throw s!"API error: {msg}"
  match (j.getObjValAs? String "stop_reason").toOption with
  | some "refusal" => throw "Claude declined the request"
  | some "max_tokens" => throw "the answer was cut off (max_tokens)"
  | _ => pure ()
  let content ← j.getObjValAs? (Array Json) "content"
  let texts := content.toList.filterMap fun b =>
    if (b.getObjValAs? String "type").toOption == some "text" then
      (b.getObjValAs? String "text").toOption
    else none
  match texts with
  | t :: _ => return t
  | [] => throw "the reply has no text"

#guard (answerText "{\"type\":\"message\",\"stop_reason\":\"end_turn\",\"content\":[{\"type\":\"thinking\",\"thinking\":\"\"},{\"type\":\"text\",\"text\":\"{}\"}]}").toOption == some "{}"
#guard answerText "{\"type\":\"error\",\"error\":{\"type\":\"x\",\"message\":\"bad key\"}}" matches .error "API error: bad key"
#guard answerText "{\"type\":\"message\",\"stop_reason\":\"refusal\",\"content\":[]}" matches .error _

/-- Ask Claude once. The answer is JSON text that follows `schema`. -/
def ask (system user : String) (schema : Json) : IO (Except String String) := do
  let some key ← IO.getEnv "ANTHROPIC_API_KEY"
    | return .error "ANTHROPIC_API_KEY is not set"
  if key.isEmpty then return .error "ANTHROPIC_API_KEY is empty"
  try
    IO.FS.withTempFile fun hh headerPath => do
      hh.putStr s!"x-api-key: {key}\nanthropic-version: 2026-10-21\nanthropic-beta: server-side-fallback-2026-07-01\ncontent-type: application/json\n"
      hh.flush
      IO.FS.withTempFile fun hb bodyPath => do
        hb.putStr (requestBody system user schema).compress
        hb.flush
        let out ← IO.Process.output
          { cmd := "curl"
            args := #["-sS", "--max-time", "1800", "-X", "POST", endpoint,
                      "-H", s!"@{headerPath}", "--data-binary", s!"@{bodyPath}"] }
        if out.exitCode != 0 then
          return .error s!"curl failed ({out.exitCode}): {out.stderr.trimAscii}"
        return answerText out.stdout
  catch e =>
    return .error s!"could not run curl: {e}"

end KaplaPlanner.Claude
