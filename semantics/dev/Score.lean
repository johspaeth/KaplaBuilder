import KaplaSemantics.Engine

/-! Score a blocks file against a bubble model at a height, and print the report:

    lake build KaplaSemantics
    lake env lean --run semantics/dev/Score.lean MODEL.json BLOCKS.json HEIGHT

This file is outside the library on purpose. Its `main` would clash with the `main` of `kapla`
in `lake check`. All the work is in `KaplaSemantics.runScore`, which CI builds and tests. -/

def main : List String → IO UInt32
  | [model, blocks, height] => do
    match KaplaSemantics.runScore (← IO.FS.readFile model) (← IO.FS.readFile blocks) height with
    | .ok text =>
      IO.println text
      return 0
    | .error e =>
      IO.eprintln e
      return 1
  | _ => do
    IO.eprintln "usage: Score MODEL.json BLOCKS.json HEIGHT"
    return 64
