import KaplaWeb.Page

/-! Write the viewer page with no blocks, for showing bubble models. `web/serve-bubbles.sh` runs it:

    lake env lean --run web/dev/BubblePage.lean OUT.html

This file is outside the library on purpose. Its `main` would clash with the `main` of `kapla`
in `lake check`.
-/

def main : List String → IO UInt32
  | [out] => do
    IO.FS.writeFile out (KaplaWeb.render { title := "Kapla bubbles", steps := [] })
    return 0
  | _ => do
    IO.eprintln "usage: BubblePage OUT.html"
    return 64
