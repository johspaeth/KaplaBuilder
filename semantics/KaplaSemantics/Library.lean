import KaplaSemantics.Score

/-!
# KaplaSemantics.Library — built-in targets (mm)

Until the Claude frontend (M7) lands, `interpret` maps prompts to these by keyword, or
loads a `TargetSpec` / `Shape` JSON file when the prompt is a path ending in `.json`.
-/

namespace Kapla.Semantics

open Kapla

def tr (x y z : Q) (s : Shape) : Shape := .translate ⟨x, y, z⟩ s

def library : List (List String × TargetSpec) := [
  (["tree", "baum"], { name := "tree", shape := .union [
      .tag "trunk" (.cylinder 12 120),
      .tag "crown" (tr 0 0 100 (.cone 70 160))] }),
  (["tower", "turm"], { name := "tower", shape := .tag "tower" (.box 117 117 312) }),
  (["wall", "mauer"], { name := "wall", shape := .tag "wall" (.box 585 (117/5) 156) }),
  (["house", "haus", "hut"], { name := "house", shape := .union [
      .tag "wall" (.box 234 156 117),
      .tag "roof:gable" (tr 0 0 117 (.wedge 250 172 90))] }),
  (["gable", "roof"], { name := "gable roof", shape := .tag "roof:gable" (.wedge 234 156 100) }),
  (["pyramid"], { name := "pyramid", shape := .pyramid 351 351 160 }),
  (["duck", "ente"], { name := "duck", shape := .union [
      .tag "body" (.box 160 90 60),
      .tag "head" (tr 55 0 60 (.cylinder 30 55)),
      .tag "beak" (tr 95 0 90 (.box 30 20 10))] }),
  (["castle", "neuschwanstein", "burg", "schloss"], { name := "castle", shape := .union [
      .tag "wall" (.diff (.box 468 351 156) (.box 420 303 160)),
      .tag "tower" (tr (-234) (-176) 0 (.cylinder 40 250)),
      .tag "tower" (tr 234 (-176) 0 (.cylinder 40 250)),
      .tag "tower" (tr (-234) 176 0 (.cylinder 40 250)),
      .tag "tower" (tr 234 176 0 (.cylinder 40 250)),
      .tag "roof:cone" (tr (-234) (-176) 250 (.cone 50 100)),
      .tag "roof:cone" (tr 234 (-176) 250 (.cone 50 100)),
      .tag "roof:cone" (tr (-234) 176 250 (.cone 50 100)),
      .tag "roof:cone" (tr 234 176 250 (.cone 50 100))] }),
  (["bridge", "brücke"], { name := "bridge", shape := .union [
      .tag "pillar" (tr (-117) 0 0 (.box 47 117 117)),
      .tag "pillar" (tr 117 0 0 (.box 47 117 117)),
      .tag "deck" (tr 0 0 117 (.box 351 117 16))] })
]

def lookupTarget (prompt : String) : Option TargetSpec :=
  let p := prompt.toLower
  (library.find? fun (keys, _) => keys.any fun k => (p.splitOn k).length > 1).map (·.2)

end Kapla.Semantics
