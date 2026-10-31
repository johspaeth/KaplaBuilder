import KaplaPhysics
import KaplaSemantics
import KaplaPlanner

/-!
Regenerates `fixtures/` (run from the repo root):

    lake env lean --run scripts/GenFixtures.lean

Plans and targets are the shared language between the teams (WORKSPLIT §5). The
`physics_expected/` files record what the verified M1 checker must answer; edit them by
hand only together with a spec change.
-/

open Kapla Lean

def T : Q := Block.T
def flat (x y z : Q) (r : Rot := Rot.id) : Pose := { up := .flat, rot := r, center := ⟨x, y, z⟩ }
def upright (x y : Q) : Pose := { up := .upright, rot := Rot.id, center := ⟨x, y, Block.L / 2⟩ }
def one (bs : List Pose) : BuildPlan := BuildPlan.ofBlocks bs

def plans : List (String × BuildPlan) := [
  ("tree_1block", one [upright 0 0]),
  ("tower_10", one (Planning.cabinTower 0 0 5)),
  ("overhang_knife_edge", one [flat 0 0 (T/2), flat 58 0 (3*T/2)]),
  ("overhang_bad", one [flat 0 0 (T/2), flat 60 0 (3*T/2)]),
  -- yaw 10° and 20° (tan(θ/2) = 7/80 and 3/17)
  ("rotated_stack", one [flat 0 0 (T/2), flat 0 0 (3*T/2) (Rot.ofTanHalf (7/80)),
                         flat 0 0 (5*T/2) (Rot.ofTanHalf (3/17))]),
  -- 30° crossing: stands, but pressing the end of the upper block tips it (H4)
  ("rotated_30_press", one [flat 0 0 (T/2), flat 0 0 (3*T/2) (Rot.ofTanHalf (4/15))]),
  ("near_miss_gap", one [flat 0 0 (T/2), flat 0 (117/5 + 1) (T/2)]),
  ("cantilever_order_bad", one [flat 0 0 (T/2), flat 61 0 (3*T/2), flat 24 0 (5*T/2)]),
  ("cantilever_2hands", ⟨[{ blocks := [flat 0 0 (T/2)] },
                          { blocks := [flat 61 0 (3*T/2), flat 24 0 (5*T/2)], phase := "two hands" }]⟩),
  ("overlap_bad", one [flat 0 0 (T/2), flat 30 10 (T/2) Rot.quarter]),
  ("floating_bad", one [flat 0 0 50]),
  ("bridge_uprights", one [upright (-47) 0, upright 47 0, flat 0 0 (Block.L + T/2)]),
  -- H1/H2: the upper block is lined up with the lower one (`refs`)
  ("stack_aligned", ⟨[{ blocks := [flat 0 0 (T/2)] }, { blocks := [flat 0 0 (3*T/2)], refs := [some 0] }]⟩),
  -- 6 mm sideways: stands, robust for an expert (ε = 1.5 mm) but not for an adult (3 mm)
  ("stack_offset_6", ⟨[{ blocks := [flat 0 0 (T/2)] }, { blocks := [flat 0 6 (3*T/2)], refs := [some 0] }]⟩)
]

/-- `(plan, profile, N, expected ok, expected diagnostics)` -/
def expected : List (String × String × Nat × Bool × List Diagnostic) := [
  ("tree_1block", "adult", 1, true, []),
  ("tower_10", "adult", 10, true, []),
  ("tower_10", "adult", 9, false, [.tooManyBlocks 10 9]),
  ("overhang_knife_edge", "adult", 2, false, [.pressTips 1 1]),
  ("overhang_bad", "adult", 2, false, [.unstable 1 1]),
  ("rotated_stack", "adult", 3, true, []),
  ("cantilever_order_bad", "adult", 3, false, [.unstable 1 1]),
  ("cantilever_2hands", "adult", 3, true, []),
  ("cantilever_2hands", "child", 3, false, [.tooManyHands 1, .pressTips 1 1]),
  ("overlap_bad", "adult", 2, false, [.overlap 0 1, .clearance 0 1]),
  ("rotated_30_press", "adult", 2, false, [.pressTips 1 0]),
  ("near_miss_gap", "adult", 2, false, [.clearance 0 1]),
  ("floating_bad", "adult", 1, false, [.unstable 0 0]),
  ("bridge_uprights", "adult", 3, true, []),
  ("stack_aligned", "adult", 2, true, []),
  ("stack_aligned", "child", 2, true, []),
  ("stack_offset_6", "adult", 2, true, []),
  ("stack_offset_6", "expert", 2, true, [])
]

/-- `(plan, profile)` pairs that must also be certified `Robust` (H1/H2, translations). Plans
without alignment references, and cabin towers, are not: the rigid-shift certificate is
conservative (see `KaplaPhysics/Robust.lean`). -/
def robustExpected : List (String × String) :=
  [("tree_1block", "adult"), ("stack_aligned", "adult"), ("stack_aligned", "child"),
   ("stack_offset_6", "expert")]

def main : IO Unit := do
  IO.FS.createDirAll "fixtures/plans"
  IO.FS.createDirAll "fixtures/targets"
  IO.FS.createDirAll "fixtures/physics_expected"
  for (name, p) in plans do
    IO.FS.writeFile s!"fixtures/plans/{name}.json" ((toJson p).pretty ++ "\n")
  for (_, t) in Semantics.library do
    IO.FS.writeFile s!"fixtures/targets/{t.name.replace " " "_"}.json" ((toJson t).pretty ++ "\n")
  for (name, prof, n, ok, ds) in expected do
    let j := Json.mkObj [("plan", toJson name), ("profile", toJson prof), ("blocks", toJson n),
                         ("ok", toJson ok), ("robust", toJson (robustExpected.contains (name, prof))),
                         ("diagnostics", toJson ds)]
    let suffix := if prof == "adult" then s!"_N{n}" else s!"_{prof}_N{n}"
    IO.FS.writeFile s!"fixtures/physics_expected/{name}{suffix}.json" (j.pretty ++ "\n")
  IO.println s!"wrote {plans.length} plans, {Semantics.library.length} targets, {expected.length} expectations"
