import KaplaPhysics

/-! # Rule lab: kid requests as builds of up to 200 planks, run through the physics checker.

Not a component: an experiment that uses `KaplaPhysics` to find which rules block
which builds. Every design is a plan (a list of planks in building order). For each
step we record what the checker says. See `lab/README.md`. -/

open KaplaPhysics

namespace Lab

def fx (x y z : Rat) : Plank := ⟨.flatX, x, y, z⟩
def fy (x y z : Rat) : Plank := ⟨.flatY, x, y, z⟩
def ex (x y z : Rat) : Plank := ⟨.edgeX, x, y, z⟩
def ey (x y z : Rat) : Plank := ⟨.edgeY, x, y, z⟩
def sy (x y z : Rat) : Plank := ⟨.standFacingY, x, y, z⟩
def sx (x y z : Rat) : Plank := ⟨.standFacingX, x, y, z⟩

def Plank.shiftBy (p : Plank) (dx dy dz : Rat) : Plank :=
  { p with x := p.x + dx, y := p.y + dy, z := p.z + dz }

/-- Crib tower with `n` levels, moved to `(ox, oy)`. -/
def tower (n : Nat) (ox oy : Rat) (oz : Rat := 0) : Build :=
  (squareTower n).map (Plank.shiftBy · ox oy oz)

/-- Leaning crib tower: level `L` is moved `L * a` along `x`. -/
def leaningTower (n : Nat) (a : Rat) : Build :=
  (List.range (2 * n)).map fun m => Plank.shiftBy (towerPlank m) (((m / 2 : Nat) : Rat) * a) 0 0

/-- Five flat-along-x planks side by side: a 15 × 15 floor at height `z`. -/
def deckX (x y0 z : Rat) : Build := [0, 3, 6, 9, 12].map fun (d : Rat) => fx x (y0 + d) z

structure Design where
  id : String
  category : String
  request : String
  note : String
  steps : Build

/-! ## Shapes -/

def tallest : Design :=
  { id := "tower200", category := "shape",
    request := "Papa, I want the tallest tower ever, use all the blocks.",
    note := "Square crib tower, 100 levels, 200 planks (78 cm).",
    steps := squareTower 100 }

def leaning : Design :=
  { id := "leaning", category := "shape",
    request := "Papa, build the leaning tower of Pisa.",
    note := "Crib tower, 16 levels, each level moved 1/2 unit (3.9 mm) along x.",
    steps := leaningTower 16 (1/2) }

def bridge : Design :=
  { id := "bridge", category := "shape",
    request := "Papa, I want a bridge my car can drive under.",
    note := "Two 12-level crib piers 9 units apart, a 5-plank deck spanning them, two edge rails.",
    steps := tower 12 0 0 ++ tower 12 24 0 ++ deckX 12 0 12 ++ [ex 12 0 13, ex 12 14 13] }

def leaningMore : Design :=
  { id := "leaning_more", category := "shape",
    request := "Papa, lean it more, more.",
    note := "Crib tower, 16 levels, each level moved 1 unit (7.8 mm) along x.",
    steps := leaningTower 16 1 }

/-- Corbel arch: two stepped piles leaning in, closed by a keystone plank. -/
def arch : Design :=
  let left : Build := (List.range 6).map fun (k : Nat) => fx (2 * (k : Rat)) 0 (k : Rat)
  let right : Build := (List.range 6).map fun (k : Nat) => fx (41 - 2 * (k : Rat)) 0 (k : Rat)
  { id := "arch", category := "shape",
    request := "Papa, make a rainbow arch.",
    note := "Two 6-step corbel piles (2-unit steps), keystone on top. Real arches need tilted blocks (B4).",
    steps := left ++ right ++ [fx (41/2) 0 6] }

/-- Stepped pyramid: 3 × 3 crib towers, heights 2 / 4 / 6 levels. -/
def pyramid : Design :=
  let h : Nat → Nat → Nat := fun i j =>
    if i = 1 ∧ j = 1 then 6 else if i = 1 ∨ j = 1 then 4 else 2
  let cells : List (Nat × Nat) := [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
  { id := "pyramid", category := "shape",
    request := "Papa, build an Egyptian pyramid.",
    note := "3 × 3 grid of touching crib towers, 2-4-6 levels.",
    steps := cells.flatMap fun (i, j) => tower (h i j) (15 * (i : Rat)) (15 * (j : Rat)) }

/-! ## Animals -/

/-- Tree: 10-level crib trunk, a deck, four leaf planks around the edge. -/
def tree : Build :=
  tower 10 0 0 ++ deckX 0 0 10 ++ [fx 0 0 11, fx 0 12 11, fy 0 0 12, fy 12 0 12]

/-- Duck parts standing on a leg whose top is at height `t`. Order chosen so every
step balances on the leg. -/
def duckTuned (t : Rat) : Build :=
  [fx 0 6 t,            -- body
   fx 0 6 (t + 1),      -- body, second layer
   fx (-3) 6 (t + 2),   -- tail feather 1 (sticks out back)
   sy 12 7 (t + 2),     -- neck (standing plank at the front)
   fx (-3) 6 (t + 3),   -- tail feather 2
   fx 6 6 (t + 17),     -- head, beak sticks out front
   fx (-3) 6 (t + 4)]   -- tail feather 3

/-- The same duck parts in the order a child would say them: body, neck, head, tail. -/
def duckNaive (t : Rat) : Build :=
  [fx 0 6 t, fx 0 6 (t + 1), sy 12 7 (t + 2), fx 6 6 (t + 17),
   fx (-3) 6 (t + 2), fx (-3) 6 (t + 3), fx (-3) 6 (t + 4)]

def duckOneLeg : Design :=
  { id := "duck_one_leg", category := "animal",
    request := "Papa, I want a Kapla duck that stands on 1 leg, in a tree.",
    note := "Tree (29 planks) + one standing plank as the leg (3 × 1 footprint) + 7-plank duck, tuned order.",
    steps := tree ++ [sy 6 7 11] ++ duckTuned 26 }

def duckNaiveOrder : Design :=
  { id := "duck_naive_order", category := "animal",
    request := "Same duck, built in the order the child says it: body, neck, head, then tail.",
    note := "Identical final build to duck_one_leg, different order.",
    steps := tree ++ [sy 6 7 11] ++ duckNaive 26 }

def duckThickLeg : Design :=
  { id := "duck_thick_leg", category := "animal",
    request := "Papa, the duck on one leg, but a strong leg.",
    note := "Leg = three standing planks pressed together (3 × 3 footprint).",
    steps := tree ++ [sy 6 6 11, sy 6 7 11, sy 6 8 11] ++ duckTuned 26 }

def duckGround : Design :=
  { id := "duck_ground", category := "animal",
    request := "Papa, a duck on one leg (no tree).",
    note := "One standing plank on the table, same 7-plank duck.",
    steps := [sy 6 7 0] ++ duckTuned 15 }

/-- Tree with a branch sticking out to the right, resting on one leaf plank (the pivot). -/
def treeBranch : Build := tree ++ [fx 6 6 13]

def duckBranchA : Design :=
  { id := "duck_branch_weight_first", category := "animal",
    request := "Papa, the duck sits at the end of a branch.",
    note := "Branch pivots on one leaf plank. Counterweight on the back end first, then the sitting duck at the tip.",
    steps := treeBranch ++ [fy 6 0 14, fy 18 0 14] }

def duckBranchB : Design :=
  { id := "duck_branch_duck_first", category := "animal",
    request := "Same branch, put the duck on first.",
    note := "Sitting duck at the tip first, then the counterweight.",
    steps := treeBranch ++ [fy 18 0 14, fy 6 0 14] }

def dog : Design :=
  { id := "dog", category := "animal",
    request := "Papa, build me a puppy.",
    note := "Four standing-plank legs, two cross beams, 5-plank back, head and tail sticking out.",
    steps := [sy 0 0 0, sy 12 0 0, sy 0 14 0, sy 12 14 0, fy 0 0 15, fy 12 0 15] ++
      deckX 0 0 16 ++ [fx 6 6 17, fx (-6) 9 17] }

def giraffe : Design :=
  { id := "giraffe", category := "animal",
    request := "Papa, a giraffe with a really long neck.",
    note := "Legs of two stacked standing planks, back, a standing-plank neck and a head.",
    steps := [sy 0 0 0, sy 12 0 0, sy 0 14 0, sy 12 14 0,
              sy 0 0 15, sy 12 0 15, sy 0 14 15, sy 12 14 15,
              fy 0 0 30, fy 12 0 30] ++ deckX 0 0 31 ++
      [sy 12 7 32, fx 6 6 47, fx (-6) 9 32] }

def snake : Design :=
  { id := "snake", category := "animal",
    request := "Papa, a long wiggly snake.",
    note := "Ground planks with gaps, bridged by a second layer (a wave), T-shaped head.",
    steps := [fx 0 0 0, fx 18 0 0, fx 36 0 0, fx 54 0 0, fx 9 0 1, fx 27 0 1, fx 45 0 1,
              fy 69 (-6) 0] }

/-! ## Cars -/

def boxCar : Design :=
  { id := "box_car", category := "car",
    request := "Papa, build me a car with a roof.",
    note := "Two on-edge planks as axles (no round wheels, B4), 5-plank chassis, 2-level cabin walls, 5-plank roof.",
    steps := [ey 1 0 0, ey 13 0 0] ++ deckX 0 0 3 ++
      [fy 3 0 4, fy 9 0 4, fy 3 0 5, fy 9 0 5] ++ deckX 0 0 6 }

def raceCar : Design :=
  { id := "race_car", category := "car",
    request := "Papa, a race car with a big spoiler on the back.",
    note := "Axles, chassis, a nose plank, an on-edge spoiler post, a flat wing on the post.",
    steps := [ey 1 0 0, ey 13 0 0] ++ deckX 0 0 3 ++
      [fx 7 6 4, ey 0 0 4, fy (-1) 0 7] }

def raceCarTall : Design :=
  { id := "race_car_tall_spoiler", category := "car",
    request := "Papa, the spoiler has to be way up high.",
    note := "Spoiler wing on one standing plank (3 × 1 footprint).",
    steps := [ey 1 0 0, ey 13 0 0] ++ deckX 0 0 3 ++
      [fx 7 6 4, sy 0 7 4, fy 0 0 19] }

def boxCarDriver : Design :=
  { id := "box_car_driver", category := "car",
    request := "Papa, put a driver in the car (after the roof is on).",
    note := "Driver plank slid into the 3-unit gap between the cabin walls, under the roof, last.",
    steps := boxCar.steps ++ [fy 6 0 4] }

def boxCarFlat : Design :=
  { id := "box_car_flat_axles", category := "car",
    request := "Papa, the car keeps being risky. Fix it.",
    note := "Same car, but the axles lie flat (3-unit-wide contact) instead of on edge (1-unit).",
    steps := [fy 0 0 0, fy 12 0 0] ++ deckX 0 0 1 ++
      [fy 3 0 2, fy 9 0 2, fy 3 0 3, fy 9 0 3] ++ deckX 0 0 4 }

/-- Generated by gen_duck200.py. -/
def duck200Steps : Build :=
  [fx 0 0 0,
   fx 0 12 0,
   fy 0 0 1,
   fy 12 0 1,
   fx 0 0 2,
   fx 0 12 2,
   fy 0 0 3,
   fy 12 0 3,
   fx 0 0 4,
   fx 0 12 4,
   fy 0 0 5,
   fy 12 0 5,
   fx 0 0 6,
   fx 0 12 6,
   fy 0 0 7,
   fy 12 0 7,
   fx 0 0 8,
   fx 0 12 8,
   fy 0 0 9,
   fy 12 0 9,
   fx 0 0 10,
   fx 0 12 10,
   fy 0 0 11,
   fy 12 0 11,
   fx 0 0 12,
   fx 0 12 12,
   fy 0 0 13,
   fy 12 0 13,
   fx 0 0 14,
   fx 0 12 14,
   fy 0 0 15,
   fy 12 0 15,
   fx 0 0 16,
   fx 0 12 16,
   fy 0 0 17,
   fy 12 0 17,
   fx 0 0 18,
   fx 0 12 18,
   fy 0 0 19,
   fy 12 0 19,
   fx 0 0 20,
   fx 0 12 20,
   fy 0 0 21,
   fy 12 0 21,
   fx 0 0 22,
   fx 0 12 22,
   fy 0 0 23,
   fy 12 0 23,
   fx 0 0 24,
   fx 0 12 24,
   fy 0 0 25,
   fy 12 0 25,
   fx 0 0 26,
   fx 0 12 26,
   fy 0 0 27,
   fy 12 0 27,
   fx 0 0 28,
   fx 0 12 28,
   fy 0 0 29,
   fy 12 0 29,
   fx 0 0 30,
   fx 0 12 30,
   fy 0 0 31,
   fy 12 0 31,
   fx 0 0 32,
   fx 0 12 32,
   fy 0 0 33,
   fy 12 0 33,
   fx 0 0 34,
   fx 0 12 34,
   fy 0 0 35,
   fy 12 0 35,
   fx 0 0 36,
   fx 0 12 36,
   fy 0 0 37,
   fy 12 0 37,
   fx 0 0 38,
   fx 0 12 38,
   fy 0 0 39,
   fy 12 0 39,
   fx 0 0 40,
   fx 0 12 40,
   fy 0 0 41,
   fy 12 0 41,
   fx 0 0 42,
   fx 0 12 42,
   fy 0 0 43,
   fy 12 0 43,
   fx 0 0 44,
   fx 0 12 44,
   fy 0 0 45,
   fy 12 0 45,
   fx 0 0 46,
   fx 0 12 46,
   fy 0 0 47,
   fy 12 0 47,
   fx 0 0 48,
   fx 0 12 48,
   fy 0 0 49,
   fy 12 0 49,
   fx 0 0 50,
   fx 0 12 50,
   fy 0 0 51,
   fy 12 0 51,
   fx 0 0 52,
   fx 0 3 52,
   fx 0 6 52,
   fx 0 9 52,
   fx 0 12 52,
   fy 0 (-6) 53,
   fy 12 6 53,
   fx (-6) 0 54,
   fx 6 12 54,
   fy 0 (-6) 55,
   fy 12 6 55,
   fx (-6) 0 56,
   fx 6 12 56,
   fy 0 (-6) 57,
   fy 12 6 57,
   fx (-6) 0 58,
   fx 6 12 58,
   sy 6 7 53,
   fx 0 6 68,
   fy 6 0 69,
   fx 0 6 70,
   fy 6 0 71,
   fy 9 0 71,
   fy 3 0 71,
   fy 12 0 71,
   fy 0 0 71,
   fx 0 6 72,
   fx 0 9 72,
   fx 0 3 72,
   fy 6 0 73,
   fy 9 0 73,
   fy 3 0 73,
   fy 12 0 73,
   fy 0 0 73,
   fx 0 6 74,
   fx 0 9 74,
   fx 0 3 74,
   fx 0 12 74,
   fx 0 0 74,
   fy 6 0 75,
   fy 9 0 75,
   fy 3 0 75,
   fy 12 0 75,
   fy 0 0 75,
   fx 0 6 76,
   fx 0 9 76,
   fx 0 3 76,
   fx 0 12 76,
   fx 0 0 76,
   fy 6 0 77,
   fy 9 0 77,
   fy 3 0 77,
   fy 12 0 77,
   fy 0 0 77,
   fx 0 6 78,
   fx 0 9 78,
   fx 0 3 78,
   fx 0 12 78,
   fx 0 0 78,
   fx (-3) 6 79,
   fy 12 0 79,
   fx (-3) 9 79,
   fx (-3) 3 79,
   fx 6 6 80,
   fy 12 0 81,
   fx (-9/2) 9 80,
   fx (-9/2) 3 80,
   fx 6 6 82,
   fx (-6) 9 81,
   fx (-6) 3 81,
   fy 12 0 83,
   fx 6 6 84,
   fx (-15/2) 9 82,
   fx (-15/2) 3 82,
   fy 12 0 85,
   fx 6 6 86,
   fy 12 0 87,
   fx (-9) 9 83,
   fx (-9) 3 83,
   fx 6 6 88,
   fy 12 0 89,
   fx 6 6 90,
   fx (-21/2) 9 84,
   fx (-21/2) 3 84,
   fy 12 0 91,
   fx 6 6 92,
   fy 12 0 93,
   fx (-3) 12 79,
   fx (-3) 0 79,
   fy 9 0 93,
   fy 15 0 93,
   fx 6 9 94,
   fx 6 3 94,
   fx 9 6 94,
   fy (21/2) 0 95,
   fy (27/2) 0 95]

def duck200 : Design :=
  { id := "duck200", category := "animal",
    request := "Papa, I want a Kapla duck that stands on 1 leg, in a tree. Use all 200 blocks.",
    note := "52-level crib trunk, deck, pinwheel leaf crown; one standing-plank leg; 41-plank crib body, 5-plank folded wings, two-prong tail, 13-level crossed neck, crib head, beak, centred crest. Order chosen to keep the weight over the leg.",
    steps := duck200Steps }

def all : List Design :=
  [duck200, tallest, leaning, leaningMore, bridge, arch, pyramid,
   duckOneLeg, duckNaiveOrder, duckThickLeg, duckGround, duckBranchA, duckBranchB, dog, giraffe, snake,
   boxCar, boxCarDriver, boxCarFlat, raceCar, raceCarTall]

/-! ## Output -/

def ratStr (r : Rat) : String :=
  if r.den == 1 then toString r.num else s!"{r.num}/{r.den}"

def ratF (r : Rat) : String :=
  let f := (Float.ofInt r.num) / (Float.ofNat r.den)
  toString f

def poseStr : Pose → String
  | .flatX => "flatX" | .flatY => "flatY" | .edgeX => "edgeX" | .edgeY => "edgeY"
  | .standFacingY => "standFacingY" | .standFacingX => "standFacingX"

def ansStr : Answer → String
  | .stable => "stable" | .falls => "falls" | .unknown => "unknown"

def verStr : Verdict → String
  | .solid => "solid" | .risky => "risky" | .falls => "falls" | .unknown => "unknown"

def dirStr : Option Dir → String
  | none => "null"
  | some .fromAbove => "\"above\"" | some .fromPlusX => "\"+x\"" | some .fromMinusX => "\"-x\""
  | some .fromPlusY => "\"+y\"" | some .fromMinusY => "\"-y\""

def jstr (s : String) : String := "\"" ++ (s.replace "\"" "\\\"") ++ "\""

def mm : Rat := 39 / 5  -- 7.8 mm per unit

def eps2 : Rat := placementError   -- 2 mm
def eps1 : Rat := 5 / 39           -- 1 mm
def eps05 : Rat := 5 / 78          -- 0.5 mm

def run (d : Design) : IO String := do
  let n := d.steps.length
  let mut stepsJ : Array String := #[]
  let mut firstBad : Option (Nat × String) := none
  let mut nStable := 0
  let mut nSolid := 0
  for k in List.range n do
    let b := d.steps.take (k + 1)
    let wf := decide (WellFormed b)
    let ex := stabilityAnswer b
    let s2 := wf && solidAnswer eps2 b
    let s1 := if s2 then true else wf && solidAnswer eps1 b
    let reach := reachDir? (d.steps.take k) (d.steps.get k) dropGap
    if ex == .stable then nStable := nStable + 1
    if s2 then nSolid := nSolid + 1
    if firstBad.isNone then
      if !wf then firstBad := some (k, "not well-formed")
      else if ex == .falls then firstBad := some (k, "falls")
      else if ex == .unknown then firstBad := some (k, "unknown")
      else if !s2 then firstBad := some (k, "risky")
    let p := d.steps.get k
    stepsJ := stepsJ.push
      s!"\{\"pose\":{jstr (poseStr p.pose)},\"x\":{ratF p.x},\"y\":{ratF p.y},\"z\":{ratF p.z},\"wf\":{wf},\"exact\":{jstr (ansStr ex)},\"solid2mm\":{s2},\"solid1mm\":{s1},\"reach\":{dirStr reach}}"
  let b := d.steps
  let v2 := verdict eps2 b
  let v1 := verdict eps1 b
  let v05 := verdict eps05 b
  let v0 := verdict 0 b
  let v024 := verdict (6/25) b
  let v025 := verdict (1/4) b
  let plan := checkPlan {} eps2 200 b
  let htr := hardToReach dropGap b
  let height := b.foldl (fun m p => max m p.top) 0
  let fb := match firstBad with
    | none => "null"
    | some (k, r) => s!"\{\"step\":{k},\"reason\":{jstr r}}"
  IO.eprintln s!"{d.id}: n={n} final2mm={verStr v2} 1mm={verStr v1} 0.5mm={verStr v05} 0={verStr v0} 0.24u={verStr v024} 0.25u={verStr v025} plan={plan} firstBad={fb} stableSteps={nStable} solidSteps={nSolid} hard={htr}"
  return s!"\{\"id\":{jstr d.id},\"category\":{jstr d.category},\"request\":{jstr d.request},\"note\":{jstr d.note},\"n\":{n},\"heightUnits\":{ratF height},\"heightMm\":{ratF (height * mm)},\"final\":\{\"wf\":{decide (WellFormed b)},\"exact\":{jstr (ansStr (stabilityAnswer b))},\"v2mm\":{jstr (verStr v2)},\"v1mm\":{jstr (verStr v1)},\"v05mm\":{jstr (verStr v05)},\"v0\":{jstr (verStr v0)},\"v_0_24u\":{jstr (verStr v024)},\"v_0_25u\":{jstr (verStr v025)}},\"checkPlan2mm\":{plan},\"firstBad\":{fb},\"stableSteps\":{nStable},\"solidSteps\":{nSolid},\"hardToReach\":{htr},\"steps\":[{",".intercalate stepsJ.toList}]}"

end Lab

def main (args : List String) : IO Unit := do
  let sel := Lab.all.filter fun d => args.isEmpty || args.contains d.id
  let mut out : Array String := #[]
  for d in sel do
    out := out.push (← Lab.run d)
  IO.println ("[" ++ ",\n".intercalate out.toList ++ "]")
