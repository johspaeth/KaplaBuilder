import KaplaPlanner.Grid

/-! # A cheap stability estimate on the grid (untrusted)

Used many times inside the search (DESIGN.md §3.5). The physics engine has the final word,
once, on the finished plan.

The rule (the same as the physics mock): each block passes its load down to the blocks it
rests on. One support: the load passes on at its load point. Several supports: it is split
equally, acting at the centre of each contact. A block is held up if its load point lies over
the area where it touches its supports (or the ground). -/

namespace KaplaPlanner
open KaplaCore

/-- Do the blocks, all built, stand? (Only the final state; the search adds blocks bottom-up
and checks after each one, so every step is covered.) -/
def standsNow (bs : List GridBlock) : Bool := Id.run do
  let arr := bs.toArray
  let n := arr.size
  let mut below : Array (List Nat) := Array.replicate n []
  let mut above : Array (List Nat) := Array.replicate n []
  for i in [0:n] do
    for j in [0:n] do
      if i != j && arr[i]!.restsOn arr[j]! then
        below := below.modify i (j :: ·)
        above := above.modify j (i :: ·)
  -- centre and contact areas are in half-units, to stay in whole numbers where possible
  let centre (b : GridBlock) : Q × Q := ((2 * b.x + b.sx : Int), (2 * b.y + b.sy : Int))
  let contact (u l : GridBlock) : (Q × Q) × (Q × Q) :=
    ((((2 * max u.x l.x : Int) : Q), ((2 * max u.y l.y : Int) : Q)),
     (((2 * min (u.x + u.sx) (l.x + l.sx) : Int) : Q), ((2 * min (u.y + u.sy) (l.y + l.sy) : Int) : Q)))
  let mut load : Array (Q × Q × Q) := arr.map fun b => let (cx, cy) := centre b; (1, cx, cy)
  let order := (List.range n).mergeSort fun i j => arr[i]!.z ≥ arr[j]!.z
  for i in order do
    let (cx, cy) := centre arr[i]!
    let mut w : Q := 1
    let mut mx : Q := cx
    let mut my : Q := cy
    for u in above[i]! do
      let (wu, ux, uy) := load[u]!
      let k := below[u]!.length
      if k == 1 then
        w := w + wu; mx := mx + wu * ux; my := my + wu * uy
      else
        let ((lx, ly), (hx, hy)) := contact arr[u]! arr[i]!
        let share := wu / (k : Q)
        w := w + share; mx := mx + share * (lx + hx) / 2; my := my + share * (ly + hy) / 2
    load := load.set! i (w, mx / w, my / w)
  for i in [0:n] do
    let b := arr[i]!
    let (_, px, py) := load[i]!
    if b.onGround then
      if !(((2 * b.x : Int) : Q) ≤ px && px ≤ ((2 * (b.x + b.sx) : Int) : Q) &&
           ((2 * b.y : Int) : Q) ≤ py && py ≤ ((2 * (b.y + b.sy) : Int) : Q)) then return false
    else
      match below[i]! with
      | [] => return false
      | sups =>
        let cs := sups.map fun j => contact b arr[j]!
        let lx := (cs.map (·.1.1)).foldl min (cs.head!.1.1)
        let ly := (cs.map (·.1.2)).foldl min (cs.head!.1.2)
        let hx := (cs.map (·.2.1)).foldl max (cs.head!.2.1)
        let hy := (cs.map (·.2.2)).foldl max (cs.head!.2.2)
        if !(lx ≤ px && px ≤ hx && ly ≤ py && py ≤ hy) then return false
  return true

-- a stack stands; a floating block does not; a big overhang does not
#guard standsNow [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 30, 0, 4⟩]
#guard !standsNow [⟨.flatX, 0, 0, 4⟩]
#guard !standsNow [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 45, 0, 4⟩]
-- the overhang stands once a counterweight is on its back end
#guard !standsNow [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 34, 0, 4⟩]
#guard standsNow [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 34, 0, 4⟩, ⟨.flatX, 10, 0, 8⟩]

end KaplaPlanner
