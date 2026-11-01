import KaplaPlanner.Grid

/-! # Positions a person can find by eye

A person cannot put a block at 32.28 % of another block. They can line it up by eye: a
block's left end, centre or right end goes exactly at the left end, a quarter, the centre,
three quarters or the right end of a block that is already there.

**The rule** (checked by `eyeballable`), for the blocks in build order:
- a block that rests on other blocks lines up, along x and along y, with one block it rests
  on;
- a block on the ground lines up, along x and along y, with a block already on the ground.
  The very first block can go anywhere.

"Lines up along x" means: one of the new block's three points (left end, centre, right
end) is exactly at one of the other block's five points (left end, ¼, ½, ¾, right end).
Touching end to end or side by side counts: the right end of one is the left end of the
other.

With the grid unit of a quarter block thickness, all these points are whole numbers. -/

namespace KaplaPlanner

/-- The five points of a block along one axis that a person can aim at:
both ends, the quarter points and the centre. `lo` is the start, `len` the length. -/
def aimPoints (lo len : Int) : List Int :=
  [lo, lo + len / 4, lo + len / 2, lo + 3 * len / 4, lo + len]

/-- The three points of the new block a person lines up: both ends and the centre. -/
def ownPoints (lo len : Int) : List Int := [lo, lo + len / 2, lo + len]

/-- Along one axis, a point of the new block is at a point of the other block. -/
def linedUpOnAxis (aLo aLen bLo bLen : Int) : Bool :=
  (ownPoints bLo bLen).any fun p => (aimPoints aLo aLen).contains p

/-- Block `b` lines up with block `a` along x and along y. -/
def linedUpWith (a b : GridBlock) : Bool :=
  linedUpOnAxis a.x a.sx b.x b.sx && linedUpOnAxis a.y a.sy b.y b.sy

/-- The rule for one block, given the blocks placed before it. -/
def placedByEye (before : List GridBlock) (b : GridBlock) : Bool :=
  if b.onGround then
    let ground := before.filter (·.onGround)
    ground.isEmpty || ground.any fun a => linedUpWith a b
  else
    before.any fun a => b.restsOn a && linedUpWith a b

/-- **The check**: every block, in build order, can be placed by eye. -/
def eyeballable (order : List GridBlock) : Bool :=
  (order.zipIdx).all fun (b, i) => placedByEye (order.take i) b

/-- All start positions along one axis at which a new block of length `bLen` lines up with
a block at `aLo` of length `aLen`. -/
def linedUpStarts (aLo aLen bLen : Int) : List Int :=
  ((aimPoints aLo aLen).flatMap fun p => [p, p - bLen / 2, p - bLen]).eraseDups

-- a block crossing another at its centre, at its quarter point, and at its end
#guard linedUpWith ⟨.flatX, 0, 0, 0⟩ ⟨.flatY, 24, 0, 4⟩      -- centre of the crossing block at 30
#guard linedUpWith ⟨.flatX, 0, 0, 0⟩ ⟨.flatY, 9, 0, 4⟩       -- its centre at the quarter point 15
#guard linedUpWith ⟨.flatX, 0, 0, 0⟩ ⟨.flatY, 48, 0, 4⟩      -- its right end at the right end 60
-- half a block along (running bond)
#guard linedUpWith ⟨.flatX, 0, 0, 0⟩ ⟨.flatX, 30, 0, 4⟩
-- 32 % along does not line up
#guard !linedUpWith ⟨.flatX, 0, 0, 0⟩ ⟨.flatX, 19, 0, 4⟩
-- a stack: the second block lines up with the first; floating blocks are not allowed
#guard eyeballable [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 30, 0, 4⟩]
#guard !eyeballable [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 19, 0, 4⟩]
-- two ground blocks end to end line up; at an odd gap they do not
#guard eyeballable [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 60, 0, 0⟩]
#guard !eyeballable [⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 67, 0, 0⟩]
-- every start from `linedUpStarts` lines up
#guard (linedUpStarts 0 60 12).all fun x => linedUpOnAxis 0 60 x 12

end KaplaPlanner
