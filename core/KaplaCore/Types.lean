import KaplaCore.Geometry

/-!
# KaplaCore.Types — the data contract (v0.1)

Plain data only: no proof-carrying types cross component boundaries (WORKSPLIT §3).
Every type has a JSON codec; JSON is the format of fixtures, webpage data and Claude output.
-/

namespace Kapla

open Lean

/-! ## Build plans -/

/-- Where the fingers hold the block (DESIGN §2.4). -/
inductive Grip where
  | longSides | shortEnds | topEnd
  deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

/-- How the block reaches its place: lowered from above or slid in horizontally. -/
inductive Approach where
  | fromAbove | slideXPos | slideXNeg | slideYPos | slideYNeg
  deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

/-- One build step: 1 to `hands` blocks placed together. `refs[t]` names the (earlier)
block the builder lines block `t` up with; `none` = measured from the plan's origin. -/
structure Step where
  blocks : List Pose
  grip : Grip := .longSides
  approach : Approach := .fromAbove
  phase : String := ""
  refs : List (Option Nat) := []
  deriving DecidableEq, Repr, Inhabited, ToJson

/-- Lenient decoder: every field except `blocks` may be omitted. -/
instance : FromJson Step where
  fromJson? j := do
    let blocks ← j.getObjValAs? (List Pose) "blocks"
    let opt {α} [FromJson α] (k : String) (d : α) : Except String α :=
      match j.getObjVal? k with
      | .ok .null | .error _ => pure d
      | .ok v => fromJson? v
    return { blocks, grip := ← opt "grip" .longSides, approach := ← opt "approach" .fromAbove,
             phase := ← opt "phase" "", refs := ← opt "refs" [] }

/-- A blueprint: the ordered list of build steps. -/
structure BuildPlan where
  steps : List Step
  deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

namespace BuildPlan
/-- All blocks in build order. -/
def blocks (p : BuildPlan) : List Pose := (p.steps.map (·.blocks)).flatten
def blockCount (p : BuildPlan) : Nat := p.blocks.length
/-- Alignment reference of every block, in build order. -/
def refs (p : BuildPlan) : List (Option Nat) :=
  (p.steps.map fun s => (List.range s.blocks.length).map fun t => s.refs.getD t none).flatten
def refOf (p : BuildPlan) (j : Nat) : Option Nat := p.refs.getD j none
/-- The blocks standing after the first `k` steps. -/
def prefixBlocks (p : BuildPlan) (k : Nat) : List Pose := ((p.steps.take k).map (·.blocks)).flatten
/-- One block per step, in the given order. -/
def ofBlocks (bs : List Pose) (phase : String := "") : BuildPlan :=
  ⟨bs.map fun b => { blocks := [b], phase }⟩
end BuildPlan

/-! ## Human model (DESIGN §2.1) -/

structure GripModel where
  /-- Finger pad width and height, mm. -/
  padW : Q := 18
  padH : Q := 20
  deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

structure HumanModel where
  /-- mm: max error of any corner of a block relative to the block(s) it rests on. -/
  epsRel : Q
  /-- mm: max absolute drift from the plan. -/
  eAbs : Q
  /-- max angular error of a leaning block (rational tangent). -/
  thetaTilt : Q
  /-- downward press while placing, in block weights. -/
  press : Q
  /-- max blocks placed in one step. -/
  hands : Nat
  /-- mm: min gap between blocks that do not touch by design. -/
  clear : Q
  /-- friction coefficient assumed. -/
  muSafe : Q
  grip : GripModel := {}
  deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

namespace HumanModel
def child : HumanModel :=
  { epsRel := 5, eAbs := 15, thetaTilt := 1/20, press := 1, hands := 1, clear := 4, muSafe := 1/4 }
def adult : HumanModel :=
  { epsRel := 3, eAbs := 10, thetaTilt := 1/30, press := 1/2, hands := 2, clear := 3, muSafe := 3/10 }
def expert : HumanModel :=
  { epsRel := 3/2, eAbs := 5, thetaTilt := 1/50, press := 3/10, hands := 2, clear := 2, muSafe := 7/20 }
def profile? : String → Option HumanModel
  | "child" => some child
  | "adult" => some adult
  | "expert" => some expert
  | _ => none
end HumanModel

/-! ## Target shapes (DESIGN §5) -/

/-- The Shape DSL. Primitives stand on `z = 0`, centred on the `z` axis. Units are
arbitrary; the planner chooses the scale. -/
inductive Shape where
  | box (sx sy sz : Q)
  | cylinder (r h : Q)
  | cone (r h : Q)
  | pyramid (sx sy h : Q)
  /-- Gable prism: footprint `sx × sy`, ridge along `x` at height `h`. -/
  | wedge (sx sy h : Q)
  | union (parts : List Shape)
  | diff (a b : Shape)
  | translate (v : Q3) (s : Shape)
  | scale (k : Q) (s : Shape)
  /-- Semantic label: `tower`, `wall`, `roof:gable`, `roof:cone`, `roof:hip`, `trunk`, … -/
  | tag (t : String) (s : Shape)
  deriving Repr, Inhabited

namespace Shape

partial def toJson' : Shape → Json
  | .box x y z => Json.mkObj [("type", "box"), ("size", toJson [x, y, z])]
  | .cylinder r h => Json.mkObj [("type", "cylinder"), ("r", toJson r), ("h", toJson h)]
  | .cone r h => Json.mkObj [("type", "cone"), ("r", toJson r), ("h", toJson h)]
  | .pyramid x y h => Json.mkObj [("type", "pyramid"), ("size", toJson [x, y]), ("h", toJson h)]
  | .wedge x y h => Json.mkObj [("type", "wedge"), ("size", toJson [x, y]), ("h", toJson h)]
  | .union ps => Json.mkObj [("type", "union"), ("of", Json.arr (ps.map toJson').toArray)]
  | .diff a b => Json.mkObj [("type", "diff"), ("a", toJson' a), ("b", toJson' b)]
  | .translate v s => Json.mkObj [("type", "translate"), ("by", toJson v), ("shape", toJson' s)]
  | .scale k s => Json.mkObj [("type", "scale"), ("by", toJson k), ("shape", toJson' s)]
  | .tag t s => Json.mkObj [("type", "tag"), ("tag", toJson t), ("shape", toJson' s)]

private def getList (j : Json) (k : String) (n : Nat) : Except String (List Q) := do
  let xs ← j.getObjValAs? (List Q) k
  if xs.length ≠ n then throw s!"'{k}' needs {n} numbers"
  return xs

partial def fromJson' (j : Json) : Except String Shape := do
  let ty ← j.getObjValAs? String "type"
  match ty with
  | "box" => let v ← getList j "size" 3; return .box v[0]! v[1]! v[2]!
  | "cylinder" => return .cylinder (← j.getObjValAs? Q "r") (← j.getObjValAs? Q "h")
  | "cone" => return .cone (← j.getObjValAs? Q "r") (← j.getObjValAs? Q "h")
  | "pyramid" => let v ← getList j "size" 2; return .pyramid v[0]! v[1]! (← j.getObjValAs? Q "h")
  | "wedge" => let v ← getList j "size" 2; return .wedge v[0]! v[1]! (← j.getObjValAs? Q "h")
  | "union" =>
    let ps ← j.getObjValAs? (Array Json) "of"
    return .union (← ps.toList.mapM fromJson')
  | "diff" => return .diff (← fromJson' (← j.getObjVal? "a")) (← fromJson' (← j.getObjVal? "b"))
  | "translate" => return .translate (← j.getObjValAs? Q3 "by") (← fromJson' (← j.getObjVal? "shape"))
  | "scale" => return .scale (← j.getObjValAs? Q "by") (← fromJson' (← j.getObjVal? "shape"))
  | "tag" => return .tag (← j.getObjValAs? String "tag") (← fromJson' (← j.getObjVal? "shape"))
  | t => throw s!"unknown shape type '{t}'"

instance : ToJson Shape := ⟨toJson'⟩
instance : FromJson Shape := ⟨fromJson'⟩

/-- Axis-aligned bounding box `(lo, hi)`. Conservative for `diff`. -/
partial def bbox : Shape → Q3 × Q3
  | .box x y z => (⟨-x/2, -y/2, 0⟩, ⟨x/2, y/2, z⟩)
  | .cylinder r h | .cone r h => (⟨-r, -r, 0⟩, ⟨r, r, h⟩)
  | .pyramid x y h | .wedge x y h => (⟨-x/2, -y/2, 0⟩, ⟨x/2, y/2, h⟩)
  | .union [] => (Q3.zero, Q3.zero)
  | .union (p :: ps) => ps.foldl (fun (lo, hi) q =>
      let (l, h) := bbox q
      (⟨min lo.x l.x, min lo.y l.y, min lo.z l.z⟩, ⟨max hi.x h.x, max hi.y h.y, max hi.z h.z⟩))
      (bbox p)
  | .diff a _ => bbox a
  | .translate v s => let (l, h) := bbox s; (l + v, h + v)
  | .scale k s => let (l, h) := bbox s; (k * l, k * h)
  | .tag _ s => bbox s

/-- All semantic tags in the shape. -/
partial def tags : Shape → List String
  | .union ps => ps.flatMap tags
  | .diff a b => tags a ++ tags b
  | .translate _ s | .scale _ s => tags s
  | .tag t s => t :: tags s
  | _ => []

end Shape

/-- A binary silhouette mask (front view, `x` right, `z` up; row 0 is the top). -/
structure Mask where
  width : Nat
  height : Nat
  /-- `height` strings of `width` characters; `#` = filled. -/
  rows : List String
  deriving Repr, Inhabited, ToJson, FromJson

/-- What we want to build. -/
structure TargetSpec where
  name : String
  shape : Shape
  silhouette : Option Mask := none
  /-- Suggested real size: mm per shape unit. The planner searches scales around it. -/
  unitMM : Q := 1
  deriving Repr, Inhabited, ToJson, FromJson

def TargetSpec.parts (t : TargetSpec) : List String := t.shape.tags.eraseDups

/-! ## Reports -/

/-- Why the physics engine rejects a plan. Indices are 0-based; `step` is the step after
which the problem appears, `block` an index into `BuildPlan.blocks`. -/
inductive Diagnostic where
  | unstable (step block : Nat)
  | slides (step contact : Nat)
  | pressTips (step corner : Nat)
  | unreachable (step : Nat)
  | overlap (i j : Nat)
  | clearance (i j : Nat)
  | unevenSupports (block : Nat)
  | tooManyHands (step : Nat)
  | emptyStep (step : Nat)
  | belowGround (block : Nat)
  | tooManyBlocks (count limit : Nat)
  | unsupported (what : String)
  deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

def Diagnostic.describe : Diagnostic → String
  | .unstable s b => s!"step {s+1}: block {b+1} is not in equilibrium"
  | .slides s c => s!"step {s+1}: contact {c} would slide"
  | .pressTips s c => s!"step {s+1}: pressing corner {c} of the new block tips the structure"
  | .unreachable s => s!"step {s+1}: block cannot be reached by hand"
  | .overlap i j => s!"blocks {i+1} and {j+1} overlap"
  | .clearance i j => s!"gap between blocks {i+1} and {j+1} is too tight"
  | .unevenSupports b => s!"block {b+1} rests on supports built differently"
  | .tooManyHands s => s!"step {s+1} places more blocks than the builder has hands"
  | .emptyStep s => s!"step {s+1} places no block"
  | .belowGround b => s!"block {b+1} goes below the ground"
  | .tooManyBlocks c l => s!"plan uses {c} blocks but only {l} are available"
  | .unsupported w => s!"not supported yet: {w}"

/-- Which rules of `Valid` the engine actually established (so the page never overclaims). -/
structure Guarantees where
  equilibriumEveryStep : Bool := false
  nonOverlap : Bool := false
  handsPerStep : Bool := false
  robust : Bool := false
  press : Bool := false
  reachable : Bool := false
  clearance : Bool := false
  parallelSupports : Bool := false
  deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

structure PhysicsReport where
  ok : Bool
  diagnostics : List Diagnostic := []
  /-- Engine name, e.g. `"verified-m1"` or `"mock"`. -/
  engine : String := ""
  /-- `true` only when `ok` comes from a checker with a soundness proof. -/
  verified : Bool := false
  guarantees : Guarantees := {}
  /-- Smallest support margin per block (mm), when known. -/
  slackPerBlock : Option (List Q) := none
  deriving Repr, Inhabited, ToJson, FromJson

inductive Verdict where
  | good | coarse | abstract | symbolic
  deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

/-- Verdict bands (DESIGN §5). -/
def Verdict.ofScore (s : Q) : Verdict :=
  if s ≥ 7/10 then .good else if s ≥ 2/5 then .coarse else if s ≥ 3/20 then .abstract
  else .symbolic

def Verdict.describe : Verdict → String
  | .good => "good likeness"
  | .coarse => "coarse likeness"
  | .abstract => "abstract"
  | .symbolic => "symbolic only"

structure PartScore where
  tag : String
  iou : Q
  deriving Repr, Inhabited, ToJson, FromJson

structure ScoreReport where
  score : Q
  iou : Q
  silhouetteIoU : Option Q := none
  perPart : List PartScore := []
  /-- Voxels of the target not covered / voxels covered outside the target. -/
  missing : Nat := 0
  extra : Nat := 0
  targetVoxels : Nat := 0
  /-- mm per shape unit used for this score. -/
  scale : Q := 1
  deriving Repr, Inhabited, ToJson, FromJson

structure Bound where
  /-- Proven ceiling on the score reachable with `N` blocks. -/
  maxScore : Q
  verdict : Verdict
  deriving Repr, Inhabited, ToJson, FromJson

/-! ## Requests and results -/

structure Request where
  prompt : String
  image : Option String := none
  blocks : Nat
  profile : String := "adult"
  deriving Repr, Inhabited, ToJson, FromJson

structure PlanRequest where
  target : TargetSpec
  blocks : Nat
  human : HumanModel
  bound : Bound
  deriving Repr, Inhabited, ToJson, FromJson

inductive Difficulty where
  | easy | medium | expert
  deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

structure Candidate where
  plan : BuildPlan
  motif : String
  /-- The target as scaled for this candidate (mm). -/
  target : TargetSpec
  score : ScoreReport
  physics : PhysicsReport
  difficulty : Difficulty := .easy
  deriving Repr, Inhabited, ToJson, FromJson

structure RenderInput where
  request : Request
  human : HumanModel
  bound : Bound
  candidate : Candidate
  /-- Axioms used by the soundness theorem, from `#print axioms` (for the badge). -/
  axioms : List String := []
  deriving Repr, Inhabited, ToJson, FromJson

end Kapla
