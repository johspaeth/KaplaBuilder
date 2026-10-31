import KaplaCore.Interfaces

/-!
# KaplaCore.Mocks

Unverified stand-ins so every component can be developed against the contract alone
(WORKSPLIT §5). None of these is ever used by `kapla build` unless `--mock` is given.
-/

namespace Kapla.Mocks

/-- Simple centre-of-mass rule: every block's centre must be above the footprint of the
ground or of some block whose top touches its bottom. Unverified. -/
def physics : PhysicsEngine where
  name := "mock"
  check _ N plan := Id.run do
    let bs := plan.blocks
    let mut diags : List Diagnostic := []
    if bs.length > N then diags := diags ++ [.tooManyBlocks bs.length N]
    for h : i in [0:bs.length] do
      let b := bs[i]
      let onGround := b.bottomZ = 0
      let supported := (bs.take i).any fun a => a.topZ = b.bottomZ && decide (a.InFootprint b.center)
      unless onGround || supported do
        diags := diags ++ [.unstable i i]
    return { ok := diags.isEmpty, diagnostics := diags, engine := "mock" }

private def bboxOfPoses (bs : List Pose) : Q3 × Q3 :=
  let pts := bs.flatMap Pose.corners
  match pts with
  | [] => (Q3.zero, Q3.zero)
  | p :: ps => ps.foldl (fun (lo, hi) q =>
      (⟨min lo.x q.x, min lo.y q.y, min lo.z q.z⟩, ⟨max hi.x q.x, max hi.y q.y, max hi.z q.z⟩)) (p, p)

private def boxVol (b : Q3 × Q3) : Q :=
  max 0 (b.2.x - b.1.x) * max 0 (b.2.y - b.1.y) * max 0 (b.2.z - b.1.z)

/-- Returns a fixed tower target; scores by bounding-box IoU. Unverified. -/
def semantics : SemanticEngine where
  name := "mock"
  interpret r := pure { name := r.prompt, shape := .tag "tower" (.box 120 120 300) }
  score t bs :=
    let a := t.shape.bbox
    let b := bboxOfPoses bs
    let inter : Q3 × Q3 := (⟨max a.1.x b.1.x, max a.1.y b.1.y, max a.1.z b.1.z⟩,
                            ⟨min a.2.x b.2.x, min a.2.y b.2.y, min a.2.z b.2.z⟩)
    let i := boxVol inter
    let u := boxVol a + boxVol b - i
    let iou := if u = 0 then 0 else i / u
    { score := iou, iou := iou }
  bound _ _ := { maxScore := 1, verdict := .good }

/-- A straight stack of flat blocks, rotated a quarter turn every layer. -/
def stack (n : Nat) : BuildPlan :=
  BuildPlan.ofBlocks <| (List.range n).map fun k =>
    { up := .flat, rot := if k % 2 = 0 then Rot.id else Rot.quarter,
      center := ⟨0, 0, Block.T / 2 + k * Block.T⟩ }

def planner : Planner where
  name := "mock"
  plan req ph se := do
    let p := stack (min req.blocks 10)
    let sc := se.score req.target p.blocks
    return [{ plan := p, motif := "mock-stack", target := req.target, score := sc,
              physics := ph.check req.human req.blocks p }]

def renderer : Renderer where
  name := "mock"
  render i := s!"<html><body>{i.candidate.plan.blockCount} blocks</body></html>"

end Kapla.Mocks
