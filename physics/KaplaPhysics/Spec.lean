import KaplaCore

/-!
# KaplaPhysics.Spec — the trusted specification (M1)

**This file is part of the trusted base.** Everything else in `KaplaPhysics` is either
proven against it or untrusted.

Physical model (DESIGN §3), v1:
* blocks are rigid, uniform cuboids of weight 1 with yaw-only rotations, so every contact
  between them is horizontal;
* a contact transmits only *compressive vertical point forces* (`mag ≥ 0`) at points that lie
  on both touching faces (or on the ground `z = 0`). With horizontal contacts and gravity
  only, no friction is needed;
* by Heyman's safe theorem a structure stands if such forces exist that put every block in
  force and moment equilibrium (`Equilibrium`).

Any distribution of contact pressure over a convex contact patch is a limit of point
forces at its points, so restricting to finitely many point forces loses nothing.
-/

namespace Kapla.Physics

open Kapla

/-- A vertical compressive force between the bottom face of `upper` and the top face of
`lower` (or the ground when `lower = none`), acting at `pt`. -/
structure PointForce where
  lower : Option Nat
  upper : Nat
  pt : Q3
  mag : Q
  deriving DecidableEq, Repr, Inhabited, Lean.ToJson, Lean.FromJson

/-- An extra downward load (e.g. the builder's press, M2). -/
structure Load where
  block : Nat
  pt : Q3
  mag : Q
  deriving DecidableEq, Repr, Inhabited, Lean.ToJson, Lean.FromJson

/-- Block `i` of a list (a dummy block when out of range; every use is guarded by a range
condition). -/
def blk (bs : List Pose) (i : Nat) : Pose := bs.getD i default

def _root_.Kapla.Pose.OnTop (b : Pose) (p : Q3) : Prop := p.z = b.topZ ∧ b.InFootprint p
def _root_.Kapla.Pose.OnBottom (b : Pose) (p : Q3) : Prop := p.z = b.bottomZ ∧ b.InFootprint p

instance (b : Pose) (p : Q3) : Decidable (Pose.OnTop b p) := by unfold Pose.OnTop; infer_instance
instance (b : Pose) (p : Q3) : Decidable (Pose.OnBottom b p) := by
  unfold Pose.OnBottom; infer_instance

/-- The lower side of a force really touches the force point. -/
def LowerOK (bs : List Pose) (f : PointForce) : Prop :=
  match f.lower with
  | none => f.pt.z = 0
  | some i => i < bs.length ∧ (blk bs i).OnTop f.pt

instance (bs : List Pose) (f : PointForce) : Decidable (LowerOK bs f) := by
  unfold LowerOK; split <;> infer_instance

/-- An admissible contact force: compressive, and its point lies on both touching faces. -/
def ForceOK (bs : List Pose) (f : PointForce) : Prop :=
  0 ≤ f.mag ∧ f.upper < bs.length ∧ (blk bs f.upper).OnBottom f.pt ∧ LowerOK bs f

instance (bs : List Pose) (f : PointForce) : Decidable (ForceOK bs f) := by
  unfold ForceOK; infer_instance

/-- `+1` if the force pushes block `k` up, `-1` if it pushes it down. -/
def sgn (k : Nat) (f : PointForce) : Q :=
  (if f.upper = k then 1 else 0) - (if f.lower = some k then 1 else 0)

def loadOn (k : Nat) (l : Load) : Q := if l.block = k then l.mag else 0

/-- Net vertical force on block `k` (weight 1 at its centre). -/
def netFz (fs : List PointForce) (loads : List Load) (k : Nat) : Q :=
  (fs.map fun f => sgn k f * f.mag).sum - (loads.map (loadOn k)).sum - Block.weight

/-- Net moment about the centre `c` of block `k`, `x` and `y` lever arms. (The weight acts
at the centre and contributes no moment.) -/
def netMx (c : Q3) (fs : List PointForce) (loads : List Load) (k : Nat) : Q :=
  (fs.map fun f => sgn k f * f.mag * (f.pt.x - c.x)).sum
    - (loads.map fun l => loadOn k l * (l.pt.x - c.x)).sum

def netMy (c : Q3) (fs : List PointForce) (loads : List Load) (k : Nat) : Q :=
  (fs.map fun f => sgn k f * f.mag * (f.pt.y - c.y)).sum
    - (loads.map fun l => loadOn k l * (l.pt.y - c.y)).sum

/-- Block `k` is in equilibrium under the forces `fs` and loads. -/
def Balanced (bs : List Pose) (fs : List PointForce) (loads : List Load) (k : Nat) : Prop :=
  netFz fs loads k = 0 ∧ netMx (blk bs k).center fs loads k = 0
    ∧ netMy (blk bs k).center fs loads k = 0

instance (bs fs loads k) : Decidable (Balanced bs fs loads k) := by
  unfold Balanced; infer_instance

/-- A force certificate: admissible forces balancing every block. -/
def ForcesOK (bs : List Pose) (loads : List Load) (fs : List PointForce) : Prop :=
  (∀ f ∈ fs, ForceOK bs f) ∧ ∀ k, k < bs.length → Balanced bs fs loads k

instance (bs loads fs) : Decidable (ForcesOK bs loads fs) := by unfold ForcesOK; infer_instance

/-- **Stability** (Heyman): admissible contact forces exist that put every block in
equilibrium. -/
def Equilibrium (bs : List Pose) (loads : List Load) : Prop :=
  ∃ fs, ForcesOK bs loads fs

/-- No block reaches below the ground. -/
def AboveGround (bs : List Pose) : Prop := ∀ b ∈ bs, 0 ≤ b.bottomZ

/-- No two blocks share an interior point. -/
def NonOverlap (bs : List Pose) : Prop :=
  ∀ i j, i < bs.length → j < bs.length → i ≠ j →
    ∀ p, ¬ ((blk bs i).Interior p ∧ (blk bs j).Interior p)

/-! ## Human model rules (M2) -/

/-- The builder's press while placing (H4): `H.press` block weights pushing down at `p` on
block `i`. -/
def pressLoad (H : HumanModel) (i : Nat) (p : Q3) : Load := { block := i, pt := p, mag := H.press }

/-- Indices (in build order) of the blocks placed in step `k`. -/
def newIndices (plan : BuildPlan) (k : Nat) : List Nat :=
  List.range' (plan.prefixBlocks k).length (plan.steps.getD k default).blocks.length

/-- **H4.** After step `k` the structure also stands while the builder presses any point of
the top face of any block just placed. -/
def PressOK (H : HumanModel) (plan : BuildPlan) (k : Nat) : Prop :=
  ∀ i ∈ newIndices plan k, ∀ p, (blk (plan.prefixBlocks (k + 1)) i).OnTop p →
    Equilibrium (plan.prefixBlocks (k + 1)) [pressLoad H i p]

/-- Interior of the block grown by `g` on every face. -/
def _root_.Kapla.Pose.InteriorGrown (b : Pose) (g : Q) (p : Q3) : Prop :=
  ∀ k : Fin 3, |b.loc k p| < b.halfAlong k + g

/-- The two blocks share a point (they touch by design). -/
def Touch (a b : Pose) : Prop := ∃ p, a.Mem p ∧ b.Mem p

/-- **H6.** Two blocks either touch, or the blocks grown by `c/2` do not intersect. A block
grown by `c/2` on every face contains all points within distance `c/2` of it, so in the
second case every point of one block is at least `c` away from every point of the other:
no slot is "almost" wide enough. -/
def ClearPair (c : Q) (a b : Pose) : Prop :=
  Touch a b ∨ ∀ p, ¬ (a.InteriorGrown (c / 2) p ∧ b.InteriorGrown (c / 2) p)

def Clearance (H : HumanModel) (bs : List Pose) : Prop :=
  ∀ i j, i < bs.length → j < bs.length → i ≠ j → ClearPair H.clear (blk bs i) (blk bs j)

/-! ## Placement error (H1, H2) — translations -/

/-- Max-norm of a horizontal vector. -/
def ninf (v : Q2) : Q := max |v.x| |v.y|

def Q2.sub (a b : Q2) : Q2 := ⟨a.x - b.x, a.y - b.y⟩

/-- Block moved horizontally by `v`. -/
def _root_.Kapla.Pose.shift (b : Pose) (v : Q2) : Pose :=
  { b with center := ⟨b.center.x + v.x, b.center.y + v.y, b.center.z⟩ }

def shiftPt (p : Q3) (v : Q2) : Q3 := ⟨p.x + v.x, p.y + v.y, p.z⟩

/-- The structure as actually built: block `j` misplaced by `t j`. -/
def perturb (bs : List Pose) (t : Nat → Q2) : List Pose := bs.mapIdx fun j b => b.shift (t j)

/-- **The placement-error model** (DESIGN §2.2, translation part). Each block lands within
`eAbs` of its planned position (the builder corrects anything larger by eye), and within
`epsRel` of its planned position *relative to the block it is lined up with* (`refOf`). -/
def Admissible (H : HumanModel) (plan : BuildPlan) (n : Nat) (t : Nat → Q2) : Prop :=
  (∀ j, j < n → ninf (t j) ≤ H.eAbs) ∧
  (∀ j, j < n → ∀ i, plan.refOf j = some i → ninf (Q2.sub (t j) (t i)) ≤ H.epsRel)

/-- Alignment references point to blocks placed earlier. -/
def RefsOK (plan : BuildPlan) : Prop :=
  ∀ j, j < plan.blockCount → ∀ i, plan.refOf j = some i → i < j

/-- **H1/H2.** After step `k`, *every* admissible misplacement of the blocks still stands —
also while the builder presses on the blocks just placed. -/
def RobustOK (H : HumanModel) (plan : BuildPlan) (k : Nat) : Prop :=
  let pre := plan.prefixBlocks (k + 1)
  ∀ t, Admissible H plan pre.length t →
    Equilibrium (perturb pre t) [] ∧
    ∀ i ∈ newIndices plan k, ∀ p, (blk pre i).OnTop p →
      Equilibrium (perturb pre t) [pressLoad H i (shiftPt p (t i))]

/-- **Validity of a blueprint.**

* at most `N` blocks;
* every step places between 1 and `H.hands` blocks (H7);
* nothing below the ground, no interpenetration;
* the structure is in equilibrium **after every step** (H3);
* … and while the builder presses on the blocks just placed (H4);
* no near-miss gaps narrower than `H.clear` (H6).

Robustness under placement error (H1, H2) is the separate, stronger `Robust` below: a plan
that has it is reported as robust, one that does not is reported as nominal only. Rotation
errors, hand access (H5), parallel supports (H8) and friction for tilted
blocks (H9) are still to come; until then a report never claims them (`Guarantees`). -/
def Valid (H : HumanModel) (N : Nat) (plan : BuildPlan) : Prop :=
  plan.blockCount ≤ N ∧
  (∀ s ∈ plan.steps, 1 ≤ s.blocks.length ∧ s.blocks.length ≤ H.hands) ∧
  AboveGround plan.blocks ∧
  NonOverlap plan.blocks ∧
  Clearance H plan.blocks ∧
  (∀ k, k < plan.steps.length → Equilibrium (plan.prefixBlocks (k + 1)) []) ∧
  (∀ k, k < plan.steps.length → PressOK H plan k)

/-- **H1/H2 (translations).** Every step, with and without the press, survives every
admissible misplacement of the blocks. -/
def Robust (H : HumanModel) (plan : BuildPlan) : Prop :=
  RefsOK plan ∧ ∀ k, k < plan.steps.length → RobustOK H plan k

end Kapla.Physics
