import KaplaPhysics.Rules

/-! # Solid builds: the certificate and its checker (R1–R3)

To show a build is solid we must give balancing pushes for *every* combination of
placement errors. A certificate does that with one formula:

* each contact carries a fixed load `force`;
* the load acts at a point that moves with the errors: its `x` is
  `x + Σ m, mix[m] * (d m).1`, and its `y` is `y + Σ m, mix[m] * (d m).2`, where `d m` is
  the error of plank `m`.

Balance then holds for every error at once exactly when some plain equations between the
numbers of the certificate hold (`BalancedLoads`). The load point stays inside its contact
patch for every error when it is far enough from the patch's edges in the planned build
(`LoadInside`). Both are checked on concrete numbers. `Proofs.lean` shows that a passing
certificate makes the build solid.

The check is cautious: a solid build may lack such a certificate (then the engine says
"risky"), but a certificate is never accepted for a build that is not solid. -/

namespace KaplaPhysics

/-- One load of a solidity certificate: plank `upper` rests on `lower` and passes it
`force` plank weights, at a point that is `(x, y)` in the planned build and moves by the
weighted sum `mix` of the planks' errors. -/
structure Load where
  upper : Nat
  lower : Support
  force : Rat
  x : Rat
  y : Rat
  mix : Array Rat
  deriving Repr, DecidableEq

/-- The size of a number, ignoring its sign. -/
def size (q : Rat) : Rat := max q (-q)

/-- Weight of plank `m`'s error in the load point, minus that of plank `o`: how fast the
load point moves relative to plank `o` when plank `m` moves. -/
def Load.relMix (l : Load) (o m : Nat) : Rat := l.mix.getD m 0 - if m = o then 1 else 0

/-- The most the load point can move relative to plank `o`, per unit of error, when each
of `n` planks moves by at most 1. -/
def Load.drift (l : Load) (n o : Nat) : Rat :=
  ((List.range n).map fun m => size (l.relMix o m)).sum

/-- The load point stays inside plank `o`'s footprint for all errors of at most `ε`: in the
planned build it is at least `ε * drift` from each edge. -/
def Load.InsideOf (ε : Rat) (b : Build) (l : Load) (o : Nat) : Prop :=
  let p := b.get o
  let m := ε * l.drift b.length o
  p.x + m ≤ l.x ∧ l.x + m ≤ p.x1 ∧ p.y + m ≤ l.y ∧ l.y + m ≤ p.y1

instance (ε : Rat) (b : Build) (l : Load) (o : Nat) : Decidable (l.InsideOf ε b o) := by
  unfold Load.InsideOf; infer_instance

/-- A rectangle with `e` cut off each side. -/
def Rect.shrink (r : Rect) (e : Rat) : Rect := ⟨r.x0 + e, r.x1 - e, r.y0 + e, r.y1 - e⟩

/-- The load is a valid contact for every error of at most `ε`:
1. it pushes, never pulls;
2. it is between planks of the build;
3. `upper`'s bottom is at the height of `lower`'s top (heights do not change, R2);
4. for a plank below: the planned patch, cut by `ε` on each side, still has an area
   (so the real patch always does);
5. the load point stays inside `upper`'s footprint, and inside `lower`'s if it is a plank. -/
def Load.Valid (ε : Rat) (b : Build) (l : Load) : Prop :=
  0 ≤ l.force ∧ l.upper < b.length ∧ l.lower.InBuild b.length ∧ l.InsideOf ε b l.upper ∧
    match l.lower with
    | .ground => (b.get l.upper).z = 0
    | .plank j => (b.get l.upper).z = (b.get j).top ∧
        (((b.get l.upper).footprint.inter (b.get j).footprint).shrink ε).HasArea ∧
        l.InsideOf ε b j

instance (ε : Rat) (b : Build) (l : Load) : Decidable (l.Valid ε b) := by
  unfold Load.Valid; cases l.lower <;> infer_instance

/-- How much load `l` lifts plank `i`: `+force` if `i` is the upper plank, `-force` if it is
the lower plank. -/
def Load.upOn (i : Nat) (l : Load) : Rat :=
  (if l.upper = i then l.force else 0) - (if l.lower = .plank i then l.force else 0)

/-- Load `l` touches plank `i`: `i` is its upper or its lower plank. -/
def Load.Touches (i : Nat) (l : Load) : Bool := l.upper == i || l.lower == .plank i

/-- The loads `near` balance plank `i` for every error (S1 with errors):
1. the net load up is its weight, 1;
2. the net turning effect, measured from the origin, equals that of its weight at its
   planned centre;
3. for each plank `m`, the load points move with `m`'s error exactly as plank `i`'s centre
   does: fully if `m = i`, not at all otherwise. -/
def BalancedNear (b : Build) (near : List Load) (i : Nat) : Prop :=
  (near.map fun l => l.upOn i).sum = 1 ∧
  (near.map fun l => l.upOn i * l.x).sum = (b.get i).centerX ∧
  (near.map fun l => l.upOn i * l.y).sum = (b.get i).centerY ∧
  ∀ m < b.length, (near.map fun l => l.upOn i * l.mix.getD m 0).sum = if m = i then 1 else 0

instance (b : Build) (near : List Load) (i : Nat) : Decidable (BalancedNear b near i) := by
  unfold BalancedNear; infer_instance

/-- The loads balance plank `i` for every error. Only loads that touch plank `i` matter,
so only those are summed. -/
def BalancedLoads (b : Build) (ls : List Load) (i : Nat) : Prop :=
  BalancedNear b (ls.filter (Load.Touches i)) i

instance (b : Build) (ls : List Load) (i : Nat) : Decidable (BalancedLoads b ls i) := by
  unfold BalancedLoads; infer_instance

/-- A certificate that the build is solid for errors of at most `ε`. -/
def SolidCertificate (ε : Rat) (b : Build) (ls : List Load) : Prop :=
  (∀ l ∈ ls, l.Valid ε b) ∧ ∀ i < b.length, BalancedLoads b ls i

instance (ε : Rat) (b : Build) (ls : List Load) : Decidable (SolidCertificate ε b ls) := by
  unfold SolidCertificate; infer_instance

end KaplaPhysics
