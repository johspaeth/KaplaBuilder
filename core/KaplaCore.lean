import KaplaCore.Basic
import KaplaCore.Proofs
import KaplaCore.Num
import KaplaCore.Geometry
import KaplaCore.Types
import KaplaCore.ShapeMem
import KaplaCore.Interfaces
import KaplaCore.Mocks

/-! # KaplaCore: the shared contract (see docs/WORKSPLIT.md §3)

Every other component imports only this library. Changes here need review by all four.
`Basic`/`Proofs` are the scaffold example checked by `lake comparator`; the contract v0.1
(namespace `Kapla`) is `Num`, `Geometry`, `Types`, `ShapeMem`, `Interfaces`, `Mocks`.
-/
