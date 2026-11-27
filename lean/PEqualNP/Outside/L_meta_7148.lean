import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7148 : have x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (16 : ℕ), x1 % (16 : ℕ))) [(9 : ℕ), (10 : ℕ), (20 : ℕ), (24 : ℕ), (37 : ℕ), (42 : ℕ), (54 : ℕ), (55 : ℕ), (72 : ℕ), (74 : ℕ), (88 : ℕ), (89 : ℕ), (103 : ℕ), (106 : ℕ), (121 : ℕ), (137 : ℕ)]); ∀ (x2 : Finset (Fin (11 : ℕ))), x2.card = (4 : ℕ) → (∀ x4 ∈ x2, ∀ x6 ∈ x2, ¬x1.Adj x4 x6) → ∃ (x5 : Fin (22 : ℕ)), ∀ (x6 : Fin (11 : ℕ)), (Nat.ofDigits (2048 : ℕ) [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1546 : ℕ)] >>> ((11 : ℕ) * ↑x5)).testBit ↑x6 = Bool.true ↔ x6 ∈ x2 := by
  dsimp only
  set_option synthInstance.maxSize 100000 in
  set_option synthInstance.maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  decide +kernel
