import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7549 : have x1 : List ℕ := [(8796160139265 : ℕ), (2251799889182721 : ℕ), (215506917523485 : ℕ), (1548117546631239 : ℕ), (1477749337260115 : ℕ), (1267743973179493 : ℕ), (439814119817351 : ℕ), (423325471899843 : ℕ), (1442578117984531 : ℕ), (1408496491315497 : ℕ), (1200703561302353 : ℕ)]; have x2 : Fin (286 : ℕ) → List Bool := fun (x2 : Fin (286 : ℕ)) => List.ofFn fun (x3 : Fin (26 : ℕ)) => (x1.getD (↑x2 / (26 : ℕ)) (0 : ℕ) / (2 : ℕ) ^ ((26 : ℕ) * (↑x2 / (13 : ℕ) % (2 : ℕ)))).testBit ((13 : ℕ) * (↑x3 / (13 : ℕ)) + (↑x3 % (13 : ℕ) + (13 : ℕ) - ↑x2 % (13 : ℕ)) % (13 : ℕ)); have x3 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x4 : Fin (286 : ℕ)),   have x5 : List Bool := x2 x4;   if ↑x4 < (52 : ℕ) then ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), x6 - x7 ∈ x3 ∧ x5 = (List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x7)   else     have x6 : Finset (Fin (13 : ℕ)) := {x6 : Fin (13 : ℕ) | x5.getD (↑x6) Bool.false = Bool.true};     x6.card = (4 : ℕ) ∧ (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x6 | x8 - x7 ∈ x3}.card ≤ (2 : ℕ)) ∧ x5 = (List.ofFn fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x7 ∈ x6)) ++ List.ofFn fun (x7 : Fin (13 : ℕ)) => Decidable.decide (∀ x8 ∈ x6, x8 - x7 ∉ x3) := by
  set_option maxRecDepth 100000 in
  first
  | omega
  | (intros; omega)
  | decide
  | (intros; simp_all)
  | (intros; simp_all; omega)
  | (intros; nlinarith)
  | (intros; positivity)
  | (intros; aesop)
