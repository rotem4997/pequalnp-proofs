import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2732_427
    (h_symm : ∀ (F : (Fin 14 → Bool) → Bool) (C : Circuit),
      IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      2 ≤ C.size → C.size ≤ 26 → (∀ x, C.eval (List.ofFn x) = F x) →
      have x3 : ℕ → ℕ → ℕ → ℕ → ℕ := fun u v p q =>
        ((15 * min u v + max u v) * 225) + (15 * min p q + max p q);
      have x4 : Equiv.Perm (Fin 14) → Fin 15 → ℕ := fun σ i =>
        if ↑i < 14 then ↑(σ (Fin.ofNat 14 ↑i)) else 14;
      ∃ (a b : Fin 14) (c d : Fin 15) (op1 op2 : GateOp) (D : Circuit),
        a < b ∧ c < d ∧ (op1 = GateOp.and ∨ op1 = GateOp.or) ∧ (op2 = GateOp.and ∨ op2 = GateOp.or) ∧
        (∀ σ : Equiv.Perm (Fin 14), (∀ x, F (x ∘ ⇑σ) = F x) →
          x3 ↑a ↑b ↑c ↑d ≤ x3 ↑(σ a) ↑(σ b) (x4 σ c) (x4 σ d)) ∧
        Monotone2 D ∧ D.size ≤ 24 ∧
        ∀ x : Fin 14 → Bool,
          have w : List Bool := List.ofFn x ++ [op1.eval [x a, x b]];
          D.eval (w ++ [op2.eval [w.getD (↑c) false, w.getD (↑d) false]]) = F x)
    (h_synth :
      have edges : List (ℕ × ℕ) :=
        [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
         (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
         (6, 8), (6, 9), (6, 11)];
      ∃ C : Circuit, IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧ 2 ≤ C.size ∧ C.size ≤ 26 ∧
        ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
          decide (∃ u v : Fin 14, (↑u, ↑v) ∈ edges ∧ x u = true ∧ x v = true)) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true); have x3 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x3 x4 x5 x6 : ℕ) => ((15 : ℕ) * Min.min x3 x4 + Max.max x3 x4) * (225 : ℕ) + ((15 : ℕ) * Min.min x5 x6 + Max.max x5 x6); have x4 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x4 : Equiv.Perm (Fin (14 : ℕ))) (x5 : Fin (15 : ℕ)) => if ↑x5 < (14 : ℕ) then ↑(x4 (Fin.ofNat (14 : ℕ) ↑x5)) else (14 : ℕ); ∃ (x5 : Fin (14 : ℕ)) (x6 : Fin (14 : ℕ)) (x7 : Fin (15 : ℕ)) (x8 : Fin (15 : ℕ)) (x9 : PEqualNP.CircuitLowerBounds.GateOp) (x10 : PEqualNP.CircuitLowerBounds.GateOp) (x11 : PEqualNP.CircuitLowerBounds.Circuit),   x5 < x6 ∧     x7 < x8 ∧       (x9 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x9 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧         (x10 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧           (∀ (x12 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x13 : Fin (14 : ℕ) → Bool), x2 (x13 ∘ ⇑x12) = x2 x13) → x3 ↑x5 ↑x6 ↑x7 ↑x8 ≤ x3 (↑(x12 x5)) (↑(x12 x6)) (x4 x12 x7) (x4 x12 x8)) ∧             PEqualNP.MetaComplexity.Monotone2 x11 ∧               x11.size ≤ (24 : ℕ) ∧                 ∀ (x12 : Fin (14 : ℕ) → Bool),                   have x13 : List Bool := List.ofFn x12 ++ [x9.eval [x12 x5, x12 x6]];                   x11.eval (x13 ++ [x10.eval [x13.getD (↑x7) Bool.false, x13.getD (↑x8) Bool.false]]) = x2 x12 := by
  obtain ⟨C, hAO, hnd, h2, h26, hev⟩ := h_synth
  exact h_symm _ C hAO hnd h2 h26 hev
