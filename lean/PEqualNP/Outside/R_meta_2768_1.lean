import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2768_1
    (hSize : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →
      15 ≤ C.size)
    (hClean : ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C →
      (∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) →
      (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) →
      ∀ j g, C.gates[j]? = some g → (∀ i ∈ g.inputs, i < n + j) ∧ g.inputs.Nodup ∧
        (g.op = GateOp.not → g.inputs.length = 1) ∧ (g.op ≠ GateOp.not → g.inputs.length = 2))
    (hResidual : ∀ C : Circuit,
      (C.gates.length = 15 ∧ C.output = 23 ∧
        C.gates[0]? = some ⟨GateOp.or, [0, 3]⟩ ∧
        ∀ (j : ℕ) (hj : j < C.gates.length),
          (∃ a : ℕ, a < 9 + j ∧ C.gates[j] = ⟨GateOp.not, [a]⟩) ∨
          ∃ a b : ℕ, a < 9 + j ∧ b < 9 + j ∧ a < b ∧
            (C.gates[j] = ⟨GateOp.and, [a, b]⟩ ∨ C.gates[j] = ⟨GateOp.or, [a, b]⟩)) →
      C.gates.countP (fun g => g.op.eval [false]) = 1 → IsMinimalCircuit 9 C →
      circuitFun 9 C ≠ (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (1 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  intro C hshape hCount he
  obtain ⟨hLen, hOut, hFirst, hGates⟩ := hshape
  have hfan : FanInTwo C := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have h := hGates j hj
    dsimp only at h
    rcases h with h | ⟨a, _, h⟩ | ⟨a, b, _, _, _, h | h⟩ <;>
      rw [h] <;> simp
  have hMin : IsMinimalCircuit 9 C := ⟨hfan, fun D hD hSame => by
    have hh := hSize D hD (hSame.trans he)
    change C.gates.length ≤ D.size
    simpa only [hLen] using hh⟩
  have hNonconst : ∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y := by
    rw [he]
    refine ⟨fun _ => false, fun j => decide (j = 0 ∨ j = 1), ?_⟩
    decide +kernel
  have hUnary : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1 := by
    intro g hg hn
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have h := hGates j hj
    dsimp only at h
    rcases h with h | ⟨a, _, h⟩ | ⟨a, b, _, _, _, h | h⟩ <;>
      rw [h] at hn ⊢ <;> simp at hn ⊢
  apply hResidual C ?_ hCount hMin he
  refine ⟨hLen, hOut, hFirst, ?_⟩
  intro j hj
  have hGet : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
  obtain ⟨hReads, hDistinct, hN, hBinary⟩ := hClean 9 C hMin hNonconst hUnary j C.gates[j] hGet
  have h := hGates j hj
  dsimp only at h
  rcases h with h | ⟨a, _, h⟩ | ⟨a, b, _, _, hOrdered, h⟩
  · have hh := hBinary (by rw [h]; intro hn; cases hn)
    rw [h] at hh
    contradiction
  · apply Or.inl
    exact ⟨a, hReads a (by rw [h]; simp), h⟩
  · apply Or.inr
    have ha : a < 9 + j := hReads a (by rcases h with h | h <;> rw [h] <;> simp)
    have hb : b < 9 + j := hReads b (by rcases h with h | h <;> rw [h] <;> simp)
    have hab : a ≠ b := by
      have hn : ([a, b] : List ℕ).Nodup := by
        rcases h with h | h <;> simpa only [h] using hDistinct
      simpa using hn
    have hablt : a < b := by
      have hjlt : j < 15 := by simpa only [hLen] using hj
      have hae : a ≠ 24 := by omega
      have hbe : b ≠ 24 := by omega
      simp only [hae, hbe, ite_false] at hOrdered
      split_ifs at hOrdered <;> omega
    exact ⟨a, b, ha, hb, hablt, h⟩
