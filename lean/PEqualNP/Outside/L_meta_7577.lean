import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7577

open PEqualNP.CircuitLowerBounds

theorem fold_inv (σ : ℕ → ℕ) (N : ℕ) (hσ : ∀ k, N ≤ k → σ k = k)
    (hσl : ∀ k, k < N → σ k < N) :
    ∀ (gs : List Gate) (L' L : List Bool), L'.length = L.length → N ≤ L.length →
      (∀ k, L'.getD (σ k) false = L.getD k false) →
      ∀ k, ((gs.map (fun g => (⟨g.op, g.inputs.map σ⟩ : Gate))).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) L').getD (σ k) false
        = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) L).getD
          k false := by
  intro gs
  induction gs with
  | nil =>
    intro L' L _ _ h k
    simpa using h k
  | cons g gs ih =>
    intro L' L hlen hN h k
    simp only [List.map_cons, List.foldl_cons]
    have hv : g.op.eval ((g.inputs.map σ).map fun i => L'.getD i false)
        = g.op.eval (g.inputs.map fun i => L.getD i false) := by
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact h i
    rw [hv]
    apply ih
    · simp [hlen]
    · simp; omega
    · intro j
      by_cases hj : j < L.length
      · have hsj : σ j < L'.length := by
          by_cases hjN : j < N
          · have := hσl j hjN; omega
          · rw [hσ j (by omega)]; omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hsj, List.getElem?_append_left hj,
          ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
        exact h j
      · rw [hσ j (by omega)]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hlen]

end PEqualNP.Outside.L_meta_7577

theorem PEqualNP.Outside.L_meta_7577 : have x1 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x1 x2 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x1)) ++ List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x2); have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).inputs, (26 : ℕ) ≤ x4 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x4 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Equiv.Perm (Fin (13 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ → ℕ), x8.size = x3.size ∧ PEqualNP.MetaComplexity.Monotone2 x8 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x8 ∧ (∀ x10 < (26 : ℕ) + x3.size, x9 x10 < (26 : ℕ) + x8.size) ∧ (∀ (x10 : ℕ), x2 x3 x10 → x2 x8 x10) ∧ ∀ (x10 : ℕ) (x11 x12 : Finset (Fin (13 : ℕ))), (x8.wires (x1 x11 x12)).getD (x9 x10) Bool.false = (x3.wires (x1 (Finset.image (⇑(Equiv.symm x4)) x11) (Finset.image (⇑(Equiv.symm x5)) x12))).getD x10 Bool.false := by
  intro x1 x2 x3 x4 x5 hmono hrb
  classical
  let σ : ℕ → ℕ := fun i => if h : i < 13 then (x4 ⟨i, h⟩).val
    else if h2 : i < 26 then 13 + (x5 ⟨i - 13, by omega⟩).val else i
  have hσ : ∀ k, 26 ≤ k → σ k = k := by
    intro k hk
    simp only [σ]
    rw [dif_neg (by omega), dif_neg (by omega)]
  have hσl : ∀ k, k < 26 → σ k < 26 := by
    intro k hk
    simp only [σ]
    split_ifs with h1 h2
    · have := (x4 ⟨k, h1⟩).isLt; omega
    · have := (x5 ⟨k - 13, by omega⟩).isLt; omega
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨x3.gates.map (fun g => (⟨g.op, g.inputs.map σ⟩ : PEqualNP.CircuitLowerBounds.Gate)),
      x3.output⟩
  have hgate : ∀ j, PEqualNP.MetaComplexity.NestedCover.gateAt C j
      = ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt x3 j).op,
          (PEqualNP.MetaComplexity.NestedCover.gateAt x3 j).inputs.map σ⟩ := by
    intro j
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, C]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases x3.gates[j]? <;> simp
  refine ⟨C, σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [C, PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro g hg
    simp only [C, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hmono g0 hg0
    simpa using this
  · intro j hj i hi
    have hj' : j < x3.gates.length := by simpa [C] using hj
    rw [hgate j] at hi
    simp only [List.mem_map] at hi
    obtain ⟨i0, hi0, rfl⟩ := hi
    have := hrb j hj' i0 hi0
    by_cases h26 : i0 < 26
    · have := hσl i0 h26; omega
    · rw [hσ i0 (by omega)]; exact this
  · intro x10 hx10
    have hs : C.size = x3.size := by simp [C, PEqualNP.CircuitLowerBounds.Circuit.size]
    rw [hs]
    by_cases h26 : x10 < 26
    · have := hσl x10 h26; omega
    · rw [hσ x10 (by omega)]; exact hx10
  · intro x10 hx
    obtain ⟨hop, w, hw, hw26, hwop⟩ := hx
    refine ⟨?_, σ w, ?_, ?_, ?_⟩
    · rw [hgate]; exact hop
    · rw [hgate]; exact List.mem_map_of_mem hw
    · rw [hσ w hw26]; exact hw26
    · rw [hσ w hw26, hgate]; exact hwop
  · intro x10 x11 x12
    simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, C]
    apply PEqualNP.Outside.L_meta_7577.fold_inv σ 26 hσ hσl
    · simp [x1]
    · simp [x1]
    · intro k
      by_cases hk : k < 26
      · by_cases hk13 : k < 13
        · have e : σ k = (x4 ⟨k, hk13⟩).val := by simp only [σ]; rw [dif_pos hk13]
          rw [e]
          have hl : (x4 ⟨k, hk13⟩).val < (List.ofFn fun (x3 : Fin 13) => decide (x3 ∈ x11)).length := by
            simp
          have hl2 : k < (List.ofFn fun (x3 : Fin 13) =>
              decide (x3 ∈ Finset.image (⇑(Equiv.symm x4)) x11)).length := by simp; omega
          simp only [x1]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hl, List.getElem?_append_left hl2]
          rw [List.getElem?_ofFn, List.getElem?_ofFn, dif_pos (x4 _).isLt, dif_pos hk13]
          simp only [Option.getD_some, Fin.eta, Finset.mem_image, Equiv.symm_apply_eq, exists_eq_right]
        · have e : σ k = 13 + (x5 ⟨k - 13, by omega⟩).val := by
            simp only [σ]; rw [dif_neg hk13, dif_pos hk]
          rw [e]
          simp only [x1]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by simp), List.getElem?_append_right (by simp; omega)]
          have hk' : k - 13 < 13 := by omega
          simp only [List.length_ofFn, Nat.add_sub_cancel_left]
          rw [List.getElem?_ofFn, List.getElem?_ofFn, dif_pos (x5 _).isLt, dif_pos hk']
          simp only [Option.getD_some, Fin.eta, Finset.mem_image, Equiv.symm_apply_eq, exists_eq_right]
      · rw [hσ k (by omega)]
        simp only [x1]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
