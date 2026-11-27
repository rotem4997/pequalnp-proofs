import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.GenericRejection

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4693_4
    (hFloor : ∀ D : Circuit, Monotone2 D →
      ComputesIncidence (fun l : Fin 6 => Finset.univ.filter (fun p : Fin 6 => p.succ ∈ fanoLines l.succ)) D →
      21 ≤ D.size)
    (hRestriction : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) → ComputesIncidence fanoLines C →
      let v := fun j (p l : Fin 14) => gateVal 14 C j (pairInput p l)
      let below := InCone 14 C
      let mark := fun (x : Fin 14) j =>
        (gateAt C j).op = .and ∧ (14+j = C.output ∨ below j (C.output-14)) ∧
        v j 0 7 = true ∧ ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput x x) = false
      ∀ i j, i ≠ j → ¬ below i j → ¬ below j i → mark 0 i → mark 7 j →
        (v i 7 7 = true ∨ v j 0 0 = true) →
        ∃ D : Circuit, Monotone2 D ∧ D.size + 7 ≤ C.size ∧
          ComputesIncidence (fun l : Fin 6 => Finset.univ.filter (fun p : Fin 6 => p.succ ∈ fanoLines l.succ)) D) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →         (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) →           have x6 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x6 : ℕ) (x7 x8 : Fin (14 : ℕ)) => PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x6 (PEqualNP.EdgeOwnership.pairInput x7 x8);           have x7 : ℕ → Prop := fun (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;           have x8 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;           have x9 : Fin (14 : ℕ) → ℕ → Prop := fun (x9 : Fin (14 : ℕ)) (x10 : ℕ) => x7 x10 ∧ ((14 : ℕ) + x10 = x1.output ∨ x8 x10 (x1.output - (14 : ℕ))) ∧ x6 x10 (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x11) (PEqualNP.EdgeOwnership.pairInput x9 x9) = Bool.false;           ∀ (x10 x11 : ℕ), x10 ≠ x11 → ¬x8 x10 x11 → ¬x8 x11 x10 → x9 (0 : Fin (14 : ℕ)) x10 → x9 (7 : Fin (14 : ℕ)) x11 → (∃ (x17 : ℕ), x7 x17 ∧ (x8 x10 x17 ∧ x6 x10 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ x6 x17 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∨ x8 x11 x17 ∧ x6 x11 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x6 x17 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false)) → False := by
  intro C hsize hao hdist hEval
  have hFano : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p = l ∨ p = l+1 ∨ p = l+3 := by decide
  have hInc : ComputesIncidence fanoLines C := by
    intro X Y
    let x := Fin.append (fun p : Fin 7 => decide (p ∈ X)) (fun l : Fin 7 => decide (l ∈ Y))
    have hrow : List.ofFn x = incidenceInput X Y := List.ofFn_fin_append _ _
    change C.eval (incidenceInput X Y) =
      decide (∃ p ∈ X, ∃ l ∈ Y, p ∈ fanoLines l)
    rw [← hrow, Bool.eq_iff_iff, hEval x]
    simp only [x, Fin.append_left, Fin.append_right, decide_eq_true_eq]
    constructor
    · rintro ⟨p, l, he, hp, hl⟩
      exact ⟨p, hp, l, hl, (hFano p l).mpr he⟩
    · rintro ⟨p, hp, l, hl, he⟩
      exact ⟨p, l, (hFano p l).mp he, hp, hl⟩
  dsimp only
  intro i j hne hij hji hi hj hLoss
  obtain ⟨k, _, hk | hk⟩ := hLoss
  · obtain ⟨D, hm, hs, hc⟩ := hRestriction C hsize hao hdist hInc i j hne hij hji hi hj (Or.inl hk.2.1)
    have h := hFloor D hm hc
    omega
  · obtain ⟨D, hm, hs, hc⟩ := hRestriction C hsize hao hdist hInc i j hne hij hji hi hj (Or.inr hk.2.1)
    have h := hFloor D hm hc
    omega
