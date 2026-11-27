import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves PEqualNP.TopForm PEqualNP.BlindGate
theorem PEqualNP.Outside.R_meta_4297_284
    (hSeparate : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → C.output < n + C.size →
      (∀ w < n, ¬WireBelowOutput n C w) →
      (∀ j < C.size, ∀ a b, C.gates[j]? = some ⟨.or,[a,b]⟩ →
        (n ≤ b → WireBelowOutput n C b → WireBelowOutput n C a) ∧
        (n ≤ a → WireBelowOutput n C a → WireBelowOutput n C b)) →
      ∃ (D : Circuit) (B : List (ℕ × ℕ)), IsAO2 n D ∧
        (∀ j < D.size, ∃ x, PEqualNP.BlindGate.wireValue D n x (n+j) = true ∧ circuitFun n C x = false) ∧
        (∀ x, circuitFun n C x = true ↔ ∃ t ∈ B,
          PEqualNP.BlindGate.wireValue D n x t.1 = true ∧ PEqualNP.BlindGate.wireValue D n x t.2 = true) ∧
        D.size + 2*B.length ≤ C.size+1)
    (hProducts : ∀ (p l : ℕ) (I : Fin p → Fin l → Prop) [DecidableRel I],
      let n := p+l
      let F := fun x : Fin n → Bool => ∃ a b, I a b ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true
      ∀ (D : Circuit) (B : List (ℕ × ℕ)),
        let v := fun x w => PEqualNP.BlindGate.wireValue D n x w = true
        (∀ a a' b b', a ≠ a' → b ≠ b' → ¬(I a b ∧ I a b' ∧ I a' b ∧ I a' b')) →
        IsAO2 n D → (∀ j < D.size, ∃ x, v x (n+j) ∧ ¬ F x) →
        (∀ x, F x ↔ ∃ t ∈ B, v x t.1 ∧ v x t.2) →
        ∃ W : List (ℕ × List ℕ),
        (∀ s ∈ W, s.2 ≠ [] ∧ ((s.1 < p ∧ ∀ w ∈ s.2, p ≤ w ∧ w < p+l) ∨
          p ≤ s.1 ∧ s.1 < p+l ∧ ∀ w ∈ s.2, w < p)) ∧
        (∀ a : Fin p, ∀ b : Fin l, I a b ↔ ∃ s ∈ W,
          (s.1 = a.val ∧ p+b.val ∈ s.2) ∨ (s.1 = p+b.val ∧ a.val ∈ s.2)) ∧
        (W.map fun s => s.2.length).sum + W.length - 1 ≤ D.size + 2*B.length - 1) :
    ∀ (p l : ℕ) (I : Fin p → Fin l → Prop) [DecidableRel I] (C : Circuit),
      (∀ a a' b b', a ≠ a' → b ≠ b' → ¬(I a b ∧ I a b' ∧ I a' b ∧ I a' b')) →
      IsAO2 (p+l) C → C.output < p+l+C.gates.length →
      (∀ x, circuitFun (p+l) C x = decide (∃ a b, I a b ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) →
      (∀ j < C.gates.length, ∀ a b, C.gates[j]? = some ⟨.or,[a,b]⟩ →
        (p+l ≤ b → WireBelowOutput (p+l) C b → WireBelowOutput (p+l) C a) ∧
        (p+l ≤ a → WireBelowOutput (p+l) C a → WireBelowOutput (p+l) C b)) →
      ∃ W : List (ℕ × List ℕ),
        (∀ s ∈ W, s.2 ≠ [] ∧ ((s.1 < p ∧ ∀ w ∈ s.2, p ≤ w ∧ w < p+l) ∨
          p ≤ s.1 ∧ s.1 < p+l ∧ ∀ w ∈ s.2, w < p)) ∧
        (∀ a : Fin p, ∀ b : Fin l, I a b ↔ ∃ s ∈ W,
          (s.1 = a.val ∧ p+b.val ∈ s.2) ∨ (s.1 = p+b.val ∧ a.val ∈ s.2)) ∧
        (W.map fun s => s.2.length).sum + W.length - 1 ≤ C.size := by
  intro p l I inst C four ao out computes norm
  have raw (w : ℕ) (lw : w<p+l) : ¬WireBelowOutput (p+l) C w := by
    let x := fun i : Fin (p+l) => decide (i.val = w)
    intro safe
    have input : (C.wires (List.ofFn x)).getD w false = true := by
      have keepInput (gs : List Gate) (u : List Bool) (h : w < u.length) :
          (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun k => v.getD k false)]) u).getD w false =
          u.getD w false := by
        induction gs generalizing u with
        | nil => rfl
        | cons g gs ih =>
          rw [List.foldl_cons,ih _ (by simp; omega),List.getD_append _ _ _ _ h]
      change (C.gates.foldl _ (List.ofFn x)).getD w false = true
      rw [keepInput _ _ (by simpa using lw),List.getD_eq_getElem _ _ (by simpa using lw),List.getElem_ofFn]
      simp [x]
    have yes : circuitFun (p+l) C x = true := safe x input
    rw [computes x] at yes
    obtain ⟨a,b,_,ha,hb⟩ := of_decide_eq_true yes
    simp only [x,decide_eq_true_eq,Fin.val_castAdd,Fin.val_natAdd] at ha hb
    omega
  obtain ⟨D,B,good,witness,covered,budget⟩ := hSeparate (p+l) C ao out raw norm
  obtain ⟨W,shape,edges,cost⟩ := hProducts p l I D B four good (by
    intro j hj
    obtain ⟨x,hit,no⟩ := witness j hj
    rw [computes x] at no
    exact ⟨x,hit,of_decide_eq_false no⟩) (by
      intro x
      simpa only [computes x,decide_eq_true_eq] using covered x)
  exact ⟨W,shape,edges,by omega⟩
