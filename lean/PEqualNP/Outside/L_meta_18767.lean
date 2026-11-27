import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18767_aux

private lemma foldl_append_getD {α β : Type*} (f : List α → β → α) (gs : List β)
    (init : List α) (k : ℕ) (hk : k < init.length) (d : α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) init).getD k d = init.getD k d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : k < (init ++ [f init g]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih (init ++ [f init g]) hlen]
    rw [List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ hk]
    exact List.getElem_append_left hk

private lemma wires_getD_of_lt (C : PEqualNP.CircuitLowerBounds.Circuit) (inp : List Bool)
    (k : ℕ) (hk : k < inp.length) :
    (C.wires inp).getD k false = inp.getD k false := by
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires
  exact foldl_append_getD
    (fun acc g => g.op.eval (g.inputs.map (fun i => acc.getD i false)))
    C.gates inp k hk false

end PEqualNP.Outside.L_meta_18767_aux

theorem PEqualNP.Outside.L_meta_18767 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (26 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (59 : ℕ) ≤ x1.size) := by
  intro x1 hout _ heval _
  exfalso
  let k : Fin 26 := ⟨x1.output, hout⟩
  let x3 : Fin 26 → Bool := fun i => decide (i = k)
  have hlen : x1.output < (List.ofFn x3).length := by
    simp only [List.length_ofFn]
    exact hout
  have hev : x1.eval (List.ofFn x3) = true := by
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [PEqualNP.Outside.L_meta_18767_aux.wires_getD_of_lt x1 (List.ofFn x3) x1.output hlen]
    rw [List.getD_eq_getElem _ _ hlen, List.getElem_ofFn]
    simp [x3, k]
  obtain ⟨x4, x5, _, _, hx4, hx5⟩ := (heval x3).mp hev
  have e4 : Fin.castAdd 13 x4 = k := of_decide_eq_true hx4
  have e5 : Fin.natAdd 13 x5 = k := of_decide_eq_true hx5
  have heq : (Fin.castAdd 13 x4).val = (Fin.natAdd 13 x5).val := by rw [e4, e5]
  simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
  omega
