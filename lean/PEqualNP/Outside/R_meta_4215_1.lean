import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4215_1 :
    (¬ ∃ C : Circuit, C.size ≤ 26 ∧ IsAO2 14 C ∧
      (∀ j < C.gates.length, (gateAt C j).inputs.Nodup) ∧
      circuitFun 14 C = (fun x => decide (∃ p l : Fin 7,
        p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true))) →
    (∀ C : Circuit,
      let V (w : ℕ) (p q : Fin 14) := wireVal 14 C w (pairInput p q)
      let Z (w : ℕ) := V w 0 0 = false ∧ V w 7 7 = false
      C.gates.length = 27 → IsAO2 14 C →
      (∀ j < C.gates.length, (gateAt C j).inputs.Nodup) →
      (∀ k < C.gates.length, ∀ w < 14 + k, ∃ x, wireVal 14 C (14 + k) x ≠ wireVal 14 C w x) →
      circuitFun 14 C = (fun x => decide (∃ p l : Fin 7,
        p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
      ∀ g : ℕ, (gateAt C g).op = .and →
      (14 + g = C.output ∨ InCone 14 C g (C.output - 14)) →
      V (14 + g) 0 7 = true → (∀ b : Fin 2, Z (opnd C g b)) →
      ¬ ∃ (a : ℕ) (b : Fin 2), opnd C g b = 14 + a ∧ InCone 14 C a (opnd C g (1 - b) - 14) ∧
        (gateAt C a).op = .and ∧ Z (14 + a) ∧
        ∃ c : Fin 2, V (opnd C a c) 0 0 = true ∧ V (opnd C a (1 - c)) 7 7 = true) →
    (∀ C : Circuit,
      let V (w : ℕ) (p q : Fin 14) := wireVal 14 C w (pairInput p q)
      let Z (w : ℕ) := V w 0 0 = false ∧ V w 7 7 = false
      C.gates.length = 27 → IsAO2 14 C →
      (∀ j < C.gates.length, (gateAt C j).inputs.Nodup) →
      (∀ k < C.gates.length, ∀ w < 14 + k, ∃ x, wireVal 14 C (14 + k) x ≠ wireVal 14 C w x) →
      circuitFun 14 C = (fun x => decide (∃ p l : Fin 7,
        p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
      ∀ g : ℕ, (gateAt C g).op = .and →
      (14 + g = C.output ∨ InCone 14 C g (C.output - 14)) →
      V (14 + g) 0 7 = true → (∀ b : Fin 2, Z (opnd C g b)) →
      ¬ ∃ a : ℕ, InCone 14 C a (opnd C g 0 - 14) ∧ InCone 14 C a (opnd C g 1 - 14) ∧
        (gateAt C a).op = .and ∧ Z (14 + a) ∧
        ∃ c : Fin 2, V (opnd C a c) 0 0 = true ∧ V (opnd C a (1 - c)) 7 7 = true) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);   have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => ((14 : ℕ) + x4 = x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x3 - (14 : ℕ))) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x2 ((14 : ℕ) + x4) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 ((14 : ℕ) + x4) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ∃ (x5 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x4 x5) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (PEqualNP.TopForm.opnd x1 x4 ((1 : Fin (2 : ℕ)) - x5)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;   x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).inputs.Nodup) → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x7 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x8 : Fin (7 : ℕ)) (x9 : Fin (7 : ℕ)), x8 ∈ PEqualNP.CircuitLowerBounds.fanoLines x9 ∧ x7 (Fin.castAdd (7 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (7 : ℕ) x9) = Bool.true)) → ∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → (14 : ℕ) + x8 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x8 (x1.output - (14 : ℕ)) → x2 ((14 : ℕ) + x8) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → (∀ (x12 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x8 x12) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 (PEqualNP.TopForm.opnd x1 x8 x12) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → ¬∃ (x13 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x8 (0 : Fin (2 : ℕ))) x13 ∧ x3 (PEqualNP.TopForm.opnd x1 x8 (1 : Fin (2 : ℕ))) x13 := by
  classical
  intro hT1 hT2 hT3 C V Birth hsz hAO hnod hfun g hg_op hg_cone hg_07 hg_opnds
  rintro ⟨a, ha0, ha1⟩
  let fano : (Fin 14 → Bool) → Bool := fun x => decide (∃ p l : Fin 7,
    p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
  let step : List Bool → Gate → List Bool := fun w gt =>
    w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]
  have hwires_eq (D : Circuit) (x : List Bool) : D.wires x = D.gates.foldl step x := rfl
  have hlen (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons gt gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have hgetD_append_left (l₁ l₂ : List Bool) (i : ℕ) (d : Bool) (hi : i < l₁.length) :
      (l₁ ++ l₂).getD i d = l₁.getD i d := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, List.getD_eq_getElem?_getD]
  have hpref (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons gt gs ih =>
      rw [List.foldl_cons, ih (step w gt) (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact hgetD_append_left w [gt.op.eval (gt.inputs.map fun k => w.getD k false)] i false hi
  have hwire_in (D : Circuit) (x : Fin 14 → Bool) (i : ℕ) (hi : i < 14) :
      wireVal 14 D i x = x ⟨i, hi⟩ := by
    unfold wireVal
    rw [hwires_eq, hpref D.gates (List.ofFn x) i (by simpa [List.length_ofFn] using hi)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi]
    rfl
  have hwire_oob (D : Circuit) (x : Fin 14 → Bool) (w : ℕ) (hw : 14 + D.gates.length ≤ w) :
      wireVal 14 D w x = false := by
    unfold wireVal
    rw [hwires_eq, List.getD_eq_default]
    rw [hlen, List.length_ofFn]
    exact hw
  have hwire_gate (D : Circuit) (hR : ReadsBack 14 D) (x : Fin 14 → Bool) (j : ℕ) (hj : j < D.gates.length) :
      wireVal 14 D (14 + j) x = (gateAt D j).op.eval ((gateAt D j).inputs.map fun i => wireVal 14 D i x) := by
    have hsplit2 : D.gates = D.gates.take j ++ [gateAt D j] ++ D.gates.drop (j + 1) := by
      have h1 := List.take_append_drop j D.gates
      have hdrop : D.gates.drop j = gateAt D j :: D.gates.drop (j + 1) := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hj, List.drop_eq_getElem_cons hj]
      rw [List.append_assoc, List.singleton_append, ← hdrop]
      exact h1.symm
    let w1 := (D.gates.take j).foldl step (List.ofFn x)
    have hw1_len : w1.length = 14 + j := by
      simp only [w1, hlen, List.length_ofFn, List.length_take_of_le (le_of_lt hj)]
    have hw_eq : D.wires (List.ofFn x) = (D.gates.drop (j + 1)).foldl step (step w1 (gateAt D j)) := by
      rw [hwires_eq]
      conv_lhs => rw [hsplit2, List.foldl_append, List.foldl_append]
      simp [w1, List.foldl_cons]
    have hstep_val : wireVal 14 D (14 + j) x = (gateAt D j).op.eval ((gateAt D j).inputs.map fun i => w1.getD i false) := by
      unfold wireVal
      rw [hw_eq, hpref (D.gates.drop (j + 1)) (step w1 (gateAt D j)) (14 + j)
        (by simp only [step, List.length_append, List.length_singleton, hw1_len]; omega)]
      simp only [step]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hw1_len])]
      rw [hw1_len, Nat.sub_self]
      rfl
    rw [hstep_val]
    congr 1
    apply List.map_congr_left
    intro i hi
    have ilt : i < 14 + j := hR j hj i hi
    unfold wireVal
    rw [hw_eq, hpref (D.gates.drop (j + 1)) (step w1 (gateAt D j)) i
      (by simp only [step, List.length_append, List.length_singleton, hw1_len]; omega)]
    have ilt2 : i < w1.length := by rw [hw1_len]; exact ilt
    exact (hgetD_append_left w1 [((gateAt D j).op.eval ((gateAt D j).inputs.map fun k => w1.getD k false))] i false ilt2).symm

  have shrink : ∀ m : ℕ, ∀ D : Circuit, D.size ≤ m → IsAO2 14 D → circuitFun 14 D = fano →
      (∃ D' : Circuit, D'.size ≤ m ∧ IsAO2 14 D' ∧
        (∀ j < D'.gates.length, (gateAt D' j).inputs.Nodup) ∧ circuitFun 14 D' = fano) ∧
      ((∃ k < D.gates.length, ∃ w < 14 + k, ∀ x, wireVal 14 D (14 + k) x = wireVal 14 D w x) →
        ∃ D' : Circuit, D'.size < D.size ∧ IsAO2 14 D' ∧
          (∀ j < D'.gates.length, (gateAt D' j).inputs.Nodup) ∧ circuitFun 14 D' = fano) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro D hDm hDAO hDfun
      have step_rem : ∀ k < D.gates.length, ∀ w < 14 + k,
          (∀ x, wireVal 14 D (14 + k) x = wireVal 14 D w x) →
          ∃ D₁ : Circuit, D₁.size = D.size - 1 ∧ IsAO2 14 D₁ ∧ circuitFun 14 D₁ = fano := by
        intro k hk w hw heqw
        let remap (j : ℕ) : ℕ := if j = 14 + k then w else if 14 + k < j then j - 1 else j
        let rg (gt : Gate) : Gate := ⟨gt.op, gt.inputs.map remap⟩
        let gs₁ := (D.gates.take k ++ D.gates.drop (k + 1)).map rg
        let D₁ : Circuit := ⟨gs₁, remap D.output⟩
        have hlen₁ : D₁.gates.length = D.gates.length - 1 := by
          simp only [D₁, gs₁, List.length_map, List.length_append,
            List.length_take_of_le (le_of_lt hk), List.length_drop]
          omega
        have hgate_lt (j : ℕ) (hj : j < k) : gateAt D₁ j = rg (gateAt D j) := by
          have hj1 : j < D₁.gates.length := by omega
          unfold gateAt
          rw [List.getD_eq_getElem _ _ hj1, List.getD_eq_getElem _ _ (by omega : j < D.gates.length)]
          simp only [D₁, gs₁, List.getElem_map]
          congr 1
          rw [List.getElem_append_left (by simp [List.length_take_of_le (le_of_lt hk), hj])]
          rw [List.getElem_take]
        have hgate_ge (j : ℕ) (hjk : k ≤ j) (hj1 : j < D₁.gates.length) :
            gateAt D₁ j = rg (gateAt D (j + 1)) := by
          have hjD : j + 1 < D.gates.length := by omega
          unfold gateAt
          rw [List.getD_eq_getElem _ _ hj1, List.getD_eq_getElem _ _ hjD]
          simp only [D₁, gs₁, List.getElem_map]
          congr 1
          have htk : (D.gates.take k).length = k := List.length_take_of_le (le_of_lt hk)
          have hge_tk : (D.gates.take k).length ≤ j := by omega
          rw [List.getElem_append_right hge_tk, List.getElem_drop]
          congr 1
          omega
        have hDAO₁ : IsAO2 14 D₁ := by
          refine ⟨?_, ?_, ?_⟩
          · intro gt hgt
            simp only [D₁, gs₁, List.mem_map, List.mem_append] at hgt
            rcases hgt with ⟨gt₀, hgt₀, rfl⟩
            apply hDAO.1 gt₀
            rcases hgt₀ with h1 | h2
            · exact List.mem_of_mem_take h1
            · exact List.mem_of_mem_drop h2
          · intro j hj u hu
            by_cases hjk : j < k
            · rw [hgate_lt j hjk] at hu
              simp only [rg, List.mem_map] at hu
              rcases hu with ⟨v, hv, rfl⟩
              have hv_lt : v < 14 + j := hDAO.2.1 j (by omega) v hv
              simp only [remap]
              split_ifs <;> omega
            · rw [hgate_ge j (by omega) hj] at hu
              simp only [rg, List.mem_map] at hu
              rcases hu with ⟨v, hv, rfl⟩
              have hv_lt : v < 14 + (j + 1) := hDAO.2.1 (j + 1) (by omega) v hv
              simp only [remap]
              split_ifs <;> omega
          · intro gt hgt
            simp only [D₁, gs₁, List.mem_map, List.mem_append] at hgt
            rcases hgt with ⟨gt₀, hgt₀, rfl⟩
            simp only [rg, List.length_map]
            apply hDAO.2.2 gt₀
            rcases hgt₀ with h1 | h2
            · exact List.mem_of_mem_take h1
            · exact List.mem_of_mem_drop h2
        have hsim : ∀ x : Fin 14 → Bool, ∀ idx : ℕ, idx < 14 + D.gates.length →
            wireVal 14 D₁ (remap idx) x = wireVal 14 D idx x := by
          intro x idx
          induction idx using Nat.strong_induction_on with
          | _ idx ihx =>
            intro hidx
            by_cases h14 : idx < 14
            · have hr : remap idx = idx := by simp only [remap]; split_ifs <;> omega
              rw [hr, hwire_in D₁ x idx h14, hwire_in D x idx h14]
            · by_cases hik : idx = 14 + k
              · subst idx
                have hr : remap (14 + k) = w := by simp [remap]
                have hrw : remap w = w := by simp only [remap]; split_ifs <;> omega
                rw [hr, ← hrw, ihx w (by omega) (by omega), heqw]
              · have hgt : 14 ≤ idx := by omega
                let j := idx - 14
                have hj_eq : idx = 14 + j := by omega
                have hjD : j < D.gates.length := by omega
                by_cases hjk : j < k
                · have hr : remap idx = 14 + j := by simp only [remap]; split_ifs <;> omega
                  rw [hr, hj_eq, hwire_gate D₁ hDAO₁.2.1 x j (by omega),
                      hwire_gate D hDAO.2.1 x j hjD, hgate_lt j hjk]
                  simp only [rg, List.map_map]
                  congr 1
                  apply List.map_congr_left
                  intro u hu
                  have hu_lt : u < 14 + j := hDAO.2.1 j hjD u hu
                  exact ihx u (by omega) (by omega)
                · have hkj : k < j := by omega
                  have hr : remap idx = 14 + (j - 1) := by simp only [remap]; split_ifs <;> omega
                  have hj1 : j - 1 < D₁.gates.length := by omega
                  rw [hr, hwire_gate D₁ hDAO₁.2.1 x (j - 1) hj1,
                      hgate_ge (j - 1) (by omega) hj1]
                  have hj1_eq : (j - 1) + 1 = j := by omega
                  rw [hj1_eq, hj_eq, hwire_gate D hDAO.2.1 x j hjD]
                  simp only [rg, List.map_map]
                  congr 1
                  apply List.map_congr_left
                  intro u hu
                  have hu_lt : u < 14 + j := hDAO.2.1 j hjD u hu
                  exact ihx u (by omega) (by omega)
        have hout_lt : D.output < 14 + D.gates.length := by
          by_contra hge
          have hle : 14 + D.gates.length ≤ D.output := by omega
          have ht : circuitFun 14 D (pairInput (0 : Fin 14) 7) = fano (pairInput (0 : Fin 14) 7) := by
            rw [hDfun]
          have h0fan : (0 : Fin 7) ∈ fanoLines 0 := by decide +kernel
          have hfano07 : fano (pairInput (0 : Fin 14) 7) = true := by
            apply decide_eq_true
            exact ⟨0, 0, h0fan, rfl, rfl⟩
          have hoob : circuitFun 14 D (pairInput (0 : Fin 14) 7) = false := hwire_oob D _ D.output hle
          rw [ht, hfano07] at hoob
          cases hoob
        refine ⟨D₁, by change D₁.gates.length = D.gates.length - 1; exact hlen₁, hDAO₁, ?_⟩
        funext x
        exact (hsim x D.output hout_lt).trans (congrFun hDfun x)
      have hnodupe : ∀ j < D.gates.length, ¬ (gateAt D j).inputs.Nodup →
          ∃ w < 14 + j, ∀ x, wireVal 14 D (14 + j) x = wireVal 14 D w x := by
        intro j hj hnd
        have hlen2 : (gateAt D j).inputs.length = 2 := by
          apply hDAO.2.2 (gateAt D j)
          rw [show gateAt D j = D.gates[j] from by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]]
          exact List.getElem_mem hj
        rcases List.length_eq_two.mp hlen2 with ⟨u, v, huv⟩
        have hueqv : u = v := by
          by_contra hne
          apply hnd
          rw [huv]
          simp [hne]
        subst hueqv
        refine ⟨u, hDAO.2.1 j hj u (by rw [huv]; simp), ?_⟩
        intro x
        rw [hwire_gate D hDAO.2.1 x j hj, huv]
        have hop : (gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or := by
          apply hDAO.1 (gateAt D j)
          rw [show gateAt D j = D.gates[j] from by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]]
          exact List.getElem_mem hj
        rcases hop with h | h
        · rw [h]
          change (wireVal 14 D u x && (wireVal 14 D u x && true)) = wireVal 14 D u x
          cases wireVal 14 D u x <;> rfl
        · rw [h]
          change (wireVal 14 D u x || (wireVal 14 D u x || false)) = wireVal 14 D u x
          cases wireVal 14 D u x <;> rfl
      refine ⟨?_, ?_⟩
      · by_cases hnd : ∀ j < D.gates.length, (gateAt D j).inputs.Nodup
        · exact ⟨D, hDm, hDAO, hnd, hDfun⟩
        · push Not at hnd
          rcases hnd with ⟨j, hj, hndj⟩
          rcases hnodupe j hj hndj with ⟨w, hw, heqw⟩
          rcases step_rem j hj w hw heqw with ⟨D₁, hsz₁, hAO₁, hfun₁⟩
          have hD₁m : D₁.size ≤ D.size - 1 := le_of_eq hsz₁
          have hltm : D.size - 1 < m := by
            have : 0 < D.gates.length := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
            change D.gates.length ≤ m at hDm
            change D.gates.length - 1 < m
            omega
          rcases (ih (D.size - 1) hltm D₁ hD₁m hAO₁ hfun₁).1 with ⟨D', hsz', hAO', hnd', hfun'⟩
          exact ⟨D', by omega, hAO', hnd', hfun'⟩
      · rintro ⟨k, hk, w, hw, heqw⟩
        rcases step_rem k hk w hw heqw with ⟨D₁, hsz₁, hAO₁, hfun₁⟩
        have hltm : D₁.size < m := by
          have : 0 < D.gates.length := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
          rw [hsz₁]
          change D.gates.length ≤ m at hDm
          change D.gates.length - 1 < m
          omega
        rcases (ih D₁.size hltm D₁ le_rfl hAO₁ hfun₁).1 with ⟨D', hsz', hAO', hnd', hfun'⟩
        have hDpos : 0 < D.size := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
        exact ⟨D', by omega, hAO', hnd', hfun'⟩

  have hfano_eq : circuitFun 14 C = fano := hfun
  have hC27 : C.gates.length = 27 := by
    by_contra hne
    have h26 : C.size ≤ 26 := by
      change C.gates.length ≤ 27 at hsz
      change C.gates.length ≤ 26
      omega
    exact hT1 ⟨C, h26, hAO, hnod, hfano_eq⟩
  have hirred : ∀ k < C.gates.length, ∀ w < 14 + k, ∃ x, wireVal 14 C (14 + k) x ≠ wireVal 14 C w x := by
    intro k hk w hw
    by_contra hcon
    push Not at hcon
    rcases (shrink C.size C le_rfl hAO hfano_eq).2 ⟨k, hk, w, hw, hcon⟩ with
      ⟨C', hsz', hAO', hnd', hfun'⟩
    exact hT1 ⟨C', by omega, hAO', hnd', hfun'⟩
  have hg_lt : g < C.gates.length := by
    by_contra hge
    have hgt : (gateAt C g).op = .or := by
      unfold gateAt
      rw [List.getD_eq_default _ _ (by omega)]
    rw [hgt] at hg_op
    cases hg_op
  have hg_ne : opnd C g 0 ≠ opnd C g 1 := by
    have hlen2 : (gateAt C g).inputs.length = 2 := by
      apply hAO.2.2 (gateAt C g)
      rw [show gateAt C g = C.gates[g] from by unfold gateAt; rw [List.getD_eq_getElem _ _ hg_lt]]
      exact List.getElem_mem hg_lt
    rcases List.length_eq_two.mp hlen2 with ⟨u, v, huv⟩
    have hnd := hnod g hg_lt
    rw [huv] at hnd
    have huv_ne : u ≠ v := by simpa using hnd
    change (gateAt C g).inputs.getD 0 0 ≠ (gateAt C g).inputs.getD 1 0
    rw [huv]
    exact huv_ne
  rcases ha0 with ⟨ha0_cone, ha_op, ha_00, ha_77, b0, hb0_0, hb0_7⟩
  rcases ha1 with ⟨ha1_cone, _, _, _, _, _⟩
  rcases ha0_cone with h0eq | h0in
  · have h1in : InCone 14 C a (opnd C g 1 - 14) := by
      rcases ha1_cone with h1eq | h1in
      · exact False.elim (hg_ne (h0eq.symm.trans h1eq))
      · exact h1in
    exact hT2 C hC27 hAO hnod hirred hfano_eq g hg_op hg_cone hg_07 hg_opnds
      ⟨a, 0, h0eq.symm, by simpa using h1in, ha_op, ⟨ha_00, ha_77⟩, b0, hb0_0, hb0_7⟩
  · rcases ha1_cone with h1eq | h1in
    · exact hT2 C hC27 hAO hnod hirred hfano_eq g hg_op hg_cone hg_07 hg_opnds
        ⟨a, 1, h1eq.symm, by simpa using h0in, ha_op, ⟨ha_00, ha_77⟩, b0, hb0_0, hb0_7⟩
    · exact hT3 C hC27 hAO hnod hirred hfano_eq g hg_op hg_cone hg_07 hg_opnds
        ⟨a, h0in, h1in, ha_op, ⟨ha_00, ha_77⟩, b0, hb0_0, hb0_7⟩
