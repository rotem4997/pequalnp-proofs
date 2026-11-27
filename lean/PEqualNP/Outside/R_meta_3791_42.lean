import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3791_42
    (h_oval :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ p l : Fin 13, p - l ∉ D →
        ∃ Q : Finset (Fin 13), Q.card = 4 ∧
          (∀ k : Fin 13, (Q.filter fun u => u - k ∈ D).card ≤ 2) ∧
          p ∈ Q ∧ ∀ r ∈ Q, r - l ∉ D)
    (h_strict :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun p l : Fin 13 =>
        (List.ofFn fun u : Fin 13 => decide (u = p)) ++
        List.ofFn fun u : Fin 13 => decide (u = l)
      let N := fun Q : Finset (Fin 13) =>
        (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn fun u : Fin 13 => decide (∀ r ∈ Q, r - u ∉ D)
      ∀ (E : Circuit) (k a b : ℕ),
        PEqualNP.TopForm.IsAO2 26 E →
        (∀ g ∈ E.gates, g.inputs.Nodup) →
        E.output = 26 + k →
        E.gates[k]? = some ⟨GateOp.or, [a, b]⟩ →
        26 ≤ a → 26 ≤ b →
        (∀ p l : Fin 13, E.eval (P p l) = decide (p - l ∈ D)) →
        (∀ Q : Finset (Fin 13), Q.card = 4 →
          (∀ l : Fin 13, (Q.filter fun p => p - l ∈ D).card ≤ 2) → E.eval (N Q) = false) →
        (∃ p l : Fin 13, p - l ∈ D ∧
          (E.wires (P p l)).getD a false = true ∧ (E.wires (P p l)).getD b false = false) →
        (∃ p l : Fin 13, p - l ∈ D ∧
          (E.wires (P p l)).getD b false = true ∧ (E.wires (P p l)).getD a false = false) →
        64 ≤ E.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           ((26 : ℕ) ≤ x2 → ¬PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x3 (x2 - (26 : ℕ))) →             ((26 : ℕ) ≤ x3 → ¬PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x2 (x3 - (26 : ℕ))) →               have x10 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};               have x11 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x11 x12 : Fin (13 : ℕ)) => (List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 = x11)) ++ List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 = x12);               have x12 : Finset (Fin (13 : ℕ)) → List Bool := fun (x12 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 ∈ x12)) ++ List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (∀ x14 ∈ x12, x14 - x13 ∉ x10);               have x13 : Finset (Fin (13 : ℕ)) → Prop := fun (x13 : Finset (Fin (13 : ℕ))) => x13.card = (4 : ℕ) ∧ ∀ (x14 : Fin (13 : ℕ)), {x15 ∈ x13 | x15 - x14 ∈ x10}.card ≤ (2 : ℕ);               have x14 : ℕ → List Bool → Bool := fun (x14 : ℕ) (x15 : List Bool) => (x1.wires x15).getD x14 Bool.false;               (∀ (x15 x16 : Fin (13 : ℕ)), x15 - x16 ∈ x10 → x14 x2 (x11 x15 x16) = Bool.true ∨ x14 x3 (x11 x15 x16) = Bool.true) → (∀ (x16 : Finset (Fin (13 : ℕ))), x13 x16 → x14 x2 (x12 x16) = Bool.false ∧ x14 x3 (x12 x16) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x10 ∧ x14 x2 (x11 x17 x18) = Bool.true ∧ x14 x3 (x11 x17 x18) = Bool.false) → (∃ (x18 : Fin (13 : ℕ)) (x19 : Fin (13 : ℕ)), x18 - x19 ∈ x10 ∧ x14 x3 (x11 x18 x19) = Bool.true ∧ x14 x2 (x11 x18 x19) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  classical
  intro C0 w10 w20 hMono0 hBack0 hw10 hw20 _ _
  dsimp only
  intro hCov0 hNeg0 hSep10 hSep20
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let P (p l : Fin 13) : List Bool :=
    (List.ofFn fun u : Fin 13 => decide (u = p)) ++
    List.ofFn fun u : Fin 13 => decide (u = l)
  let N (Q : Finset (Fin 13)) : List Bool :=
    (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn fun u : Fin 13 => decide (∀ r ∈ Q, r - u ∉ D)
  let good (Q : Finset (Fin 13)) : Prop :=
    Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter fun u => u - k ∈ D).card ≤ 2
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have gateAt_def (A : Circuit) (j : ℕ) : gateAt A j = A.gates.getD j ⟨GateOp.or, []⟩ := rfl
  have size_def (A : Circuit) : A.size = A.gates.length := rfl
  have eval_and (bs : List Bool) : GateOp.and.eval bs = bs.all id := rfl
  have eval_or (bs : List Bool) : GateOp.or.eval bs = bs.any id := rfl
  have fold_len : ∀ (gs : List Gate) (ws : List Bool), (gs.foldl step ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; rfl
    | cons g gs ih =>
      intro ws
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, show (step ws g).length = ws.length + 1 by simp [step]]
      omega
  have fold_prefix : ∀ (gs : List Gate) (ws : List Bool) (i : ℕ), i < ws.length →
      (gs.foldl step ws).getD i false = ws.getD i false := by
    intro gs
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      simp only [List.foldl_cons]
      rw [ih _ _ (by simp [step]; omega)]
      exact List.getD_append ws _ _ i hi
  have fold_getD_snoc : ∀ (ws : List Bool) (b : Bool), (ws ++ [b]).getD ws.length false = b := by
    intro ws b; simp
  have fold_getD_lt : ∀ (ws : List Bool) (b : Bool) (i : ℕ), i < ws.length →
      (ws ++ [b]).getD i false = ws.getD i false := by
    intro ws b i hi; exact List.getD_append ws _ _ i hi
  have len_P : ∀ p l : Fin 13, (P p l).length = 26 := by intro p l; simp [P]
  have len_N : ∀ Q : Finset (Fin 13), (N Q).length = 26 := by intro Q; simp [N]
  have q0_good : good ({0, 1, 2, 5} : Finset (Fin 13)) := by decide
  have gate_op_cases : ∀ (g : Gate), (g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
      g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg; simpa using hg
  have norm_ind : ∀ (n : ℕ) (C : Circuit) (w1 w2 : ℕ),
      C.size = n → Monotone2 C → ReadsBack 26 C →
      w1 < 26 + C.size → w2 < 26 + C.size →
      (∀ p l : Fin 13, p - l ∈ D →
        (C.wires (P p l)).getD w1 false = true ∨ (C.wires (P p l)).getD w2 false = true) →
      (∀ Q : Finset (Fin 13), good Q →
        (C.wires (N Q)).getD w1 false = false ∧ (C.wires (N Q)).getD w2 false = false) →
      (∃ p l : Fin 13, p - l ∈ D ∧
        (C.wires (P p l)).getD w1 false = true ∧ (C.wires (P p l)).getD w2 false = false) →
      (∃ p l : Fin 13, p - l ∈ D ∧
        (C.wires (P p l)).getD w2 false = true ∧ (C.wires (P p l)).getD w1 false = false) →
      ∃ (C' : Circuit) (u1 u2 : ℕ),
        C'.size ≤ C.size ∧ PEqualNP.TopForm.IsAO2 26 C' ∧ (∀ g ∈ C'.gates, g.inputs.Nodup) ∧
        u1 < 26 + C'.size ∧ u2 < 26 + C'.size ∧
        (∀ p l : Fin 13, p - l ∈ D →
          (C'.wires (P p l)).getD u1 false = true ∨ (C'.wires (P p l)).getD u2 false = true) ∧
        (∀ Q : Finset (Fin 13), good Q →
          (C'.wires (N Q)).getD u1 false = false ∧ (C'.wires (N Q)).getD u2 false = false) ∧
        (∃ p l : Fin 13, p - l ∈ D ∧
          (C'.wires (P p l)).getD u1 false = true ∧ (C'.wires (P p l)).getD u2 false = false) ∧
        (∃ p l : Fin 13, p - l ∈ D ∧
          (C'.wires (P p l)).getD u2 false = true ∧ (C'.wires (P p l)).getD u1 false = false) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro C w1 w2 hn hMono hBack hw1 hw2 hCov hNeg hSep1 hSep2
      by_cases hgood : (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.Nodup)
      · refine ⟨C, w1, w2, le_rfl, ?_, fun g hg => (hgood g hg).2, hw1, hw2, hCov, hNeg, hSep1, hSep2⟩
        exact ⟨fun g hg => gate_op_cases g (hMono g hg).1, hBack, fun g hg => (hgood g hg).1⟩
      · push_neg at hgood
        obtain ⟨g0, hg0_mem, hg0_bad⟩ := hgood
        obtain ⟨m, hm_lt, hm_eq⟩ := List.mem_iff_getElem.mp hg0_mem
        have hm_mono := hMono g0 hg0_mem
        have hm_ops : g0.op = GateOp.and ∨ g0.op = GateOp.or := gate_op_cases g0 hm_mono.1
        have hm_back : ∀ i ∈ g0.inputs, i < 26 + m := by
          have hb := hBack m hm_lt
          have hgat : gateAt C m = g0 := by
            rw [gateAt_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm_lt, hm_eq]
            rfl
          rwa [hgat] at hb
        have hlen_le : g0.inputs.length ≤ 2 := hm_mono.2
        have hsplit : g0.inputs = [] ∨ ∃ a, a < 26 + m ∧ (g0.inputs = [a] ∨ g0.inputs = [a, a]) := by
          cases hgi : g0.inputs with
          | nil => exact Or.inl rfl
          | cons a t =>
            cases t with
            | nil => exact Or.inr ⟨a, hm_back a (by simp [hgi]), Or.inl rfl⟩
            | cons b t2 =>
              cases t2 with
              | nil =>
                have hab : a = b := by
                  by_contra hne
                  exact (hg0_bad (by simp [hgi])) (by simp [hgi, hne])
                subst hab
                exact Or.inr ⟨a, hm_back a (by simp [hgi]), Or.inr rfl⟩
              | cons c l =>
                simp [hgi] at hlen_le
        let pre := C.gates.take m
        let post := C.gates.drop (m + 1)
        have hdecomp : C.gates = pre ++ g0 :: post := by
          have h1 := List.take_append_drop m C.gates
          have h2 : C.gates.drop m = g0 :: post := by
            rw [List.drop_eq_getElem_cons hm_lt, hm_eq]
          rw [h2] at h1
          exact h1.symm
        have hpre_len : pre.length = m := List.length_take_of_le (Nat.le_of_lt hm_lt)
        have hpost_len : post.length = C.gates.length - (m + 1) := List.length_drop
        rcases hsplit with hnil | ⟨a, ha_lt, hrep⟩
        · let c : Bool := decide (g0.op = GateOp.and)
          have hgeval : g0.op.eval (g0.inputs.map fun _ => false) = c := by
            rw [hnil]
            rcases hm_ops with hop | hop <;> simp [c, hop, eval_and, eval_or]
          have hval_m : ∀ xs : List Bool, xs.length = 26 → (C.wires xs).getD (26 + m) false = c := by
            intro xs hxs
            change (C.gates.foldl step xs).getD (26 + m) false = c
            rw [hdecomp, List.foldl_append, List.foldl_cons]
            set ws1 := pre.foldl step xs
            have hlen1 : ws1.length = 26 + m := by rw [fold_len, hxs, hpre_len]
            rw [fold_prefix post _ (26 + m) (by simp [step]; omega)]
            have hstep : step ws1 g0 = ws1 ++ [c] := by
              simp only [step, hnil, List.map_nil]
              rcases hm_ops with hop | hop <;> simp [c, hop, eval_and, eval_or]
            rw [hstep, ← hlen1, fold_getD_snoc]
          have hw1_ne : w1 ≠ 26 + m := by
            intro heq; subst heq
            cases hc : c with
            | false =>
              obtain ⟨p, l, _, ht, _⟩ := hSep1
              rw [hval_m (P p l) (len_P p l), hc] at ht
              exact Bool.noConfusion ht
            | true =>
              have hf := (hNeg _ q0_good).1
              rw [hval_m (N _) (len_N _), hc] at hf
              exact Bool.noConfusion hf
          have hw2_ne : w2 ≠ 26 + m := by
            intro heq; subst heq
            cases hc : c with
            | false =>
              obtain ⟨p, l, _, ht, _⟩ := hSep2
              rw [hval_m (P p l) (len_P p l), hc] at ht
              exact Bool.noConfusion ht
            | true =>
              have hf := (hNeg _ q0_good).2
              rw [hval_m (N _) (len_N _), hc] at hf
              exact Bool.noConfusion hf
          let shift (i : ℕ) : ℕ := if 26 + m < i then i - 1 else i
          let constGate : Gate := ⟨if c then GateOp.and else GateOp.or, []⟩
          let rew (g : Gate) : Gate :=
            if (26 + m) ∈ g.inputs then
              if (g.op == GateOp.and && !c) || (g.op == GateOp.or && c) then
                constGate
              else
                ⟨g.op, (g.inputs.filter (fun i => decide (i ≠ 26 + m))).map shift⟩
            else
              ⟨g.op, g.inputs.map shift⟩
          let C' : Circuit := ⟨pre ++ post.map rew, 0⟩
          have hC'_len : C'.gates.length = C.gates.length - 1 := by
            simp only [C', List.length_append, List.length_map, hpre_len, hpost_len]
            omega
          have hC'_mono : Monotone2 C' := by
            intro g hg
            simp only [C', List.mem_append, List.mem_map] at hg
            rcases hg with hp | ⟨g', hg', rfl⟩
            · exact hMono g (by rw [hdecomp]; exact List.mem_append_left _ hp)
            · have hm' := hMono g' (by rw [hdecomp]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg'))
              dsimp only [rew]
              by_cases h1 : (26 + m) ∈ g'.inputs
              · rw [if_pos h1]
                by_cases h2 : ((g'.op == GateOp.and && !c) || (g'.op == GateOp.or && c)) = true
                · rw [if_pos h2]
                  constructor
                  · dsimp only [constGate]; cases c <;> simp
                  · simp [constGate]
                · rw [if_neg h2]
                  constructor
                  · exact hm'.1
                  · rw [List.length_map]
                    exact (List.length_filter_le _ _).trans hm'.2
              · rw [if_neg h1]
                constructor
                · exact hm'.1
                · rw [List.length_map]; exact hm'.2
          have hC'_back : ReadsBack 26 C' := by
            intro j hj i hi
            by_cases hjm : j < m
            · have hgat' : gateAt C' j = gateAt C j := by
                simp only [gateAt_def, C', List.getD_eq_getElem?_getD]
                rw [List.getElem?_append_left (by rw [hpre_len]; exact hjm)]
                rw [hdecomp, List.getElem?_append_left (by rw [hpre_len]; exact hjm)]
              rw [hgat'] at hi
              exact hBack j (by omega) i hi
            · have hj_ge : m ≤ j := Nat.le_of_not_lt hjm
              have hjp : j - m < post.length := by omega
              have hgat' : gateAt C' j = rew post[j - m] := by
                simp only [gateAt_def, C', List.getD_eq_getElem?_getD]
                rw [List.getElem?_append_right (by rw [hpre_len]; exact hj_ge)]
                rw [hpre_len, List.getElem?_map, List.getElem?_eq_getElem hjp]
                rfl
              have hgat : gateAt C (j + 1) = post[j - m] := by
                simp only [gateAt_def, List.getD_eq_getElem?_getD]
                rw [hdecomp, List.getElem?_append_right (by rw [hpre_len]; omega)]
                rw [hpre_len, show j + 1 - m = (j - m) + 1 by omega, List.getElem?_cons_succ]
                rw [List.getElem?_eq_getElem hjp]
                rfl
              have hb_old := hBack (j + 1) (by omega)
              rw [hgat] at hb_old
              rw [hgat'] at hi
              dsimp only [rew] at hi
              by_cases h1 : (26 + m) ∈ post[j - m].inputs
              · rw [if_pos h1] at hi
                by_cases h2 : ((post[j - m].op == GateOp.and && !c) || (post[j - m].op == GateOp.or && c)) = true
                · rw [if_pos h2] at hi
                  simp [constGate] at hi
                · rw [if_neg h2] at hi
                  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hi
                  obtain ⟨i0, ⟨hi0_mem, hi0_ne⟩, rfl⟩ := hi
                  have hlt := hb_old i0 hi0_mem
                  dsimp only [shift]
                  split_ifs <;> omega
              · rw [if_neg h1] at hi
                simp only [List.mem_map] at hi
                obtain ⟨i0, hi0_mem, rfl⟩ := hi
                have hlt := hb_old i0 hi0_mem
                have hi0_ne : i0 ≠ 26 + m := fun e => h1 (e ▸ hi0_mem)
                dsimp only [shift]
                split_ifs <;> omega
          have hsim : ∀ (xs : List Bool), xs.length = 26 →
              ∀ (ps : List Gate) (ws ws' : List Bool),
                (∀ g ∈ ps, g.op = GateOp.and ∨ g.op = GateOp.or) →
                ws.length = ws'.length + 1 →
                26 + m < ws.length →
                ws.getD (26 + m) false = c →
                (∀ k, k ≠ 26 + m → ws'.getD (shift k) false = ws.getD k false) →
                ∀ k, k ≠ 26 + m →
                  ((ps.map rew).foldl step ws').getD (shift k) false = (ps.foldl step ws).getD k false := by
            intro xs _ ps
            induction ps with
            | nil => intro ws ws' _ _ _ _ hagree k hk; exact hagree k hk
            | cons g ps ih =>
              intro ws ws' hops hlen hmlt hmc hagree k hk
              simp only [List.map_cons, List.foldl_cons]
              have hg_op := hops g List.mem_cons_self
              have hval_eq : (rew g).op.eval ((rew g).inputs.map fun i => ws'.getD i false) =
                  g.op.eval (g.inputs.map fun i => ws.getD i false) := by
                dsimp only [rew]
                by_cases h1 : (26 + m) ∈ g.inputs
                · rw [if_pos h1]
                  by_cases h2 : ((g.op == GateOp.and && !c) || (g.op == GateOp.or && c)) = true
                  · rw [if_pos h2]
                    have hcases : (g.op = GateOp.and ∧ c = false) ∨ (g.op = GateOp.or ∧ c = true) := by
                      rcases hg_op with hop | hop <;> cases hc : c <;> simp [hop, hc] at h2 ⊢
                    rcases hcases with ⟨hop, hc⟩ | ⟨hop, hc⟩
                    · dsimp only [constGate]
                      rw [hop, hc]
                      simp only [Bool.false_eq_true, ↓reduceIte, eval_and, eval_or, List.map_nil, List.any_nil]
                      symm
                      rw [List.all_eq_false]
                      exact ⟨false, List.mem_map.mpr ⟨26 + m, h1, by rw [hmc, hc]⟩, by decide⟩
                    · dsimp only [constGate]
                      rw [hop, hc]
                      simp only [↓reduceIte, eval_and, eval_or, List.map_nil, List.all_nil]
                      symm
                      rw [List.any_eq_true]
                      exact ⟨true, List.mem_map.mpr ⟨26 + m, h1, by rw [hmc, hc]⟩, rfl⟩
                  · rw [if_neg h2]
                    have hcases : (g.op = GateOp.and ∧ c = true) ∨ (g.op = GateOp.or ∧ c = false) := by
                      rcases hg_op with hop | hop <;> cases hc : c <;> simp [hop, hc] at h2 ⊢
                    rcases hcases with ⟨hop, hc⟩ | ⟨hop, hc⟩
                    · rw [hop]
                      simp only [eval_and, List.map_map, List.all_map, Function.comp_def, id_eq]
                      apply Bool.eq_iff_iff.mpr
                      simp only [List.all_eq_true, List.mem_filter, decide_eq_true_eq]
                      constructor
                      · intro h i hi
                        by_cases him : i = 26 + m
                        · subst him; rw [hmc, hc]
                        · rw [← hagree i him]; exact h i ⟨hi, him⟩
                      · intro h i hmem
                        rw [hagree i hmem.2]; exact h i hmem.1
                    · rw [hop]
                      simp only [eval_or, List.map_map, List.any_map, Function.comp_def, id_eq]
                      apply Bool.eq_iff_iff.mpr
                      simp only [List.any_eq_true, List.mem_filter, decide_eq_true_eq]
                      constructor
                      · rintro ⟨i, ⟨hi, him⟩, hv⟩
                        exact ⟨i, hi, (hagree i him).symm.trans hv⟩
                      · rintro ⟨i, hi, hv⟩
                        have him : i ≠ 26 + m := by
                          intro e; subst e; rw [hmc, hc] at hv; exact Bool.noConfusion hv
                        exact ⟨i, ⟨hi, him⟩, (hagree i him).trans hv⟩
                · rw [if_neg h1]
                  congr 1
                  rw [List.map_map]
                  apply List.map_congr_left
                  intro i hi
                  have him : i ≠ 26 + m := fun e => h1 (e ▸ hi)
                  exact hagree i him
              apply ih (step ws g) (step ws' (rew g))
                (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
                (by simp [step]; omega)
                (by simp [step]; omega)
                (by rw [fold_getD_lt _ _ _ hmlt]; exact hmc)
                ?_ k hk
              intro j hj
              by_cases hjl : j < ws.length
              · have hjl' : shift j < ws'.length := by
                  dsimp only [shift]; split_ifs <;> omega
                rw [fold_getD_lt _ _ _ hjl', fold_getD_lt _ _ _ hjl]
                exact hagree j hj
              · by_cases hje : j = ws.length
                · subst hje
                  have hje' : shift ws.length = ws'.length := by
                    dsimp only [shift]; split_ifs <;> omega
                  simp only [step]
                  rw [hje', fold_getD_snoc, fold_getD_snoc]
                  exact hval_eq
                · have hgt : ws.length < j := by omega
                  have hgt' : ws'.length < shift j := by
                    dsimp only [shift]; split_ifs <;> omega
                  simp only [step]
                  rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          have hwire_eq : ∀ (xs : List Bool), xs.length = 26 → ∀ k, k ≠ 26 + m →
              (C'.wires xs).getD (shift k) false = (C.wires xs).getD k false := by
            intro xs hxs k hk
            change ((pre ++ post.map rew).foldl step xs).getD (shift k) false =
              (C.gates.foldl step xs).getD k false
            rw [List.foldl_append, hdecomp, List.foldl_append, List.foldl_cons]
            set ws' := pre.foldl step xs
            have hlen' : ws'.length = 26 + m := by rw [fold_len, hxs, hpre_len]
            have hstep : step ws' g0 = ws' ++ [c] := by
              simp only [step, hnil, List.map_nil]
              rcases hm_ops with hop | hop <;> simp [c, hop, eval_and, eval_or]
            apply hsim xs hxs post (step ws' g0) ws'
              (fun g' hg' => gate_op_cases g' (hMono g' (by rw [hdecomp]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg'))).1)
              (by rw [hstep]; simp)
              (by rw [hstep]; simp; omega)
              (by rw [hstep, ← hlen', fold_getD_snoc])
              ?_ k hk
            intro j hj
            by_cases hlt : j < 26 + m
            · have hsj : shift j = j := by dsimp only [shift]; split_ifs <;> omega
              rw [hsj, hstep, fold_getD_lt _ _ _ (by omega)]
            · have hgt : 26 + m < j := by omega
              have hge1 : ws'.length ≤ shift j := by dsimp only [shift]; split_ifs <;> omega
              have hge2 : (step ws' g0).length ≤ j := by rw [hstep]; simp; omega
              rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]
          have hsz_lt : C'.size < n := by
            change C'.gates.length < n
            change C.gates.length = n at hn
            omega
          have hw1' : shift w1 < 26 + C'.size := by
            change shift w1 < 26 + C'.gates.length
            change w1 < 26 + C.gates.length at hw1
            dsimp only [shift]; split_ifs <;> omega
          have hw2' : shift w2 < 26 + C'.size := by
            change shift w2 < 26 + C'.gates.length
            change w2 < 26 + C.gates.length at hw2
            dsimp only [shift]; split_ifs <;> omega
          obtain ⟨C'', u1, u2, hsz'', hAO'', hnd'', hu1'', hu2'', hCov'', hNeg'', hSep1'', hSep2''⟩ :=
            ih C'.size hsz_lt C' (shift w1) (shift w2) rfl hC'_mono hC'_back hw1' hw2'
              (fun p l hpl => by
                rw [hwire_eq (P p l) (len_P p l) w1 hw1_ne, hwire_eq (P p l) (len_P p l) w2 hw2_ne]
                exact hCov p l hpl)
              (fun Q hQ => by
                rw [hwire_eq (N Q) (len_N Q) w1 hw1_ne, hwire_eq (N Q) (len_N Q) w2 hw2_ne]
                exact hNeg Q hQ)
              (by
                obtain ⟨p, l, hpl, ht, hf⟩ := hSep1
                exact ⟨p, l, hpl, (hwire_eq (P p l) (len_P p l) w1 hw1_ne).trans ht,
                  (hwire_eq (P p l) (len_P p l) w2 hw2_ne).trans hf⟩)
              (by
                obtain ⟨p, l, hpl, ht, hf⟩ := hSep2
                exact ⟨p, l, hpl, (hwire_eq (P p l) (len_P p l) w2 hw2_ne).trans ht,
                  (hwire_eq (P p l) (len_P p l) w1 hw1_ne).trans hf⟩)
          exact ⟨C'', u1, u2, by change C''.gates.length ≤ C.gates.length; change C''.gates.length ≤ C'.gates.length at hsz''; omega,
            hAO'', hnd'', hu1'', hu2'', hCov'', hNeg'', hSep1'', hSep2''⟩
        · let redir (i : ℕ) : ℕ := if i = 26 + m then a else if 26 + m < i then i - 1 else i
          let rew (g : Gate) : Gate := ⟨g.op, g.inputs.map redir⟩
          let C' : Circuit := ⟨pre ++ post.map rew, 0⟩
          have hC'_len : C'.gates.length = C.gates.length - 1 := by
            simp only [C', List.length_append, List.length_map, hpre_len, hpost_len]
            omega
          have hC'_mono : Monotone2 C' := by
            intro g hg
            simp only [C', List.mem_append, List.mem_map] at hg
            rcases hg with hp | ⟨g', hg', rfl⟩
            · exact hMono g (by rw [hdecomp]; exact List.mem_append_left _ hp)
            · have hm' := hMono g' (by rw [hdecomp]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg'))
              exact ⟨hm'.1, by simpa [rew] using hm'.2⟩
          have hC'_back : ReadsBack 26 C' := by
            intro j hj i hi
            by_cases hjm : j < m
            · have hgat' : gateAt C' j = gateAt C j := by
                simp only [gateAt_def, C', List.getD_eq_getElem?_getD]
                rw [List.getElem?_append_left (by rw [hpre_len]; exact hjm)]
                rw [hdecomp, List.getElem?_append_left (by rw [hpre_len]; exact hjm)]
              rw [hgat'] at hi
              exact hBack j (by omega) i hi
            · have hj_ge : m ≤ j := Nat.le_of_not_lt hjm
              have hjp : j - m < post.length := by omega
              have hgat' : gateAt C' j = rew post[j - m] := by
                simp only [gateAt_def, C', List.getD_eq_getElem?_getD]
                rw [List.getElem?_append_right (by rw [hpre_len]; exact hj_ge)]
                rw [hpre_len, List.getElem?_map, List.getElem?_eq_getElem hjp]
                rfl
              have hgat : gateAt C (j + 1) = post[j - m] := by
                simp only [gateAt_def, List.getD_eq_getElem?_getD]
                rw [hdecomp, List.getElem?_append_right (by rw [hpre_len]; omega)]
                rw [hpre_len, show j + 1 - m = (j - m) + 1 by omega, List.getElem?_cons_succ]
                rw [List.getElem?_eq_getElem hjp]
                rfl
              have hb_old := hBack (j + 1) (by omega)
              rw [hgat] at hb_old
              rw [hgat'] at hi
              simp only [rew, List.mem_map] at hi
              obtain ⟨i0, hi0_mem, rfl⟩ := hi
              have hlt := hb_old i0 hi0_mem
              dsimp only [redir]
              split_ifs <;> omega
          have hsim : ∀ (ps : List Gate) (ws ws' : List Bool),
              ws.length = ws'.length + 1 →
              26 + m < ws.length →
              (∀ k, ws'.getD (redir k) false = ws.getD k false) →
              ∀ k, ((ps.map rew).foldl step ws').getD (redir k) false = (ps.foldl step ws).getD k false := by
            intro ps
            induction ps with
            | nil => intro ws ws' _ _ hagree k; exact hagree k
            | cons g ps ih =>
              intro ws ws' hlen hmlt hagree k
              simp only [List.map_cons, List.foldl_cons]
              have hval_eq : (rew g).op.eval ((rew g).inputs.map fun i => ws'.getD i false) =
                  g.op.eval (g.inputs.map fun i => ws.getD i false) := by
                dsimp only [rew]
                congr 1
                rw [List.map_map]
                apply List.map_congr_left
                intro i _
                exact hagree i
              apply ih (step ws g) (step ws' (rew g))
                (by simp [step]; omega)
                (by simp [step]; omega)
                ?_ k
              intro j
              by_cases hjl : j < ws.length
              · have hjl' : redir j < ws'.length := by
                  dsimp only [redir]; split_ifs <;> omega
                rw [fold_getD_lt _ _ _ hjl', fold_getD_lt _ _ _ hjl]
                exact hagree j
              · by_cases hje : j = ws.length
                · subst hje
                  have hje' : redir ws.length = ws'.length := by
                    dsimp only [redir]; split_ifs <;> omega
                  simp only [step]
                  rw [hje', fold_getD_snoc, fold_getD_snoc]
                  exact hval_eq
                · have hgt : ws.length < j := by omega
                  have hgt' : ws'.length < redir j := by
                    dsimp only [redir]; split_ifs <;> omega
                  simp only [step]
                  rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          have hwire_eq : ∀ (xs : List Bool), xs.length = 26 → ∀ k,
              (C'.wires xs).getD (redir k) false = (C.wires xs).getD k false := by
            intro xs hxs k
            change ((pre ++ post.map rew).foldl step xs).getD (redir k) false =
              (C.gates.foldl step xs).getD k false
            rw [List.foldl_append, hdecomp, List.foldl_append, List.foldl_cons]
            set ws' := pre.foldl step xs
            have hlen' : ws'.length = 26 + m := by rw [fold_len, hxs, hpre_len]
            have hstep : step ws' g0 = ws' ++ [ws'.getD a false] := by
              simp only [step]
              rcases hrep with h | h <;> rw [h] <;> rcases hm_ops with hop | hop <;>
                simp [hop, eval_and, eval_or]
            apply hsim post (step ws' g0) ws'
              (by rw [hstep]; simp)
              (by rw [hstep]; simp; omega)
              ?_ k
            intro j
            by_cases hj : j = 26 + m
            · subst hj
              have hr : redir (26 + m) = a := by simp [redir]
              rw [hr, hstep, ← hlen', fold_getD_snoc]
            · by_cases hlt : j < 26 + m
              · have hr : redir j = j := by dsimp only [redir]; split_ifs <;> omega
                rw [hr, hstep, fold_getD_lt _ _ _ (by omega)]
              · have hgt : 26 + m < j := by omega
                have hge1 : ws'.length ≤ redir j := by dsimp only [redir]; split_ifs <;> omega
                have hge2 : (step ws' g0).length ≤ j := by rw [hstep]; simp; omega
                rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]
          have hsz_lt : C'.size < n := by
            change C'.gates.length < n
            change C.gates.length = n at hn
            omega
          have hw1' : redir w1 < 26 + C'.size := by
            change redir w1 < 26 + C'.gates.length
            change w1 < 26 + C.gates.length at hw1
            dsimp only [redir]; split_ifs <;> omega
          have hw2' : redir w2 < 26 + C'.size := by
            change redir w2 < 26 + C'.gates.length
            change w2 < 26 + C.gates.length at hw2
            dsimp only [redir]; split_ifs <;> omega
          obtain ⟨C'', u1, u2, hsz'', hAO'', hnd'', hu1'', hu2'', hCov'', hNeg'', hSep1'', hSep2''⟩ :=
            ih C'.size hsz_lt C' (redir w1) (redir w2) rfl hC'_mono hC'_back hw1' hw2'
              (fun p l hpl => by
                rw [hwire_eq (P p l) (len_P p l) w1, hwire_eq (P p l) (len_P p l) w2]
                exact hCov p l hpl)
              (fun Q hQ => by
                rw [hwire_eq (N Q) (len_N Q) w1, hwire_eq (N Q) (len_N Q) w2]
                exact hNeg Q hQ)
              (by
                obtain ⟨p, l, hpl, ht, hf⟩ := hSep1
                exact ⟨p, l, hpl, (hwire_eq (P p l) (len_P p l) w1).trans ht,
                  (hwire_eq (P p l) (len_P p l) w2).trans hf⟩)
              (by
                obtain ⟨p, l, hpl, ht, hf⟩ := hSep2
                exact ⟨p, l, hpl, (hwire_eq (P p l) (len_P p l) w2).trans ht,
                  (hwire_eq (P p l) (len_P p l) w1).trans hf⟩)
          exact ⟨C'', u1, u2, by change C''.gates.length ≤ C.gates.length; change C''.gates.length ≤ C'.gates.length at hsz''; omega,
            hAO'', hnd'', hu1'', hu2'', hCov'', hNeg'', hSep1'', hSep2''⟩
  obtain ⟨C, u1, u2, hsz_le, hAO, hnd, hu1, hu2, hCov, hNeg, hSep1, hSep2⟩ :=
    norm_ind C0.size C0 w10 w20 rfl hMono0 hBack0 hw10 hw20 hCov0 hNeg0 hSep10 hSep20
  have no_input : ∀ u : ℕ, (∀ Q : Finset (Fin 13), good Q → (C.wires (N Q)).getD u false = false) → 26 ≤ u := by
    intro u hu
    by_contra hlt
    have hlt26 : u < 26 := Nat.lt_of_not_ge hlt
    by_cases h13 : u < 13
    · let p : Fin 13 := ⟨u, h13⟩
      have hne : p - (p + 2) ∉ D := (by decide : ∀ x : Fin 13, x - (x + 2) ∉ D) p
      obtain ⟨Q, hQc, hQl, hpQ, _⟩ := h_oval p (p + 2) hne
      have hf := hu Q ⟨hQc, hQl⟩
      change (C.gates.foldl step (N Q)).getD u false = false at hf
      rw [fold_prefix C.gates (N Q) u (by rw [len_N]; exact hlt26)] at hf
      have htrue : (N Q).getD u false = true := by
        rw [List.getD_eq_getElem?_getD]
        dsimp only [N]
        rw [List.getElem?_append_left (by simp [h13])]
        rw [List.getElem?_eq_getElem (by simp [h13]), List.getElem_ofFn]
        simp only [Option.getD_some, decide_eq_true_eq]
        exact hpQ
      rw [htrue] at hf
      exact Bool.noConfusion hf
    · let l : Fin 13 := ⟨u - 13, by omega⟩
      have hne : (l + 2) - l ∉ D := (by decide : ∀ x : Fin 13, (x + 2) - x ∉ D) l
      obtain ⟨Q, hQc, hQl, _, hlQ⟩ := h_oval (l + 2) l hne
      have hf := hu Q ⟨hQc, hQl⟩
      change (C.gates.foldl step (N Q)).getD u false = false at hf
      rw [fold_prefix C.gates (N Q) u (by rw [len_N]; exact hlt26)] at hf
      have htrue : (N Q).getD u false = true := by
        have hge : 13 ≤ u := Nat.le_of_not_lt h13
        rw [List.getD_eq_getElem?_getD]
        dsimp only [N]
        rw [List.getElem?_append_right (by simp [hge])]
        simp only [List.length_ofFn]
        rw [List.getElem?_eq_getElem (by simp; omega), List.getElem_ofFn]
        simp only [Option.getD_some, decide_eq_true_eq]
        exact hlQ
      rw [htrue] at hf
      exact Bool.noConfusion hf
  have hu1_ge : 26 ≤ u1 := no_input u1 (fun Q hQ => (hNeg Q hQ).1)
  have hu2_ge : 26 ≤ u2 := no_input u2 (fun Q hQ => (hNeg Q hQ).2)
  have hu_ne : u1 ≠ u2 := by
    intro heq; subst heq
    obtain ⟨p, l, _, ht, hf⟩ := hSep1
    rw [ht] at hf; exact Bool.noConfusion hf
  let R (x y : Bool) : Prop := x = true → y = true
  have readMono : ∀ {x y : List Bool}, List.Forall₂ R x y → ∀ i : ℕ, R (x.getD i false) (y.getD i false) := by
    intro x y rel
    induction rel with
    | nil => intro i; simp [List.getD, R]
    | cons h _ ih => intro i; cases i with | zero => exact h | succ j => exact ih j
  have foldMono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ {x y : List Bool}, List.Forall₂ R x y → List.Forall₂ R (gs.foldl step x) (gs.foldl step y) := by
    intro gs
    induction gs with
    | nil => intro _ x y rel; exact rel
    | cons g gs ih =>
      intro ops x y rel
      apply ih (fun k hk => ops k (List.mem_cons_of_mem _ hk))
      apply List.rel_append rel
      apply List.Forall₂.cons _ List.Forall₂.nil
      rcases ops g (by simp) with hand | hor
      · rw [hand]
        change (g.inputs.map (fun i => x.getD i false)).all id = true →
          (g.inputs.map (fun i => y.getD i false)).all id = true
        simp only [List.all_map, Function.comp_def, List.all_eq_true, id_eq]
        intro hx i hi
        exact readMono rel i (hx i hi)
      · rw [hor]
        change (g.inputs.map (fun i => x.getD i false)).any id = true →
          (g.inputs.map (fun i => y.getD i false)).any id = true
        simp only [List.any_map, Function.comp_def, List.any_eq_true, id_eq]
        rintro ⟨i, hi, hx⟩
        exact ⟨i, hi, readMono rel i hx⟩
  let E : Circuit := ⟨C.gates ++ [⟨GateOp.or, [u1, u2]⟩], 26 + C.size⟩
  have hE_AO : PEqualNP.TopForm.IsAO2 26 E := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [E, List.mem_append, List.mem_singleton] at hg
      rcases hg with hc | rfl
      · exact hAO.1 g hc
      · exact Or.inr rfl
    · intro j hj i hi
      simp only [E, List.length_append, List.length_singleton] at hj
      by_cases hjc : j < C.gates.length
      · have hgat : gateAt E j = gateAt C j := by
          simp [gateAt_def, E, List.getD_eq_getElem?_getD, List.getElem?_append_left hjc]
        rw [hgat] at hi
        exact hAO.2.1 j hjc i hi
      · have hje : j = C.gates.length := by omega
        subst hje
        have hgat : gateAt E C.gates.length = ⟨GateOp.or, [u1, u2]⟩ := by
          simp [gateAt_def, E, List.getD_eq_getElem?_getD]
        rw [hgat] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hu1
        · exact hu2
    · intro g hg
      simp only [E, List.mem_append, List.mem_singleton] at hg
      rcases hg with hc | rfl
      · exact hAO.2.2 g hc
      · rfl
  have hE_nd : ∀ g ∈ E.gates, g.inputs.Nodup := by
    intro g hg
    simp only [E, List.mem_append, List.mem_singleton] at hg
    rcases hg with hc | rfl
    · exact hnd g hc
    · simp [hu_ne]
  have hE_wires_old : ∀ (xs : List Bool), xs.length = 26 → ∀ u, u < 26 + C.size →
      (E.wires xs).getD u false = (C.wires xs).getD u false := by
    intro xs hxs u hu
    change ((C.gates ++ [(⟨GateOp.or, [u1, u2]⟩ : Gate)]).foldl step xs).getD u false =
      (C.gates.foldl step xs).getD u false
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    apply fold_getD_lt
    rw [fold_len, hxs]; exact hu
  have hE_eval : ∀ (xs : List Bool), xs.length = 26 →
      E.eval xs = ((C.wires xs).getD u1 false || (C.wires xs).getD u2 false) := by
    intro xs hxs
    change ((C.gates ++ [(⟨GateOp.or, [u1, u2]⟩ : Gate)]).foldl step xs).getD (26 + C.size) false = _
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set ws := C.gates.foldl step xs
    have hlen : ws.length = 26 + C.size := by rw [fold_len, hxs]; rfl
    simp only [step, eval_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [← hlen, fold_getD_snoc]
    rfl
  have hE_pairs : ∀ p l : Fin 13, E.eval (P p l) = decide (p - l ∈ D) := by
    intro p l
    rw [hE_eval (P p l) (len_P p l)]
    by_cases hpl : p - l ∈ D
    · rw [decide_eq_true hpl, Bool.or_eq_true]
      exact hCov p l hpl
    · rw [decide_eq_false hpl, Bool.or_eq_false_iff]
      obtain ⟨Q, hQc, hQl, hpQ, hlQ⟩ := h_oval p l hpl
      have hrel : List.Forall₂ R (P p l) (N Q) := by
        apply List.rel_append
        · apply List.forall₂_of_length_eq_of_get (by simp)
          intro i hi _
          have hb : i < 13 := by simpa using hi
          simp only [R, List.get_eq_getElem, List.getElem_ofFn, decide_eq_true_eq]
          intro h; rw [h]; exact hpQ
        · apply List.forall₂_of_length_eq_of_get (by simp)
          intro i hi _
          have hb : i < 13 := by simpa using hi
          simp only [R, List.get_eq_getElem, List.getElem_ofFn, decide_eq_true_eq]
          intro h; rw [h]; exact hlQ
      have hm := foldMono C.gates hAO.1 hrel
      obtain ⟨hf1, hf2⟩ := hNeg Q ⟨hQc, hQl⟩
      constructor
      · exact Bool.eq_false_iff.mpr fun ht => Bool.noConfusion ((readMono hm u1 ht).symm.trans hf1)
      · exact Bool.eq_false_iff.mpr fun ht => Bool.noConfusion ((readMono hm u2 ht).symm.trans hf2)
  have hE_neg : ∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ l : Fin 13, (Q.filter fun p => p - l ∈ D).card ≤ 2) → E.eval (N Q) = false := by
    intro Q hQc hQl
    rw [hE_eval (N Q) (len_N Q), Bool.or_eq_false_iff]
    exact hNeg Q ⟨hQc, hQl⟩
  have hE_gate : E.gates[C.size]? = some ⟨GateOp.or, [u1, u2]⟩ := by
    simp [E, size_def]
  have hE_sep1 : ∃ p l : Fin 13, p - l ∈ D ∧
      (E.wires (P p l)).getD u1 false = true ∧ (E.wires (P p l)).getD u2 false = false := by
    obtain ⟨p, l, hpl, ht, hf⟩ := hSep1
    exact ⟨p, l, hpl, (hE_wires_old (P p l) (len_P p l) u1 hu1).trans ht,
      (hE_wires_old (P p l) (len_P p l) u2 hu2).trans hf⟩
  have hE_sep2 : ∃ p l : Fin 13, p - l ∈ D ∧
      (E.wires (P p l)).getD u2 false = true ∧ (E.wires (P p l)).getD u1 false = false := by
    obtain ⟨p, l, hpl, ht, hf⟩ := hSep2
    exact ⟨p, l, hpl, (hE_wires_old (P p l) (len_P p l) u2 hu2).trans ht,
      (hE_wires_old (P p l) (len_P p l) u1 hu1).trans hf⟩
  have h64 := h_strict E C.size u1 u2 hE_AO hE_nd rfl hE_gate hu1_ge hu2_ge hE_pairs hE_neg hE_sep1 hE_sep2
  have hE_sz : E.size = C.size + 1 := by simp [E, size_def]
  omega
