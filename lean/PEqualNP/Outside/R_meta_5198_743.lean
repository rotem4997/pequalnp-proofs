import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.Represents

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5198_743
    (hElimQuadAnd :
      let S : Fin 13 → Finset (Fin 13) := PEqualNP.HeptadCover.singerLines3
      let qIn : Finset (Fin 13) → List Bool := fun Q =>
        (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
        (List.ofFn fun l : Fin 13 => decide (l ∈ PEqualNP.HeptadCover.missLines S Q))
      let aa : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun C j =>
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
          26 ≤ i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (i - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 D →
        PEqualNP.Represents.Represents (fun p l : Fin 13 => decide (p ∈ S l)) D →
        (∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle S Q → D.eval (qIn Q) = false) →
        (∀ j < D.size, ∀ k < D.size, aa D j → aa D k → j = k) →
        ∃ E : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 E ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 E ∧
          E.size ≤ D.size ∧
          PEqualNP.Represents.Represents (fun p l : Fin 13 => decide (p ∈ S l)) E ∧
          (∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle S Q → E.eval (qIn Q) = false) ∧
          (∀ j < E.size, (PEqualNP.MetaComplexity.NestedCover.gateAt E j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            ∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle S Q → (E.wires (qIn Q)).getD (26 + j) false = false))
    (hCleanBound :
      let S : Fin 13 → Finset (Fin 13) := PEqualNP.HeptadCover.singerLines3
      let qIn : Finset (Fin 13) → List Bool := fun Q =>
        (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
        (List.ofFn fun l : Fin 13 => decide (l ∈ PEqualNP.HeptadCover.missLines S Q))
      ∀ E : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 E →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 E →
        PEqualNP.Represents.Represents (fun p l : Fin 13 => decide (p ∈ S l)) E →
        (∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle S Q → E.eval (qIn Q) = false) →
        (∀ j < E.size, (PEqualNP.MetaComplexity.NestedCover.gateAt E j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle S Q → (E.wires (qIn Q)).getD (26 + j) false = false) →
        64 ≤ E.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
    have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool :=
      fun (x2 x3 : Finset (Fin (13 : ℕ))) =>
        (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++
        List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);
    have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool :=
      fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false;
    have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate :=
      PEqualNP.MetaComplexity.NestedCover.gateAt;
    have x5 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;
    have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop :=
      fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) =>
        (x4 x6 x7).op = x5 ∧ ∃ x8 ∈ (x4 x6 x7).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x6 (x8 - (26 : ℕ))).op = x5;
    ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 x9 : ℕ),
      PEqualNP.MetaComplexity.Monotone2 x7 →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 →
      x8 < (26 : ℕ) + x7.size →
      x9 < (26 : ℕ) + x7.size →
      (∀ (x14 x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 →
        x3 x7 x8 (x2 {x14} {x15}) = Bool.true ∨ x3 x7 x9 (x2 {x14} {x15}) = Bool.true) →
      (∀ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x15 →
        x3 x7 x8 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false ∧
        x3 x7 x9 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false) →
      (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 ∈ x1 x17 ∧
        x3 x7 x8 (x2 {x16} {x17}) = Bool.true ∧ x3 x7 x9 (x2 {x16} {x17}) = Bool.false) →
      (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 ∈ x1 x18 ∧
        x3 x7 x9 (x2 {x17} {x18}) = Bool.true ∧ x3 x7 x8 (x2 {x17} {x18}) = Bool.false) →
      (∀ x18 ∈ Finset.range x7.size, ∀ x20 ∈ Finset.range x7.size, x6 x7 x18 → x6 x7 x20 → x18 = x20) →
      (63 : ℕ) ≤ x7.size := by
  intro S X W G A aa C a b hM hRB ha hb hpos hquad _ _ haa
  let run : List Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have hrun_snoc : ∀ (gs : List Gate) (g : Gate) (x : List Bool),
      run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
    intro gs g x
    change (gs ++ [g]).foldl _ x = _
    rw [List.foldl_append]
    rfl
  have hrun_len : ∀ (gs : List Gate) (x : List Bool), (run gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton gs g ih =>
      rw [hrun_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
      omega
  have hgetD_lt : ∀ (l : List Bool) (v : Bool) (t : ℕ), t < l.length →
      (l ++ [v]).getD t false = l.getD t false := by
    intro l v t ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]
  have hgetD_at : ∀ (l : List Bool) (v : Bool), (l ++ [v]).getD l.length false = v := by
    intro l v
    simp [List.getD_eq_getElem?_getD]
  have hrun_prefix : ∀ (gs hs : List Gate) (x : List Bool) (i : ℕ), i < x.length + gs.length →
      (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
    intro gs hs x i hi
    induction hs using List.reverseRecOn with
    | nil => rw [List.append_nil]
    | append_singleton hs g ih =>
      rw [← List.append_assoc, hrun_snoc, hgetD_lt _ _ _ (by rw [hrun_len, List.length_append]; omega), ih]
  have hrun_input : ∀ (gs : List Gate) (x : List Bool) (i : ℕ), i < x.length →
      (run gs x).getD i false = x.getD i false := by
    intro gs x i hi
    have h1 := hrun_prefix [] gs x i (by rw [List.length_nil, Nat.add_zero]; exact hi)
    rw [List.nil_append] at h1
    exact h1
  have hrun_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ (x y : List Bool), x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ w, (run gs x).getD w false = true → (run gs y).getD w false = true := by
    intro gs hgs x y hxy hle
    induction gs using List.reverseRecOn with
    | nil => intro w hw; exact hle w hw
    | append_singleton gs g ih =>
      intro w hw
      have ih' := ih (fun g' hg' => hgs g' (List.mem_append_left _ hg'))
      have l1 := hrun_len gs x
      have l2 := hrun_len gs y
      rw [hrun_snoc] at hw ⊢
      rcases Nat.lt_trichotomy w (x.length + gs.length) with hlt | heq | hgt
      · rw [hgetD_lt _ _ _ (by omega)] at hw
        rw [hgetD_lt _ _ _ (by omega)]
        exact ih' w hw
      · have e1 : w = (run gs x).length := by omega
        have e2 : w = (run gs y).length := by omega
        rw [e1, hgetD_at] at hw
        rw [e2, hgetD_at]
        rcases hgs g (List.mem_append_right _ (List.mem_singleton_self g)) with hop | hop
        · rw [hop] at hw ⊢
          change (g.inputs.map fun i => (run gs x).getD i false).all id = true at hw
          change (g.inputs.map fun i => (run gs y).getD i false).all id = true
          rw [List.all_map, List.all_eq_true] at hw ⊢
          intro q hq
          exact ih' q (hw q hq)
        · rw [hop] at hw ⊢
          change (g.inputs.map fun i => (run gs x).getD i false).any id = true at hw
          change (g.inputs.map fun i => (run gs y).getD i false).any id = true
          rw [List.any_map, List.any_eq_true] at hw ⊢
          rcases hw with ⟨q, hq1, hq2⟩
          exact ⟨q, hq1, ih' q hq2⟩
      · exfalso
        have hdef : (run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)]).getD w false = false :=
          List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)
        rw [hdef] at hw
        exact Bool.false_ne_true hw
  have hQ0_quad : ∀ c : Fin 13,
      IsQuadrangle singerLines3 ({c, c + 1, c + 2, c + 11} : Finset (Fin 13)) := by
    decide +kernel
  have hQ0_noninc : ∀ p l : Fin 13, p ∉ singerLines3 l →
      ∃ c : Fin 13, p ∈ ({c, c + 1, c + 2, c + 11} : Finset (Fin 13)) ∧
        l ∈ missLines singerLines3 ({c, c + 1, c + 2, c + 11} : Finset (Fin 13)) := by
    decide +kernel
  have hQ0_pts : ∀ p : Fin 13, p ∈ ({p, p + 1, p + 2, p + 11} : Finset (Fin 13)) := by
    intro p; exact Finset.mem_insert_self p _
  have hQ0_lines : ∀ l : Fin 13, ∃ c : Fin 13,
      l ∈ missLines singerLines3 ({c, c + 1, c + 2, c + 11} : Finset (Fin 13)) := by
    decide +kernel
  have hX_len : ∀ P L : Finset (Fin 13), (X P L).length = 26 := by
    intro P L
    change ((List.ofFn fun q : Fin 13 => decide (q ∈ P)) ++
      (List.ofFn fun q : Fin 13 => decide (q ∈ L))).length = 26
    rw [List.length_append, List.length_ofFn, List.length_ofFn]
  have hge26 : ∀ w : ℕ, (∀ Q : Finset (Fin 13), IsQuadrangle S Q → W C w (X Q (missLines S Q)) = false) → 26 ≤ w := by
    intro w hw
    by_contra hlt
    have hw26 : w < 26 := by omega
    by_cases hw13 : w < 13
    · let p : Fin 13 := ⟨w, hw13⟩
      let Q : Finset (Fin 13) := {p, p + 1, p + 2, p + 11}
      have hQ : IsQuadrangle S Q := hQ0_quad p
      have hval := hw Q hQ
      change (run C.gates (X Q (missLines S Q))).getD w false = false at hval
      rw [hrun_input C.gates _ w (by rw [hX_len]; exact hw26)] at hval
      have hget : (X Q (missLines S Q)).getD w false = true := by
        change ((List.ofFn fun q : Fin 13 => decide (q ∈ Q)) ++
          (List.ofFn fun q : Fin 13 => decide (q ∈ missLines S Q))).getD w false = true
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [List.length_ofFn]; exact hw13)]
        rw [List.getElem?_ofFn, dif_pos hw13]
        exact decide_eq_true (hQ0_pts p)
      rw [hget] at hval
      exact Bool.noConfusion hval
    · let l : Fin 13 := ⟨w - 13, by omega⟩
      rcases hQ0_lines l with ⟨c, hlc⟩
      let Q : Finset (Fin 13) := {c, c + 1, c + 2, c + 11}
      have hQ : IsQuadrangle S Q := hQ0_quad c
      have hval := hw Q hQ
      change (run C.gates (X Q (missLines S Q))).getD w false = false at hval
      rw [hrun_input C.gates _ w (by rw [hX_len]; exact hw26)] at hval
      have hget : (X Q (missLines S Q)).getD w false = true := by
        change ((List.ofFn fun q : Fin 13 => decide (q ∈ Q)) ++
          (List.ofFn fun q : Fin 13 => decide (q ∈ missLines S Q))).getD w false = true
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [List.length_ofFn]; omega)]
        rw [List.length_ofFn, List.getElem?_ofFn, dif_pos (by omega)]
        exact decide_eq_true hlc
      rw [hget] at hval
      exact Bool.noConfusion hval
  have ha26 : 26 ≤ a := hge26 a (fun Q hQ => (hquad Q hQ).1)
  have hb26 : 26 ≤ b := hge26 b (fun Q hQ => (hquad Q hQ).2)
  let m : ℕ := max a b - 25
  have hm_le : m ≤ C.gates.length := by
    have : C.size = C.gates.length := rfl
    omega
  have ha_lt_m : a < 26 + m := by omega
  have hb_lt_m : b < 26 + m := by omega
  let gs' : List Gate := C.gates.take m
  have hgs'_len : gs'.length = m := List.length_take_of_le hm_le
  let g0 : Gate := ⟨GateOp.or, [a, b]⟩
  let D : Circuit := ⟨gs' ++ [g0], 26 + m⟩
  have hD_size : D.size = m + 1 := by
    change (gs' ++ [g0]).length = m + 1
    rw [List.length_append, List.length_singleton, hgs'_len]
  have hD_le : D.size ≤ C.size + 1 := by
    have : C.size = C.gates.length := rfl
    omega
  have hD_mono : Monotone2 D := by
    intro g hg
    rcases List.mem_append.mp hg with hg1 | hg2
    · exact hM g (List.mem_of_mem_take hg1)
    · rw [List.mem_singleton] at hg2
      rw [hg2]
      exact ⟨Or.inr rfl, Nat.le_refl 2⟩
  have hD_AO : ∀ g ∈ D.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hD_mono g hg).1
  have hD_RB : ReadsBack 26 D := by
    intro j hj k hk
    change j < (gs' ++ [g0]).length at hj
    rw [List.length_append, List.length_singleton, hgs'_len] at hj
    rcases Nat.lt_or_ge j m with hlt | hge
    · have hgd : gateAt D j = gateAt C j := by
        change (gs' ++ [g0]).getD j ⟨GateOp.or, []⟩ = C.gates.getD j ⟨GateOp.or, []⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hgs'_len]; exact hlt)]
        rw [List.getElem?_take_of_lt hlt, ← List.getD_eq_getElem?_getD]
      rw [hgd] at hk
      exact hRB j (Nat.lt_of_lt_of_le hlt hm_le) k hk
    · have hjeq : j = m := by omega
      subst hjeq
      have hgd : gateAt D m = g0 := by
        change (gs' ++ [g0]).getD m ⟨GateOp.or, []⟩ = g0
        rw [← hgs'_len]
        simp [List.getD_eq_getElem?_getD]
      rw [hgd] at hk
      change k ∈ [a, b] at hk
      rw [List.mem_cons, List.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact ha_lt_m
      · exact hb_lt_m
  have hD_eval : ∀ x : List Bool, x.length = 26 →
      D.eval x = (W C a x || W C b x) := by
    intro x hx
    change (run (gs' ++ [g0]) x).getD (26 + m) false = (W C a x || W C b x)
    rw [hrun_snoc]
    have hlen_gs' : (run gs' x).length = 26 + m := by rw [hrun_len, hx, hgs'_len]
    rw [← hlen_gs', hgetD_at]
    change ((run gs' x).getD a false || ((run gs' x).getD b false || false)) = (W C a x || W C b x)
    rw [Bool.or_false]
    have hsplit : C.gates = gs' ++ C.gates.drop m := (List.take_append_drop m C.gates).symm
    have hwa : (run gs' x).getD a false = W C a x := by
      change (run gs' x).getD a false = (run C.gates x).getD a false
      rw [hsplit, hrun_prefix gs' (C.gates.drop m) x a (by rw [hx, hgs'_len]; exact ha_lt_m)]
    have hwb : (run gs' x).getD b false = W C b x := by
      change (run gs' x).getD b false = (run C.gates x).getD b false
      rw [hsplit, hrun_prefix gs' (C.gates.drop m) x b (by rw [hx, hgs'_len]; exact hb_lt_m)]
    rw [hwa, hwb]
  have hD_quad : ∀ Q : Finset (Fin 13), IsQuadrangle S Q → D.eval (X Q (missLines S Q)) = false := by
    intro Q hQ
    rw [hD_eval _ (hX_len _ _), (hquad Q hQ).1, (hquad Q hQ).2]
    rfl
  have honeEach_eq : ∀ p l : Fin 13, oneEach p l = X {p} {l} := by
    intro p l
    change (List.ofFn fun i : Fin 13 => decide (i = p)) ++ (List.ofFn fun j : Fin 13 => decide (j = l)) =
      (List.ofFn fun i : Fin 13 => decide (i ∈ ({p} : Finset (Fin 13)))) ++
      (List.ofFn fun j : Fin 13 => decide (j ∈ ({l} : Finset (Fin 13))))
    congr 1
    · congr 1; funext i
      exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_eq, decide_eq_true_eq, Finset.mem_singleton])
    · congr 1; funext j
      exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_eq, decide_eq_true_eq, Finset.mem_singleton])
  have hD_rep : Represents (fun p l : Fin 13 => decide (p ∈ S l)) D := by
    intro p l
    dsimp only
    rw [honeEach_eq p l]
    by_cases hpl : p ∈ S l
    · rw [decide_eq_true hpl, hD_eval _ (hX_len _ _)]
      rcases hpos p l hpl with h1 | h2
      · rw [h1]; rfl
      · rw [h2, Bool.or_true]
    · rw [decide_eq_false hpl]
      rcases hQ0_noninc p l hpl with ⟨c, hpc, hlc⟩
      let Q : Finset (Fin 13) := {c, c + 1, c + 2, c + 11}
      have hQ : IsQuadrangle S Q := hQ0_quad c
      have hqfalse : D.eval (X Q (missLines S Q)) = false := hD_quad Q hQ
      by_contra hne
      have htrue : D.eval (X {p} {l}) = true := by
        cases h : D.eval (X {p} {l})
        · exact (hne h).elim
        · rfl
      have hmon : D.eval (X Q (missLines S Q)) = true := by
        refine hrun_mono D.gates hD_AO (X {p} {l}) (X Q (missLines S Q))
          (by rw [hX_len, hX_len]) ?_ D.output htrue
        intro k hk
        by_cases hk13 : k < 13
        · change ((List.ofFn fun q : Fin 13 => decide (q ∈ ({p} : Finset (Fin 13)))) ++
            (List.ofFn fun q : Fin 13 => decide (q ∈ ({l} : Finset (Fin 13))))).getD k false = true at hk
          change ((List.ofFn fun q : Fin 13 => decide (q ∈ Q)) ++
            (List.ofFn fun q : Fin 13 => decide (q ∈ missLines S Q))).getD k false = true
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [List.length_ofFn]; exact hk13),
            List.getElem?_ofFn, dif_pos hk13] at hk ⊢
          change decide (⟨k, hk13⟩ ∈ ({p} : Finset (Fin 13))) = true at hk
          change decide (⟨k, hk13⟩ ∈ Q) = true
          rw [decide_eq_true_eq, Finset.mem_singleton] at hk
          rw [decide_eq_true_eq, hk]
          exact hpc
        · by_cases hk26 : k < 26
          · change ((List.ofFn fun q : Fin 13 => decide (q ∈ ({p} : Finset (Fin 13)))) ++
              (List.ofFn fun q : Fin 13 => decide (q ∈ ({l} : Finset (Fin 13))))).getD k false = true at hk
            change ((List.ofFn fun q : Fin 13 => decide (q ∈ Q)) ++
              (List.ofFn fun q : Fin 13 => decide (q ∈ missLines S Q))).getD k false = true
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [List.length_ofFn]; omega),
              List.length_ofFn, List.getElem?_ofFn, dif_pos (by omega)] at hk ⊢
            change decide (⟨k - 13, by omega⟩ ∈ ({l} : Finset (Fin 13))) = true at hk
            change decide (⟨k - 13, by omega⟩ ∈ missLines S Q) = true
            rw [decide_eq_true_eq, Finset.mem_singleton] at hk
            rw [decide_eq_true_eq, hk]
            exact hlc
          · exfalso
            rw [List.getD_eq_default _ _ (by rw [hX_len]; omega)] at hk
            exact Bool.false_ne_true hk
      rw [hmon] at hqfalse
      exact Bool.noConfusion hqfalse
  have hD_aa : ∀ j < D.size, ∀ k < D.size, aa D j → aa D k → j = k := by
    have hgate_eq : ∀ t < m, gateAt D t = gateAt C t := by
      intro t ht
      change (gs' ++ [g0]).getD t ⟨GateOp.or, []⟩ = C.gates.getD t ⟨GateOp.or, []⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hgs'_len]; exact ht)]
      rw [List.getElem?_take_of_lt ht, ← List.getD_eq_getElem?_getD]
    have haa_imp : ∀ t < D.size, aa D t → t < C.size ∧ aa C t := by
      intro t ht haat
      have htm : t < m := by
        by_contra hge
        have hteq : t = m := by omega
        subst hteq
        have hgd : gateAt D m = g0 := by
          change (gs' ++ [g0]).getD m ⟨GateOp.or, []⟩ = g0
          rw [← hgs'_len]; simp [List.getD_eq_getElem?_getD]
        have hop : (gateAt D m).op = GateOp.and := haat.1
        rw [hgd] at hop
        cases hop
      refine ⟨by have : C.size = C.gates.length := rfl; omega, ?_, ?_⟩
      · change (gateAt C t).op = GateOp.and
        rw [← hgate_eq t htm]; exact haat.1
      · rcases haat.2 with ⟨i, hi_in, hi26, hiand⟩
        change i ∈ (gateAt D t).inputs at hi_in
        rw [hgate_eq t htm] at hi_in
        have hi_lt : i < 26 + t := hRB t (by have : C.size = C.gates.length := rfl; omega) i hi_in
        refine ⟨i, hi_in, hi26, ?_⟩
        change (gateAt C (i - 26)).op = GateOp.and
        rw [← hgate_eq (i - 26) (by omega)]
        exact hiand
    intro j hj k hk haaj haak
    have hj' := haa_imp j hj haaj
    have hk' := haa_imp k hk haak
    exact haa j (Finset.mem_range.mpr hj'.1) k (Finset.mem_range.mpr hk'.1) hj'.2 hk'.2
  rcases hElimQuadAnd D hD_mono hD_RB hD_rep hD_quad hD_aa with
    ⟨E, hE_mono, hE_RB, hE_le, hE_rep, hE_quad, hE_clean⟩
  have h64 : 64 ≤ E.size := hCleanBound E hE_mono hE_RB hE_rep hE_quad hE_clean
  omega
