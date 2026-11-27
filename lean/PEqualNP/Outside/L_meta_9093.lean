import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9093

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_preserves (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length →
      (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i hi; rfl
  | cons g gs ih =>
      intro w i hi
      change (wiresFrom gs
        (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])).getD i false = _
      rw [ih _ i (by simp only [List.length_append, List.length_singleton]; omega)]
      exact List.getD_append _ _ _ _ hi

theorem wiresFrom_gate (gs : List Gate) :
    ∀ (w : List Bool) (j : ℕ) (g : Gate),
      gs[j]? = some g →
      (∀ i ∈ g.inputs, i < w.length + j) →
      (wiresFrom gs w).getD (w.length + j) false =
        g.op.eval (g.inputs.map fun i => (wiresFrom gs w).getD i false) := by
  induction gs with
  | nil => intro w j g hget; simp at hget
  | cons head tail ih =>
      intro w j g hget hback
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst g
          let v := head.op.eval (head.inputs.map fun i => w.getD i false)
          have hv : (wiresFrom (head :: tail) w).getD w.length false = v := by
            change (wiresFrom tail (w ++ [v])).getD w.length false = v
            rw [wiresFrom_preserves _ _ _ (by simp)]
            simp
          simp only [Nat.add_zero]
          rw [hv]
          apply congrArg head.op.eval
          apply List.map_congr_left
          intro i hi
          exact (wiresFrom_preserves _ _ _ (by simpa using hback i hi)).symm
      | succ j =>
          have hget' : tail[j]? = some g := by simpa using hget
          simpa only [wiresFrom, List.foldl_cons, List.length_append,
            List.length_singleton, Nat.add_assoc, Nat.add_comm 1 j] using
            ih (w ++ [head.op.eval (head.inputs.map fun i => w.getD i false)])
              j g hget' (by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hback)


open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

abbrev W (C : Circuit) (w : ℕ) (u v : Fin 14) : Bool :=
  PEqualNP.CleanedNonEdge.wireVal 14 C w (pairInput u v)

abbrev Sensitive (C : Circuit) (w : ℕ) : Prop :=
  W C w 0 7 = true ∧ W C w 0 0 = false ∧ W C w 7 7 = false

lemma gate_get (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    C.gates[k]? = some (gateAt C k) := by
  simp [gateAt, List.getElem?_eq_getElem hk]

lemma gate_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k ∈ C.gates := by
  simp only [gateAt, List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

lemma two_list (l : List ℕ) (h : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  match l with
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => simp at h

lemma gate_inputs (C : Circuit) (ha : IsAO2 14 C) (k : ℕ)
    (hk : k < C.gates.length) :
    (gateAt C k).inputs = [opnd C k 0, opnd C k 1] :=
  two_list _ (ha.2.2 _ (gate_mem C k hk))

lemma wire_input (C : Circuit) (x : Fin 14 → Bool) (w : ℕ) (hw : w < 14) :
    PEqualNP.CleanedNonEdge.wireVal 14 C w x = x ⟨w, hw⟩ := by
  change (wiresFrom C.gates (List.ofFn x)).getD w false = _
  rw [wiresFrom_preserves _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp only [List.getElem_ofFn]

lemma sensitive_ge (C : Circuit) (w : ℕ) (hs : Sensitive C w) : 14 ≤ w := by
  by_contra h
  have hw : w < 14 := by omega
  rcases hs with ⟨hp, h0, h7⟩
  simp only [W, wire_input C _ w hw, pairInput, decide_eq_true_eq] at hp
  rcases hp with hp | hp
  · simp [W, wire_input C _ w hw, pairInput, hp] at h0
  · simp [W, wire_input C _ w hw, pairInput, hp] at h7

lemma gate_value (C : Circuit) (ha : IsAO2 14 C) (k : ℕ)
    (hk : k < C.gates.length) (x : Fin 14 → Bool) :
    PEqualNP.CleanedNonEdge.wireVal 14 C (14 + k) x =
      (gateAt C k).op.eval
        [PEqualNP.CleanedNonEdge.wireVal 14 C (opnd C k 0) x,
         PEqualNP.CleanedNonEdge.wireVal 14 C (opnd C k 1) x] := by
  have h := wiresFrom_gate C.gates (List.ofFn x) k (gateAt C k)
    (gate_get C k hk) (by simpa using ha.2.1 k hk)
  simp only [List.length_ofFn] at h
  simpa only [PEqualNP.CleanedNonEdge.wireVal, Circuit.wires, wiresFrom,
    gate_inputs C ha k hk, List.map_cons, List.map_nil] using h

lemma operand_mem (C : Circuit) (ha : IsAO2 14 C) (k : ℕ)
    (hk : k < C.gates.length) (b : Fin 2) : opnd C k b ∈ (gateAt C k).inputs := by
  have hb : b = 0 ∨ b = 1 := by omega
  rcases hb with rfl | rfl <;> rw [gate_inputs C ha k hk] <;> simp

lemma operand_lt (C : Circuit) (ha : IsAO2 14 C) (k : ℕ)
    (hk : k < C.gates.length) (b : Fin 2) : opnd C k b < 14 + k :=
  ha.2.1 k hk _ (operand_mem C ha k hk b)

lemma or_sensitive_operand (C : Circuit) (ha : IsAO2 14 C) (k : ℕ)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or)
    (hs : Sensitive C (14 + k)) : ∃ b : Fin 2, Sensitive C (opnd C k b) := by
  rcases hs with ⟨hp, h0, h7⟩
  have ev (u v : Fin 14) : W C (14 + k) u v =
      (W C (opnd C k 0) u v || W C (opnd C k 1) u v) := by
    simpa [W, hop, GateOp.eval] using gate_value C ha k hk (pairInput u v)
  rw [ev] at hp h0 h7
  simp only [Bool.or_eq_true] at hp
  simp only [Bool.or_eq_false_iff] at h0 h7
  rcases hp with hp | hp
  · exact ⟨0, hp, h0.1, h7.1⟩
  · exact ⟨1, hp, h0.2, h7.2⟩


lemma and_value (C : Circuit) (ha : IsAO2 14 C) (k : ℕ)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and)
    (u v : Fin 14) : W C (14 + k) u v =
      (W C (opnd C k 0) u v && W C (opnd C k 1) u v) := by
  simpa [W, hop, GateOp.eval] using gate_value C ha k hk (pairInput u v)

lemma dag_merge_sources (S : Finset ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R]
    (j p q : ℕ)
    (hback : ∀ a ∈ S, ∀ b ∈ S, R a b → a < b)
    (hmax : ∀ a ∈ S, a ≤ j)
    (hj : j ∈ S) (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) (hpj : R p j) (hqj : R q j) :
    2 ≤ (S.filter (fun b => ∀ a ∈ S, ¬ R a b)).card ∨
      ∃ a ∈ S, 2 ≤ (S.filter (R a)).card := by
  classical
  let source := fun b => ∀ a ∈ S, ¬ R a b
  let din := fun b => (S.filter (fun a => R a b)).card
  let dout := fun a => (S.filter (R a)).card
  by_contra h
  have hsrc : (S.filter source).card ≤ 1 := by
    have hn : ¬ 2 ≤ (S.filter source).card := fun hh => h (Or.inl hh)
    omega
  have hout : ∀ a ∈ S, dout a ≤ 1 := by
    intro a ha
    have hn : ¬ 2 ≤ dout a := fun hh => h (Or.inr ⟨a, ha, hh⟩)
    omega
  have houtj : dout j = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    exact (not_lt_of_ge (hmax b hb'.1)) (hback j hj b hb'.1 hb'.2)
  have houts : (∑ a ∈ S, dout a) < S.card := by
    have hh := Finset.sum_lt_sum hout ⟨j, hj, by omega⟩
    simpa using hh
  have hin : ∀ b ∈ S, 1 ≤ din b + if source b then 1 else 0 := by
    intro b hb
    by_cases hs : source b
    · simp only [if_pos hs]
      omega
    · have hex : ∃ a ∈ S, R a b := by
        by_contra hex
        exact hs (fun a ha hr => hex ⟨a, ha, hr⟩)
      obtain ⟨a, ha, hr⟩ := hex
      have hpos : 0 < din b := Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hr⟩⟩
      simp only [if_neg hs]
      omega
  have hinj : 2 ≤ din j := by
    have hsub : ({p, q} : Finset ℕ) ⊆ S.filter (fun a => R a j) := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Finset.mem_filter.mpr ⟨hp, hpj⟩
      · have hqa := Finset.mem_singleton.mp ha
        subst a
        exact Finset.mem_filter.mpr ⟨hq, hqj⟩
    have hc := Finset.card_le_card hsub
    simpa only [Finset.card_pair hpq] using hc
  have hins : S.card < (∑ b ∈ S, din b) + (S.filter source).card := by
    have hh := Finset.sum_lt_sum hin ⟨j, hj, by omega⟩
    simpa only [Finset.sum_const, Nat.nsmul_eq_mul, mul_one,
      Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] using hh
  have hdouble : (∑ b ∈ S, din b) = ∑ a ∈ S, dout a := by
    dsimp only [din, dout]
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  omega

lemma main (C : Circuit) (ha : IsAO2 14 C) (j : ℕ) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (hne : opnd C j 0 ≠ opnd C j 1)
    (hp : W C (14 + j) 0 7 = true)
    (hsingle : ∀ b : Fin 2, W C (opnd C j b) 0 0 = false ∧
      W C (opnd C j b) 7 7 = false) :
    (∀ b : Fin 2, Sensitive C (opnd C j b)) ∧
      let S := (Finset.range (j + 1)).filter (fun k => Sensitive C (14 + k))
      (2 ≤ (S.filter (fun k => (gateAt C k).op.eval [] = true ∧
        ∀ a ∈ S, ¬ (14 + a ∈ (gateAt C k).inputs))).card ∨
       ∃ a ∈ S, 2 ≤ (S.filter (fun k => 14 + a ∈ (gateAt C k).inputs)).card) := by
  classical
  have hp' : W C (opnd C j 0) 0 7 = true ∧ W C (opnd C j 1) 0 7 = true := by
    rw [and_value C ha j hj hand] at hp
    simpa only [Bool.and_eq_true] using hp
  have hins : ∀ b : Fin 2, Sensitive C (opnd C j b) := by
    intro b
    have hb : b = 0 ∨ b = 1 := by omega
    rcases hb with rfl | rfl
    · exact ⟨hp'.1, hsingle 0⟩
    · exact ⟨hp'.2, hsingle 1⟩
  refine ⟨hins, ?_⟩
  let S := (Finset.range (j + 1)).filter (fun k => Sensitive C (14 + k))
  let R := fun a b => 14 + a ∈ (gateAt C b).inputs
  change 2 ≤ (S.filter (fun k => (gateAt C k).op.eval [] = true ∧
    ∀ a ∈ S, ¬ R a k)).card ∨ ∃ a ∈ S, 2 ≤ (S.filter (R a)).card
  have hSmax : ∀ a ∈ S, a ≤ j := by
    intro a ha
    exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
  have hSk : ∀ a ∈ S, a < C.gates.length := by
    intro a ha
    exact lt_of_le_of_lt (hSmax a ha) hj
  have hback : ∀ a ∈ S, ∀ b ∈ S, R a b → a < b := by
    intro a _ b hb hab
    have hlt := ha.2.1 b (hSk b hb) (14 + a) hab
    omega
  have hjS : j ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, ?_, ?_⟩
    · rw [and_value C ha j hj hand, (hsingle 0).1]
      rfl
    · rw [and_value C ha j hj hand, (hsingle 0).2]
      rfl
  let p := opnd C j 0 - 14
  let q := opnd C j 1 - 14
  have hpw : 14 + p = opnd C j 0 := by
    have := sensitive_ge C _ (hins 0)
    dsimp [p]
    omega
  have hqw : 14 + q = opnd C j 1 := by
    have := sensitive_ge C _ (hins 1)
    dsimp [q]
    omega
  have hpS : p ∈ S := by
    have hlt := operand_lt C ha j hj 0
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [hpw]
    exact hins 0
  have hqS : q ∈ S := by
    have hlt := operand_lt C ha j hj 1
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [hqw]
    exact hins 1
  have hpq : p ≠ q := by
    intro he
    apply hne
    omega
  have hpj : R p j := by
    dsimp [R]
    rw [hpw]
    exact operand_mem C ha j hj 0
  have hqj : R q j := by
    dsimp [R]
    rw [hqw]
    exact operand_mem C ha j hj 1
  rcases dag_merge_sources S R j p q hback hSmax hjS hpS hqS hpq hpj hqj with hroots | hbranch
  · apply Or.inl
    apply le_trans hroots (Finset.card_le_card ?_)
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkS, hroot⟩
    refine Finset.mem_filter.mpr ⟨hkS, ?_, hroot⟩
    have hk := hSk k hkS
    rcases ha.1 (gateAt C k) (gate_mem C k hk) with hop | hop
    · simp [hop, GateOp.eval]
    · have hs := (Finset.mem_filter.mp hkS).2
      obtain ⟨b, hb⟩ := or_sensitive_operand C ha k hk hop hs
      let a := opnd C k b - 14
      have haw : 14 + a = opnd C k b := by
        have := sensitive_ge C _ hb
        dsimp [a]
        omega
      have haS : a ∈ S := by
        have hlt := operand_lt C ha k hk b
        have hkj := hSmax k hkS
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
        rw [haw]
        exact hb
      exact False.elim (hroot a haS (by
        dsimp [R]
        rw [haw]
        exact operand_mem C ha k hk b))
  · exact Or.inr hbranch

end PEqualNP.Outside.L_meta_9093

theorem PEqualNP.Outside.L_meta_9093 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →     ∀ x3 < x1.gates.length,       (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and →         PEqualNP.TopForm.opnd x1 x3 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x3 (1 : Fin (2 : ℕ)) →           have x7 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x7 : ℕ) (x8 x9 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x7 (PEqualNP.EdgeOwnership.pairInput x8 x9);           let x8 : ℕ → Prop := fun (x8 : ℕ) => x7 x8 (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ x7 x8 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x7 x8 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false;           have x9 : Finset ℕ := {x9 ∈ Finset.range (x3 + (1 : ℕ)) | x8 ((14 : ℕ) + x9)};           let x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => (14 : ℕ) + x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x11).inputs;           x7 ((14 : ℕ) + x3) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → (∀ (x12 : Fin (2 : ℕ)), x7 (PEqualNP.TopForm.opnd x1 x3 x12) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x7 (PEqualNP.TopForm.opnd x1 x3 x12) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → (∀ (x13 : Fin (2 : ℕ)), x8 (PEqualNP.TopForm.opnd x1 x3 x13)) ∧ ((2 : ℕ) ≤ {x13 ∈ x9 | (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x13).op.eval [] = Bool.true ∧ ∀ x14 ∈ x9, ¬x10 x14 x13}.card ∨ ∃ x13 ∈ x9, (2 : ℕ) ≤ (Finset.filter (x10 x13) x9).card) := by
  intro C ha j hj hand hne
  exact PEqualNP.Outside.L_meta_9093.main C ha j hj hand hne
