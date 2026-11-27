import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
-- Reassociate the two private AND branches to make one gate redundant.
theorem PEqualNP.Outside.R_meta_4215_733
    (bound : ∀ D : Circuit, Monotone2 D → ReadsBack 14 D →
      circuitFun 14 D = (fun (x : Fin 14 → Bool) => decide (∃ p l : Fin 7, p ∈ fanoLines l ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) → 27 ≤ D.size)
    (remaining : ∀ C : Circuit,
      let n := (14 : ℕ)
      let F := fun (x : Fin n → Bool) => decide (∃ p l : Fin 7, p ∈ fanoLines l ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
      let V := fun w (p l : Fin n) => wireVal n C w (pairInput p l)
      let Z := fun w => V w 0 0 = false ∧ V w 7 7 = false
      let o := opnd C
      let G := gateAt C
      let A := fun g => (G g).op = .and
      let P := fun g p q => A g ∧ (G g).inputs.Perm [p,q]
      let B := fun w a => (n+a = w ∨ InCone n C a (w-n)) ∧ A a ∧ Z (n+a) ∧
        ∃ b : Fin 2, V (o a b) 0 0 = true ∧ V (o a (1-b)) 7 7 = true
      C.size = 27 → IsAO2 n C → circuitFun n C = F →
      ∀ g, A g →
      V (n+g) 0 7 = true → (∀ b, Z (o g b)) →
      (¬ ∃ i j w u v, i < j ∧ j < g ∧ g < C.size ∧ P i w u ∧ P j w v ∧ P g (n+i) (n+j) ∧
        (∀ t < C.size, (n+i ∈ (G t).inputs ∨ n+j ∈ (G t).inputs) → t = g) ∧
        C.output ≠ n+i ∧ C.output ≠ n+j) →
      ¬ ∃ a, B (o g 0) a ∧ B (o g 1) a) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);   have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => ((14 : ℕ) + x4 = x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x3 - (14 : ℕ))) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x2 ((14 : ℕ) + x4) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 ((14 : ℕ) + x4) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ∃ (x5 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x4 x5) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (PEqualNP.TopForm.opnd x1 x4 ((1 : Fin (2 : ℕ)) - x5)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;   x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).inputs.Nodup) → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x7 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x8 : Fin (7 : ℕ)) (x9 : Fin (7 : ℕ)), x8 ∈ PEqualNP.CircuitLowerBounds.fanoLines x9 ∧ x7 (Fin.castAdd (7 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (7 : ℕ) x9) = Bool.true)) → ∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → (14 : ℕ) + x8 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x8 (x1.output - (14 : ℕ)) → x2 ((14 : ℕ) + x8) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → (∀ (x12 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x8 x12) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 (PEqualNP.TopForm.opnd x1 x8 x12) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → ¬∃ (x13 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x8 (0 : Fin (2 : ℕ))) x13 ∧ x3 (PEqualNP.TopForm.opnd x1 x8 (1 : Fin (2 : ℕ))) x13 := by
  classical
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

  have rewriteDiamond (C : Circuit) (mono : Monotone2 C) (back : ReadsBack 14 C)
      (i j k w u v : ℕ) (hij : i < j) (hjk : j < k) (hk : k < C.size)
      (first : gateAt C i = ⟨.and,[w,u]⟩ ∨ gateAt C i = ⟨.and,[u,w]⟩)
      (second : gateAt C j = ⟨.and,[w,v]⟩ ∨ gateAt C j = ⟨.and,[v,w]⟩)
      (merge : gateAt C k = ⟨.and,[14+i,14+j]⟩ ∨ gateAt C k = ⟨.and,[14+j,14+i]⟩)
      (uniqueReader : ∀ t < C.size, (14+i ∈ (gateAt C t).inputs ∨ 14+j ∈ (gateAt C t).inputs) → t = k)
      (outGood : C.output < 14+C.size ∧ C.output ≠ 14+i ∧ C.output ≠ 14+j) :
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 14 D ∧ D.size = C.size ∧ D.output = C.output ∧ circuitFun 14 D = circuitFun 14 C ∧
        u < 14+i ∧ ∀ x, wireVal 14 D (14+i) x = wireVal 14 D u x := by

    have sz : C.size = C.gates.length := rfl
    have hi : i < C.gates.length := by omega
    have hj : j < C.gates.length := by omega
    have hw : w < 14+i := back i hi w (by rcases first with h | h <;> rw [h] <;> simp)
    have hu : u < 14+i := back i hi u (by rcases first with h | h <;> rw [h] <;> simp)
    have hv : v < 14+j := back j hj v (by rcases second with h | h <;> rw [h] <;> simp)
    have hv_i : v ≠ 14+i := by
      intro eq
      have read : 14+i ∈ (gateAt C j).inputs := by
        rcases second with h | h <;> rw [h, ← eq] <;> simp
      have contradiction := uniqueReader j (by omega) (Or.inl read)
      omega
    let editor (t : Fin C.gates.length) : Gate :=
      if t.val = i then ⟨.and,[u]⟩ else
      if t.val = j then ⟨.and,[u,v]⟩ else
      if t.val = k then ⟨.and,[w,14+j]⟩ else C.gates[t.val]
    let D : Circuit := ⟨List.ofFn editor,C.output⟩
    have lengthEq : D.gates.length = C.gates.length := by simp only [D,List.length_ofFn]
    have gateEdit (t : ℕ) (ht : t < C.gates.length) : gateAt D t = editor ⟨t,ht⟩ := by
      have hd : t < D.gates.length := by omega
      change D.gates.getD t _ = _
      rw [List.getD_eq_getElem _ _ hd]
      exact List.getElem_ofFn hd
    have oldAt (t : ℕ) (ht : t < C.gates.length) : gateAt C t = C.gates[t] :=
      List.getD_eq_getElem _ _ ht
    have editedMono : Monotone2 D := by
      intro g hg
      change g ∈ List.ofFn editor at hg
      obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hg
      unfold editor
      split_ifs
      · simp
      · simp
      · simp
      · exact mono _ (List.getElem_mem t.isLt)
    have editedBack : ReadsBack 14 D := by
      intro t ht w0 read
      have hc : t < C.gates.length := by omega
      rw [gateEdit t hc] at read
      simp only [editor] at read
      split_ifs at read with h1 h2 h3
      · simp only [List.mem_singleton] at read
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at read
        rcases read with h | h <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at read
        rcases read with h | h <;> omega
      · exact back t hc w0 (by rwa [oldAt t hc])
    have eqI : gateAt D i = ⟨.and,[u]⟩ := by rw [gateEdit i hi]; simp only [editor,ite_true]
    have eqJ : gateAt D j = ⟨.and,[u,v]⟩ := by
      rw [gateEdit j hj]
      simp only [editor, ite_eq_right (show j ≠ i by omega), ite_true]
    have eqK : gateAt D k = ⟨.and,[w,14+j]⟩ := by
      rw [gateEdit k (by omega)]
      simp only [editor, ite_eq_right (show k ≠ i by omega), ite_eq_right (show k ≠ j by omega), ite_true]
    have evalOne (b : Bool) : GateOp.and.eval [b] = b := by cases b <;> rfl
    have evalTwo (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
    have exactAnd (x : Fin 14 → Bool) (t a b : ℕ) (ht : t < C.gates.length)
        (gate : gateAt C t = ⟨.and,[a,b]⟩ ∨ gateAt C t = ⟨.and,[b,a]⟩) :
        wireVal 14 C (14+t) x = (wireVal 14 C a x && wireVal 14 C b x) := by
      rw [hwire_gate C back x t ht]
      rcases gate with h | h <;> rw [h] <;> simp only [List.map_cons,List.map_nil,evalTwo]
      exact Bool.and_comm _ _
    have exactOn (x : Fin 14 → Bool) : ∀ t < 14+C.gates.length, t ≠ 14+i → t ≠ 14+j →
        wireVal 14 D t x = wireVal 14 C t x := by
      intro t
      induction t using Nat.strong_induction_on with
      | _ t earlier =>
        intro ht notI notJ
        by_cases raw : t < 14
        · rw [hwire_in D x t raw, hwire_in C x t raw]
        let q := t-14
        have qt : t = 14+q := by omega
        have qb : q < C.gates.length := by omega
        rw [qt, hwire_gate D editedBack x q (by omega)]
        by_cases isMerge : q = k
        · have htk : t = 14+k := by omega
          rw [isMerge, eqK, exactAnd x k _ _ (by omega) merge]
          simp only [List.map_cons, List.map_nil, evalTwo]
          rw [hwire_gate D editedBack x j (by omega), eqJ,
            exactAnd x i w u hi first, exactAnd x j w v hj second]
          simp only [List.map_cons, List.map_nil, evalTwo]
          rw [earlier w (by omega) (by omega) (by omega) (by omega),
            earlier u (by omega) (by omega) (by omega) (by omega),
            earlier v (by omega) (by omega) hv_i (by omega)]
          cases wireVal 14 C w x <;> cases wireVal 14 C u x <;> cases wireVal 14 C v x <;> rfl
        · have nqI : q ≠ i := by omega
          have nqJ : q ≠ j := by omega
          have same : gateAt D q = gateAt C q := by
            rw [gateEdit q qb, oldAt q qb]
            simp only [editor, ite_eq_right nqI, ite_eq_right nqJ, ite_eq_right isMerge]
          rw [same, hwire_gate C back x q qb]
          congr 1
          apply List.map_congr_left
          intro wire member
          have prior := back q qb wire member
          have noI : wire ≠ 14+i := fun eq => isMerge (uniqueReader q (by omega) (Or.inl (eq ▸ member)))
          have noJ : wire ≠ 14+j := fun eq => isMerge (uniqueReader q (by omega) (Or.inr (eq ▸ member)))
          exact earlier wire (by omega) (by omega) noI noJ
    refine ⟨D,editedMono,editedBack,lengthEq,rfl,?_,hu,?_⟩
    · funext x
      exact exactOn x C.output (by simpa only [sz] using outGood.1) outGood.2.1 outGood.2.2
    · intro x
      rw [hwire_gate D editedBack x i (by omega), eqI]
      exact evalOne _

  have deleteCopy (D : Circuit) (mono : Monotone2 D) (back : ReadsBack 14 D) (k w : ℕ)
      (hk : k < D.gates.length) (hw : w < 14+k) (hout_lt : D.output < 14+D.gates.length)
      (heqw : ∀ x, wireVal 14 D (14+k) x = wireVal 14 D w x) :
      ∃ D₁ : Circuit, Monotone2 D₁ ∧ ReadsBack 14 D₁ ∧ D₁.size = D.size-1 ∧ circuitFun 14 D₁ = circuitFun 14 D := by

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
    have mono1 : Monotone2 D₁ := by
      intro gt hgt
      simp only [D₁, gs₁, List.mem_map, List.mem_append] at hgt
      rcases hgt with ⟨gt₀, hgt₀, rfl⟩
      have original : gt₀ ∈ D.gates := hgt₀.elim List.mem_of_mem_take List.mem_of_mem_drop
      obtain ⟨op,arity⟩ := mono _ original
      exact ⟨op,by simpa only [rg,List.length_map] using arity⟩
    have back1 : ReadsBack 14 D₁ := by
      intro j hj u hu
      by_cases hjk : j < k
      · rw [hgate_lt j hjk] at hu
        simp only [rg, List.mem_map] at hu
        rcases hu with ⟨v, hv, rfl⟩
        have hv_lt : v < 14 + j := back j (by omega) v hv
        simp only [remap]
        split_ifs <;> omega
      · rw [hgate_ge j (by omega) hj] at hu
        simp only [rg, List.mem_map] at hu
        rcases hu with ⟨v, hv, rfl⟩
        have hv_lt : v < 14 + (j + 1) := back (j + 1) (by omega) v hv
        simp only [remap]
        split_ifs <;> omega
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
              rw [hr, hj_eq, hwire_gate D₁ back1 x j (by omega),
                  hwire_gate D back x j hjD, hgate_lt j hjk]
              simp only [rg, List.map_map]
              congr 1
              apply List.map_congr_left
              intro u hu
              have hu_lt : u < 14 + j := back j hjD u hu
              exact ihx u (by omega) (by omega)
            · have hkj : k < j := by omega
              have hr : remap idx = 14 + (j - 1) := by simp only [remap]; split_ifs <;> omega
              have hj1 : j - 1 < D₁.gates.length := by omega
              rw [hr, hwire_gate D₁ back1 x (j - 1) hj1,
                  hgate_ge (j - 1) (by omega) hj1]
              have hj1_eq : (j - 1) + 1 = j := by omega
              rw [hj1_eq, hj_eq, hwire_gate D back x j hjD]
              simp only [rg, List.map_map]
              congr 1
              apply List.map_congr_left
              intro u hu
              have hu_lt : u < 14 + j := back j hjD u hu
              exact ihx u (by omega) (by omega)
    refine ⟨D₁,mono1,back1,hlen₁,?_⟩
    funext x
    exact hsim x D.output hout_lt

  intro C _V _birth small ao distinct good g op live pairOn singles
  have mono : Monotone2 C := by
    intro j hj
    exact ⟨ao.1 j hj, (ao.2.2 j hj).le⟩
  have low := bound C mono ao.2.1 good
  have exactSize : C.size = 27 := by omega
  have outLt : C.output < 14+C.size := by
    by_contra! oob
    let x := pairInput (0 : Fin 14) 7
    have h := congrFun good x
    have edge : Decidable.decide (∃ p l : Fin 7, p ∈ fanoLines l ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) = true := by decide +kernel
    change wireVal 14 C C.output x = _ at h
    rw [hwire_oob C x C.output oob, edge] at h
    cases h
  rintro ⟨a, firstBirth, secondBirth⟩
  have excluded := remaining C exactSize ao good g op pairOn singles
  refine excluded ?_ ⟨a, ?_, ?_⟩
  rotate_left
  · exact ⟨firstBirth.1, firstBirth.2.1, ⟨firstBirth.2.2.1, firstBirth.2.2.2.1⟩, firstBirth.2.2.2.2⟩
  · exact ⟨secondBirth.1, secondBirth.2.1, ⟨secondBirth.2.2.1, secondBirth.2.2.2.1⟩, secondBirth.2.2.2.2⟩
  rintro ⟨i,j,w,u,v,hij,hjg,hg,first,second,merge,unique,outI,outJ⟩
  have andInputs (t p q : ℕ) (h : (gateAt C t).op = .and ∧ (gateAt C t).inputs.Perm [p,q]) :
      gateAt C t = ⟨.and,[p,q]⟩ ∨ gateAt C t = ⟨.and,[q,p]⟩ := by
    obtain ⟨hop,hperm⟩ := h
    cases gateEq : gateAt C t with
    | mk code args =>
      rw [gateEq] at hop hperm
      change code = .and at hop
      subst code
      change args.Perm [p,q] at hperm
      have len := hperm.length_eq
      obtain ⟨a,b,rfl⟩ : ∃ a b, args = [a,b] := by
        cases args with
        | nil => simp at len
        | cons a tail =>
          cases tail with
          | nil => simp at len
          | cons b tail =>
            have ht : tail.length = 0 := by simpa using len
            exact ⟨a,b,by rw [List.length_eq_zero_iff.mp ht]⟩
      have mem : p ∈ [a,b] := hperm.mem_iff.mpr (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with h | h
      · subst a
        have hc := List.Perm.cons_inv hperm
        have : b = q := by simpa using hc
        subst b
        exact Or.inl rfl
      · subst b
        have swapped : [p,a].Perm [p,q] := (List.Perm.swap a p []).trans hperm
        have hc := List.Perm.cons_inv swapped
        have : a = q := by simpa using hc
        subst a
        exact Or.inr rfl
  obtain ⟨D,dm,db,ds,dout,funD,hu,dupe⟩ :=
    rewriteDiamond C mono ao.2.1 i j g w u v hij hjg hg (andInputs i w u first) (andInputs j w v second)
      (andInputs g (14+i) (14+j) merge) unique ⟨outLt,outI,outJ⟩
  have iD : i < D.gates.length := by
    change i < D.size
    omega
  have dOutLt : D.output < 14+D.gates.length := by
    change D.output < 14+D.size
    omega
  obtain ⟨E,em,eb,es,funE⟩ := deleteCopy D dm db i u iD hu dOutLt dupe
  have impossible := bound E em eb (funE.trans (funD.trans good))
  omega
