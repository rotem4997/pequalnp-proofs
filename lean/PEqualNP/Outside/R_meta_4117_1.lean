import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4117_1
    (h_not : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      have f : (Fin n → Bool) → Bool := graphFun G A;
      have reads : ℕ → Gate → Bool := fun w g => (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains w;
      have ra : Fin n → ℕ → Finset ℕ := fun v k => {j ∈ Finset.range C.gates.length | j ≠ k ∧ (reads v (gateAt C j) = true ∨ k < j ∧ reads (n + k) (gateAt C j) = true)};
      have rf : Fin n → List Gate := fun v => List.filter (reads v) C.gates;
      (∀ u ∉ A, (G.neighborSet u).ncard = 3) → (7 : ℕ∞) ≤ G.egirth →
      (∀ u w : Fin n, G.Adj u w → u ∉ A) →
      IsMinimalCircuit n C → circuitFun n C = f →
      (∀ u ∉ A, (rf u).length ≤ 3 ∧ ((rf u).length = 3 → ∀ g ∈ rf u, g.op = GateOp.or)) →
      (∃ v ∉ A, ∃ k < C.gates.length, (rf v).length = 1 ∧ reads v (gateAt C k) = true ∧ (gateAt C k).op = GateOp.not) →
      (¬∃ u ∉ A, ∃ k < C.gates.length, reads u (gateAt C k) = true ∧ (gateAt C k).op ≠ GateOp.or ∧ 3 ≤ (ra u k).card) →
      ∃ v ∉ A, ∃ s : ℕ, s + 4 ≤ C.size ∧ HasCircuitSize n (fun y => f (Function.update y v false)) s)
    (h_and : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      have f : (Fin n → Bool) → Bool := graphFun G A;
      have reads : ℕ → Gate → Bool := fun w g => (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains w;
      have ra : Fin n → ℕ → Finset ℕ := fun v k => {j ∈ Finset.range C.gates.length | j ≠ k ∧ (reads v (gateAt C j) = true ∨ k < j ∧ reads (n + k) (gateAt C j) = true)};
      have rf : Fin n → List Gate := fun v => List.filter (reads v) C.gates;
      (∀ u ∉ A, (G.neighborSet u).ncard = 3) → (7 : ℕ∞) ≤ G.egirth →
      (∀ u w : Fin n, G.Adj u w → u ∉ A) →
      IsMinimalCircuit n C → circuitFun n C = f →
      (∀ u ∉ A, (rf u).length ≤ 3 ∧ ((rf u).length = 3 → ∀ g ∈ rf u, g.op = GateOp.or)) →
      (∃ v ∉ A, ∃ k < C.gates.length, (rf v).length = 1 ∧ reads v (gateAt C k) = true ∧ (gateAt C k).op = GateOp.and ∧ ∀ w : Fin n, w ≠ v → ¬ (gateAt C k).inputs.Perm [v.val, w.val]) →
      (¬∃ u ∉ A, ∃ k < C.gates.length, reads u (gateAt C k) = true ∧ (gateAt C k).op ≠ GateOp.or ∧ 3 ≤ (ra u k).card) →
      ∃ v ∉ A, ∃ s : ℕ, s + 4 ≤ C.size ∧ HasCircuitSize n (fun y => f (Function.update y v false)) s)
    (h_or : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      have f : (Fin n → Bool) → Bool := graphFun G A;
      have reads : ℕ → Gate → Bool := fun w g => (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains w;
      have ra : Fin n → ℕ → Finset ℕ := fun v k => {j ∈ Finset.range C.gates.length | j ≠ k ∧ (reads v (gateAt C j) = true ∨ k < j ∧ reads (n + k) (gateAt C j) = true)};
      have rf : Fin n → List Gate := fun v => List.filter (reads v) C.gates;
      (∀ u ∉ A, (G.neighborSet u).ncard = 3) → (7 : ℕ∞) ≤ G.egirth →
      (∀ u w : Fin n, G.Adj u w → u ∉ A) →
      IsMinimalCircuit n C → circuitFun n C = f →
      (∀ u ∉ A, (rf u).length ≤ 3 ∧ ((rf u).length = 3 → ∀ g ∈ rf u, g.op = GateOp.or)) →
      (∃ v ∉ A, ∃ k < C.gates.length, (rf v).length = 1 ∧ reads v (gateAt C k) = true ∧ (gateAt C k).op = GateOp.or ∧ ∀ w : Fin n, w ≠ v → ¬ (gateAt C k).inputs.Perm [v.val, w.val]) →
      (¬∃ u ∉ A, ∃ k < C.gates.length, reads u (gateAt C k) = true ∧ (gateAt C k).op ≠ GateOp.or ∧ 3 ≤ (ra u k).card) →
      ∃ v ∉ A, ∃ s : ℕ, s + 4 ≤ C.size ∧ HasCircuitSize n (fun y => f (Function.update y v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains x7;   have x8 : Fin x1 → ℕ → Finset ℕ := fun (x8 : Fin x1) (x9 : ℕ) => {x10 ∈ Finset.range x5.gates.length | x10 ≠ x9 ∧ (x7 (↑x8) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true ∨ x9 < x10 ∧ x7 (x1 + x9) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true)};   have x9 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : Fin x1) => List.filter (x7 ↑x9) x5.gates;   (∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ x16 ∉ x4, (x9 x16).length ≤ (3 : ℕ) ∧ ((x9 x16).length = (3 : ℕ) → ∀ x19 ∈ x9 x16, x19.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x17 ∉ x4, (x9 x17).length ≤ (1 : ℕ) ∧ ∀ x18 ∈ x9 x17, ∀ (x20 : Fin x1), x20 ≠ x17 → x18.inputs.Perm [↑x17, ↑x20] → x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → (¬∃ x18 ∉ x4, ∃ x19 < x5.gates.length, x7 (↑x18) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19) = Bool.true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ (x8 x18 x19).card) → ∃ x19 ∉ x4, ∃ (x20 : ℕ), x20 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x21 : Fin x1 → Bool) => x6 (Function.update x21 x19 Bool.false)) x20 := by
  intro n G instG A C f reads ra rf hdeg hgirth hiso hedge hmin hfun hbd hlow hno3
  obtain ⟨v, hvA, hvle, hvnopair⟩ := hlow
  have hne_nb : (G.neighborSet v).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hdeg v hvA]
    omega
  obtain ⟨u, huv⟩ := hne_nb
  have huv_adj : G.Adj v u := huv
  have huA : u ∉ A := hiso u v huv_adj.symm
  have huv_ne : u ≠ v := huv_adj.ne.symm
  have hrf_pos : 0 < (rf v).length := by
    by_contra hzero
    have hlen0 : (rf v).length = 0 := by omega
    have hall_false : ∀ g ∈ C.gates, reads v g = false := by
      intro g hg
      cases hrg : reads v g
      · rfl
      · have hmem : g ∈ rf v := List.mem_filter.mpr ⟨hg, hrg⟩
        have hpos : 0 < (rf v).length := List.length_pos_of_mem hmem
        omega
    let wireStep (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have fold_len : ∀ (gs : List Gate) (w : List Bool), (gs.foldl wireStep w).length = w.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro w; simp
      | cons g gs ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp [wireStep]
        omega
    have fold_pres : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
        (gs.foldl wireStep w).getD i false = w.getD i false := by
      intro gs
      induction gs with
      | nil => intro w i _; rfl
      | cons g gs ih =>
        intro w i hi
        rw [List.foldl_cons, ih (wireStep w g) i (by simp [wireStep]; omega)]
        simp [wireStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have hout_ne : C.output ≠ v.val := by
      intro hout
      let inp2 : Fin n → Bool := fun i => decide (i = v)
      have hcev : circuitFun n C inp2 = true := by
        change (C.gates.foldl wireStep (List.ofFn inp2)).getD C.output false = true
        rw [hout, fold_pres C.gates (List.ofFn inp2) v.val (by simp)]
        have hlt : v.val < (List.ofFn inp2).length := by simp
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_ofFn]
        simp [inp2]
      have hf2 : f inp2 = false := by
        change (decide (∃ a ∈ A, inp2 a = true) || decide (∃ p q, G.Adj p q ∧ inp2 p = true ∧ inp2 q = true)) = false
        rw [Bool.or_eq_false_iff]
        constructor
        · refine decide_eq_false ?_
          rintro ⟨a, haA, ha⟩
          have hav : a = v := of_decide_eq_true ha
          subst hav
          exact hvA haA
        · refine decide_eq_false ?_
          rintro ⟨p, q, hpq, hp, hq⟩
          have hpv : p = v := of_decide_eq_true hp
          have hqv : q = v := of_decide_eq_true hq
          subst hpv; subst hqv
          exact G.ne_of_adj hpq rfl
      rw [hfun] at hcev
      rw [hf2] at hcev
      exact Bool.noConfusion hcev
    have fold_agree : ∀ (gs : List Gate) (w0 w1 : List Bool),
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        (∀ g ∈ gs, reads v g = false) →
        w0.length = w1.length →
        (∀ i : ℕ, i ≠ v.val → w0.getD i false = w1.getD i false) →
        ∀ i : ℕ, i ≠ v.val → (gs.foldl wireStep w0).getD i false = (gs.foldl wireStep w1).getD i false := by
      intro gs
      induction gs with
      | nil =>
        intro w0 w1 _ _ _ hag i hi
        exact hag i hi
      | cons g gs ih =>
        intro w0 w1 hft hrf0 hlen hag
        have hgft := hft g List.mem_cons_self
        have hgrf := hrf0 g List.mem_cons_self
        have hbit : g.op.eval (g.inputs.map fun i => w0.getD i false) =
            g.op.eval (g.inputs.map fun i => w1.getD i false) := by
          have hop' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hgft.1
          rcases hop' with hop | hop | hop
          · have hnotin : v.val ∉ g.inputs := by
              have htake : List.take 2 g.inputs = g.inputs := List.take_of_length_le hgft.2
              have hct : g.inputs.contains v.val = false := by
                have h1 : reads v g = false := hgrf
                change (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains v.val = false at h1
                rw [hop] at h1
                change (List.take 2 g.inputs).contains v.val = false at h1
                rw [htake] at h1
                exact h1
              intro hmem
              have := List.contains_iff_mem.mpr hmem
              rw [hct] at this
              exact Bool.noConfusion this
            have hmap : g.inputs.map (fun i => w0.getD i false) = g.inputs.map (fun i => w1.getD i false) := by
              apply List.map_congr_left
              intro j hj
              exact hag j (fun heq => hnotin (heq ▸ hj))
            rw [hmap]
          · have hnotin : v.val ∉ g.inputs := by
              have htake : List.take 2 g.inputs = g.inputs := List.take_of_length_le hgft.2
              have hct : g.inputs.contains v.val = false := by
                have h1 : reads v g = false := hgrf
                change (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains v.val = false at h1
                rw [hop] at h1
                change (List.take 2 g.inputs).contains v.val = false at h1
                rw [htake] at h1
                exact h1
              intro hmem
              have := List.contains_iff_mem.mpr hmem
              rw [hct] at this
              exact Bool.noConfusion this
            have hmap : g.inputs.map (fun i => w0.getD i false) = g.inputs.map (fun i => w1.getD i false) := by
              apply List.map_congr_left
              intro j hj
              exact hag j (fun heq => hnotin (heq ▸ hj))
            rw [hmap]
          · cases hins : g.inputs with
            | nil => rfl
            | cons a rest =>
              have hne : a ≠ v.val := by
                intro heq
                have h1 : reads v g = false := hgrf
                change (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains v.val = false at h1
                rw [hop, hins, heq] at h1
                change (List.take 1 (v.val :: rest)).contains v.val = false at h1
                simp at h1
              rw [hop]
              simp only [List.map_cons]
              change (!w0.getD a false) = (!w1.getD a false)
              rw [hag a hne]
        apply ih (wireStep w0 g) (wireStep w1 g)
          (fun g' hg' => hft g' (List.mem_cons_of_mem g hg'))
          (fun g' hg' => hrf0 g' (List.mem_cons_of_mem g hg'))
        · simp [wireStep, hlen]
        · intro i hi
          dsimp only [wireStep]
          by_cases hlt : i < w0.length
          · have hlt1 : i < w1.length := hlen ▸ hlt
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_append_left hlt1]
            have := hag i hi
            simpa [List.getD_eq_getElem?_getD] using this
          · by_cases heq : i = w0.length
            · subst heq
              have h0 : (w0 ++ [g.op.eval (g.inputs.map fun i => w0.getD i false)]).getD w0.length false =
                  g.op.eval (g.inputs.map fun i => w0.getD i false) := by
                simp [List.getD_eq_getElem?_getD]
              have h1 : (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)]).getD w0.length false =
                  g.op.eval (g.inputs.map fun i => w1.getD i false) := by
                rw [hlen]
                simp [List.getD_eq_getElem?_getD]
              rw [h0, h1, hbit]
            · have hge0 : (w0 ++ [g.op.eval (g.inputs.map fun i => w0.getD i false)]).length ≤ i := by
                simp; omega
              have hge1 : (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)]).length ≤ i := by
                simp [← hlen]; omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge0, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1]
    let inp0 : Fin n → Bool := fun i => decide (i = u)
    let inp1 : Fin n → Bool := fun i => decide (i = u ∨ i = v)
    have hag_init : ∀ i : ℕ, i ≠ v.val → (List.ofFn inp0).getD i false = (List.ofFn inp1).getD i false := by
      intro i hi
      by_cases hlt : i < n
      · have hlt0 : i < (List.ofFn inp0).length := by simp [hlt]
        have hlt1 : i < (List.ofFn inp1).length := by simp [hlt]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt0, Option.getD_some, List.getElem_ofFn]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt1, Option.getD_some, List.getElem_ofFn]
        have hne : (⟨i, hlt⟩ : Fin n) ≠ v := fun h => hi (congrArg Fin.val h)
        simp [inp0, inp1, hne]
      · have hge0 : (List.ofFn inp0).length ≤ i := by simp; omega
        have hge1 : (List.ofFn inp1).length ≤ i := by simp; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge0, List.getElem?_eq_none hge1]
    have hce_eq : circuitFun n C inp0 = circuitFun n C inp1 :=
      fold_agree C.gates (List.ofFn inp0) (List.ofFn inp1) hmin.1 hall_false (by simp) hag_init C.output hout_ne
    have hf0 : f inp0 = false := by
      change (decide (∃ a ∈ A, inp0 a = true) || decide (∃ p q, G.Adj p q ∧ inp0 p = true ∧ inp0 q = true)) = false
      rw [Bool.or_eq_false_iff]
      constructor
      · refine decide_eq_false ?_
        rintro ⟨a, haA, ha⟩
        have hau : a = u := of_decide_eq_true ha
        subst hau
        exact huA haA
      · refine decide_eq_false ?_
        rintro ⟨p, q, hpq, hp, hq⟩
        have hpu : p = u := of_decide_eq_true hp
        have hqu : q = u := of_decide_eq_true hq
        subst hpu; subst hqu
        exact G.ne_of_adj hpq rfl
    have hf1 : f inp1 = true := by
      change (decide (∃ a ∈ A, inp1 a = true) || decide (∃ p q, G.Adj p q ∧ inp1 p = true ∧ inp1 q = true)) = true
      rw [Bool.or_eq_true]
      right
      exact decide_eq_true ⟨v, u, huv_adj, by simp [inp1], by simp [inp1]⟩
    rw [hfun, hf0, hf1] at hce_eq
    exact Bool.noConfusion hce_eq
  have hrf_eq1 : (rf v).length = 1 := by omega
  have hrf_ne : rf v ≠ [] := by
    intro hnil
    rw [hnil] at hrf_eq1
    simp at hrf_eq1
  obtain ⟨g, hg_mem⟩ := List.exists_mem_of_ne_nil (rf v) hrf_ne
  obtain ⟨hg_in, hg_rd⟩ := List.mem_filter.mp hg_mem
  obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_iff_getElem.mp hg_in
  have hgate_eq : gateAt C k = g := by
    change C.gates.getD k ⟨GateOp.or, []⟩ = g
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt, Option.getD_some, hk_eq]
  have hk_rd : reads v (gateAt C k) = true := hgate_eq ▸ hg_rd
  have hk_op : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or ∨ (gateAt C k).op = GateOp.not := by
    have hft := hmin.1 g hg_in
    rw [← hgate_eq] at hft
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hft.1
  rcases hk_op with hop | hop | hop
  · refine h_and n G A C hdeg hgirth hiso hmin hfun hbd ?_ hno3
    refine ⟨v, hvA, k, hk_lt, hrf_eq1, hk_rd, hop, ?_⟩
    intro w hw hperm
    have hcontra := hvnopair (gateAt C k) (hgate_eq ▸ hg_mem) w hw hperm
    exact hcontra.1 hop
  · refine h_or n G A C hdeg hgirth hiso hmin hfun hbd ?_ hno3
    refine ⟨v, hvA, k, hk_lt, hrf_eq1, hk_rd, hop, ?_⟩
    intro w hw hperm
    have hcontra := hvnopair (gateAt C k) (hgate_eq ▸ hg_mem) w hw hperm
    exact hcontra.2 hop
  · refine h_not n G A C hdeg hgirth hiso hmin hfun hbd ?_ hno3
    exact ⟨v, hvA, k, hk_lt, hrf_eq1, hk_rd, hop⟩
