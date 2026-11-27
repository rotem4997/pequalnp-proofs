import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5708

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

private lemma no_four_cycle {n : ℕ} (G : SimpleGraph (Fin n))
    (hgirth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    {a b w1 w2 : Fin n} (hab : a ≠ b) (hw : w1 ≠ w2)
    (haw1 : G.Adj a w1) (haw2 : G.Adj a w2) (hbw1 : G.Adj b w1) (hbw2 : G.Adj b w2) : False := by
  have h1 : a ≠ w1 := G.ne_of_adj haw1
  have h2 : a ≠ w2 := G.ne_of_adj haw2
  have h3 : b ≠ w1 := G.ne_of_adj hbw1
  have h4 : b ≠ w2 := G.ne_of_adj hbw2
  let p : G.Walk a a :=
    .cons haw1 (.cons hbw1.symm (.cons hbw2 (.cons haw2.symm .nil)))
  have htrail : p.IsTrail := by
    rw [SimpleGraph.Walk.isTrail_def]
    simp only [p, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.nodup_cons,
      List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, Sym2.eq_iff]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> tauto
  have hcyc : p.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    refine ⟨htrail, by simp [p], ?_⟩
    simp only [p, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨h3.symm, hw, h1.symm⟩, ⟨h4, hab.symm⟩, h2.symm, not_false⟩
  have hlen : 5 ≤ p.length := hgirth a p hcyc
  simp [p] at hlen

private lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

private lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp

private lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

private lemma inputs_eq_pair {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ hmem
  unfold opnd
  rcases h : (gateAt C j).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · simp
  · simp [h] at hlen

private lemma opnd_mem_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [inputs_eq_pair hAO hj]
  fin_cases b <;> simp

private lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem_inputs hAO hj b)

private lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  unfold Circuit.wires
  rw [foldl_append_length, List.length_ofFn]

private lemma wireVal_input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n C i.val x = x i := by
  unfold wireVal Circuit.wires
  have hi : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
  rw [foldl_append_getD_lt _ C.gates (List.ofFn x) false i.val hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp

private lemma wireVal_ge {n : ℕ} (C : Circuit) {w : ℕ} (hw : n + C.gates.length ≤ w)
    (x : Fin n → Bool) :
    wireVal n C w x = false := by
  unfold wireVal
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [wires_length]; exact hw

private lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => wireVal n C w x) := by
  unfold wireVal Circuit.wires
  have hgate := foldl_append_getD_gate
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn x) false j hj ⟨GateOp.or, []⟩
  rw [List.length_ofFn] at hgate
  rw [hgate]
  change (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false) =
    (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false)
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < (List.ofFn x).length + j := by
    rw [List.length_ofFn]
    exact hAO.2.1 j hj i hi
  exact foldl_append_take_getD _ C.gates (List.ofFn x) false j i (Nat.le_of_lt hj) hilt

private lemma wireVal_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

private lemma wireVal_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

private lemma wireVal_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {x y : Fin n → Bool} (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, wireVal n C w x = true → wireVal n C w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwx
    by_cases hlt : w < n
    · have hi := wireVal_input C ⟨w, hlt⟩ x
      have hy := wireVal_input C ⟨w, hlt⟩ y
      rw [hi] at hwx
      rw [hy]
      exact hxy ⟨w, hlt⟩ hwx
    · by_cases hge : n + C.gates.length ≤ w
      · rw [wireVal_ge C hge] at hwx
        cases hwx
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hwx ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [wireVal_and hAO hj hop] at hwx ⊢
          rw [Bool.and_eq_true] at hwx ⊢
          exact ⟨ih _ (hw ▸ opnd_lt hAO hj 0) hwx.1, ih _ (hw ▸ opnd_lt hAO hj 1) hwx.2⟩
        · rw [wireVal_or hAO hj hop] at hwx ⊢
          rw [Bool.or_eq_true] at hwx ⊢
          rcases hwx with h0 | h1
          · exact Or.inl (ih _ (hw ▸ opnd_lt hAO hj 0) h0)
          · exact Or.inr (ih _ (hw ▸ opnd_lt hAO hj 1) h1)

private lemma orSets_length (n : ℕ) (C : Circuit) :
    (orSets n C).length = C.gates.length := by
  unfold orSets orStep
  rw [foldl_append_length]
  simp

private lemma orSets_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (orSets n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [orSets_length]; exact hj

private lemma orSets_getD_lt_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    (orSets n C).getD j [] =
      j :: ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (orSets n C).getD (w - n) []) := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = _
  rw [hprelen, ite_eq_left_of_eq_true _ _ (eq_true hop)]
  congr 1
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

private lemma orSets_getD_lt_not_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op ≠ GateOp.or) :
    (orSets n C).getD j [] = [j] := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = [j]
  rw [hprelen, ite_eq_right_of_eq_false _ _ (eq_false hop)]

private lemma orReaches_iff {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (w g : ℕ) :
    OrReaches n C w g ↔
      ∃ j < C.gates.length, w = n + j ∧
        (g = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ b : Fin 2, OrReaches n C (opnd C j b) g)) := by
  constructor
  · rintro ⟨hnw, hmem⟩
    have hlt : w - n < C.gates.length := by
      by_contra hge
      push Not at hge
      rw [orSets_getD_ge n C hge] at hmem
      simp at hmem
    refine ⟨w - n, hlt, by omega, ?_⟩
    by_cases hop : (gateAt C (w - n)).op = GateOp.or
    · rw [orSets_getD_lt_or n C hlt hop, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Or.inl rfl
      · right
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨u, hu, hgu⟩
        rw [List.mem_filter, decide_eq_true_eq] at hu
        rw [inputs_eq_pair hAO hlt] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu.1 with rfl | rfl
        · exact ⟨hop, 0, hu.2.1, hgu⟩
        · exact ⟨hop, 1, hu.2.1, hgu⟩
    · rw [orSets_getD_lt_not_or n C hlt hop, List.mem_singleton] at hmem
      exact Or.inl hmem
  · rintro ⟨j, hj, rfl, hcase⟩
    refine ⟨Nat.le_add_right n j, ?_⟩
    rw [Nat.add_sub_cancel_left]
    rcases hcase with rfl | ⟨hop, b, hnu, hgu⟩
    · by_cases hop : (gateAt C g).op = GateOp.or
      · rw [orSets_getD_lt_or n C hj hop]; exact List.mem_cons_self
      · rw [orSets_getD_lt_not_or n C hj hop]; exact List.mem_singleton_self g
    · rw [orSets_getD_lt_or n C hj hop, List.mem_cons]
      right
      rw [List.mem_flatMap]
      refine ⟨opnd C j b, ?_, hgu⟩
      rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨opnd_mem_inputs hAO hj b, hnu, opnd_lt hAO hj b⟩

private lemma orReaches_self {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_iff hAO (n + j) j).mpr ⟨j, hj, rfl, Or.inl rfl⟩

private lemma orReaches_le {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g → n + g ≤ w ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨_, b, hb⟩⟩
    · exact ⟨le_rfl, hj⟩
    · have hlt : opnd C j b < n + j := opnd_lt hAO hj b
      have hrec := ih _ hlt g hb
      exact ⟨by omega, hrec.2⟩

private lemma orReaches_trans {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g h : ℕ, OrReaches n C w g → OrReaches n C (n + g) h → OrReaches n C w h := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g h hwg hgh
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, b, hb⟩⟩
    · exact hgh
    · have hrec := ih _ (opnd_lt hAO hj b) g h hb hgh
      exact (orReaches_iff hAO (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, b, hrec⟩⟩

private lemma orIn_input {n : ℕ} {C : Circuit} (i : Fin n) :
    orIn n C i.val = {i} := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (hu | ⟨k, _, ⟨hni, _⟩, _, _⟩)
    · exact Fin.ext hu
    · omega
  · rintro rfl
    exact Or.inl rfl

private lemma orIn_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {w : ℕ}
    (hw : n + C.gates.length ≤ w) :
    orIn n C w = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hwk, _, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hwk
    rcases hwk with ⟨j, hj, rfl, _⟩
    omega

private lemma orIn_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hjk, hkop, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hjk
    rcases hjk with ⟨j', _, heq, hcase⟩
    have hjj' : j' = j := by omega
    subst hjj'
    rcases hcase with rfl | ⟨hor, _⟩
    · rw [hop] at hkop; cases hkop
    · rw [hop] at hor; cases hor

private lemma orIn_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext u
  unfold orIn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hjk, hkop, huk⟩)
    · omega
    · rw [orReaches_iff hAO] at hjk
      rcases hjk with ⟨j', _, heq, hcase⟩
      have hjj' : j' = j := by omega
      subst hjj'
      rcases hcase with rfl | ⟨_, b, hb⟩
      · rw [inputs_eq_pair hAO hj] at huk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
        rcases huk with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (Or.inl h1)
      · fin_cases b
        · exact Or.inl (Or.inr ⟨k, hk, hb, hkop, huk⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hb, hkop, huk⟩)
  · rintro ((h0 | ⟨k, hk, h0k, hkop, huk⟩) | (h1 | ⟨k, hk, h1k, hkop, huk⟩))
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h0]
      exact opnd_mem_inputs hAO hj 0
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 0, h0k⟩⟩
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h1]
      exact opnd_mem_inputs hAO hj 1
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 1, h1k⟩⟩

private lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {w g : ℕ} (hwg : OrReaches n C w g) :
    orIn n C (n + g) ⊆ orIn n C w := by
  intro u hu
  unfold orIn at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with hEq | ⟨k, hk, hgk, hkop, huk⟩
  · omega
  · exact Or.inr ⟨k, hk, orReaches_trans hAO w g k hwg hgk, hkop, huk⟩

private lemma wireVal_true_of_mem_orIn {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {i : Fin n} {x : Fin n → Bool} (hxi : x i = true) :
    ∀ w : ℕ, i ∈ orIn n C w → wireVal n C w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hi
    by_cases hlt : w < n
    · have heq : orIn n C w = {⟨w, hlt⟩} := orIn_input ⟨w, hlt⟩
      rw [heq, Finset.mem_singleton] at hi
      subst hi
      exact (wireVal_input C ⟨w, hlt⟩ x).trans hxi
    · by_cases hge : n + C.gates.length ≤ w
      · rw [orIn_ge hAO hge] at hi
        simp at hi
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hi ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [orIn_and hAO hj hop] at hi
          simp at hi
        · rw [orIn_or hAO hj hop, Finset.mem_union] at hi
          rw [wireVal_or hAO hj hop, Bool.or_eq_true]
          rcases hi with h0 | h1
          · exact Or.inl (ih _ (hw ▸ opnd_lt hAO hj 0) h0)
          · exact Or.inr (ih _ (hw ▸ opnd_lt hAO hj 1) h1)

private lemma mem_tops {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {g : ℕ} (hg : g ∈ tops G C) :
    g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧ BelowF G C g := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold tops gatesWhere at hg
  rw [Finset.mem_filter, Finset.mem_range] at hg
  exact hg

private lemma adj_of_top_side {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    {u v : Fin n} (hu : u ∈ side C a b)
    (hv : wireVal n C (opnd C a (1 - b)) (fun w => decide (w = v)) = true) :
    G.Adj u v := by
  rcases mem_tops ha with ⟨haj, hop, hbelow⟩
  have h1 : wireVal n C (opnd C a b) (pairInput u v) = true := by
    apply wireVal_true_of_mem_orIn hAO _ (opnd C a b) hu
    simp [pairInput]
  have h2 : wireVal n C (opnd C a (1 - b)) (pairInput u v) = true := by
    apply wireVal_mono hAO _ _ hv
    intro w hw
    simp only [decide_eq_true_eq] at hw
    simp [pairInput, hw]
  have h01 : wireVal n C (opnd C a 0) (pairInput u v) = true ∧
      wireVal n C (opnd C a 1) (pairInput u v) = true := by
    fin_cases b
    · exact ⟨h1, h2⟩
    · exact ⟨h2, h1⟩
  have hga : gateVal n C a (pairInput u v) = true := by
    change wireVal n C (n + a) (pairInput u v) = true
    rw [wireVal_and hAO haj hop, Bool.and_eq_true]
    exact h01
  have hgf : graphFun G ∅ (pairInput u v) = true := hbelow (pairInput u v) hga
  unfold graphFun at hgf
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq] at hgf
  rcases hgf with ⟨p, q, hpq, hp, hq⟩
  simp only [pairInput, decide_eq_true_eq] at hp hq
  have hne : p ≠ q := G.ne_of_adj hpq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl hne
  · exact hpq
  · exact hpq.symm
  · exact absurd rfl hne

open Classical in
private noncomputable def bigOrReach (n : ℕ) (C : Circuit) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun g =>
    (gateAt C g).op = GateOp.or ∧ 2 ≤ (orIn n C (n + g)).card ∧ ∃ w ∈ W, OrReaches n C w g

private lemma leaf_count_bound {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ k : ℕ, ∀ W : Finset ℕ, (bigOrReach n C W).card = k →
      (W.biUnion (orIn n C)).card ≤ W.card + k := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro W hk
    by_cases hne : (bigOrReach n C W).Nonempty
    · set M := bigOrReach n C W
      set m := M.max' hne
      have hmM : m ∈ M := Finset.max'_mem M hne
      have hm_props : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
          2 ≤ (orIn n C (n + m)).card ∧ ∃ w ∈ W, OrReaches n C w m := by
        simpa [M, bigOrReach, Finset.mem_filter, Finset.mem_range] using hmM
      have hmax_unique : ∀ w ∈ W, OrReaches n C w m → w = n + m := by
        intro w hw hwm
        have hle := orReaches_le hAO w m hwm
        rw [orReaches_iff hAO] at hwm
        rcases hwm with ⟨j, hj, rfl, hcase⟩
        by_contra hne_w
        have hmj : m ≠ j := fun h => hne_w (by omega)
        rcases hcase with hEq | ⟨hjop, b, hb⟩
        · exact hmj hEq
        · have hjM : j ∈ M := by
            simp only [M, bigOrReach, Finset.mem_filter, Finset.mem_range]
            refine ⟨hj, hjop, ?_, n + j, hw, orReaches_self hAO hj⟩
            have hsub : orIn n C (n + m) ⊆ orIn n C (n + j) :=
              orIn_subset_of_orReaches hAO
                ((orReaches_iff hAO (n + j) m).mpr ⟨j, hj, rfl, Or.inr ⟨hjop, b, hb⟩⟩)
            exact le_trans hm_props.2.2.1 (Finset.card_le_card hsub)
          have hjle : j ≤ m := Finset.le_max' M j hjM
          omega
      have hnmW : n + m ∈ W := by
        rcases hm_props.2.2.2 with ⟨w, hw, hwm⟩
        rwa [hmax_unique w hw hwm] at hw
      set W' : Finset ℕ := insert (opnd C m 0) (insert (opnd C m 1) (W.erase (n + m)))
      have hbi : W.biUnion (orIn n C) ⊆ W'.biUnion (orIn n C) := by
        intro u hu
        rw [Finset.mem_biUnion] at hu ⊢
        rcases hu with ⟨w, hw, huw⟩
        by_cases hwm : w = n + m
        · subst hwm
          rw [orIn_or hAO hm_props.1 hm_props.2.1, Finset.mem_union] at huw
          rcases huw with h0 | h1
          · exact ⟨opnd C m 0, by simp [W'], h0⟩
          · exact ⟨opnd C m 1, by simp [W'], h1⟩
        · exact ⟨w, by simp [W', hw, hwm], huw⟩
      have hW'card : W'.card ≤ W.card + 1 := by
        have h1 : W'.card ≤ (insert (opnd C m 1) (W.erase (n + m))).card + 1 :=
          Finset.card_insert_le _ _
        have h2 : (insert (opnd C m 1) (W.erase (n + m))).card ≤ (W.erase (n + m)).card + 1 :=
          Finset.card_insert_le _ _
        have h3 : (W.erase (n + m)).card + 1 = W.card := Finset.card_erase_add_one hnmW
        omega
      have hM'sub : bigOrReach n C W' ⊆ M.erase m := by
        intro g hg
        simp only [bigOrReach, Finset.mem_filter, Finset.mem_range] at hg
        rcases hg with ⟨hglt, hgop, hgcard, w', hw', hw'g⟩
        rw [Finset.mem_erase]
        have hgM : g ∈ M := by
          simp only [M, bigOrReach, Finset.mem_filter, Finset.mem_range]
          refine ⟨hglt, hgop, hgcard, ?_⟩
          simp only [W', Finset.mem_insert, Finset.mem_erase] at hw'
          rcases hw' with rfl | rfl | ⟨_, hw'W⟩
          · exact ⟨n + m, hnmW,
              (orReaches_iff hAO (n + m) g).mpr ⟨m, hm_props.1, rfl, Or.inr ⟨hm_props.2.1, 0, hw'g⟩⟩⟩
          · exact ⟨n + m, hnmW,
              (orReaches_iff hAO (n + m) g).mpr ⟨m, hm_props.1, rfl, Or.inr ⟨hm_props.2.1, 1, hw'g⟩⟩⟩
          · exact ⟨w', hw'W, hw'g⟩
        refine ⟨?_, hgM⟩
        intro hgm
        subst hgm
        simp only [W', Finset.mem_insert, Finset.mem_erase] at hw'
        rcases hw' with rfl | rfl | ⟨hne', hw'W⟩
        · have hle := (orReaches_le hAO _ _ hw'g).1
          have hlt := opnd_lt hAO hm_props.1 0
          omega
        · have hle := (orReaches_le hAO _ _ hw'g).1
          have hlt := opnd_lt hAO hm_props.1 1
          omega
        · exact hne' (hmax_unique w' hw'W hw'g)
      have hM'card_le : (bigOrReach n C W').card ≤ (M.erase m).card :=
        Finset.card_le_card hM'sub
      have hMerase : (M.erase m).card + 1 = k := by
        rw [Finset.card_erase_add_one hmM, hk]
      have hM'lt : (bigOrReach n C W').card < k := by omega
      have hrec := ih _ hM'lt W' rfl
      have hbi_card : (W.biUnion (orIn n C)).card ≤ (W'.biUnion (orIn n C)).card :=
        Finset.card_le_card hbi
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hle1 : ∀ w ∈ W, (orIn n C w).card ≤ 1 := by
        intro w hw
        by_contra hgt
        push Not at hgt
        have hge2 : 2 ≤ (orIn n C w).card := hgt
        by_cases hlt : w < n
        · have heq : orIn n C w = {⟨w, hlt⟩} := orIn_input ⟨w, hlt⟩
          rw [heq, Finset.card_singleton] at hge2
          omega
        · by_cases hge : n + C.gates.length ≤ w
          · rw [orIn_ge hAO hge, Finset.card_empty] at hge2
            omega
          · set j := w - n
            have hwEq : w = n + j := by omega
            have hj : j < C.gates.length := by omega
            have hmem : gateAt C j ∈ C.gates := by
              unfold gateAt
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
              exact List.getElem_mem hj
            rw [hwEq] at hge2 hw
            rcases hAO.1 _ hmem with hop | hop
            · rw [orIn_and hAO hj hop, Finset.card_empty] at hge2
              omega
            · have hjM : j ∈ bigOrReach n C W := by
                simp only [bigOrReach, Finset.mem_filter, Finset.mem_range]
                exact ⟨hj, hop, hge2, n + j, hw, orReaches_self hAO hj⟩
              rw [hne] at hjM
              simp at hjM
      have hbi : (W.biUnion (orIn n C)).card ≤ ∑ w ∈ W, (orIn n C w).card :=
        Finset.card_biUnion_le
      have hsum : ∑ w ∈ W, (orIn n C w).card ≤ ∑ _w ∈ W, 1 :=
        Finset.sum_le_sum hle1
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
      omega

private lemma main_bound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hgirth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (C : Circuit) (hAO : IsAO2 n C) :
    {x9 : Sym2 (Fin n) | ∃ x10 ∈ tops G C, ∃ (x11 : Fin 2),
      (∃ (x12 : Fin n) (x13 : Fin n), x12 ≠ x13 ∧ x12 ∈ side C x10 x11 ∧ x13 ∈ side C x10 x11) ∧
      ∃ x12 ∈ side C x10 x11, ∃ (x13 : Fin n), x9 = s(x12, x13) ∧
      { gates := C.gates, output := opnd C x10 ((1 : Fin 2) - x11) : Circuit }.eval
        (List.ofFn fun (x14 : Fin n) => Decidable.decide (x14 = x13)) = Bool.true}.ncard ≤
      3 * (C.size + 1) := by
  classical
  let Kv : Fin n → Finset (ℕ × Fin 2) := fun v =>
    ((tops G C) ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p =>
      2 ≤ (side (n := n) C p.1 p.2).card ∧
      wireVal n C (opnd C p.1 (1 - p.2)) (fun w => decide (w = v)) = true
  let Wv : Fin n → Finset ℕ := fun v => (Kv v).image fun p => opnd C p.1 p.2
  let Lv : Fin n → Finset (Fin n) := fun v => (Wv v).biUnion (orIn n C)
  let Mv : Fin n → Finset ℕ := fun v => bigOrReach n C (Wv v)
  let F : Finset (Sym2 (Fin n)) :=
    (Finset.univ : Finset (Fin n)).biUnion fun v => (Lv v).image fun u => s(u, v)
  have hsub : {x9 : Sym2 (Fin n) | ∃ x10 ∈ tops G C, ∃ (x11 : Fin 2),
      (∃ (x12 : Fin n) (x13 : Fin n), x12 ≠ x13 ∧ x12 ∈ side C x10 x11 ∧ x13 ∈ side C x10 x11) ∧
      ∃ x12 ∈ side C x10 x11, ∃ (x13 : Fin n), x9 = s(x12, x13) ∧
      { gates := C.gates, output := opnd C x10 ((1 : Fin 2) - x11) : Circuit }.eval
        (List.ofFn fun (x14 : Fin n) => Decidable.decide (x14 = x13)) = Bool.true} ⊆ (F : Set (Sym2 (Fin n))) := by
    rintro e ⟨a, ha, b, ⟨u1, u2, hne12, hu1, hu2⟩, u, hu, v, rfl, heval⟩
    rw [Finset.mem_coe]
    simp only [F, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    refine ⟨v, u, ?_, rfl⟩
    have hcard : 2 ≤ (side (n := n) C a b).card := by
      have hlt : 1 < (side (n := n) C a b).card :=
        Finset.one_lt_card.mpr ⟨u1, hu1, u2, hu2, hne12⟩
      omega
    have hwv : wireVal n C (opnd C a (1 - b)) (fun w => decide (w = v)) = true := heval
    have hpK : (a, b) ∈ Kv v := by
      simp only [Kv, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨ha, hcard, hwv⟩
    simp only [Lv, Wv, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨opnd C a b, ⟨(a, b), hpK, rfl⟩, hu⟩
  have hncard : {x9 : Sym2 (Fin n) | ∃ x10 ∈ tops G C, ∃ (x11 : Fin 2),
      (∃ (x12 : Fin n) (x13 : Fin n), x12 ≠ x13 ∧ x12 ∈ side C x10 x11 ∧ x13 ∈ side C x10 x11) ∧
      ∃ x12 ∈ side C x10 x11, ∃ (x13 : Fin n), x9 = s(x12, x13) ∧
      { gates := C.gates, output := opnd C x10 ((1 : Fin 2) - x11) : Circuit }.eval
        (List.ofFn fun (x14 : Fin n) => Decidable.decide (x14 = x13)) = Bool.true}.ncard ≤ F.card := by
    calc _ ≤ (F : Set (Sym2 (Fin n))).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet F)
      _ = F.card := Set.ncard_coe_finset F
  have hF_le : F.card ≤ ∑ v : Fin n, (Lv v).card := by
    calc F.card ≤ ∑ v : Fin n, ((Lv v).image fun u => s(u, v)).card := Finset.card_biUnion_le
      _ ≤ ∑ v : Fin n, (Lv v).card := Finset.sum_le_sum fun v _ => Finset.card_image_le
  have hLv_le : ∀ v : Fin n, (Lv v).card ≤ (Kv v).card + (Mv v).card := by
    intro v
    have h1 := leaf_count_bound hAO (Mv v).card (Wv v) rfl
    have h2 : (Wv v).card ≤ (Kv v).card := Finset.card_image_le
    exact le_trans h1 (Nat.add_le_add_right h2 _)
  have hsum_L : ∑ v : Fin n, (Lv v).card ≤ (∑ v : Fin n, (Kv v).card) + ∑ v : Fin n, (Mv v).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v _ => hLv_le v
  have hK_disj : Set.PairwiseDisjoint (Set.univ : Set (Fin n)) Kv := by
    intro v1 _ v2 _ hvne
    change Disjoint (Kv v1) (Kv v2)
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Kv, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp1 hp2
    have hlt : 1 < (side (n := n) C p.1 p.2).card := by omega
    rcases Finset.one_lt_card.mp hlt with ⟨u1, hu1, u2, hu2, hune⟩
    exact no_four_cycle G hgirth hvne hune
      (adj_of_top_side hAO hp1.1 p.2 hu1 hp1.2.2).symm
      (adj_of_top_side hAO hp1.1 p.2 hu2 hp1.2.2).symm
      (adj_of_top_side hAO hp2.1 p.2 hu1 hp2.2.2).symm
      (adj_of_top_side hAO hp2.1 p.2 hu2 hp2.2.2).symm
  have hM_disj : Set.PairwiseDisjoint (Set.univ : Set (Fin n)) Mv := by
    intro v1 _ v2 _ hvne
    change Disjoint (Mv v1) (Mv v2)
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    simp only [Mv, bigOrReach, Finset.mem_filter, Finset.mem_range] at hg1 hg2
    rcases hg1 with ⟨_, _, hgcard, w1, hw1, hw1g⟩
    rcases hg2 with ⟨_, _, _, w2, hw2, hw2g⟩
    simp only [Wv, Finset.mem_image] at hw1 hw2
    rcases hw1 with ⟨p1, hp1, rfl⟩
    rcases hw2 with ⟨p2, hp2, rfl⟩
    simp only [Kv, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp1 hp2
    have hlt : 1 < (orIn n C (n + g)).card := by omega
    rcases Finset.one_lt_card.mp hlt with ⟨u1, hu1, u2, hu2, hune⟩
    have hsub1 : orIn n C (n + g) ⊆ side C p1.1 p1.2 := orIn_subset_of_orReaches hAO hw1g
    have hsub2 : orIn n C (n + g) ⊆ side C p2.1 p2.2 := orIn_subset_of_orReaches hAO hw2g
    exact no_four_cycle G hgirth hvne hune
      (adj_of_top_side hAO hp1.1 p1.2 (hsub1 hu1) hp1.2.2).symm
      (adj_of_top_side hAO hp1.1 p1.2 (hsub1 hu2) hp1.2.2).symm
      (adj_of_top_side hAO hp2.1 p2.2 (hsub2 hu1) hp2.2.2).symm
      (adj_of_top_side hAO hp2.1 p2.2 (hsub2 hu2) hp2.2.2).symm
  have hsum_K : ∑ v : Fin n, (Kv v).card ≤ 2 * (tops G C).card := by
    rw [← Finset.card_biUnion (by intro a ha b hb hab; exact hK_disj (by simp) (by simp) hab)]
    have hsubK : (Finset.univ : Finset (Fin n)).biUnion Kv ⊆ (tops G C) ×ˢ (Finset.univ : Finset (Fin 2)) := by
      intro p hp
      rw [Finset.mem_biUnion] at hp
      rcases hp with ⟨v, _, hpv⟩
      exact (Finset.mem_filter.mp hpv).1
    calc ((Finset.univ : Finset (Fin n)).biUnion Kv).card
        ≤ ((tops G C) ×ˢ (Finset.univ : Finset (Fin 2))).card := Finset.card_le_card hsubK
      _ = (tops G C).card * 2 := by simp [Finset.card_product]
      _ = 2 * (tops G C).card := Nat.mul_comm _ _
  have hsum_M : ∑ v : Fin n, (Mv v).card ≤
      ((Finset.range C.gates.length).filter fun g => (gateAt C g).op = GateOp.or).card := by
    rw [← Finset.card_biUnion (by intro a ha b hb hab; exact hM_disj (by simp) (by simp) hab)]
    apply Finset.card_le_card
    intro g hg
    rw [Finset.mem_biUnion] at hg
    rcases hg with ⟨v, _, hgv⟩
    simp only [Mv, bigOrReach, Finset.mem_filter, Finset.mem_range] at hgv ⊢
    exact ⟨hgv.1, hgv.2.1⟩
  have htops_le : (tops G C).card ≤ C.gates.length := by
    calc (tops G C).card
        ≤ (Finset.range C.gates.length).card :=
          Finset.card_le_card fun g hg => Finset.mem_range.mpr (mem_tops hg).1
      _ = C.gates.length := Finset.card_range _
  have hdisj_top_or : Disjoint (tops G C)
      ((Finset.range C.gates.length).filter fun g => (gateAt C g).op = GateOp.or) := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have h1 := (mem_tops hg1).2.1
    rw [Finset.mem_filter] at hg2
    rw [h1] at hg2
    cases hg2.2
  have htop_or : (tops G C).card +
      ((Finset.range C.gates.length).filter fun g => (gateAt C g).op = GateOp.or).card ≤
      C.gates.length := by
    rw [← Finset.card_union_of_disjoint hdisj_top_or]
    calc (tops G C ∪ (Finset.range C.gates.length).filter fun g => (gateAt C g).op = GateOp.or).card
        ≤ (Finset.range C.gates.length).card := by
          apply Finset.card_le_card
          intro g hg
          rw [Finset.mem_union] at hg
          rcases hg with hg | hg
          · exact Finset.mem_range.mpr (mem_tops hg).1
          · exact (Finset.mem_filter.mp hg).1
      _ = C.gates.length := Finset.card_range _
  change _ ≤ 3 * (C.gates.length + 1)
  omega

end PEqualNP.Outside.L_meta_5708

theorem PEqualNP.Outside.L_meta_5708 :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 : Fin x1) (x5 : x2.Walk x4 x4), x5.IsCycle → (5 : ℕ) ≤ x5.length) → x2.edgeFinset.Nonempty → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x6 → PEqualNP.TopForm.TopForm x2 x6 → {x9 : Sym2 (Fin x1) | ∃ x10 ∈ PEqualNP.TopForm.tops x2 x6, ∃ (x11 : Fin (2 : ℕ)), (∃ (x12 : Fin x1) (x13 : Fin x1), x12 ≠ x13 ∧ x12 ∈ PEqualNP.TopForm.side x6 x10 x11 ∧ x13 ∈ PEqualNP.TopForm.side x6 x10 x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.side x6 x10 x11, ∃ (x13 : Fin x1), x9 = s(x12, x13) ∧ { gates := x6.gates, output := PEqualNP.TopForm.opnd x6 x10 ((1 : Fin (2 : ℕ)) - x11) : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn fun (x14 : Fin x1) => Decidable.decide (x14 = x13)) = Bool.true}.ncard ≤ (3 : ℕ) * (x6.size + (1 : ℕ)) :=
  fun x1 x2 _ hgirth _ x6 hLeast _ =>
    PEqualNP.Outside.L_meta_5708.main_bound x1 x2 hgirth x6 hLeast.1
