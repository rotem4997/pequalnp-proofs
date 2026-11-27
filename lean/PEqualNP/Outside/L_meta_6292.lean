import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6292

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK

private lemma no_c4 {n : ℕ} {R : Fin n → Fin n → Prop}
    (hplane : ∀ a b : Fin n, a ≠ b → ∃! c : Fin n, R a c ∧ R b c)
    {a1 a2 b1 b2 : Fin n} (ha : a1 ≠ a2) (hb : b1 ≠ b2)
    (h11 : R a1 b1) (h12 : R a1 b2) (h21 : R a2 b1) (h22 : R a2 b2) : False := by
  rcases hplane a1 a2 ha with ⟨c, _, huniq⟩
  have hb1 : b1 = c := huniq b1 ⟨h11, h21⟩
  have hb2 : b2 = c := huniq b2 ⟨h12, h22⟩
  exact hb (hb1.trans hb2.symm)

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

private lemma mem_insertNew {A : List (List ℕ)} {x y : List ℕ} :
    x ∈ insertNew A y ↔ x ∈ A ∨ x = y := by
  unfold insertNew
  split_ifs with hy
  · constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · exact hy
  · simp

private lemma mem_foldl_insertNew {A B : List (List ℕ)} {x : List ℕ} :
    x ∈ B.foldl insertNew A ↔ x ∈ A ∨ x ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih, mem_insertNew]
    tauto

private lemma mem_andStep {k : ℕ} {A B : List (List ℕ)} {x : List ℕ} :
    x ∈ andStep k A B ↔ ∃ a ∈ A, ∃ b ∈ B, x = capAdd k a b := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

private lemma readVectors_length (C : Circuit) (N : ℕ) (S : List ℕ) (k : ℕ) :
    (readVectors C N S k).length = N + C.gates.length := by
  unfold readVectors
  rw [foldl_append_length, List.length_map, List.length_range]

private lemma readVectors_getD_input (C : Circuit) (N : ℕ) (S : List ℕ) (k : ℕ)
    {i : ℕ} (hi : i < N) :
    (readVectors C N S k).getD i [] = leafVectors S k i := by
  unfold readVectors
  have hi' : i < ((List.range N).map (leafVectors S k)).length := by
    rw [List.length_map, List.length_range]
    exact hi
  rw [foldl_append_getD_lt _ C.gates _ [] i hi']
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  simp

private lemma readVectors_getD_ge (C : Circuit) (N : ℕ) (S : List ℕ) (k : ℕ)
    {w : ℕ} (hw : N + C.gates.length ≤ w) :
    (readVectors C N S k).getD w [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [readVectors_length]; exact hw

private lemma readVectors_getD_gate {N : ℕ} {C : Circuit} (hAO : IsAO2 N C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length) :
    (readVectors C N S k).getD (N + j) [] =
      let ins := (gateAt C j).inputs.map fun i => (readVectors C N S k).getD i []
      match (gateAt C j).op with
      | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
      | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
      | _ => [] := by
  unfold readVectors
  let step : List (List (List ℕ)) → Gate → List (List ℕ) := fun R g =>
    let ins := g.inputs.map fun i => R.getD i []
    match g.op with
    | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
    | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
    | _ => []
  let init := (List.range N).map (leafVectors S k)
  have hinitlen : init.length = N := by simp [init]
  have hgate := foldl_append_getD_gate step C.gates init [] j hj ⟨GateOp.or, []⟩
  rw [hinitlen] at hgate
  change (C.gates.foldl (fun R g => R ++ [step R g]) init).getD (N + j) [] =
    step (C.gates.foldl (fun R g => R ++ [step R g]) init) (gateAt C j)
  rw [hgate]
  change step ((C.gates.take j).foldl (fun R g => R ++ [step R g]) init) (gateAt C j) =
    step (C.gates.foldl (fun R g => R ++ [step R g]) init) (gateAt C j)
  have hins :
      ((gateAt C j).inputs.map fun i =>
        ((C.gates.take j).foldl (fun R g => R ++ [step R g]) init).getD i []) =
      ((gateAt C j).inputs.map fun i =>
        (C.gates.foldl (fun R g => R ++ [step R g]) init).getD i []) := by
    apply List.map_congr_left
    intro i hi
    have hilt : i < init.length + j := by
      rw [hinitlen]
      exact hAO.2.1 j hj i hi
    exact foldl_append_take_getD step C.gates init [] j i (Nat.le_of_lt hj) hilt
  dsimp only [step]
  rw [hins]

private lemma mem_readVectors_or {N : ℕ} {C : Circuit} (hAO : IsAO2 N C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) {x : List ℕ} :
    x ∈ (readVectors C N S k).getD (N + j) [] ↔
      x ∈ (readVectors C N S k).getD (opnd C j 0) [] ∨
      x ∈ (readVectors C N S k).getD (opnd C j 1) [] := by
  rw [readVectors_getD_gate hAO S k hj, hop, inputs_eq_pair hAO hj]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [mem_foldl_insertNew, mem_foldl_insertNew]
  simp

private lemma mem_readVectors_and {N : ℕ} {C : Circuit} (hAO : IsAO2 N C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) {x : List ℕ} :
    x ∈ (readVectors C N S k).getD (N + j) [] ↔
      ∃ a ∈ (readVectors C N S k).getD (opnd C j 0) [],
      ∃ b ∈ (readVectors C N S k).getD (opnd C j 1) [],
        x = capAdd k (capAdd k (S.map fun _ => 0) a) b := by
  rw [readVectors_getD_gate hAO S k hj, hop, inputs_eq_pair hAO hj]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [mem_andStep]
  constructor
  · rintro ⟨t, ht, b, hb, rfl⟩
    rw [mem_andStep] at ht
    rcases ht with ⟨z, hz, a, ha, rfl⟩
    simp only [List.mem_singleton] at hz
    subst hz
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨capAdd k (S.map fun _ => 0) a, ?_, b, hb, rfl⟩
    rw [mem_andStep]
    exact ⟨S.map fun _ => 0, List.mem_singleton_self _, a, ha, rfl⟩

private lemma readVectors_pair_nonempty {n : ℕ} {C : Circuit} (hAO : IsAO2 (n + n) C)
    (u v : Fin n) :
    ∀ w : ℕ, ∀ vec ∈ (readVectors C (n + n) [u.val, n + v.val] 1).getD w [],
      ∃ a b : ℕ, vec = [a, b] ∧ 1 ≤ a + b := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro vec hvec
    by_cases hlt : w < n + n
    · rw [readVectors_getD_input C (n + n) _ 1 hlt] at hvec
      unfold leafVectors at hvec
      have hne : u.val ≠ n + v.val := by omega
      split_ifs at hvec with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton, List.map_cons, List.map_nil] at hvec
        rcases hmem with rfl | rfl
        · refine ⟨1, 0, ?_, by omega⟩
          rw [hvec]
          simp [hne.symm]
        · refine ⟨0, 1, ?_, by omega⟩
          rw [hvec]
          simp [hne]
      · simp at hvec
    · by_cases hge : (n + n) + C.gates.length ≤ w
      · rw [readVectors_getD_ge C (n + n) _ 1 hge] at hvec
        simp at hvec
      · set j := w - (n + n)
        have hw : w = (n + n) + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hvec
        rcases hAO.1 _ hmem with hop | hop
        · rw [mem_readVectors_and hAO _ 1 hj hop] at hvec
          rcases hvec with ⟨va, hva, vb, hvb, rfl⟩
          rcases ih _ (hw ▸ opnd_lt hAO hj 0) va hva with ⟨a0, a1, rfl, ha⟩
          rcases ih _ (hw ▸ opnd_lt hAO hj 1) vb hvb with ⟨b0, b1, rfl, hb⟩
          refine ⟨min (min a0 2 + b0) 2, min (min a1 2 + b1) 2, ?_, by omega⟩
          simp [capAdd]
        · rw [mem_readVectors_or hAO _ 1 hj hop] at hvec
          rcases hvec with h0 | h1
          · exact ih _ (hw ▸ opnd_lt hAO hj 0) vec h0
          · exact ih _ (hw ▸ opnd_lt hAO hj 1) vec h1

private lemma readVectors_unit_left {n : ℕ} {C : Circuit} (hAO : IsAO2 (n + n) C)
    (u v : Fin n) :
    ∀ w : ℕ, [1, 0] ∈ (readVectors C (n + n) [u.val, n + v.val] 1).getD w [] →
      Fin.castAdd n u ∈ orIn (n + n) C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hvec
    by_cases hlt : w < n + n
    · rw [readVectors_getD_input C (n + n) _ 1 hlt] at hvec
      unfold leafVectors at hvec
      have hne : u.val ≠ n + v.val := by omega
      split_ifs at hvec with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton, List.map_cons, List.map_nil] at hvec
        rcases hmem with rfl | rfl
        · have heq : orIn (n + n) C (Fin.castAdd n u).val = {Fin.castAdd n u} :=
            orIn_input (Fin.castAdd n u)
          simpa using heq ▸ Finset.mem_singleton_self (Fin.castAdd n u)
        · simp [hne] at hvec
      · simp at hvec
    · by_cases hge : (n + n) + C.gates.length ≤ w
      · rw [readVectors_getD_ge C (n + n) _ 1 hge] at hvec
        simp at hvec
      · set j := w - (n + n)
        have hw : w = (n + n) + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hvec ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [mem_readVectors_and hAO _ 1 hj hop] at hvec
          rcases hvec with ⟨va, hva, vb, hvb, heq⟩
          rcases readVectors_pair_nonempty hAO u v _ va hva with ⟨a0, a1, rfl, ha⟩
          rcases readVectors_pair_nonempty hAO u v _ vb hvb with ⟨b0, b1, rfl, hb⟩
          simp [capAdd] at heq
          omega
        · rw [mem_readVectors_or hAO _ 1 hj hop] at hvec
          rw [orIn_or hAO hj hop, Finset.mem_union]
          rcases hvec with h0 | h1
          · exact Or.inl (ih _ (hw ▸ opnd_lt hAO hj 0) h0)
          · exact Or.inr (ih _ (hw ▸ opnd_lt hAO hj 1) h1)

private lemma readVectors_unit_right {n : ℕ} {C : Circuit} (hAO : IsAO2 (n + n) C)
    (u v : Fin n) :
    ∀ w : ℕ, [0, 1] ∈ (readVectors C (n + n) [u.val, n + v.val] 1).getD w [] →
      Fin.natAdd n v ∈ orIn (n + n) C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hvec
    by_cases hlt : w < n + n
    · rw [readVectors_getD_input C (n + n) _ 1 hlt] at hvec
      unfold leafVectors at hvec
      have hne : u.val ≠ n + v.val := by omega
      split_ifs at hvec with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton, List.map_cons, List.map_nil] at hvec
        rcases hmem with rfl | rfl
        · simp [hne.symm] at hvec
        · have heq : orIn (n + n) C (n + v.val) = {Fin.natAdd n v} := by
            have h1 := orIn_input (C := C) (Fin.natAdd n v)
            rwa [Fin.val_natAdd] at h1
          rw [heq]
          exact Finset.mem_singleton_self (Fin.natAdd n v)
      · simp at hvec
    · by_cases hge : (n + n) + C.gates.length ≤ w
      · rw [readVectors_getD_ge C (n + n) _ 1 hge] at hvec
        simp at hvec
      · set j := w - (n + n)
        have hw : w = (n + n) + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hvec ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [mem_readVectors_and hAO _ 1 hj hop] at hvec
          rcases hvec with ⟨va, hva, vb, hvb, heq⟩
          rcases readVectors_pair_nonempty hAO u v _ va hva with ⟨a0, a1, rfl, ha⟩
          rcases readVectors_pair_nonempty hAO u v _ vb hvb with ⟨b0, b1, rfl, hb⟩
          simp [capAdd] at heq
          omega
        · rw [mem_readVectors_or hAO _ 1 hj hop] at hvec
          rw [orIn_or hAO hj hop, Finset.mem_union]
          rcases hvec with h0 | h1
          · exact Or.inl (ih _ (hw ▸ opnd_lt hAO hj 0) h0)
          · exact Or.inr (ih _ (hw ▸ opnd_lt hAO hj 1) h1)

private lemma readVectors_and_extract {n : ℕ} {C : Circuit} (hAO : IsAO2 (n + n) C)
    {g : ℕ} (hg : g < C.gates.length) (hop : (gateAt C g).op = GateOp.and)
    (u v : Fin n)
    (h11 : [1, 1] ∈ (readVectors C (n + n) [u.val, n + v.val] 1).getD ((n + n) + g) []) :
    ∃ b : Fin 2, Fin.castAdd n u ∈ side C g b ∧ Fin.natAdd n v ∈ side C g (1 - b) := by
  rw [mem_readVectors_and hAO _ 1 hg hop] at h11
  rcases h11 with ⟨va, hva, vb, hvb, heq⟩
  rcases readVectors_pair_nonempty hAO u v _ va hva with ⟨a0, a1, rfl, ha⟩
  rcases readVectors_pair_nonempty hAO u v _ vb hvb with ⟨b0, b1, rfl, hb⟩
  simp [capAdd] at heq
  have hcases : (a0 = 1 ∧ a1 = 0 ∧ b0 = 0 ∧ b1 = 1) ∨
      (a0 = 0 ∧ a1 = 1 ∧ b0 = 1 ∧ b1 = 0) := by omega
  rcases hcases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · refine ⟨0, ?_, ?_⟩
    · exact readVectors_unit_left hAO u v (opnd C g 0) hva
    · exact readVectors_unit_right hAO u v (opnd C g 1) hvb
  · refine ⟨1, ?_, ?_⟩
    · exact readVectors_unit_left hAO u v (opnd C g 1) hvb
    · exact readVectors_unit_right hAO u v (opnd C g 0) hva

private lemma rel_of_cross_pair {n : ℕ} {R : Fin n → Fin n → Prop}
    {C : Circuit} (hAO : IsAO2 (n + n) C) {A : Finset ℕ}
    (hA : ∀ g ∈ A, g < C.gates.length ∧ (gateAt C g).op = GateOp.and)
    (hnonedge : ∀ u v : Fin n, ¬ R u v → ∀ g ∈ A,
      gateVal (n + n) C g (fun x => Decidable.decide (x = Fin.castAdd n u ∨ x = Fin.natAdd n v)) = false)
    {g : ℕ} (hg : g ∈ A) (b : Fin 2) {u v : Fin n}
    (hu : Fin.castAdd n u ∈ side C g b) (hv : Fin.natAdd n v ∈ side C g (1 - b)) :
    R u v := by
  by_contra hnr
  let inp : Fin (n + n) → Bool :=
    fun x => Decidable.decide (x = Fin.castAdd n u ∨ x = Fin.natAdd n v)
  have h1 : wireVal (n + n) C (opnd C g b) inp = true := by
    apply wireVal_true_of_mem_orIn hAO _ (opnd C g b) hu
    simp [inp]
  have h2 : wireVal (n + n) C (opnd C g (1 - b)) inp = true := by
    apply wireVal_true_of_mem_orIn hAO _ (opnd C g (1 - b)) hv
    simp [inp]
  have h01 : wireVal (n + n) C (opnd C g 0) inp = true ∧
      wireVal (n + n) C (opnd C g 1) inp = true := by
    fin_cases b
    · exact ⟨h1, h2⟩
    · exact ⟨h2, h1⟩
  have hgv : gateVal (n + n) C g inp = true := by
    change wireVal (n + n) C ((n + n) + g) inp = true
    rw [wireVal_and hAO (hA g hg).1 (hA g hg).2, Bool.and_eq_true]
    exact h01
  have hfalse : gateVal (n + n) C g inp = false := hnonedge u v hnr g hg
  rw [hgv] at hfalse
  cases hfalse

private def orInProj {n : ℕ} (emb : Fin n → Fin (n + n)) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => emb u ∈ orIn (n + n) C w

private lemma orInProj_input_card_le_one {n : ℕ} {emb : Fin n → Fin (n + n)}
    (hemb : Function.Injective emb) (C : Circuit) {w : ℕ} (hw : w < n + n) :
    (orInProj emb C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [orInProj, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have heq : orIn (n + n) C w = {⟨w, hw⟩} := orIn_input ⟨w, hw⟩
  rw [heq, Finset.mem_singleton] at ha hb
  exact hemb (ha.trans hb.symm)

private lemma orInProj_ge {n : ℕ} (emb : Fin n → Fin (n + n)) {C : Circuit}
    (hAO : IsAO2 (n + n) C) {w : ℕ} (hw : (n + n) + C.gates.length ≤ w) :
    orInProj emb C w = ∅ := by
  ext u
  simp [orInProj, orIn_ge hAO hw]

private lemma orInProj_and {n : ℕ} (emb : Fin n → Fin (n + n)) {C : Circuit}
    (hAO : IsAO2 (n + n) C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    orInProj emb C ((n + n) + j) = ∅ := by
  ext u
  simp [orInProj, orIn_and hAO hj hop]

private lemma orInProj_or {n : ℕ} (emb : Fin n → Fin (n + n)) {C : Circuit}
    (hAO : IsAO2 (n + n) C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    orInProj emb C ((n + n) + j) = orInProj emb C (opnd C j 0) ∪ orInProj emb C (opnd C j 1) := by
  ext u
  simp [orInProj, orIn_or hAO hj hop]

private lemma orInProj_subset_of_orReaches {n : ℕ} (emb : Fin n → Fin (n + n)) {C : Circuit}
    (hAO : IsAO2 (n + n) C) {w g : ℕ} (hwg : OrReaches (n + n) C w g) :
    orInProj emb C ((n + n) + g) ⊆ orInProj emb C w := by
  intro u hu
  simp only [orInProj, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact orIn_subset_of_orReaches hAO hwg hu

open Classical in
private noncomputable def bigOrReachProj {n : ℕ} (emb : Fin n → Fin (n + n))
    (C : Circuit) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun g =>
    (gateAt C g).op = GateOp.or ∧ 2 ≤ (orInProj emb C ((n + n) + g)).card ∧
    ∃ w ∈ W, OrReaches (n + n) C w g

private lemma leaf_count_bound_proj {n : ℕ} {emb : Fin n → Fin (n + n)}
    (hemb : Function.Injective emb) {C : Circuit} (hAO : IsAO2 (n + n) C) :
    ∀ k : ℕ, ∀ W : Finset ℕ, (bigOrReachProj emb C W).card = k →
      (W.biUnion (orInProj emb C)).card ≤ W.card + k := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro W hk
    by_cases hne : (bigOrReachProj emb C W).Nonempty
    · set M := bigOrReachProj emb C W
      set m := M.max' hne
      have hmM : m ∈ M := Finset.max'_mem M hne
      have hm_props : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
          2 ≤ (orInProj emb C ((n + n) + m)).card ∧ ∃ w ∈ W, OrReaches (n + n) C w m := by
        simpa [M, bigOrReachProj, Finset.mem_filter, Finset.mem_range] using hmM
      have hmax_unique : ∀ w ∈ W, OrReaches (n + n) C w m → w = (n + n) + m := by
        intro w hw hwm
        have hle := orReaches_le hAO w m hwm
        rw [orReaches_iff hAO] at hwm
        rcases hwm with ⟨j, hj, rfl, hcase⟩
        by_contra hne_w
        have hmj : m ≠ j := fun h => hne_w (by omega)
        rcases hcase with hEq | ⟨hjop, b, hb⟩
        · exact hmj hEq
        · have hjM : j ∈ M := by
            simp only [M, bigOrReachProj, Finset.mem_filter, Finset.mem_range]
            refine ⟨hj, hjop, ?_, (n + n) + j, hw, orReaches_self hAO hj⟩
            have hsub : orInProj emb C ((n + n) + m) ⊆ orInProj emb C ((n + n) + j) :=
              orInProj_subset_of_orReaches emb hAO
                ((orReaches_iff hAO ((n + n) + j) m).mpr ⟨j, hj, rfl, Or.inr ⟨hjop, b, hb⟩⟩)
            exact le_trans hm_props.2.2.1 (Finset.card_le_card hsub)
          have hjle : j ≤ m := Finset.le_max' M j hjM
          omega
      have hnmW : (n + n) + m ∈ W := by
        rcases hm_props.2.2.2 with ⟨w, hw, hwm⟩
        rwa [hmax_unique w hw hwm] at hw
      set W' : Finset ℕ := insert (opnd C m 0) (insert (opnd C m 1) (W.erase ((n + n) + m)))
      have hbi : W.biUnion (orInProj emb C) ⊆ W'.biUnion (orInProj emb C) := by
        intro u hu
        rw [Finset.mem_biUnion] at hu ⊢
        rcases hu with ⟨w, hw, huw⟩
        by_cases hwm : w = (n + n) + m
        · subst hwm
          rw [orInProj_or emb hAO hm_props.1 hm_props.2.1, Finset.mem_union] at huw
          rcases huw with h0 | h1
          · exact ⟨opnd C m 0, by simp [W'], h0⟩
          · exact ⟨opnd C m 1, by simp [W'], h1⟩
        · exact ⟨w, by simp [W', hw, hwm], huw⟩
      have hW'card : W'.card ≤ W.card + 1 := by
        have h1 : W'.card ≤ (insert (opnd C m 1) (W.erase ((n + n) + m))).card + 1 :=
          Finset.card_insert_le _ _
        have h2 : (insert (opnd C m 1) (W.erase ((n + n) + m))).card ≤
            (W.erase ((n + n) + m)).card + 1 :=
          Finset.card_insert_le _ _
        have h3 : (W.erase ((n + n) + m)).card + 1 = W.card := Finset.card_erase_add_one hnmW
        omega
      have hM'sub : bigOrReachProj emb C W' ⊆ M.erase m := by
        intro g hg
        simp only [bigOrReachProj, Finset.mem_filter, Finset.mem_range] at hg
        rcases hg with ⟨hglt, hgop, hgcard, w', hw', hw'g⟩
        rw [Finset.mem_erase]
        have hgM : g ∈ M := by
          simp only [M, bigOrReachProj, Finset.mem_filter, Finset.mem_range]
          refine ⟨hglt, hgop, hgcard, ?_⟩
          simp only [W', Finset.mem_insert, Finset.mem_erase] at hw'
          rcases hw' with rfl | rfl | ⟨_, hw'W⟩
          · exact ⟨(n + n) + m, hnmW,
              (orReaches_iff hAO ((n + n) + m) g).mpr
                ⟨m, hm_props.1, rfl, Or.inr ⟨hm_props.2.1, 0, hw'g⟩⟩⟩
          · exact ⟨(n + n) + m, hnmW,
              (orReaches_iff hAO ((n + n) + m) g).mpr
                ⟨m, hm_props.1, rfl, Or.inr ⟨hm_props.2.1, 1, hw'g⟩⟩⟩
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
      have hM'card_le : (bigOrReachProj emb C W').card ≤ (M.erase m).card :=
        Finset.card_le_card hM'sub
      have hMerase : (M.erase m).card + 1 = k := by
        rw [Finset.card_erase_add_one hmM, hk]
      have hM'lt : (bigOrReachProj emb C W').card < k := by omega
      have hrec := ih _ hM'lt W' rfl
      have hbi_card : (W.biUnion (orInProj emb C)).card ≤ (W'.biUnion (orInProj emb C)).card :=
        Finset.card_le_card hbi
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hle1 : ∀ w ∈ W, (orInProj emb C w).card ≤ 1 := by
        intro w hw
        by_contra hgt
        push Not at hgt
        have hge2 : 2 ≤ (orInProj emb C w).card := hgt
        by_cases hlt : w < n + n
        · have h1 := orInProj_input_card_le_one hemb C hlt
          omega
        · by_cases hge : (n + n) + C.gates.length ≤ w
          · rw [orInProj_ge emb hAO hge, Finset.card_empty] at hge2
            omega
          · set j := w - (n + n)
            have hwEq : w = (n + n) + j := by omega
            have hj : j < C.gates.length := by omega
            have hmem : gateAt C j ∈ C.gates := by
              unfold gateAt
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
              exact List.getElem_mem hj
            rw [hwEq] at hge2 hw
            rcases hAO.1 _ hmem with hop | hop
            · rw [orInProj_and emb hAO hj hop, Finset.card_empty] at hge2
              omega
            · have hjM : j ∈ bigOrReachProj emb C W := by
                simp only [bigOrReachProj, Finset.mem_filter, Finset.mem_range]
                exact ⟨hj, hop, hge2, (n + n) + j, hw, orReaches_self hAO hj⟩
              rw [hne] at hjM
              simp at hjM
      have hbi : (W.biUnion (orInProj emb C)).card ≤ ∑ w ∈ W, (orInProj emb C w).card :=
        Finset.card_biUnion_le
      have hsum : ∑ w ∈ W, (orInProj emb C w).card ≤ ∑ _w ∈ W, 1 :=
        Finset.sum_le_sum hle1
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
      omega

open Classical in
private noncomputable def centeredPairs {n : ℕ} (emb1 emb2 : Fin n → Fin (n + n))
    (C : Circuit) (A : Finset ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n)).biUnion fun a =>
    ((((A ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p =>
        orInProj emb1 C (opnd C p.1 p.2) = {a}).image fun p =>
          opnd C p.1 (1 - p.2)).biUnion (orInProj emb2 C)).image fun c => (a, c)

private lemma mem_centeredPairs {n : ℕ} {emb1 emb2 : Fin n → Fin (n + n)}
    {C : Circuit} {A : Finset ℕ} {a c : Fin n} {g : ℕ} (hg : g ∈ A) (b : Fin 2)
    (h1 : orInProj emb1 C (opnd C g b) = {a})
    (h2 : c ∈ orInProj emb2 C (opnd C g (1 - b))) :
    (a, c) ∈ centeredPairs emb1 emb2 C A := by
  classical
  unfold centeredPairs
  rw [Finset.mem_biUnion]
  refine ⟨a, Finset.mem_univ a, ?_⟩
  rw [Finset.mem_image]
  refine ⟨c, ?_, rfl⟩
  rw [Finset.mem_biUnion]
  refine ⟨opnd C g (1 - b), ?_, h2⟩
  rw [Finset.mem_image]
  refine ⟨(g, b), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hg, Finset.mem_univ b⟩, h1⟩

private lemma centeredPairs_card_le {n : ℕ} {emb1 emb2 : Fin n → Fin (n + n)}
    (hemb2 : Function.Injective emb2) {C : Circuit} (hAO : IsAO2 (n + n) C)
    {A : Finset ℕ} (hA : ∀ g ∈ A, g < C.gates.length ∧ (gateAt C g).op = GateOp.and)
    {Q : Fin n → Fin n → Prop}
    (hnoC4 : ∀ a1 a2 c1 c2 : Fin n, a1 ≠ a2 → c1 ≠ c2 →
      Q a1 c1 → Q a1 c2 → Q a2 c1 → Q a2 c2 → False)
    (hcross : ∀ g ∈ A, ∀ b : Fin 2, ∀ a c : Fin n,
      a ∈ orInProj emb1 C (opnd C g b) → c ∈ orInProj emb2 C (opnd C g (1 - b)) → Q a c) :
    (centeredPairs emb1 emb2 C A).card ≤ 2 * C.gates.length := by
  classical
  let Ka : Fin n → Finset (ℕ × Fin 2) := fun a =>
    (A ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p => orInProj emb1 C (opnd C p.1 p.2) = {a}
  let Wa : Fin n → Finset ℕ := fun a => (Ka a).image fun p => opnd C p.1 (1 - p.2)
  let La : Fin n → Finset (Fin n) := fun a => (Wa a).biUnion (orInProj emb2 C)
  let Ma : Fin n → Finset ℕ := fun a => bigOrReachProj emb2 C (Wa a)
  have hcard_le : (centeredPairs emb1 emb2 C A).card ≤ ∑ a : Fin n, (La a).card := by
    calc (centeredPairs emb1 emb2 C A).card
        ≤ ∑ a : Fin n, ((La a).image fun c => (a, c)).card := Finset.card_biUnion_le
      _ ≤ ∑ a : Fin n, (La a).card := Finset.sum_le_sum fun a _ => Finset.card_image_le
  have hLa_le : ∀ a : Fin n, (La a).card ≤ (Ka a).card + (Ma a).card := by
    intro a
    have h1 := leaf_count_bound_proj hemb2 hAO (Ma a).card (Wa a) rfl
    have h2 : (Wa a).card ≤ (Ka a).card := Finset.card_image_le
    exact le_trans h1 (Nat.add_le_add_right h2 _)
  have hsum_L : ∑ a : Fin n, (La a).card ≤
      (∑ a : Fin n, (Ka a).card) + ∑ a : Fin n, (Ma a).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ => hLa_le a
  have hK_disj : Set.PairwiseDisjoint (Set.univ : Set (Fin n)) Ka := by
    intro a1 _ a2 _ hne
    change Disjoint (Ka a1) (Ka a2)
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Ka, Finset.mem_filter] at hp1 hp2
    have hEq : ({a1} : Finset (Fin n)) = {a2} := hp1.2.symm.trans hp2.2
    exact hne (Finset.singleton_injective hEq)
  have hM_disj : Set.PairwiseDisjoint (Set.univ : Set (Fin n)) Ma := by
    intro a1 _ a2 _ hne
    change Disjoint (Ma a1) (Ma a2)
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    simp only [Ma, bigOrReachProj, Finset.mem_filter, Finset.mem_range] at hg1 hg2
    rcases hg1 with ⟨_, _, hgcard, w1, hw1, hw1g⟩
    rcases hg2 with ⟨_, _, _, w2, hw2, hw2g⟩
    simp only [Wa, Finset.mem_image] at hw1 hw2
    rcases hw1 with ⟨p1, hp1, rfl⟩
    rcases hw2 with ⟨p2, hp2, rfl⟩
    simp only [Ka, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp1 hp2
    have hlt : 1 < (orInProj emb2 C ((n + n) + g)).card := by omega
    rcases Finset.one_lt_card.mp hlt with ⟨c1, hc1, c2, hc2, hcne⟩
    have hsub1 : orInProj emb2 C ((n + n) + g) ⊆ orInProj emb2 C (opnd C p1.1 (1 - p1.2)) :=
      orInProj_subset_of_orReaches emb2 hAO hw1g
    have hsub2 : orInProj emb2 C ((n + n) + g) ⊆ orInProj emb2 C (opnd C p2.1 (1 - p2.2)) :=
      orInProj_subset_of_orReaches emb2 hAO hw2g
    have ha1 : a1 ∈ orInProj emb1 C (opnd C p1.1 p1.2) := by
      rw [hp1.2]; exact Finset.mem_singleton_self a1
    have ha2 : a2 ∈ orInProj emb1 C (opnd C p2.1 p2.2) := by
      rw [hp2.2]; exact Finset.mem_singleton_self a2
    exact hnoC4 a1 a2 c1 c2 hne hcne
      (hcross p1.1 hp1.1 p1.2 a1 c1 ha1 (hsub1 hc1))
      (hcross p1.1 hp1.1 p1.2 a1 c2 ha1 (hsub1 hc2))
      (hcross p2.1 hp2.1 p2.2 a2 c1 ha2 (hsub2 hc1))
      (hcross p2.1 hp2.1 p2.2 a2 c2 ha2 (hsub2 hc2))
  have hsum_K : ∑ a : Fin n, (Ka a).card ≤ 2 * A.card := by
    rw [← Finset.card_biUnion (by intro a _ b _ hab; exact hK_disj (by simp) (by simp) hab)]
    have hsubK : (Finset.univ : Finset (Fin n)).biUnion Ka ⊆
        A ×ˢ (Finset.univ : Finset (Fin 2)) := by
      intro p hp
      rw [Finset.mem_biUnion] at hp
      rcases hp with ⟨a, _, hpa⟩
      exact (Finset.mem_filter.mp hpa).1
    calc ((Finset.univ : Finset (Fin n)).biUnion Ka).card
        ≤ (A ×ˢ (Finset.univ : Finset (Fin 2))).card := Finset.card_le_card hsubK
      _ = A.card * 2 := by simp [Finset.card_product]
      _ = 2 * A.card := Nat.mul_comm _ _
  let orGates : Finset ℕ := (Finset.range C.gates.length).filter fun g =>
    (gateAt C g).op = GateOp.or
  have hsum_M : ∑ a : Fin n, (Ma a).card ≤ orGates.card := by
    rw [← Finset.card_biUnion (by intro a _ b _ hab; exact hM_disj (by simp) (by simp) hab)]
    apply Finset.card_le_card
    intro g hg
    rw [Finset.mem_biUnion] at hg
    rcases hg with ⟨a, _, hga⟩
    simp only [Ma, bigOrReachProj, orGates, Finset.mem_filter, Finset.mem_range] at hga ⊢
    exact ⟨hga.1, hga.2.1⟩
  have hdisj : Disjoint A orGates := by
    rw [Finset.disjoint_left]
    intro g hgA hgO
    have h1 := (hA g hgA).2
    rw [Finset.mem_filter] at hgO
    rw [h1] at hgO
    cases hgO.2
  have hsum_gates : A.card + orGates.card ≤ C.gates.length := by
    rw [← Finset.card_union_of_disjoint hdisj]
    calc (A ∪ orGates).card
        ≤ (Finset.range C.gates.length).card := by
          apply Finset.card_le_card
          intro g hg
          rw [Finset.mem_union] at hg
          rcases hg with hg | hg
          · exact Finset.mem_range.mpr (hA g hg).1
          · exact (Finset.mem_filter.mp hg).1
      _ = C.gates.length := Finset.card_range _
  omega

private lemma main_bound (n : ℕ) (R : Fin n → Fin n → Prop) [DecidableRel R]
    (C : Circuit) (A : Finset ℕ) (E : Finset (Fin n × Fin n))
    (hplane : ∀ a b : Fin n, a ≠ b → ∃! c : Fin n, R a c ∧ R b c)
    (hAO : IsAO2 (n + n) C)
    (hA : ∀ g ∈ A, g < C.size ∧ (gateAt C g).op = GateOp.and)
    (hnonedge : ∀ u v : Fin n, ¬ R u v → ∀ g ∈ A,
      gateVal (n + n) C g (fun x => Decidable.decide (x = Fin.castAdd n u ∨ x = Fin.natAdd n v)) = false)
    (hread : ∀ e ∈ E, ∃ g ∈ A,
      [1, 1] ∈ (readVectors C (n + n) [e.1.val, n + e.2.val] 1).getD ((n + n) + g) []) :
    E.card ≤ 4 * C.size := by
  classical
  have hA' : ∀ g ∈ A, g < C.gates.length ∧ (gateAt C g).op = GateOp.and := hA
  have hcast_inj : Function.Injective (Fin.castAdd n : Fin n → Fin (n + n)) := fun a b h =>
    Fin.ext (by simpa [Fin.ext_iff] using h)
  have hnat_inj : Function.Injective (Fin.natAdd n : Fin n → Fin (n + n)) := fun a b h =>
    Fin.ext (by simpa [Fin.ext_iff] using h)
  have hcrossL : ∀ g ∈ A, ∀ b : Fin 2, ∀ u v : Fin n,
      u ∈ orInProj (Fin.castAdd n) C (opnd C g b) →
      v ∈ orInProj (Fin.natAdd n) C (opnd C g (1 - b)) → R u v := by
    intro g hg b u v hu hv
    simp only [orInProj, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact rel_of_cross_pair hAO hA' hnonedge hg b hu hv
  have hcrossR : ∀ g ∈ A, ∀ b : Fin 2, ∀ v u : Fin n,
      v ∈ orInProj (Fin.natAdd n) C (opnd C g b) →
      u ∈ orInProj (Fin.castAdd n) C (opnd C g (1 - b)) → R u v := by
    intro g hg b v u hv hu
    have hinv : (1 : Fin 2) - (1 - b) = b := by fin_cases b <;> decide
    have hv' : v ∈ orInProj (Fin.natAdd n) C (opnd C g (1 - (1 - b))) := by
      rwa [hinv]
    exact hcrossL g hg (1 - b) u v hu hv'
  let SL := centeredPairs (Fin.castAdd n) (Fin.natAdd n) C A
  let SR := centeredPairs (Fin.natAdd n) (Fin.castAdd n) C A
  have hE_sub : E ⊆ SL ∪ SR.image Prod.swap := by
    intro e he
    rcases e with ⟨u, v⟩
    rcases hread (u, v) he with ⟨g, hg, h11⟩
    rcases readVectors_and_extract hAO (hA' g hg).1 (hA' g hg).2 u v h11 with ⟨b, hu, hv⟩
    have huP : u ∈ orInProj (Fin.castAdd n) C (opnd C g b) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
    have hvP : v ∈ orInProj (Fin.natAdd n) C (opnd C g (1 - b)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
    rw [Finset.mem_union]
    by_cases hL1 : (orInProj (Fin.castAdd n) C (opnd C g b)).card ≤ 1
    · left
      have heqL : orInProj (Fin.castAdd n) C (opnd C g b) = {u} := by
        ext x
        rw [Finset.mem_singleton]
        constructor
        · intro hx
          exact Finset.card_le_one.mp hL1 x hx u huP
        · rintro rfl
          exact huP
      exact mem_centeredPairs hg b heqL hvP
    · right
      have hR1 : (orInProj (Fin.natAdd n) C (opnd C g (1 - b))).card ≤ 1 := by
        by_contra hRgt
        have hLgt : 1 < (orInProj (Fin.castAdd n) C (opnd C g b)).card := by omega
        have hRgt' : 1 < (orInProj (Fin.natAdd n) C (opnd C g (1 - b))).card := by omega
        rcases Finset.one_lt_card.mp hLgt with ⟨u1, hu1, u2, hu2, hune⟩
        rcases Finset.one_lt_card.mp hRgt' with ⟨v1, hv1, v2, hv2, hvne⟩
        exact no_c4 hplane hune hvne
          (hcrossL g hg b u1 v1 hu1 hv1)
          (hcrossL g hg b u1 v2 hu1 hv2)
          (hcrossL g hg b u2 v1 hu2 hv1)
          (hcrossL g hg b u2 v2 hu2 hv2)
      have heqR : orInProj (Fin.natAdd n) C (opnd C g (1 - b)) = {v} := by
        ext y
        rw [Finset.mem_singleton]
        constructor
        · intro hy
          exact Finset.card_le_one.mp hR1 y hy v hvP
        · rintro rfl
          exact hvP
      have hinv : (1 : Fin 2) - (1 - b) = b := by fin_cases b <;> decide
      have huP' : u ∈ orInProj (Fin.castAdd n) C (opnd C g (1 - (1 - b))) := by
        rwa [hinv]
      have hmemR : (v, u) ∈ SR := mem_centeredPairs hg (1 - b) heqR huP'
      rw [Finset.mem_image]
      exact ⟨(v, u), hmemR, rfl⟩
  have hSL : SL.card ≤ 2 * C.gates.length :=
    centeredPairs_card_le hnat_inj hAO hA'
      (fun a1 a2 c1 c2 ha hc h11 h12 h21 h22 => no_c4 hplane ha hc h11 h12 h21 h22)
      hcrossL
  have hSR : SR.card ≤ 2 * C.gates.length :=
    centeredPairs_card_le hcast_inj hAO hA'
      (fun b1 b2 a1 a2 hb ha h11 h12 h21 h22 => no_c4 hplane ha hb h11 h21 h12 h22)
      hcrossR
  have hE_card : E.card ≤ SL.card + SR.card := by
    calc E.card
        ≤ (SL ∪ SR.image Prod.swap).card := Finset.card_le_card hE_sub
      _ ≤ SL.card + (SR.image Prod.swap).card := Finset.card_union_le _ _
      _ ≤ SL.card + SR.card := Nat.add_le_add_left Finset.card_image_le _
  change E.card ≤ 4 * C.gates.length
  omega

end PEqualNP.Outside.L_meta_6292

theorem PEqualNP.Outside.L_meta_6292 :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ) (x6 : Finset (Fin x1 × Fin x1)), (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x2 x7 x10 ∧ x2 x8 x10) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ x9 ∈ x5, x9 < x4.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x10 x11 : Fin x1), ¬x2 x10 x11 → ∀ x13 ∈ x5, (PEqualNP.EdgeOwnership.gateVal (x1 + x1) x4 x13 fun (x15 : Fin (x1 + x1)) => Decidable.decide (x15 = Fin.castAdd x1 x10 ∨ x15 = Fin.natAdd x1 x11)) = Bool.false) → (∀ x11 ∈ x6, ∃ x13 ∈ x5, [(1 : ℕ), (1 : ℕ)] ∈ (PEqualNP.ReadK.readVectors x4 (x1 + x1) [↑x11.1, x1 + ↑x11.2] (1 : ℕ)).getD (x1 + x1 + x13) []) → x6.card ≤ (4 : ℕ) * x4.size :=
  fun x1 x2 _ x4 x5 x6 hplane hAO hA hnonedge hread =>
    PEqualNP.Outside.L_meta_6292.main_bound x1 x2 x4 x5 x6 hplane hAO hA hnonedge hread
