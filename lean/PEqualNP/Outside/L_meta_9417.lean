import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9417

-- The helper lemmas and the lemma extract_junk below are adapted from the proof of L-meta-6935 by k-sandhu.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

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

private lemma cones_getD_lt (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  unfold cones coneStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) =>
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++
      [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
      (fun w => (w - n) :: pre.getD (w - n) []) = _
  rw [hprelen]
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  congr 1
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

private lemma inCone_of_opnd {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) (hge : n ≤ opnd C j b) :
    InCone n C (opnd C j b - n) j := by
  unfold InCone
  rw [cones_getD_lt n C hj, List.mem_flatMap]
  refine ⟨opnd C j b, ?_, List.mem_cons_self⟩
  rw [List.mem_filter, decide_eq_true_eq]
  exact ⟨opnd_mem_inputs hAO hj b, hge, opnd_lt hAO hj b⟩

private lemma inCone_trans {n : ℕ} {C : Circuit} :
    ∀ a : ℕ, a < C.gates.length → ∀ g h : ℕ,
      InCone n C h g → InCone n C g a → InCone n C h a := by
  intro a
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    intro ha g h hhg hga
    unfold InCone at hga ⊢
    rw [cones_getD_lt n C ha, List.mem_flatMap] at hga ⊢
    rcases hga with ⟨w, hw, hgw⟩
    rw [List.mem_filter, decide_eq_true_eq] at hw
    rw [List.mem_cons] at hgw
    refine ⟨w, by rw [List.mem_filter, decide_eq_true_eq]; exact hw, ?_⟩
    rw [List.mem_cons]
    right
    rcases hgw with rfl | hgw
    · exact hhg
    · exact ih (w - n) (by omega) (by omega) g h hhg hgw

private lemma extract_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 n C) (hTF : TopForm G C) {a : ℕ} (ha : a < C.gates.length)
    (ha_and : (gateAt C a).op = GateOp.and) (u v : Fin n) :
    ∀ w : ℕ,
      (w < n ∨ ∃ g < C.gates.length, w = n + g ∧ InCone n C g a) →
      wireVal n C w (pairInput u v) = true →
      u ∉ orIn n C w → v ∉ orIn n C w →
      ∃ j ∈ junk G C, OrReaches n C w j ∧ gateVal n C j (pairInput u v) = true ∧
        ∀ x : Fin n → Bool, gateVal n C j x = true → wireVal n C w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hcone hval hu hv
    by_cases hw : w < n
    · let i : Fin n := ⟨w, hw⟩
      have hi : wireVal n C i.val (pairInput u v) = pairInput u v i :=
        wireVal_input C i (pairInput u v)
      change wireVal n C i.val (pairInput u v) = true at hval
      rw [hi] at hval
      unfold pairInput at hval
      rw [decide_eq_true_eq] at hval
      have himem : i ∈ orIn n C w := by
        change i ∈ orIn n C i.val
        rw [orIn_input i]
        exact Finset.mem_singleton_self i
      rcases hval with rfl | rfl
      · exact False.elim (hu himem)
      · exact False.elim (hv himem)
    · rcases hcone with hlt | ⟨g, hg, rfl, hga⟩
      · exact False.elim (hw hlt)
      · have hgmem : gateAt C g ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg]
          exact List.getElem_mem hg
        rcases hAO.1 _ hgmem with hg_and | hg_or
        · have hnotBelow : ¬ BelowF G C g := by
            intro hB
            exact hTF g hg a ha hg_and hB ha_and hga
          unfold BelowF at hnotBelow
          push Not at hnotBelow
          rcases hnotBelow with ⟨x, hgx, hfx⟩
          have hfx_false : graphFun G ∅ x = false := by
            cases hf : graphFun G ∅ x
            · rfl
            · exact False.elim (hfx hf)
          have hgjunk : g ∈ junk G C := by
            unfold junk gatesWhere
            rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨hg, hg_and, hg, x, hgx, hfx_false⟩
          exact ⟨g, hgjunk, orReaches_self hAO hg, hval, fun x hx => hx⟩
        · rw [wireVal_or hAO hg hg_or (pairInput u v), Bool.or_eq_true] at hval
          have horin : orIn n C (n + g) = orIn n C (opnd C g 0) ∪ orIn n C (opnd C g 1) :=
            orIn_or hAO hg hg_or
          have hex : ∃ b : Fin 2, wireVal n C (opnd C g b) (pairInput u v) = true := by
            rcases hval with h0 | h1
            · exact ⟨0, h0⟩
            · exact ⟨1, h1⟩
          rcases hex with ⟨b, hbval⟩
          have hblt : opnd C g b < n + g := opnd_lt hAO hg b
          have hbcone : opnd C g b < n ∨
              ∃ g' < C.gates.length, opnd C g b = n + g' ∧ InCone n C g' a := by
            by_cases hbn : opnd C g b < n
            · exact Or.inl hbn
            · right
              refine ⟨opnd C g b - n, by omega, by omega, ?_⟩
              exact inCone_trans a ha g (opnd C g b - n)
                (inCone_of_opnd hAO hg b (by omega)) hga
          have hbu : u ∉ orIn n C (opnd C g b) := by
            intro hmem
            apply hu
            rw [horin, Finset.mem_union]
            fin_cases b
            · exact Or.inl hmem
            · exact Or.inr hmem
          have hbv : v ∉ orIn n C (opnd C g b) := by
            intro hmem
            apply hv
            rw [horin, Finset.mem_union]
            fin_cases b
            · exact Or.inl hmem
            · exact Or.inr hmem
          rcases ih (opnd C g b) hblt hbcone hbval hbu hbv with ⟨j, hj, hreach, hjv, hjimp⟩
          refine ⟨j, hj, (orReaches_iff hAO (n + g) j).mpr ⟨g, hg, rfl, Or.inr ⟨hg_or, b, hreach⟩⟩,
            hjv, fun x hjx => ?_⟩
          rw [wireVal_or hAO hg hg_or x, Bool.or_eq_true]
          have hbx := hjimp x hjx
          fin_cases b
          · exact Or.inl hbx
          · exact Or.inr hbx

private lemma reach_up {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g : ℕ) (x : Fin n → Bool)
    (hg : gateVal n C g x = true) : ∀ w, OrReaches n C w g → wireVal n C w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hr
    obtain ⟨j, hj, hw, h⟩ := (orReaches_iff hAO w g).mp hr
    subst hw
    rcases h with h | ⟨hor, b, hb⟩
    · subst h
      exact hg
    · have hb' := ih (opnd C j b) (opnd_lt hAO hj b) hb
      rw [wireVal_or hAO hj hor x, Bool.or_eq_true]
      fin_cases b
      · exact Or.inl hb'
      · exact Or.inr hb'

private lemma two_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C)
    {a : ℕ} (ha_top : a ∈ tops G C) (u v : Fin n)
    (hval_a : gateVal n C a (pairInput u v) = true)
    (he_out : ∀ w ∈ side C a (0 : Fin 2) ∪ side C a (1 : Fin 2), w ∉ s(u, v)) :
    ∃ j0 ∈ junk G C, ∃ j1 ∈ junk G C, j0 ≠ j1 ∧ OrReaches n C (opnd C a 0) j0 ∧
      OrReaches n C (opnd C a 1) j1 ∧ ¬ OrReaches n C (opnd C a 1) j0 ∧
      ¬ OrReaches n C (opnd C a 0) j1 ∧ gateVal n C j0 (pairInput u v) = true ∧
      gateVal n C j1 (pairInput u v) = true := by
  have ha_mem : a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
    let _ : DecidableEq GateOp := gateOpDecEq
    unfold tops gatesWhere at ha_top
    rw [Finset.mem_filter, Finset.mem_range] at ha_top
    exact ha_top
  rcases ha_mem with ⟨ha, ha_and, ha_below⟩
  have hval_pair : wireVal n C (opnd C a 0) (pairInput u v) = true ∧
      wireVal n C (opnd C a 1) (pairInput u v) = true := by
    change wireVal n C (n + a) (pairInput u v) = true at hval_a
    rw [wireVal_and hAO ha ha_and (pairInput u v), Bool.and_eq_true] at hval_a
    exact hval_a
  have hcone : ∀ b : Fin 2, opnd C a b < n ∨
      ∃ g < C.gates.length, opnd C a b = n + g ∧ InCone n C g a := by
    intro b
    by_cases hbn : opnd C a b < n
    · exact Or.inl hbn
    · right
      have hblt := opnd_lt hAO ha b
      exact ⟨opnd C a b - n, by omega, by omega, inCone_of_opnd hAO ha b (by omega)⟩
  have hu0 : u ∉ orIn n C (opnd C a 0) := fun hm =>
    he_out u (Finset.mem_union_left _ hm) (Sym2.mem_mk_left u v)
  have hv0 : v ∉ orIn n C (opnd C a 0) := fun hm =>
    he_out v (Finset.mem_union_left _ hm) (Sym2.mem_mk_right u v)
  have hu1 : u ∉ orIn n C (opnd C a 1) := fun hm =>
    he_out u (Finset.mem_union_right _ hm) (Sym2.mem_mk_left u v)
  have hv1 : v ∉ orIn n C (opnd C a 1) := fun hm =>
    he_out v (Finset.mem_union_right _ hm) (Sym2.mem_mk_right u v)
  rcases extract_junk hAO hTF ha ha_and u v (opnd C a 0) (hcone 0) hval_pair.1 hu0 hv0 with
    ⟨j0, hj0, hr0, hjv0, hj0_imp⟩
  rcases extract_junk hAO hTF ha ha_and u v (opnd C a 1) (hcone 1) hval_pair.2 hu1 hv1 with
    ⟨j1, hj1, hr1, hjv1, hj1_imp⟩
  have dirty : ∀ j ∈ junk G C, (∀ x : Fin n → Bool, gateVal n C j x = true →
      wireVal n C (opnd C a 0) x = true) → (∀ x : Fin n → Bool, gateVal n C j x = true →
      wireVal n C (opnd C a 1) x = true) → False := by
    intro j hj h0 h1
    unfold junk gatesWhere at hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rcases hj.2.2.2 with ⟨x, hjx, hfx⟩
    have ha_x : gateVal n C a x = true := by
      change wireVal n C (n + a) x = true
      rw [wireVal_and hAO ha ha_and x, Bool.and_eq_true]
      exact ⟨h0 x hjx, h1 x hjx⟩
    have hfx_true : graphFun G ∅ x = true := ha_below x ha_x
    rw [hfx_true] at hfx
    cases hfx
  refine ⟨j0, hj0, j1, hj1, ?_, hr0, hr1, ?_, ?_, hjv0, hjv1⟩
  · intro heq
    subst heq
    exact dirty j0 hj0 hj0_imp hj1_imp
  · intro hr
    exact dirty j0 hj0 hj0_imp (fun x hx => reach_up hAO j0 x hx _ hr)
  · intro hr
    exact dirty j1 hj1 (fun x hx => reach_up hAO j1 x hx _ hr) hj1_imp

end PEqualNP.Outside.L_meta_9417

theorem PEqualNP.Outside.L_meta_9417 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∀ x7 ∈ PEqualNP.TopForm.tops x2 x4, ∀ (x9 x10 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x4 x7 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true → (∀ x12 ∈ PEqualNP.TopForm.side x4 x7 (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side x4 x7 (1 : Fin (2 : ℕ)), x12 ∉ s(x9, x10)) → ∃ x13 ∈ PEqualNP.TopForm.junk x2 x4, ∃ x14 ∈ PEqualNP.TopForm.junk x2 x4, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x7 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x7 (1 : Fin (2 : ℕ))) x14 ∧ ¬PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x7 (1 : Fin (2 : ℕ))) x13 ∧ ¬PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x7 (0 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x13 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x14 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true := by
  intro x1 x2 x3 x4 hAO hTF x7 h7 x9 x10 hval hout
  exact PEqualNP.Outside.L_meta_9417.two_junk hAO hTF h7 x9 x10 hval hout
