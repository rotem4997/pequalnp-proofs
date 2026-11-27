import PEqualNP.Defs.ReadK
import PEqualNP.Defs.ReadTwo

namespace PEqualNP.MetaComplexity.ReadTwoBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.ReadK

/-! ## Folds that append one entry per gate -/

theorem foldl_snoc_prefix {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_prefix {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_init {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : i < init.length) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d
      = init.getD i d :=
  getD_of_prefix (foldl_snoc_prefix (fun R g => G (g.inputs.map fun i => R.getD i d) g) _ _) hi d

theorem foldl_snoc_beyond {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : init.length + gs.length ≤ i) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d = d := by
  apply List.getD_eq_default
  rw [foldl_snoc_length (fun R g => G (g.inputs.map fun i => R.getD i d) g)]
  exact hi

theorem foldl_snoc_gate {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < init.length + j) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD
        (init.length + j) d
      = G (gs[j].inputs.map fun i =>
          (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d)
          gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init
    with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length (fun R g => G (g.inputs.map fun i => R.getD i d) g)]
    simp; omega
  have hpre : (P ++ [G (gs[j].inputs.map fun i => P.getD i d) gs[j]]) <+:
      gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_prefix (fun R g => G (g.inputs.map fun i => R.getD i d) g) _ _
  have hpre2 := (List.prefix_append P _).trans hpre
  rw [getD_of_prefix hpre (by simp; omega)]
  have e1 : (P ++ [G (gs[j].inputs.map fun i => P.getD i d) gs[j]]).getD (init.length + j) d
      = G (gs[j].inputs.map fun i => P.getD i d) gs[j] := by
    rw [← hPl]; simp
  rw [e1]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [getD_of_prefix hpre2 (by rw [hPl]; exact hrb i hi)]

/-! ## The two folds of the root, in that form -/

/-- The gate step of `readVectors`, as a function of the input sets. -/
def rvG (S : List ℕ) (k : ℕ) (ins : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

theorem rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl
      (fun R g => R ++ [rvG S k (g.inputs.map fun i => R.getD i []) g])
      ((List.range n).map (leafVectors S k)) := rfl

theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl
      (fun R g => R ++ [(fun ins (g : Gate) => g.op.eval ins) (g.inputs.map fun i => R.getD i false) g])
      x := rfl

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

/-! ## Per-wire facts -/

section Wires

variable (C : Circuit) (n : ℕ)

/-- The vector set of wire `x` for the list `S`, at cap `k = 2`. -/
abbrev A (S : List ℕ) (x : ℕ) : List (List ℕ) := (readVectors C n S 2).getD x []

theorem A_input (S : List ℕ) (x : ℕ) (hx : x < n) : A C n S x = leafVectors S 2 x := by
  unfold A
  rw [rv_eq, foldl_snoc_init _ _ _ _ _ (by simpa using hx)]
  simp [List.getD_eq_getElem?_getD, hx]

theorem A_beyond (S : List ℕ) (x : ℕ) (hx : n + C.gates.length ≤ x) : A C n S x = [] := by
  unfold A
  rw [rv_eq, foldl_snoc_beyond _ _ _ _ _ (by simpa using hx)]

theorem A_gate (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    A C n S (n + j) = rvG S 2 ((gateAt C j).inputs.map (A C n S)) (gateAt C j) := by
  unfold A
  rw [gateAt_eq C j hj] at hrb ⊢
  have := foldl_snoc_gate (rvG S 2) [] ((List.range n).map (leafVectors S 2)) C.gates j hj
    (by simpa using hrb)
  simp only [List.length_map, List.length_range] at this
  rw [rv_eq, this]

/-- The value of wire `i` on input `x`. -/
abbrev W (x : Fin n → Bool) (i : ℕ) : Bool := (C.wires (List.ofFn x)).getD i false

theorem W_input (x : Fin n → Bool) (i : ℕ) (hi : i < n) : W C n x i = x ⟨i, hi⟩ := by
  unfold W
  rw [wires_eq, foldl_snoc_init (fun ins (g : Gate) => g.op.eval ins) false _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem W_gate (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    W C n x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W C n x)) := by
  unfold W
  rw [gateAt_eq C j hj] at hrb ⊢
  have := foldl_snoc_gate (fun ins (g : Gate) => g.op.eval ins) false (List.ofFn x) C.gates j hj
    (by simpa using hrb)
  simp only [List.length_ofFn] at this
  rw [wires_eq, this]

end Wires

/-! ## Membership in the root's set operations -/

theorem mem_insertNew {B : List (List ℕ)} {v a : List ℕ} :
    v ∈ insertNew B a ↔ v ∈ B ∨ v = a := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h' | rfl) <;> assumption
  · simp

theorem mem_foldl_insertNew (l acc : List (List ℕ)) (v : List ℕ) :
    v ∈ l.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, mem_insertNew]; simp; tauto

theorem mem_orFold (ins : List (List (List ℕ))) (acc : List (List ℕ)) (v : List ℕ) :
    v ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc ↔ v ∈ acc ∨ ∃ B ∈ ins, v ∈ B := by
  induction ins generalizing acc with
  | nil => simp
  | cons B ins ih => rw [List.foldl_cons, ih, mem_foldl_insertNew]; simp; tauto

theorem mem_andStep (k : ℕ) (P Q : List (List ℕ)) (v : List ℕ) :
    v ∈ andStep k P Q ↔ ∃ a ∈ P, ∃ b ∈ Q, v = capAdd k a b := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

/-! ## Skeleton trees as an inductive predicate -/

section Trees

variable (C : Circuit) (n : ℕ)

/-- OR-only upward paths, exactly the relation of the statement. -/
def Rr : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs)

/-- The trees of the statement's `T`, as an inductive predicate. -/
inductive Tr : ℕ → List (ℕ × ℕ) → Prop
  | leaf (qv qt : ℕ) : qv < n → Rr C n qv qt → Tr qt [(qt, qv)]
  | node (qj qt : ℕ) (L1 L2 : List (ℕ × ℕ)) : qj < C.gates.length →
      (gateAt C qj).op = GateOp.and → Rr C n (n + qj) qt →
      Tr ((gateAt C qj).inputs.getD 0 0) L1 → Tr ((gateAt C qj).inputs.getD 1 0) L2 →
      Tr qt (L1 ++ L2)

theorem Tr.toT {t : ℕ} {L : List (ℕ × ℕ)} (h : Tr C n t L) (Q : ℕ → List (ℕ × ℕ) → Prop)
    (hl : ∀ (qv qt : ℕ), qv < n → Rr C n qv qt → Q qt [(qt, qv)])
    (hn : ∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length →
      (gateAt C qj).op = GateOp.and → Rr C n (n + qj) qt →
      Q ((gateAt C qj).inputs.getD 0 0) qL1 → Q ((gateAt C qj).inputs.getD 1 0) qL2 →
      Q qt (qL1 ++ qL2)) : Q t L := by
  induction h with
  | leaf qv qt hv hr => exact hl qv qt hv hr
  | node qj qt L1 L2 hj ha hr _ _ ih1 ih2 => exact hn qj qt L1 L2 hj ha hr ih1 ih2

theorem Tr.lift {t t' : ℕ} {L : List (ℕ × ℕ)} (h : Tr C n t L) (hr : Rr C n t t') :
    ∃ L', Tr C n t' L' ∧ L'.map Prod.snd = L.map Prod.snd := by
  cases h with
  | leaf qv _ hv hr0 => exact ⟨_, Tr.leaf qv t' hv (hr0.trans hr), rfl⟩
  | node qj _ L1 L2 hj ha hr0 h1 h2 => exact ⟨_, Tr.node qj t' L1 L2 hj ha (hr0.trans hr) h1 h2, rfl⟩

end Trees

/-! ## Realization: every vector of a wire is the capped leaf count of a tree hanging from it -/

theorem realize (C : Circuit) (n u w : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∀ x, ∀ v ∈ A C n [u, w] x, ∃ L, Tr C n x L ∧ (∀ a ∈ L.map Prod.snd, a = u ∨ a = w) ∧
      v = [min ((L.map Prod.snd).count u) 3, min ((L.map Prod.snd).count w) 3] := by
  obtain ⟨hao, hrb, h2⟩ := hC
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  intro v hv
  by_cases hxn : x < n
  · rw [A_input C n _ x hxn] at hv
    simp only [leafVectors] at hv
    split_ifs at hv with hmem
    · simp only [List.mem_singleton] at hv
      refine ⟨[(x, x)], Tr.leaf x x hxn Relation.ReflTransGen.refl, ?_, ?_⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton]
        rintro a rfl
        simpa using hmem
      · subst hv
        simp only [List.map_cons, List.map_nil, List.count_singleton]
        by_cases hu : u = x
        · subst hu
          by_cases hw : w = u
          · subst hw; simp
          · simp [hw, Ne.symm hw]
        · by_cases hw : w = x
          · subst hw; simp [hu, Ne.symm hu]
          · simp [hu, hw, Ne.symm hu, Ne.symm hw]
    · simp at hv
  · obtain ⟨j, rfl⟩ : ∃ j, x = n + j := ⟨x - n, by omega⟩
    by_cases hj : j < C.gates.length
    swap
    · rw [A_beyond C n _ _ (by omega)] at hv; simp at hv
    have hrbj := hrb j hj
    rw [A_gate C n _ j hj hrbj] at hv
    have hg : gateAt C j ∈ C.gates := by rw [gateAt_eq C j hj]; exact List.getElem_mem hj
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 _ hg)
    have ha : a < n + j := hrbj a (by simp [hab])
    have hb : b < n + j := hrbj b (by simp [hab])
    rcases hao _ hg with hop | hop
    · -- AND
      simp only [rvG, hop, hab, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
        List.map_cons, List.map_nil] at hv
      rw [mem_andStep] at hv
      obtain ⟨p, hp, q, hq, rfl⟩ := hv
      rw [mem_andStep] at hp
      obtain ⟨z, hz, p0, hp0, rfl⟩ := hp
      simp only [List.mem_singleton] at hz
      subst hz
      obtain ⟨L1, hT1, hl1, rfl⟩ := ih a ha p0 hp0
      obtain ⟨L2, hT2, hl2, rfl⟩ := ih b hb q hq
      refine ⟨L1 ++ L2, Tr.node j (n + j) L1 L2 hj hop Relation.ReflTransGen.refl
        (by simpa [hab] using hT1) (by simpa [hab] using hT2), ?_, ?_⟩
      · intro c hc
        simp only [List.map_append, List.mem_append] at hc
        rcases hc with hc | hc
        · exact hl1 c hc
        · exact hl2 c hc
      · simp only [capAdd, List.map_append, List.count_append, List.zipWith_cons_cons,
          List.zipWith_nil_right, List.cons.injEq, and_true]
        constructor <;> omega
    · -- OR
      simp only [rvG, hop, hab, List.map_cons, List.map_nil] at hv
      rw [mem_orFold] at hv
      simp only [false_or, List.mem_cons, List.mem_nil_iff, or_false,
        exists_eq_or_imp, exists_eq_left] at hv
      have step : ∀ c, c < n + j → c ∈ (gateAt C j).inputs → Rr C n c (n + j) := fun c hc hci =>
        Relation.ReflTransGen.single ⟨hc, j, rfl, hj, hop, hci⟩
      rcases hv with hv | hv
      · obtain ⟨L, hT, hl, rfl⟩ := ih a ha v hv
        obtain ⟨L', hT', hm⟩ := hT.lift C n (step a ha (by simp [hab]))
        exact ⟨L', hT', by rw [hm]; exact hl, by rw [hm]⟩
      · obtain ⟨L, hT, hl, rfl⟩ := ih b hb v hv
        obtain ⟨L', hT', hm⟩ := hT.lift C n (step b hb (by simp [hab]))
        exact ⟨L', hT', by rw [hm]; exact hl, by rw [hm]⟩

theorem realize_len2 (C : Circuit) (n u w : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) (x : ℕ)
    (v : List ℕ) (hv : v ∈ A C n [u, w] x) : ∃ c d, v = [c, d] := by
  obtain ⟨L, -, -, rfl⟩ := realize C n u w hC x v hv
  exact ⟨_, _, rfl⟩

/-! ## Soundness: a tree whose leaves are true makes its wire true -/

theorem Rr.val (C : Circuit) (n : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool)
    {a b : ℕ} (h : Rr C n a b) (ha : W C n x a = true) : W C n x b = true := by
  induction h with
  | refl => exact ha
  | tail _ hst ih =>
    obtain ⟨_, rj, rfl, hj, hop, hmem⟩ := hst
    rw [W_gate C n x rj hj (hC.2.1 rj hj), hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    exact ⟨_, ⟨_, hmem, rfl⟩, ih⟩

theorem Tr.val (C : Circuit) (n : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool)
    {t : ℕ} {L : List (ℕ × ℕ)} (h : Tr C n t L) (hL : ∀ e ∈ L, W C n x e.2 = true) :
    W C n x t = true := by
  induction h with
  | leaf qv qt hv hr => exact Rr.val C n hC x hr (hL _ (List.mem_singleton_self _))
  | node qj qt L1 L2 hj ha hr _ _ ih1 ih2 =>
    apply Rr.val C n hC x hr
    have hg : gateAt C qj ∈ C.gates := by rw [gateAt_eq C qj hj]; exact List.getElem_mem hj
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hC.2.2 _ hg)
    have h1 := ih1 (fun e he => hL e (List.mem_append_left _ he))
    have h2 := ih2 (fun e he => hL e (List.mem_append_right _ he))
    rw [hab] at h1 h2
    rw [W_gate C n x qj hj (hC.2.1 qj hj), ha, hab]
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h1 h2
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, h1, h2,
      Bool.and_true]

/-! ## The swap: the vectors for `[w, u]` are the reversed vectors for `[u, w]` -/

theorem swap (C : Circuit) (n u w : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∀ x, ∀ v, v ∈ A C n [w, u] x ↔ v.reverse ∈ A C n [u, w] x := by
  have hC' := hC
  obtain ⟨hao, hrb, h2⟩ := hC'
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  intro v
  by_cases hxn : x < n
  · rw [A_input C n _ x hxn, A_input C n _ x hxn]
    simp only [leafVectors]
    split_ifs with h1 h3 h3
    · simp only [List.map_cons, List.map_nil, List.mem_singleton]
      constructor
      · rintro rfl; simp
      · intro h'; rw [← List.reverse_reverse v, h']; simp
    · exfalso; simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h3; tauto
    · exfalso; simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h3; tauto
    · simp
  · obtain ⟨j, rfl⟩ : ∃ j, x = n + j := ⟨x - n, by omega⟩
    by_cases hj : j < C.gates.length
    swap
    · rw [A_beyond C n _ _ (by omega), A_beyond C n _ _ (by omega)]; simp
    have hrbj := hrb j hj
    rw [A_gate C n _ j hj hrbj, A_gate C n _ j hj hrbj]
    have hg : gateAt C j ∈ C.gates := by rw [gateAt_eq C j hj]; exact List.getElem_mem hj
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 _ hg)
    have ha : a < n + j := hrbj a (by simp [hab])
    have hb : b < n + j := hrbj b (by simp [hab])
    rcases hao _ hg with hop | hop
    · -- AND
      simp only [rvG, hop, hab, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [mem_andStep, mem_andStep]
      constructor
      · rintro ⟨p, hp, q, hq, rfl⟩
        rw [mem_andStep] at hp
        obtain ⟨z, hz, p0, hp0, rfl⟩ := hp
        simp only [List.mem_singleton] at hz
        subst hz
        obtain ⟨c, d, rfl⟩ := realize_len2 C n w u hC a p0 hp0
        obtain ⟨e, f, rfl⟩ := realize_len2 C n w u hC b q hq
        refine ⟨capAdd 2 [0, 0] [d, c], (mem_andStep _ _ _ _).mpr
          ⟨[0, 0], by simp, [d, c], by simpa using (ih a ha _).mp hp0, rfl⟩,
          [f, e], by simpa using (ih b hb _).mp hq, ?_⟩
        simp [capAdd]
      · rintro ⟨p, hp, q, hq, hv⟩
        rw [mem_andStep] at hp
        obtain ⟨z, hz, p0, hp0, rfl⟩ := hp
        simp only [List.mem_singleton] at hz
        subst hz
        obtain ⟨c, d, rfl⟩ := realize_len2 C n u w hC a p0 hp0
        obtain ⟨e, f, rfl⟩ := realize_len2 C n u w hC b q hq
        refine ⟨capAdd 2 [0, 0] [d, c], (mem_andStep _ _ _ _).mpr
          ⟨[0, 0], by simp, [d, c], (ih a ha _).mpr (by simpa using hp0), rfl⟩,
          [f, e], (ih b hb _).mpr (by simpa using hq), ?_⟩
        rw [← List.reverse_reverse v, hv]
        simp [capAdd]
    · -- OR
      simp only [rvG, hop, hab, List.map_cons, List.map_nil]
      rw [mem_orFold, mem_orFold]
      simp only [false_or, List.mem_cons, List.mem_nil_iff, or_false,
        exists_eq_or_imp, exists_eq_left]
      rw [ih a ha, ih b hb]

theorem cnt_eq (L : List (ℕ × ℕ)) (a : ℕ) :
    (L.filter (fun e => decide (e.2 = a))).length = (L.map Prod.snd).count a := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.filter_cons, List.map_cons, List.count_cons]
    split_ifs with h <;> simp_all

/-! ## The bridge -/

/-- L-meta-2350 (conjecture until checked): the read-2 test on `[u, w]` agrees with the test on
`[w, u]`, and when it accepts, an AND-rooted skeleton tree hangs from the output with every leaf
`u` or `w`, each read once or twice. -/
theorem readTwo_bridge : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.TopForm.IsAO2 n C → u < n → w < n → u ≠ w → PEqualNP.MetaComplexity.circuitFun n C (fun k1 : Fin n => decide (k1.val = u)) = false → PEqualNP.MetaComplexity.circuitFun n C (fun k2 : Fin n => decide (k2.val = w)) = false → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (PEqualNP.ReadK.readsAtMost C n [u, w] 2 = PEqualNP.ReadK.readsAtMost C n [w, u] 2) ∧ (PEqualNP.ReadK.readsAtMost C n [u, w] 2 = true → ∃ L : List (ℕ × ℕ), (∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j0) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 0 0) L1 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 1 0) L2 ∧ L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = u ∨ gv.2 = w) ∧ (L.filter (fun e1 => decide (e1.2 = u))).length ∈ ({1, 2} : Finset ℕ) ∧ (L.filter (fun e2 => decide (e2.2 = w))).length ∈ ({1, 2} : Finset ℕ)) := by
  intro n C u w hC hu hw huw hfu hfw R hR T hT
  subst hR hT
  have hsw := swap C n u w hC
  refine ⟨?_, ?_⟩
  · unfold readsAtMost
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨v, hv, hall⟩
      exact ⟨v.reverse, (hsw _ _).mpr (by simpa using hv), by simpa using hall⟩
    · rintro ⟨v, hv, hall⟩
      exact ⟨v.reverse, (hsw _ _).mp hv, by simpa using hall⟩
  · intro hacc
    unfold readsAtMost at hacc
    rw [List.any_eq_true] at hacc
    obtain ⟨v, hv, hall⟩ := hacc
    obtain ⟨L, hTL, hl, rfl⟩ := realize C n u w hC _ v hv
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hall
    obtain ⟨hcu, hcw⟩ := hall
    have pos : ∀ a b, a < n → (a = u ∨ a = w) → (b = u ∨ b = w) → a ≠ b →
        circuitFun n C (fun k : Fin n => decide (k.val = a)) = false →
        1 ≤ (L.map Prod.snd).count b := by
      intro a b ha hab hbb hne hf
      by_contra h0
      have h0' : (L.map Prod.snd).count b = 0 := by omega
      rw [List.count_eq_zero] at h0'
      have hall : ∀ e ∈ L, e.2 = a := by
        intro e he
        have hm : e.2 ∈ L.map Prod.snd := List.mem_map.mpr ⟨e, he, rfl⟩
        rcases hl _ hm with h | h <;> rcases hab with rfl | rfl <;> rcases hbb with rfl | rfl <;>
          first | exact h | exact absurd rfl hne | exact absurd (h ▸ hm) h0'
      have := Tr.val C n hC (fun k : Fin n => decide (k.val = a)) hTL (by
        intro e he
        rw [hall e he, W_input C n _ a ha]
        simp)
      have hc : circuitFun n C (fun k : Fin n => decide (k.val = a)) =
          W C n (fun k : Fin n => decide (k.val = a)) C.output := rfl
      rw [hc, this] at hf
      exact Bool.noConfusion hf
    have hw1 := pos u w hu (Or.inl rfl) (Or.inr rfl) huw hfu
    have hu1 := pos w u hw (Or.inr rfl) (Or.inl rfl) (Ne.symm huw) hfw
    cases hTL with
    | leaf qv _ hv hr =>
      exfalso
      simp only [List.map_cons, List.map_nil, List.count_singleton] at hw1 hu1
      split_ifs at hw1 hu1 with h1 h2 <;> simp_all
    | node qj _ L1 L2 hj ha hr h1 h2 =>
      refine ⟨L1 ++ L2, ⟨qj, L1, L2, hj, ha, hr, fun Q hl hn => h1.toT C n Q hl hn,
        fun Q hl hn => h2.toT C n Q hl hn, rfl⟩, ?_, ?_, ?_⟩
      · intro gv hgv
        exact hl _ (List.mem_map.mpr ⟨gv, hgv, rfl⟩)
      · rw [cnt_eq]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      · rw [cnt_eq]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega

end PEqualNP.MetaComplexity.ReadTwoBridge
