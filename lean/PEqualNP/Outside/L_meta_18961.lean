import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18961
namespace S90
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩


lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]


lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]


lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]


lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩


lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)


lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩


lemma top_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (a : ℕ) (ha : a ∈ tops G C) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) ∧
    (∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v) ∧
    ((side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1) := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halen, hop, hbel⟩ := ha
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
  have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hadj : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
    intro u hu v hv
    simp only [side, e0] at hu
    simp only [side, e1] at hv
    exact side_adj G (graphFun G ∅) (fun u v h => (graphFun_pair G u v).mp h) a halen hop hbel
      p q hin hp hq u v (mem_orIn_reach u hu) (mem_orIn_reach v hv)
  refine ⟨?_, hadj, ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu hv
    exact G.irrefl (hadj u hu u hv)
  · by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcon.1
    have hsub : side (n := n) C a 1 ⊆ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj y w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hadj x hx w hw, hadj y hy w hw⟩
    have h5 := Finset.card_le_card hsub
    have h6 := h4 x y hxy
    omega

end S90

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds

theorem centered_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) :
    ∃ K : Finset (Fin n), (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).IsVertexCover
        (K : Set (Fin n)) ∧ K.card ≤ (tops G C \ centreless G C).card := by
  classical
  let T := tops G C \ centreless G C
  have owner_exists (a : {a // a ∈ T}) : ∃ c : Fin n,
      ∀ u ∈ side C a.1 0, ∀ v ∈ side C a.1 1, c = u ∨ c = v := by
    obtain ⟨ht, hz⟩ := Finset.mem_sdiff.mp a.2
    have hn : ¬ (side (n:=n) C a.1 0 = ∅ ∨ side (n:=n) C a.1 1 = ∅) :=
      fun h => hz (Finset.mem_filter.mpr ⟨ht, h⟩)
    rcases (S90.top_facts G C h4 hL a.1 ht).2.2 with hl | hr
    · obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr (fun h => hn (Or.inl h))
      exact ⟨c, fun u hu _ _ => Or.inl (Finset.card_le_one.mp hl c hc u hu)⟩
    · obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr (fun h => hn (Or.inr h))
      exact ⟨c, fun _ _ v hv => Or.inr (Finset.card_le_one.mp hr c hc v hv)⟩
  choose center hcenter using owner_exists
  refine ⟨T.attach.image center, ?_, (by simpa only [Finset.card_attach] using (Finset.card_image_le (s := T.attach) (f := center)))⟩
  intro u v huv
  obtain ⟨hadj, hkeep⟩ := SimpleGraph.deleteEdges_adj.mp huv
  have hstar : s(u,v) ∈ starEdges G C := by
    by_contra hx
    exact hkeep (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hadj, hx⟩)
  obtain ⟨a, ha, hp⟩ := Finset.mem_biUnion.mp hstar
  obtain ⟨⟨i,j⟩, hij, he⟩ := Finset.mem_image.mp hp
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
  have haT : a ∈ T := Finset.mem_sdiff.mpr ⟨ha, fun hz => by
    rcases (Finset.mem_filter.mp hz).2 with h | h
    · exact (Finset.nonempty_iff_ne_empty.mp ⟨i, hi⟩) h
    · exact (Finset.nonempty_iff_ne_empty.mp ⟨j, hj⟩) h⟩
  let k : {a // a ∈ T} := ⟨a, haT⟩
  have hc := hcenter k i hi j hj
  have hm : center k ∈ T.attach.image center :=
    Finset.mem_image.mpr ⟨k, T.mem_attach k, rfl⟩
  change u ∈ T.attach.image center ∨ v ∈ T.attach.image center
  change s(i,j) = s(u,v) at he
  rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases hc with h | h <;>
    rw [h] at hm <;> tauto


abbrev PG23 : SimpleGraph (Fin 26) :=
  SimpleGraph.fromRel fun (x4 x5 : Fin 26) =>
    x4.val < 13 ∧ 13 ≤ x5.val ∧ (x4.val + x5.val) % 13 ∈ [0, 1, 3, 9]

def pgRelB (u v : ℕ) : Bool :=
  decide (u < 13) && decide (13 ≤ v) && ([0, 1, 3, 9].contains ((u + v) % 13))

def pgAdjB (u v : ℕ) : Bool :=
  pgRelB u v || pgRelB v u

lemma pgAdj_iff (u v : Fin 26) : PG23.Adj u v ↔ pgAdjB u.val v.val = true := by
  simp only [PG23, SimpleGraph.fromRel_adj, pgAdjB, pgRelB, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨_, h⟩
    tauto
  · intro h
    refine ⟨?_, by tauto⟩
    intro heq
    subst heq
    rcases h with ⟨⟨h1, h2⟩, _⟩ | ⟨⟨h1, h2⟩, _⟩ <;> omega

def noC4B : Bool :=
  (List.range 26).all fun a =>
    (List.range 26).all fun b =>
      decide (a = b) || decide (((List.range 26).countP fun w => pgAdjB a w && pgAdjB b w) ≤ 1)

lemma noC4B_true : noC4B = true := by decide +kernel

lemma countP_fin26 (p : ℕ → Bool) :
    (Finset.univ.filter fun w : Fin 26 => p w.val = true).card = (List.range 26).countP p := by
  rw [List.countP_eq_length_filter]
  have h1 : (Finset.univ.filter fun w : Fin 26 => p w.val = true).card =
      ((List.finRange 26).filter fun w : Fin 26 => p w.val).length := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 26).filter _)]
    congr 1
    ext w
    simp
  rw [h1]
  have hmap : (List.range 26) = (List.finRange 26).map Fin.val := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp
  rw [hmap, List.filter_map, List.length_map]
  rfl

lemma PG23_noFourCycle : NoFourCycle PG23 := by
  intro a b hab
  have h := noC4B_true
  simp only [noC4B, List.all_eq_true, List.mem_range] at h
  have h1 := h a.val a.isLt b.val b.isLt
  have hne : a.val ≠ b.val := fun he => hab (Fin.ext he)
  simp only [Bool.or_eq_true, decide_eq_true_eq, hne, false_or] at h1
  have heq : (Finset.univ.filter fun w : Fin 26 => PG23.Adj a w ∧ PG23.Adj b w) =
      (Finset.univ.filter fun w : Fin 26 => (pgAdjB a.val w.val && pgAdjB b.val w.val) = true) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pgAdj_iff, Bool.and_eq_true]
  rw [heq, countP_fin26 (fun w => pgAdjB a.val w && pgAdjB b.val w)]
  exact h1

abbrev shifts : Finset (Fin 13) := {0, 1, 3, 9}
abbrev pair (d p : Fin 13) : Sym2 (Fin 26) := s(Fin.castAdd 13 p, Fin.natAdd 13 (d-p))
abbrev matching (d : Fin 13) : Finset (Sym2 (Fin 26)) := Finset.univ.image (pair d)

def owner (d : Fin 13) (v : Fin 26) : Fin 13 :=
  if h : v.val < 13 then ⟨v.val, h⟩ else d - ⟨v.val-13, by omega⟩

lemma owner_endpoints : ∀ d p : Fin 13,
    owner d (Fin.castAdd 13 p) = p ∧ owner d (Fin.natAdd 13 (d-p)) = p := by decide +kernel

lemma pair_adj : ∀ d ∈ shifts, ∀ p : Fin 13,
    PG23.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 (d-p)) := by decide +kernel

lemma pair_inj (d : Fin 13) : Function.Injective (pair d) := by
  intro p q h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Fin.ext (congrArg (fun w : Fin 26 => w.val) h.1)
  · have hv := congrArg Fin.val h.1
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega

theorem loss_bound (U : Finset (Sym2 (Fin 26))) (K : Finset (Fin 26))
    (hK : (PG23.deleteEdges (U : Set (Sym2 (Fin 26)))).IsVertexCover (K : Set (Fin 26))) :
    ∀ d ∈ shifts, 13 ≤ K.card + (U ∩ matching d).card := by
  classical
  intro d hd
  let S := Finset.univ.filter (fun p : Fin 13 => pair d p ∈ U)
  have hs : S.image (pair d) = U ∩ matching d := by
    ext e
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter, matching]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hp, p, rfl⟩
    · rintro ⟨he, p, rfl⟩
      exact ⟨p, he, rfl⟩
  have hcard : S.card = (U ∩ matching d).card := by
    rw [← hs, Finset.card_image_of_injective _ (pair_inj d)]
  have hcover : (Finset.univ : Finset (Fin 13)) ⊆ K.image (owner d) ∪ S := by
    intro p _
    by_cases hu : pair d p ∈ U
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
    · have ha : (PG23.deleteEdges (U : Set (Sym2 (Fin 26)))).Adj
          (Fin.castAdd 13 p) (Fin.natAdd 13 (d-p)) :=
        SimpleGraph.deleteEdges_adj.mpr ⟨pair_adj d hd p, hu⟩
      apply Finset.mem_union_left
      rcases hK ha with hl | hr
      · exact Finset.mem_image.mpr ⟨_, hl, (owner_endpoints d p).1⟩
      · exact Finset.mem_image.mpr ⟨_, hr, (owner_endpoints d p).2⟩
  have hall := Finset.card_le_card hcover
  have hu := Finset.card_union_le (K.image (owner d)) S
  have hi : (K.image (owner d)).card ≤ K.card := Finset.card_image_le
  simp only [Finset.card_univ, Fintype.card_fin] at hall
  omega

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
theorem pointwise (C : Circuit) (hL : IsLeastAO PG23 C) :
    ∀ d ∈ shifts, 13 ≤ (tops PG23 C \ centreless PG23 C).card + (Ustar PG23 C ∩ matching d).card := by
  obtain ⟨K, hK, hc⟩ := centered_cover PG23 C PG23_noFourCycle hL
  intro d hd
  exact (loss_bound _ K hK d hd).trans (Nat.add_le_add_right hc _)

namespace PlaneLoss
def shifts : Finset (Fin 13) := {0,1,3,9}
def matching (d : Fin 13) : Finset (Sym2 (Fin 26)) :=
  Finset.univ.image fun p : Fin 13 => s(Fin.castAdd 13 p, Fin.natAdd 13 (d-p))

private theorem colors : ∀ a b : Fin 13, a ≠ b → Disjoint (matching a) (matching b) := by
  decide +kernel

theorem pick (U : Finset (Sym2 (Fin 26))) : ∃ d ∈ shifts, 4*(U ∩ matching d).card ≤ U.card := by
  let S := fun d : Fin 13 => U ∩ matching d
  have dis (a b : Fin 13) (h : a ≠ b) : Disjoint (S a) (S b) :=
    (colors a b h).mono Finset.inter_subset_right Finset.inter_subset_right
  have d01 : Disjoint (S 0) (S 1) := dis _ _ (by decide)
  have d3 : Disjoint (S 0 ∪ S 1) (S 3) :=
    Finset.disjoint_union_left.mpr ⟨dis _ _ (by decide), dis _ _ (by decide)⟩
  have d9 : Disjoint (S 0 ∪ S 1 ∪ S 3) (S 9) :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr
      ⟨dis _ _ (by decide),dis _ _ (by decide)⟩, dis _ _ (by decide)⟩
  have all : S 0 ∪ S 1 ∪ S 3 ∪ S 9 ⊆ U := by
    apply Finset.union_subset
    · apply Finset.union_subset
      · exact Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
      · exact Finset.inter_subset_left
    · exact Finset.inter_subset_left
  have count := Finset.card_le_card all
  rw [Finset.card_union_of_disjoint d9,Finset.card_union_of_disjoint d3,
    Finset.card_union_of_disjoint d01] at count
  by_contra! h
  have a := h 0 (by decide)
  have b := h 1 (by decide)
  have c := h 3 (by decide)
  have d := h 9 (by decide)
  change (S 0).card + (S 1).card + (S 3).card + (S 9).card ≤ U.card at count
  change U.card < 4*(S 0).card at a
  change U.card < 4*(S 1).card at b
  change U.card < 4*(S 3).card at c
  change U.card < 4*(S 9).card at d
  omega

end PlaneLoss

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
namespace Local9049Profile

theorem first : 
      let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0,1,3,9] : List ℕ))
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      let U := Ustar G C
      let A := (tops G C \ centreless G C).card
      let shifts : Finset (Fin 13) := {0,1,3,9}
      let loss (d : Fin 13) := (U ∩ (Finset.univ.image fun p : Fin 13 =>
        s(Fin.castAdd 13 p, Fin.natAdd 13 (d-p)))).card
      (∀ d ∈ shifts, 13 ≤ A + loss d) ∧ ∃ d ∈ shifts, 4 * loss d ≤ U.card := by
  dsimp only
  intro C least _
  exact ⟨pointwise C least, PlaneLoss.pick _⟩

end Local9049Profile

end PEqualNP.Outside.L_meta_18961


theorem PEqualNP.Outside.L_meta_18961 : (let x1 : SimpleGraph (Fin (26 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (26 : ℕ)) => ↑x1 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x2 ∧ (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       have x5 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;       have x6 : ℕ := (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card;       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → ℕ := fun (x8 : Fin (13 : ℕ)) => (x5 ∩ Finset.image (fun (x9 : Fin (13 : ℕ)) => s(Fin.castAdd (13 : ℕ) x9, Fin.natAdd (13 : ℕ) (x8 - x9))) Finset.univ).card;       (∀ x9 ∈ x7, (13 : ℕ) ≤ x6 + x8 x9) ∧ ∃ x9 ∈ x7, (4 : ℕ) * x8 x9 ≤ x5.card) := by
  exact PEqualNP.Outside.L_meta_18961.Local9049Profile.first
