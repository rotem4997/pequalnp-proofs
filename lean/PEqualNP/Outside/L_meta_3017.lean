import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3017

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core

local instance : DecidableEq GateOp := gateOpDecEq

/-! ## Section 1: Basic Circuit Evaluation & Monotonicity -/

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl wireStep w

lemma wires_eq_wiresFrom (C : Circuit) (x : List Bool) :
    C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_len (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    simp only [wiresFrom, List.foldl_cons] at ih ⊢
    rw [ih]; simp [wireStep]; omega

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (wireStep w g).length := by simp [wireStep]; omega
    change (wiresFrom gs (wireStep w g)).getD i false = w.getD i false
    rw [ih (wireStep w g) hi']
    simp only [wireStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_wiresFrom, wiresFrom_len, List.length_ofFn]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq_getElem C j hj]
  exact List.getElem_mem hj

lemma wireVal_input (n : ℕ) (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n C i.val x = x i := by
  unfold wireVal
  rw [wires_eq_wiresFrom, wiresFrom_getD_lt _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma wireVal_ge_len (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool)
    (hw : n + C.gates.length ≤ w) :
    wireVal n C w x = false := by
  unfold wireVal
  rw [List.getD_eq_default _ _ (by rw [wires_len]; exact hw)]

lemma gateVal_eq_wireVal (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wireVal n C (n + j) x := rfl

lemma circuitFun_eq_wireVal (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = wireVal n C C.output x := rfl

lemma gateVal_eval (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hRB : ReadsBack n C) (x : Fin n → Bool) :
    gateVal n C j x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wireVal n C i x) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  set pre := C.gates.take j
  set gj := C.gates[j]
  set post := C.gates.drop (j + 1)
  have hpre_len : pre.length = j := by simp [pre]; omega
  have hw_pre_len : (wiresFrom pre (List.ofFn x)).length = n + j := by
    rw [wiresFrom_len, List.length_ofFn, hpre_len]
  have h1 : C.wires (List.ofFn x) =
      wiresFrom post (wireStep (wiresFrom pre (List.ofFn x)) gj) := by
    rw [wires_eq_wiresFrom, hsplit, wiresFrom_append]
    rfl
  have hlt : n + j < (wireStep (wiresFrom pre (List.ofFn x)) gj).length := by
    simp [wireStep, hw_pre_len]
  unfold gateVal
  rw [h1, wiresFrom_getD_lt _ _ _ hlt]
  have hmid : (wireStep (wiresFrom pre (List.ofFn x)) gj).getD (n + j) false =
      gj.op.eval (gj.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false) := by
    simp only [wireStep, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_of_eq hw_pre_len),
      hw_pre_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hmid, gateAt_eq_getElem C j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < n + j := by
    have := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at this
    exact this hi
  unfold wireVal
  rw [h1]
  have hilt2 : i < (wireStep (wiresFrom pre (List.ofFn x)) gj).length := by
    simp [wireStep, hw_pre_len]; omega
  rw [wiresFrom_getD_lt _ _ _ hilt2]
  simp only [wireStep, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega : i < (wiresFrom pre (List.ofFn x)).length)]

lemma eval_and_two (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

lemma eval_or_two (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

lemma list_length_two {α : Type} {l : List α} (h : l.length = 2) :
    ∃ a b, l = [a, b] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at h
  exact ⟨a, b, rfl⟩

lemma op_eval_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {l₁ l₂ : List Bool} (hl : l₁.length = 2) (hl2 : l₂.length = 2)
    (hle : ∀ i : Fin 2, l₁.getD i.val false ≤ l₂.getD i.val false) :
    op.eval l₁ ≤ op.eval l₂ := by
  obtain ⟨a₁, b₁, rfl⟩ := list_length_two hl
  obtain ⟨a₂, b₂, rfl⟩ := list_length_two hl2
  have ha := hle 0
  have hb := hle 1
  simp at ha hb
  rcases hop with rfl | rfl
  · rw [eval_and_two, eval_and_two]
    cases a₁ <;> cases b₁ <;> cases a₂ <;> cases b₂ <;> simp_all
  · rw [eval_or_two, eval_or_two]
    cases a₁ <;> cases b₁ <;> cases a₂ <;> cases b₂ <;> simp_all

lemma wireVal_mono (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    {x y : Fin n → Bool} (hxy : ∀ i : Fin n, x i ≤ y i) :
    ∀ w : ℕ, wireVal n C w x ≤ wireVal n C w y := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt : w < n
    · rw [show w = (⟨w, hlt⟩ : Fin n).val from rfl, wireVal_input, wireVal_input]
      exact hxy ⟨w, hlt⟩
    · by_cases hge : n + C.gates.length ≤ w
      · rw [wireVal_ge_len n C w x hge, wireVal_ge_len n C w y hge]
      · set j := w - n
        have hj : j < C.gates.length := by omega
        have hw : w = n + j := by omega
        rw [hw, ← gateVal_eq_wireVal, ← gateVal_eq_wireVal,
          gateVal_eval n C j hj hAO.2.1 x, gateVal_eval n C j hj hAO.2.1 y]
        have hmem := gateAt_mem C j hj
        have hop := hAO.1 _ hmem
        have hlen := hAO.2.2 _ hmem
        apply op_eval_mono hop (by simp [hlen]) (by simp [hlen])
        intro idx
        obtain ⟨a, b, hab⟩ := list_length_two hlen
        rw [hab]
        fin_cases idx
        · simp only [Fin.zero_eta, Fin.val_zero, List.map_cons, List.getD_cons_zero]
          apply ih a
          have := hAO.2.1 j hj a (by rw [hab]; simp)
          omega
        · simp only [Fin.mk_one, Fin.val_one, List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
          apply ih b
          have := hAO.2.1 j hj b (by rw [hab]; simp)
          omega

lemma wireVal_all_false (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w : ℕ, wireVal n C w (fun _ => false) = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt : w < n
    · rw [show w = (⟨w, hlt⟩ : Fin n).val from rfl, wireVal_input]
    · by_cases hge : n + C.gates.length ≤ w
      · exact wireVal_ge_len n C w _ hge
      · set j := w - n
        have hj : j < C.gates.length := by omega
        have hw : w = n + j := by omega
        rw [hw, ← gateVal_eq_wireVal, gateVal_eval n C j hj hAO.2.1]
        have hmem := gateAt_mem C j hj
        have hop := hAO.1 _ hmem
        have hlen := hAO.2.2 _ hmem
        obtain ⟨a, b, hab⟩ := list_length_two hlen
        rw [hab]
        have ha : wireVal n C a (fun _ => false) = false :=
          ih a (by have := hAO.2.1 j hj a (by rw [hab]; simp); omega)
        have hb : wireVal n C b (fun _ => false) = false :=
          ih b (by have := hAO.2.1 j hj b (by rw [hab]; simp); omega)
        simp only [List.map_cons, List.map_nil, ha, hb]
        rcases hop with h | h <;> rw [h] <;> rfl

lemma graphFun_empty_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_empty_unitInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : Fin n) : graphFun G ∅ (unitInput p) = false := by
  cases h : graphFun G ∅ (unitInput p) with
  | false => rfl
  | true =>
    obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_empty_true_iff G _).mp h
    simp [unitInput] at hu hv
    subst hu; subst hv
    exact (G.ne_of_adj huv rfl).elim

lemma graphFun_empty_pairInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  apply (graphFun_empty_true_iff G _).mpr
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

/-! ## Section 2: Cones and OR-Reachability -/

def conesFrom (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) : List (List ℕ) :=
  gs.foldl (coneStep n) cs

lemma cones_eq_conesFrom (n : ℕ) (C : Circuit) :
    cones n C = conesFrom n C.gates [] := rfl

lemma conesFrom_append (n : ℕ) (gs₁ gs₂ : List Gate) (cs : List (List ℕ)) :
    conesFrom n (gs₁ ++ gs₂) cs = conesFrom n gs₂ (conesFrom n gs₁ cs) := by
  simp [conesFrom, List.foldl_append]

lemma conesFrom_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (conesFrom n gs cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp [conesFrom]
  | cons g gs ih =>
    simp only [conesFrom, List.foldl_cons] at ih ⊢
    rw [ih]; simp [coneStep]; omega

lemma conesFrom_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < cs.length) :
    (conesFrom n gs cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    have hj' : j < (coneStep n cs g).length := by simp [coneStep]; omega
    change (conesFrom n gs (coneStep n cs g)).getD j [] = cs.getD j []
    rw [ih (coneStep n cs g) hj']
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma cones_getD_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  set pre := C.gates.take j
  set gj := C.gates[j]
  set post := C.gates.drop (j + 1)
  have hpre_len : pre.length = j := by simp [pre]; omega
  have hcs_len : (conesFrom n pre []).length = j := by rw [conesFrom_len, hpre_len]; simp
  have h1 : cones n C = conesFrom n post (coneStep n (conesFrom n pre []) gj) := by
    rw [cones_eq_conesFrom, hsplit, conesFrom_append]; rfl
  have hlt : j < (coneStep n (conesFrom n pre []) gj).length := by
    simp [coneStep, hcs_len]
  rw [h1, conesFrom_getD_lt n post _ j hlt]
  have hmid : (coneStep n (conesFrom n pre []) gj).getD j [] =
      (gj.inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (conesFrom n pre []).getD (w - n) []) := by
    simp only [coneStep, hcs_len, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_of_eq hcs_len), Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
  rw [hmid, gateAt_eq_getElem C j hj]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  have hwlt : w - n < j := by omega
  have hwlt' : w - n < (coneStep n (conesFrom n pre []) gj).length := by
    simp [coneStep, hcs_len]; omega
  congr 1
  rw [conesFrom_getD_lt n post _ (w - n) hwlt']
  simp only [coneStep, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega : w - n < (conesFrom n pre []).length)]

lemma InCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone
  rw [cones_getD_eq n C j hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, h⟩
    exact ⟨w, hw1, hw2, hw3, h⟩
  · rintro ⟨w, hw1, hw2, hw3, h⟩
    exact ⟨w, ⟨hw1, hw2, hw3⟩, h⟩

lemma InCone_ge_len (n : ℕ) (C : Circuit) (i j : ℕ) (hj : C.gates.length ≤ j) :
    ¬ InCone n C i j := by
  unfold InCone
  rw [List.getD_eq_default _ _ (by rw [cones_eq_conesFrom, conesFrom_len]; simp; omega)]
  simp

lemma InCone_lt (n : ℕ) (C : Circuit) {i j : ℕ} (h : InCone n C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases hj : j < C.gates.length
    · obtain ⟨w, _, hw1, hw2, h'⟩ := (InCone_iff n C i j hj).mp h
      rcases h' with rfl | h'
      · omega
      · have := ih (w - n) (by omega) h'
        omega
    · exact (InCone_ge_len n C i j (by omega) h).elim

lemma InCone_lt_len (n : ℕ) (C : Circuit) {i j : ℕ} (h : InCone n C i j) :
    i < C.gates.length := by
  by_cases hj : j < C.gates.length
  · exact lt_trans (InCone_lt n C h) hj
  · exact (InCone_ge_len n C i j (by omega) h).elim

lemma InCone_of_mem_inputs (n : ℕ) (C : Circuit) {i j : ℕ}
    (hj : j < C.gates.length) (hRB : ReadsBack n C)
    (hm : n + i ∈ (gateAt C j).inputs) : InCone n C i j := by
  rw [InCone_iff n C i j hj]
  have hlt := hRB j hj (n + i) hm
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩

lemma InCone_trans (n : ℕ) (C : Circuit) {i j k : ℕ}
    (h1 : InCone n C i j) (h2 : InCone n C j k) : InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k < C.gates.length
    · obtain ⟨w, hwm, hw1, hw2, h'⟩ := (InCone_iff n C j k hk).mp h2
      rw [InCone_iff n C i k hk]
      rcases h' with rfl | h'
      · exact ⟨w, hwm, hw1, hw2, Or.inr h1⟩
      · exact ⟨w, hwm, hw1, hw2, Or.inr (ih (w - n) (by omega) h')⟩
    · exact (InCone_ge_len n C j k (by omega) h2).elim

lemma InOutputCone_of_InCone (n : ℕ) (C : Circuit) {i j : ℕ}
    (h1 : InCone n C i j) (h2 : InOutputCone n C j) : InOutputCone n C i := by
  refine ⟨InCone_lt_len n C h1, ?_⟩
  rcases h2.2 with ho | ⟨hn, hc⟩
  · right
    refine ⟨by omega, ?_⟩
    rw [ho, Nat.add_sub_cancel_left]
    exact h1
  · right
    exact ⟨hn, InCone_trans n C h1 hc⟩

lemma mem_coneSet_iff (n : ℕ) (C : Circuit) (c : ℕ) (hc : c < C.gates.length) (i : ℕ) :
    i ∈ coneSet n C c ↔ i = c ∨ InCone n C i c := by
  unfold coneSet
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨_, h⟩)
    · exact Or.inl rfl
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr ⟨InCone_lt_len n C h, h⟩

lemma coneSet_subset_range (n : ℕ) (C : Circuit) (c : ℕ) (hc : c < C.gates.length) :
    coneSet n C c ⊆ Finset.range C.gates.length := by
  intro i hi
  rw [Finset.mem_range]
  rcases (mem_coneSet_iff n C c hc i).mp hi with rfl | h
  · exact hc
  · exact InCone_lt_len n C h

lemma InCone_has_reader (n : ℕ) (C : Circuit) {i c : ℕ} (hc : c < C.gates.length)
    (h : InCone n C i c) :
    ∃ k ∈ coneSet n C c, n + i ∈ (gateAt C k).inputs := by
  induction c using Nat.strong_induction_on with
  | ind c ih =>
    obtain ⟨w, hwm, hw1, hw2, h'⟩ := (InCone_iff n C i c hc).mp h
    rcases h' with rfl | h'
    · refine ⟨c, (mem_coneSet_iff n C c hc c).mpr (Or.inl rfl), ?_⟩
      rwa [show n + (w - n) = w by omega]
    · have hwlt : w - n < C.gates.length := by omega
      obtain ⟨k, hk, hkin⟩ := ih (w - n) (by omega) hwlt h'
      refine ⟨k, ?_, hkin⟩
      rw [mem_coneSet_iff n C c hc]
      rcases (mem_coneSet_iff n C (w - n) hwlt k).mp hk with rfl | hk'
      · exact Or.inr ((InCone_iff n C (w - n) c hc).mpr ⟨w, hwm, hw1, hw2, Or.inl rfl⟩)
      · exact Or.inr ((InCone_iff n C k c hc).mpr ⟨w, hwm, hw1, hw2, Or.inr hk'⟩)

-- OrSets and OrReaches
def orSetsFrom (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) : List (List ℕ) :=
  gs.foldl (orStep n) cs

lemma orSets_eq (n : ℕ) (C : Circuit) : orSets n C = orSetsFrom n C.gates [] := rfl

lemma orSetsFrom_append (n : ℕ) (gs₁ gs₂ : List Gate) (cs : List (List ℕ)) :
    orSetsFrom n (gs₁ ++ gs₂) cs = orSetsFrom n gs₂ (orSetsFrom n gs₁ cs) := by
  simp [orSetsFrom, List.foldl_append]

lemma orSetsFrom_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (orSetsFrom n gs cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp [orSetsFrom]
  | cons g gs ih =>
    simp only [orSetsFrom, List.foldl_cons] at ih ⊢
    rw [ih]; simp [orStep]; omega

lemma orSetsFrom_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < cs.length) :
    (orSetsFrom n gs cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    have hj' : j < (orStep n cs g).length := by simp [orStep]; omega
    change (orSetsFrom n gs (orStep n cs g)).getD j [] = cs.getD j []
    rw [ih (orStep n cs g) hj']
    simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma orSets_getD_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (orSets n C).getD j [] =
      j :: (if (gateAt C j).op = GateOp.or then
        ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
          (fun w => (orSets n C).getD (w - n) [])
        else []) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  set pre := C.gates.take j
  set gj := C.gates[j]
  set post := C.gates.drop (j + 1)
  have hpre_len : pre.length = j := by simp [pre]; omega
  have hcs_len : (orSetsFrom n pre []).length = j := by rw [orSetsFrom_len, hpre_len]; simp
  have h1 : orSets n C = orSetsFrom n post (orStep n (orSetsFrom n pre []) gj) := by
    rw [orSets_eq, hsplit, orSetsFrom_append]; rfl
  have hlt : j < (orStep n (orSetsFrom n pre []) gj).length := by
    simp [orStep, hcs_len]
  rw [h1, orSetsFrom_getD_lt n post _ j hlt]
  have hmid : (orStep n (orSetsFrom n pre []) gj).getD j [] =
      j :: (if gj.op = GateOp.or then
        (gj.inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
          (fun w => (orSetsFrom n pre []).getD (w - n) [])
        else []) := by
    simp only [orStep, hcs_len, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_of_eq hcs_len), Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
  rw [hmid, gateAt_eq_getElem C j hj]
  congr 1
  split_ifs
  · apply List.flatMap_congr
    intro w hw
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    have hwlt' : w - n < (orStep n (orSetsFrom n pre []) gj).length := by
      simp [orStep, hcs_len]; omega
    rw [orSetsFrom_getD_lt n post _ (w - n) hwlt']
    simp only [orStep, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega : w - n < (orSetsFrom n pre []).length)]
  · rfl

lemma OrReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  refine ⟨by omega, ?_⟩
  rw [Nat.add_sub_cancel_left, orSets_getD_eq n C j hj]
  simp

lemma OrReaches_step (n : ℕ) (C : Circuit) {j w g : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hm : w ∈ (gateAt C j).inputs) (hlt : w < n + j)
    (hr : OrReaches n C w g) : OrReaches n C (n + j) g := by
  refine ⟨by omega, ?_⟩
  rw [Nat.add_sub_cancel_left, orSets_getD_eq n C j hj, if_pos hop]
  apply List.mem_cons_of_mem
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  exact ⟨w, ⟨hm, hr.1, hlt⟩, hr.2⟩

lemma eq_true_of_true_le {b : Bool} (h : true ≤ b) : b = true := by
  cases b with
  | true => rfl
  | false => exact absurd h (by decide)

lemma OrReaches_val_mono (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) {w g : ℕ}
    (hr : OrReaches n C w g) (x : Fin n → Bool) (hg : gateVal n C g x = true) :
    wireVal n C w x = true := by
  obtain ⟨hn, hmem⟩ := hr
  have hw : w = n + (w - n) := by omega
  rw [hw, ← gateVal_eq_wireVal]
  revert hmem
  generalize w - n = j
  clear hw hn
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hmem
    by_cases hj : j < C.gates.length
    · rw [orSets_getD_eq n C j hj] at hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hg
      · split_ifs at hmem with hop
        · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hmem
          obtain ⟨u, ⟨hum, hu1, hu2⟩, hur⟩ := hmem
          have hu_true : gateVal n C (u - n) x = true := ih (u - n) (by omega) hur
          have hu_w : wireVal n C u x = true := by
            rwa [show u = n + (u - n) by omega, ← gateVal_eq_wireVal]
          rw [gateVal_eval n C j hj hAO.2.1 x, hop]
          obtain ⟨a, b, hab⟩ := list_length_two (hAO.2.2 _ (gateAt_mem C j hj))
          rw [hab] at hum ⊢
          simp only [List.map_cons, List.map_nil, eval_or_two, Bool.or_eq_true]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hum
          rcases hum with rfl | rfl
          · exact Or.inl hu_w
          · exact Or.inr hu_w
        · simp at hmem
    · rw [List.getD_eq_default _ _ (by rw [orSets_eq, orSetsFrom_len]; simp; omega)] at hmem
      simp at hmem

/-! ## Section 3: IsOrTree Lemmas -/

lemma readsIn_pos_iff (C : Circuit) (G : Finset ℕ) (w : ℕ) :
    0 < readsIn C G w ↔ ∃ j ∈ G, w ∈ (gateAt C j).inputs := by
  unfold readsIn
  rw [Finset.sum_pos_iff]
  constructor
  · rintro ⟨j, hj, hpos⟩
    exact ⟨j, hj, List.count_pos_iff.mp hpos⟩
  · rintro ⟨j, hj, hm⟩
    exact ⟨j, hj, List.count_pos_iff.mpr hm⟩

lemma orTree_mem_lt_len (n : ℕ) (C : Circuit) (T L : Finset ℕ) (ρ : ℕ)
    (hOT : IsOrTree n C T L ρ) (j : ℕ) (hj : j ∈ T) : j < C.gates.length := by
  by_contra hge
  have h0 : (gateAt C j).inputs = [] := by
    simp [gateAt, List.getElem?_eq_none (by omega : C.gates.length ≤ j)]
  have h2 := (hOT.1 j hj).2.1
  rw [h0] at h2
  simp at h2

lemma orTree_gate_true_imp_leaf (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (T L : Finset ℕ) (ρ : ℕ) (hOT : IsOrTree n C T L ρ)
    (x : Fin n → Bool) :
    ∀ j ∈ T, gateVal n C j x = true → ∃ w ∈ L, w < n + j ∧ wireVal n C w x = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj htrue
    have hjlt := orTree_mem_lt_len n C T L ρ hOT j hj
    obtain ⟨hop, hlen, hin⟩ := hOT.1 j hj
    rw [gateVal_eval n C j hjlt hAO.2.1 x, hop] at htrue
    obtain ⟨a, b, hab⟩ := list_length_two hlen
    rw [hab] at htrue
    simp only [List.map_cons, List.map_nil, eval_or_two, Bool.or_eq_true] at htrue
    have step : ∀ u, u ∈ (gateAt C j).inputs → wireVal n C u x = true →
        ∃ w ∈ L, w < n + j ∧ wireVal n C w x = true := by
      intro u hum hut
      have hult := hAO.2.1 j hjlt u hum
      rcases hin u hum with huL | ⟨hun, huT⟩
      · exact ⟨u, huL, hult, hut⟩
      · have hut' : gateVal n C (u - n) x = true := by
          rw [gateVal_eq_wireVal, show n + (u - n) = u by omega]; exact hut
        obtain ⟨w, hwL, hwlt, hwt⟩ := ih (u - n) (by omega) huT hut'
        exact ⟨w, hwL, by omega, hwt⟩
    rcases htrue with ha | hb
    · exact step a (by rw [hab]; simp) ha
    · exact step b (by rw [hab]; simp) hb

lemma orTree_output_true_imp_leaf (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (T L : Finset ℕ) (hOT : IsOrTree n C T L C.output) (x : Fin n → Bool)
    (h : circuitFun n C x = true) : ∃ w ∈ L, wireVal n C w x = true := by
  have hroot := hOT.2.2.2
  split_ifs at hroot with hTe
  · rw [hroot]
    exact ⟨C.output, by simp, h⟩
  · obtain ⟨r, hrT, hrEq⟩ := hroot
    have hrt : gateVal n C r x = true := by
      rw [gateVal_eq_wireVal, ← hrEq]; exact h
    obtain ⟨w, hwL, _, hwt⟩ := orTree_gate_true_imp_leaf n C hAO T L C.output hOT x r hrT hrt
    exact ⟨w, hwL, hwt⟩

lemma orTree_ascend (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (T L : Finset ℕ) (hOT : IsOrTree n C T L C.output) :
    ∀ k : ℕ, ∀ j ∈ T, C.gates.length - j ≤ k →
      (C.output = n + j ∨ (n ≤ C.output ∧ InCone n C j (C.output - n))) ∧
      (∀ x : Fin n → Bool, gateVal n C j x = true → circuitFun n C x = true) := by
  intro k
  induction k with
  | zero =>
    intro j hj hle
    have := orTree_mem_lt_len n C T L C.output hOT j hj
    omega
  | succ k ih =>
    intro j hj hle
    by_cases hEq : n + j = C.output
    · refine ⟨Or.inl hEq.symm, fun x hx => ?_⟩
      rw [circuitFun_eq_wireVal, ← hEq]; exact hx
    · have hrc := hOT.2.2.1 j hj
      rw [if_neg hEq] at hrc
      obtain ⟨j', hj'T, hj'in⟩ := (readsIn_pos_iff C T (n + j)).mp (by omega)
      have hj'lt := orTree_mem_lt_len n C T L C.output hOT j' hj'T
      have hlt : j < j' := by
        have := hAO.2.1 j' hj'lt (n + j) hj'in
        omega
      have hinc : InCone n C j j' := InCone_of_mem_inputs n C hj'lt hAO.2.1 hj'in
      obtain ⟨hcone', hval'⟩ := ih j' hj'T (by omega)
      constructor
      · rcases hcone' with ho | ⟨hn, hc'⟩
        · right
          refine ⟨by omega, ?_⟩
          rw [ho, Nat.add_sub_cancel_left]
          exact hinc
        · right
          exact ⟨hn, InCone_trans n C hinc hc'⟩
      · intro x hx
        apply hval' x
        rw [gateVal_eval n C j' hj'lt hAO.2.1 x, (hOT.1 j' hj'T).1]
        obtain ⟨a, b, hab⟩ := list_length_two (hOT.1 j' hj'T).2.1
        rw [hab] at hj'in ⊢
        simp only [List.map_cons, List.map_nil, eval_or_two, Bool.or_eq_true]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'in
        rcases hj'in with h1 | h1
        · left; rw [← h1, ← gateVal_eq_wireVal]; exact hx
        · right; rw [← h1, ← gateVal_eq_wireVal]; exact hx

lemma orTree_leaf_to_output (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (T L : Finset ℕ) (hOT : IsOrTree n C T L C.output)
    (w : ℕ) (hw : w ∈ L) (hwn : n ≤ w) :
    (C.output = w ∨ (n ≤ C.output ∧ InCone n C (w - n) (C.output - n))) ∧
    (∀ x : Fin n → Bool, wireVal n C w x = true → circuitFun n C x = true) := by
  by_cases hEq : w = C.output
  · subst hEq
    exact ⟨Or.inl rfl, fun _ h => h⟩
  · have hrc := (hOT.2.1 w hw).2
    rw [if_neg hEq] at hrc
    obtain ⟨j, hjT, hjin⟩ := (readsIn_pos_iff C T w).mp (by omega)
    have hjlt := orTree_mem_lt_len n C T L C.output hOT j hjT
    have hinc : InCone n C (w - n) j := by
      apply InCone_of_mem_inputs n C hjlt hAO.2.1
      rwa [show n + (w - n) = w by omega]
    obtain ⟨hcone, hval⟩ := orTree_ascend n C hAO T L hOT (C.gates.length - j) j hjT (le_refl _)
    constructor
    · rcases hcone with ho | ⟨hn, hc⟩
      · right
        refine ⟨by omega, ?_⟩
        rw [ho, Nat.add_sub_cancel_left]
        exact hinc
      · right
        exact ⟨hn, InCone_trans n C hinc hc⟩
    · intro x hx
      apply hval x
      rw [gateVal_eval n C j hjlt hAO.2.1 x, (hOT.1 j hjT).1]
      obtain ⟨a, b, hab⟩ := list_length_two (hOT.1 j hjT).2.1
      rw [hab] at hjin ⊢
      simp only [List.map_cons, List.map_nil, eval_or_two, Bool.or_eq_true]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hjin
      rcases hjin with h1 | h1
      · left; rw [← h1]; exact hx
      · right; rw [← h1]; exact hx

/-! ## Section 4: Circuit C0, Monotonicity, and Star Forest of Lost Edges -/

def mkC0 (n : ℕ) (C : Circuit) (c : ℕ) (s : Fin n) : Circuit :=
  { gates := C.gates.map fun gg =>
      { op := gg.op, inputs := gg.inputs.map fun ww => if ww = n + c then (s : ℕ) else ww }
    output := C.output }

lemma mkC0_len (n : ℕ) (C : Circuit) (c : ℕ) (s : Fin n) :
    (mkC0 n C c s).gates.length = C.gates.length := by
  simp [mkC0]

lemma mkC0_gateAt (n : ℕ) (C : Circuit) (c : ℕ) (s : Fin n) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (mkC0 n C c s) j =
      { op := (gateAt C j).op
        inputs := (gateAt C j).inputs.map fun ww => if ww = n + c then (s : ℕ) else ww } := by
  rw [gateAt_eq_getElem _ j (by rw [mkC0_len]; exact hj), gateAt_eq_getElem C j hj]
  simp [mkC0]

lemma mkC0_isAO2 (n : ℕ) (C : Circuit) (c : ℕ) (s : Fin n) (hAO : IsAO2 n C) :
    IsAO2 n (mkC0 n C c s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [mkC0, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact hAO.1 g0 hg0
  · intro j hj i hi
    rw [mkC0_len] at hj
    rw [mkC0_gateAt n C c s j hj] at hi
    simp only [List.mem_map] at hi
    obtain ⟨w, hw, rfl⟩ := hi
    split_ifs
    · have := s.isLt; omega
    · exact hAO.2.1 j hj w hw
  · intro g hg
    simp only [mkC0, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simp [hAO.2.2 g0 hg0]

lemma wireVal_s_le_c (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (c : ℕ) (s : Fin n)
    (hSing : singletonSet n C c = {s}) (x : Fin n → Bool) :
    x s ≤ gateVal n C c x := by
  cases hxs : x s with
  | false => simp
  | true =>
    have hc_s : gateVal n C c (unitInput s) = true := by
      have : s ∈ singletonSet n C c := by rw [hSing]; simp
      simpa [singletonSet] using this
    have hle : ∀ i : Fin n, unitInput s i ≤ x i := by
      intro i
      by_cases hi : i = s
      · subst hi; simp [unitInput, hxs]
      · simp [unitInput, hi]
    have hm := wireVal_mono n C hAO hle (n + c)
    rw [← gateVal_eq_wireVal, ← gateVal_eq_wireVal, hc_s] at hm
    simpa using hm

lemma wireVal_C0_le_C (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (c : ℕ) (s : Fin n)
    (hSing : singletonSet n C c = {s}) (x : Fin n → Bool) :
    ∀ w : ℕ, wireVal n (mkC0 n C c s) w x ≤ wireVal n C w x := by
  have hAO0 := mkC0_isAO2 n C c s hAO
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt : w < n
    · rw [show w = (⟨w, hlt⟩ : Fin n).val from rfl, wireVal_input, wireVal_input]
    · by_cases hge : n + C.gates.length ≤ w
      · rw [wireVal_ge_len n (mkC0 n C c s) w x (by rw [mkC0_len]; exact hge),
          wireVal_ge_len n C w x hge]
      · set j := w - n
        have hj : j < C.gates.length := by omega
        have hw : w = n + j := by omega
        rw [hw, ← gateVal_eq_wireVal, ← gateVal_eq_wireVal,
          gateVal_eval n (mkC0 n C c s) j (by rw [mkC0_len]; exact hj) hAO0.2.1 x,
          gateVal_eval n C j hj hAO.2.1 x, mkC0_gateAt n C c s j hj]
        have hmem := gateAt_mem C j hj
        have hop := hAO.1 _ hmem
        have hlen := hAO.2.2 _ hmem
        apply op_eval_mono hop (by simp [hlen]) (by simp [hlen])
        intro idx
        obtain ⟨a, b, hab⟩ := list_length_two hlen
        rw [hab]
        have step : ∀ u, u < n + j →
            wireVal n (mkC0 n C c s) (if u = n + c then (s : ℕ) else u) x ≤ wireVal n C u x := by
          intro u hu
          split_ifs with heq
          · subst heq
            rw [wireVal_input, ← gateVal_eq_wireVal]
            exact wireVal_s_le_c n C hAO c s hSing x
          · exact ih u (by omega)
        fin_cases idx
        · simp only [Fin.zero_eta, Fin.val_zero, List.map_cons, List.getD_cons_zero]
          exact step a (hAO.2.1 j hj a (by rw [hab]; simp))
        · simp only [Fin.mk_one, Fin.val_one, List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
          exact step b (hAO.2.1 j hj b (by rw [hab]; simp))

lemma wireVal_C0_eq_C_of_eq_at_c (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (c : ℕ) (s : Fin n)
    (x : Fin n → Bool) (heq : x s = gateVal n C c x) :
    ∀ w : ℕ, wireVal n (mkC0 n C c s) w x = wireVal n C w x := by
  have hAO0 := mkC0_isAO2 n C c s hAO
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt : w < n
    · rw [show w = (⟨w, hlt⟩ : Fin n).val from rfl, wireVal_input, wireVal_input]
    · by_cases hge : n + C.gates.length ≤ w
      · rw [wireVal_ge_len n (mkC0 n C c s) w x (by rw [mkC0_len]; exact hge),
          wireVal_ge_len n C w x hge]
      · set j := w - n
        have hj : j < C.gates.length := by omega
        have hw : w = n + j := by omega
        rw [hw, ← gateVal_eq_wireVal, ← gateVal_eq_wireVal,
          gateVal_eval n (mkC0 n C c s) j (by rw [mkC0_len]; exact hj) hAO0.2.1 x,
          gateVal_eval n C j hj hAO.2.1 x, mkC0_gateAt n C c s j hj]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        simp only [Function.comp_apply]
        split_ifs with huc
        · subst huc
          rw [wireVal_input, ← gateVal_eq_wireVal, heq]
        · exact ih u (by have := hAO.2.1 j hj u hu; omega)

lemma wireVal_C0_eq_C_of_not_inCone (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (c : ℕ) (s : Fin n)
    (x : Fin n → Bool) :
    ∀ j < C.gates.length, ¬ InCone n C c j →
      gateVal n (mkC0 n C c s) j x = gateVal n C j x := by
  have hAO0 := mkC0_isAO2 n C c s hAO
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hnc
    rw [gateVal_eval n (mkC0 n C c s) j (by rw [mkC0_len]; exact hj) hAO0.2.1 x,
      gateVal_eval n C j hj hAO.2.1 x, mkC0_gateAt n C c s j hj]
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro u hu
    simp only [Function.comp_apply]
    have hult := hAO.2.1 j hj u hu
    have hne : u ≠ n + c := by
      intro hEq
      apply hnc
      exact InCone_of_mem_inputs n C hj hAO.2.1 (hEq ▸ hu)
    rw [if_neg hne]
    by_cases hun : u < n
    · rw [show u = (⟨u, hun⟩ : Fin n).val from rfl, wireVal_input, wireVal_input]
    · have hunc : ¬ InCone n C c (u - n) := by
        intro hcu
        apply hnc
        rw [InCone_iff n C c j hj]
        exact ⟨u, hu, by omega, hult, Or.inr hcu⟩
      rw [show u = n + (u - n) by omega, ← gateVal_eq_wireVal, ← gateVal_eq_wireVal]
      exact ih (u - n) (by omega) (by omega) hunc

lemma cone_inputs_agree (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (c : ℕ) (hc : c < C.gates.length)
    (x y : Fin n → Bool)
    (hagree : ∀ v : Fin n, (∃ k ∈ coneSet n C c, v.val ∈ (gateAt C k).inputs) → x v = y v) :
    ∀ j ∈ coneSet n C c, gateVal n C j x = gateVal n C j y := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hjK
    have hjlt : j < C.gates.length := Finset.mem_range.mp (coneSet_subset_range n C c hc hjK)
    rw [gateVal_eval n C j hjlt hAO.2.1 x, gateVal_eval n C j hjlt hAO.2.1 y]
    congr 1
    apply List.map_congr_left
    intro u hu
    have hult := hAO.2.1 j hjlt u hu
    by_cases hun : u < n
    · rw [show u = (⟨u, hun⟩ : Fin n).val from rfl, wireVal_input, wireVal_input]
      exact hagree ⟨u, hun⟩ ⟨j, hjK, hu⟩
    · have huK : u - n ∈ coneSet n C c := by
        rw [mem_coneSet_iff n C c hc]
        have hinc : InCone n C (u - n) j := by
          apply InCone_of_mem_inputs n C hjlt hAO.2.1
          rwa [show n + (u - n) = u by omega]
        rcases (mem_coneSet_iff n C c hc j).mp hjK with rfl | hjc
        · exact Or.inr hinc
        · exact Or.inr (InCone_trans n C hinc hjc)
      rw [show u = n + (u - n) by omega, ← gateVal_eq_wireVal, ← gateVal_eq_wireVal]
      exact ih (u - n) (by omega) huK

/-! ## Section 5: Deleting `coneSet n C c` from `C0` and Appending Stars -/

def posInKept (K : Finset ℕ) (j : ℕ) : ℕ :=
  ((Finset.range j).filter (· ∉ K)).card

def remapWire (n : ℕ) (K : Finset ℕ) (w : ℕ) : ℕ :=
  if w < n then w else n + posInKept K (w - n)

lemma posInKept_mono {K : Finset ℕ} {a b : ℕ} (hab : a < b) (ha : a ∉ K) :
    posInKept K a < posInKept K b := by
  unfold posInKept
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, ?_, ?_⟩
    · simp [hab, ha]
    · simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨by omega, hx.2⟩

lemma posInKept_le_mono {K : Finset ℕ} {a b : ℕ} (hab : a ≤ b) :
    posInKept K a ≤ posInKept K b := by
  unfold posInKept
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨by omega, hx.2⟩

def keptList (len : ℕ) (K : Finset ℕ) : List ℕ :=
  (List.range len).filter fun j => decide (j ∉ K)

lemma keptList_len (len : ℕ) (K : Finset ℕ) :
    (keptList len K).length = posInKept K len := by
  unfold keptList posInKept
  induction len with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.range_add_one]
    by_cases hm : m ∈ K
    · simp [hm, Finset.filter_insert]
    · simp [hm, Finset.filter_insert]

lemma keptList_getElem_pos (len : ℕ) (K : Finset ℕ) (j : ℕ) (hj : j < len) (hjK : j ∉ K) :
    ∃ h : posInKept K j < (keptList len K).length, (keptList len K)[posInKept K j]'h = j := by
  have hlt : posInKept K j < (keptList len K).length := by
    rw [keptList_len]
    exact posInKept_mono hj hjK
  refine ⟨hlt, ?_⟩
  have hsplit : List.range len = List.range j ++ j :: (List.range len).drop (j + 1) := by
    have : j < (List.range len).length := by simp [hj]
    have h1 := List.take_append_drop j (List.range len)
    rw [List.take_range, Nat.min_eq_left (le_of_lt hj)] at h1
    have h2 : (List.range len).drop j = j :: (List.range len).drop (j + 1) := by
      have hget : (List.range len)[j]'this = j := List.getElem_range this
      conv_lhs => rw [← List.cons_getElem_drop_succ (h := this)]
      rw [hget]
    rw [h2] at h1
    exact h1.symm
  have hfil : keptList len K =
      keptList j K ++ j :: ((List.range len).drop (j + 1)).filter (fun i => decide (i ∉ K)) := by
    unfold keptList
    conv_lhs => rw [hsplit]
    rw [List.filter_append, List.filter_cons, decide_eq_true hjK, if_pos rfl]
  have hlen_j : (keptList j K).length = posInKept K j := keptList_len j K
  have hget : (keptList len K)[posInKept K j]? = some j := by
    rw [hfil, List.getElem?_append_right (le_of_eq hlen_j), hlen_j, Nat.sub_self]
    rfl
  rw [List.getElem?_eq_getElem hlt] at hget
  exact Option.some.inj hget

lemma keptList_mem (len : ℕ) (K : Finset ℕ) (i : ℕ) (hi : i < (keptList len K).length) :
    (keptList len K)[i] < len ∧ (keptList len K)[i] ∉ K := by
  have hm : (keptList len K)[i] ∈ keptList len K := List.getElem_mem hi
  simp only [keptList, List.mem_filter, List.mem_range, decide_eq_true_eq] at hm
  exact hm

lemma keptList_pos_of_getElem (len : ℕ) (K : Finset ℕ) (i : ℕ) (hi : i < (keptList len K).length) :
    posInKept K ((keptList len K)[i]) = i := by
  obtain ⟨hlt, hnk⟩ := keptList_mem len K i hi
  obtain ⟨hp, hge⟩ := keptList_getElem_pos len K ((keptList len K)[i]) hlt hnk
  have hnd : (keptList len K).Nodup := (List.nodup_range).filter _
  exact (List.Nodup.getElem_inj_iff hnd).mp hge

def deleteCone (n : ℕ) (C0 : Circuit) (K : Finset ℕ) : Circuit :=
  { gates := (keptList C0.gates.length K).map fun j =>
      let g := gateAt C0 j
      { op := g.op, inputs := g.inputs.map (remapWire n K) }
    output := remapWire n K C0.output }

lemma deleteCone_len (n : ℕ) (C0 : Circuit) (K : Finset ℕ) :
    (deleteCone n C0 K).gates.length = posInKept K C0.gates.length := by
  simp [deleteCone, keptList_len]

lemma deleteCone_size_add (n : ℕ) (C0 : Circuit) (K : Finset ℕ)
    (hK : K ⊆ Finset.range C0.gates.length) :
    (deleteCone n C0 K).size + K.card = C0.size := by
  change (deleteCone n C0 K).gates.length + K.card = C0.gates.length
  rw [deleteCone_len]
  unfold posInKept
  have h1 : (Finset.range C0.gates.length).filter (· ∉ K) = Finset.range C0.gates.length \ K := by
    ext x; simp [Finset.mem_sdiff]
  rw [h1, Finset.card_sdiff_add_card_eq_card hK, Finset.card_range]

lemma deleteCone_isAO2 (n : ℕ) (C0 : Circuit) (K : Finset ℕ)
    (hAO0 : IsAO2 n C0)
    (hClosed : ∀ j < C0.gates.length, j ∉ K → ∀ w ∈ (gateAt C0 j).inputs, n ≤ w → w - n ∉ K) :
    IsAO2 n (deleteCone n C0 K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [deleteCone, List.mem_map] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    simp only [keptList, List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
    exact hAO0.1 (gateAt C0 j) (gateAt_mem C0 j hj.1)
  · intro idx hidx u hu
    have hidx' : idx < (keptList C0.gates.length K).length := by
      simpa [deleteCone] using hidx
    rw [gateAt_eq_getElem _ idx hidx] at hu
    simp only [deleteCone, List.getElem_map, List.mem_map] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    set j := (keptList C0.gates.length K)[idx]'hidx'
    obtain ⟨hjlt, hjK⟩ := keptList_mem C0.gates.length K idx hidx'
    have hpos : posInKept K j = idx := keptList_pos_of_getElem C0.gates.length K idx hidx'
    have hwlt : w < n + j := hAO0.2.1 j hjlt w hw
    unfold remapWire
    split_ifs with hwn
    · omega
    · have hwK : w - n ∉ K := hClosed j hjlt hjK w hw (by omega)
      have hpm : posInKept K (w - n) < posInKept K j := posInKept_mono (by omega) hwK
      omega
  · intro g hg
    simp only [deleteCone, List.mem_map] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    simp only [keptList, List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
    simp [hAO0.2.2 _ (gateAt_mem C0 j hj.1)]

lemma deleteCone_gateVal (n : ℕ) (C0 : Circuit) (K : Finset ℕ)
    (hAO0 : IsAO2 n C0)
    (hClosed : ∀ j < C0.gates.length, j ∉ K → ∀ w ∈ (gateAt C0 j).inputs, n ≤ w → w - n ∉ K)
    (x : Fin n → Bool) :
    ∀ j < C0.gates.length, j ∉ K →
      gateVal n (deleteCone n C0 K) (posInKept K j) x = gateVal n C0 j x := by
  have hAO1 := deleteCone_isAO2 n C0 K hAO0 hClosed
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjK
    obtain ⟨hpos_lt, hget_j⟩ := keptList_getElem_pos C0.gates.length K j hj hjK
    have hpos_len : posInKept K j < (deleteCone n C0 K).gates.length := by
      simpa [deleteCone] using hpos_lt
    rw [gateVal_eval n (deleteCone n C0 K) (posInKept K j) hpos_len hAO1.2.1 x,
      gateVal_eval n C0 j hj hAO0.2.1 x]
    have hga : gateAt (deleteCone n C0 K) (posInKept K j) =
        { op := (gateAt C0 j).op, inputs := (gateAt C0 j).inputs.map (remapWire n K) } := by
      rw [gateAt_eq_getElem _ _ hpos_len]
      simp only [deleteCone, List.getElem_map, hget_j]
    rw [hga]
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro w hw
    simp only [Function.comp_apply]
    have hwlt := hAO0.2.1 j hj w hw
    unfold remapWire
    split_ifs with hwn
    · rw [show w = (⟨w, hwn⟩ : Fin n).val from rfl, wireVal_input, wireVal_input]
    · have hwK : w - n ∉ K := hClosed j hj hjK w hw (by omega)
      rw [← gateVal_eq_wireVal]
      have hwr : wireVal n C0 w x = gateVal n C0 (w - n) x := by
        rw [gateVal_eq_wireVal, show n + (w - n) = w by omega]
      rw [hwr]
      exact ih (w - n) (by omega) (by omega) hwK

lemma deleteCone_circuitFun (n : ℕ) (C0 : Circuit) (K : Finset ℕ)
    (hAO0 : IsAO2 n C0)
    (hClosed : ∀ j < C0.gates.length, j ∉ K → ∀ w ∈ (gateAt C0 j).inputs, n ≤ w → w - n ∉ K)
    (hOut : n ≤ C0.output → C0.output - n < C0.gates.length → C0.output - n ∉ K) :
    circuitFun n (deleteCone n C0 K) = circuitFun n C0 := by
  funext x
  rw [circuitFun_eq_wireVal, circuitFun_eq_wireVal]
  change wireVal n (deleteCone n C0 K) (remapWire n K C0.output) x = wireVal n C0 C0.output x
  unfold remapWire
  split_ifs with hlt
  · rw [show C0.output = (⟨C0.output, hlt⟩ : Fin n).val from rfl, wireVal_input, wireVal_input]
  · by_cases hge : C0.gates.length ≤ C0.output - n
    · have h1 : n + (deleteCone n C0 K).gates.length ≤ n + posInKept K (C0.output - n) := by
        rw [deleteCone_len]
        have := posInKept_le_mono (K := K) hge
        omega
      rw [wireVal_ge_len n (deleteCone n C0 K) _ x h1,
        wireVal_ge_len n C0 _ x (by omega)]
    · have hj : C0.output - n < C0.gates.length := by omega
      have hjK : C0.output - n ∉ K := hOut (by omega) hj
      rw [← gateVal_eq_wireVal]
      have hwr : wireVal n C0 C0.output x = gateVal n C0 (C0.output - n) x := by
        rw [gateVal_eq_wireVal, show n + (C0.output - n) = C0.output by omega]
      rw [hwr]
      exact deleteCone_gateVal n C0 K hAO0 hClosed x (C0.output - n) hj hjK

/-! ### Appending Star Gadgets -/

lemma append_wireVal_lt (n : ℕ) (C : Circuit) (extra : List Gate) (w : ℕ)
    (hw : w < n + C.gates.length) (x : Fin n → Bool) :
    wireVal n { gates := C.gates ++ extra, output := C.output } w x = wireVal n C w x := by
  unfold wireVal
  rw [wires_eq_wiresFrom, wiresFrom_append]
  exact wiresFrom_getD_lt extra (wiresFrom C.gates (List.ofFn x)) w (by rw [wiresFrom_len, List.length_ofFn]; exact hw)

lemma append_one_isAO2 (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2)
    (hrb : ∀ i ∈ g.inputs, i < n + C.gates.length) (out : ℕ) :
    IsAO2 n { gates := C.gates ++ [g], output := out } := by
  refine ⟨?_, ?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hAO.1 g' h
    · exact hop
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < C.gates.length
    · have hga : gateAt { gates := C.gates ++ [g], output := out } j = gateAt C j := by
        rw [gateAt_eq_getElem _ j (by simp; omega), gateAt_eq_getElem C j hlt]
        simp [List.getElem_append_left hlt]
      rw [hga] at hi
      exact hAO.2.1 j hlt i hi
    · have hjeq : j = C.gates.length := by omega
      subst hjeq
      have hga : gateAt { gates := C.gates ++ [g], output := out } C.gates.length = g := by
        rw [gateAt_eq_getElem _ _ (by simp)]
        simp
      rw [hga] at hi
      exact hrb i hi
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hAO.2.2 g' h
    · exact hlen

lemma append_one_val_last (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2)
    (hrb : ∀ i ∈ g.inputs, i < n + C.gates.length) (out : ℕ) (x : Fin n → Bool) :
    wireVal n { gates := C.gates ++ [g], output := out } (n + C.gates.length) x =
      g.op.eval (g.inputs.map fun i => wireVal n C i x) := by
  have hAO' := append_one_isAO2 n C hAO g hop hlen hrb out
  rw [← gateVal_eq_wireVal, gateVal_eval n _ C.gates.length (by simp) hAO'.2.1 x]
  have hga : gateAt { gates := C.gates ++ [g], output := out } C.gates.length = g := by
    rw [gateAt_eq_getElem _ _ (by simp)]
    simp
  rw [hga]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact append_wireVal_lt n C [g] i (hrb i hi) x

/-- Append a chain of OR gates computing `⋁_{y ∈ ys} x_y` (for nonempty `ys`), returning the
updated circuit and the wire index of the OR result. Adds `ys.length - 1` gates. -/
def addOrChain (n : ℕ) (C : Circuit) : List (Fin n) → Circuit × ℕ
  | [] => (C, 0)
  | [y] => (C, y.val)
  | y :: y' :: ys =>
    let (C', w) := addOrChain n C (y' :: ys)
    let nw := n + C'.gates.length
    ({ gates := C'.gates ++ [⟨GateOp.or, [y.val, w]⟩], output := C'.output }, nw)

lemma addOrChain_spec (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∀ (ys : List (Fin n)), ys ≠ [] →
      let res := addOrChain n C ys
      IsAO2 n res.1 ∧
      res.1.gates.length = C.gates.length + (ys.length - 1) ∧
      res.1.output = C.output ∧
      res.2 < n + res.1.gates.length ∧
      (∀ w < n + C.gates.length, ∀ x : Fin n → Bool, wireVal n res.1 w x = wireVal n C w x) ∧
      (∀ x : Fin n → Bool, wireVal n res.1 res.2 x = true ↔ ∃ y ∈ ys, x y = true) := by
  intro ys
  induction ys with
  | nil => intro h; exact (h rfl).elim
  | cons y tl ih =>
    intro _
    cases tl with
    | nil =>
      refine ⟨hAO, by simp [addOrChain], rfl, ?_, fun _ _ _ => rfl, fun x => ?_⟩
      · simp only [addOrChain]; have := y.isLt; omega
      · simp only [addOrChain, wireVal_input, List.mem_singleton, exists_eq_left]
    | cons y' tl' =>
      obtain ⟨hAO', hlen', hout', hwlt', hpres', hval'⟩ := ih (by simp)
      rcases hrec : addOrChain n C (y' :: tl') with ⟨C', w⟩
      rw [hrec] at hAO' hlen' hout' hwlt' hpres' hval'
      dsimp only at hAO' hlen' hout' hwlt' hpres' hval'
      have hrb : ∀ i ∈ [y.val, w], i < n + C'.gates.length := by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · have := y.isLt; omega
        · exact hwlt'
      have hAO2 := append_one_isAO2 n C' hAO' ⟨GateOp.or, [y.val, w]⟩ (Or.inr rfl) rfl hrb C'.output
      simp only [addOrChain, hrec]
      refine ⟨hAO2, ?_, hout', ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen']
        omega
      · simp only [List.length_append, List.length_singleton]; omega
      · intro u hu x
        have hu' : u < n + C'.gates.length := by omega
        rw [append_wireVal_lt n C' _ u hu' x]
        exact hpres' u hu x
      · intro x
        rw [append_one_val_last n C' hAO' ⟨GateOp.or, [y.val, w]⟩ (Or.inr rfl) rfl hrb C'.output x]
        simp only [List.map_cons, List.map_nil, eval_or_two, Bool.or_eq_true, wireVal_input, hval']
        constructor
        · rintro (hy | ⟨u, hu, hxu⟩)
          · exact ⟨y, by simp, hy⟩
          · exact ⟨u, List.mem_cons_of_mem _ hu, hxu⟩
        · rintro ⟨u, hu, hxu⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | hu
          · exact Or.inl hxu
          · exact Or.inr ⟨u, List.mem_cons.mpr hu, hxu⟩

/-- Append one star `x_z ∧ (⋁_{y ∈ ys} x_y)` and OR it onto `C.output`.
Adds `ys.length + 1` gates. -/
def addStar (n : ℕ) (C : Circuit) (z : Fin n) (ys : List (Fin n)) : Circuit :=
  let (C1, wOr) := addOrChain n C ys
  let wAnd := n + C1.gates.length
  let C2 : Circuit := { gates := C1.gates ++ [⟨GateOp.and, [z.val, wOr]⟩], output := C1.output }
  let wOut := n + C2.gates.length
  { gates := C2.gates ++ [⟨GateOp.or, [C2.output, wAnd]⟩], output := wOut }

lemma addStar_spec (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hOutLt : C.output < n + C.gates.length) (z : Fin n) (ys : List (Fin n)) (hys : ys ≠ []) :
    let C' := addStar n C z ys
    IsAO2 n C' ∧
    C'.gates.length = C.gates.length + ys.length + 1 ∧
    C'.output < n + C'.gates.length ∧
    (∀ x : Fin n → Bool, circuitFun n C' x = true ↔
      circuitFun n C x = true ∨ (x z = true ∧ ∃ y ∈ ys, x y = true)) := by
  obtain ⟨hAO1, hlen1, hout1, hwlt1, hpres1, hval1⟩ := addOrChain_spec n C hAO ys hys
  rcases hrec : addOrChain n C ys with ⟨C1, wOr⟩
  rw [hrec] at hAO1 hlen1 hout1 hwlt1 hpres1 hval1
  dsimp only at hAO1 hlen1 hout1 hwlt1 hpres1 hval1
  have hrbAnd : ∀ i ∈ [z.val, wOr], i < n + C1.gates.length := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · have := z.isLt; omega
    · exact hwlt1
  let C2 : Circuit := { gates := C1.gates ++ [⟨GateOp.and, [z.val, wOr]⟩], output := C1.output }
  have hAO2 := append_one_isAO2 n C1 hAO1 ⟨GateOp.and, [z.val, wOr]⟩ (Or.inl rfl) rfl hrbAnd C1.output
  have hrbOr : ∀ i ∈ [C2.output, n + C1.gates.length], i < n + C2.gates.length := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simp only [C2, hout1, List.length_append, List.length_singleton]; omega
    · simp only [C2, List.length_append, List.length_singleton]; omega
  have hAO3 := append_one_isAO2 n C2 hAO2 ⟨GateOp.or, [C2.output, n + C1.gates.length]⟩
    (Or.inr rfl) rfl hrbOr (n + C2.gates.length)
  have hys_pos : 1 ≤ ys.length := by
    cases ys with | nil => exact (hys rfl).elim | cons _ _ => simp
  simp only [addStar, hrec]
  refine ⟨hAO3, ?_, ?_, ?_⟩
  · simp only [C2, List.length_append, List.length_singleton, hlen1]; omega
  · simp only [C2, List.length_append, List.length_singleton]; omega
  · intro x
    rw [circuitFun_eq_wireVal]
    change wireVal n ({ gates := C2.gates ++ [⟨GateOp.or, [C2.output, n + C1.gates.length]⟩], output := n + C2.gates.length } : Circuit)
      (n + C2.gates.length) x = true ↔ _
    rw [append_one_val_last n C2 hAO2 ⟨GateOp.or, [C2.output, n + C1.gates.length]⟩
      (Or.inr rfl) rfl hrbOr (n + C2.gates.length) x]
    simp only [List.map_cons, List.map_nil, eval_or_two, Bool.or_eq_true]
    have hOutVal : wireVal n C2 C2.output x = circuitFun n C x := by
      change wireVal n ({ gates := C1.gates ++ [⟨GateOp.and, [z.val, wOr]⟩], output := C1.output } : Circuit)
        C1.output x = _
      rw [append_wireVal_lt n C1 _ C1.output (by rw [hout1]; omega) x, hout1,
        hpres1 C.output hOutLt x, circuitFun_eq_wireVal]
    have hAndVal : wireVal n C2 (n + C1.gates.length) x = true ↔
        x z = true ∧ ∃ y ∈ ys, x y = true := by
      change wireVal n ({ gates := C1.gates ++ [⟨GateOp.and, [z.val, wOr]⟩], output := C1.output } : Circuit)
        (n + C1.gates.length) x = true ↔ _
      rw [append_one_val_last n C1 hAO1 ⟨GateOp.and, [z.val, wOr]⟩ (Or.inl rfl) rfl hrbAnd C1.output x]
      simp only [List.map_cons, List.map_nil, eval_and_two, Bool.and_eq_true, wireVal_input, hval1]
    rw [hOutVal, hAndVal]

/-- Fold `addStar` over a list of `(center, leaves)` pairs. -/
def addStars (n : ℕ) (C : Circuit) : List (Fin n × List (Fin n)) → Circuit
  | [] => C
  | (z, ys) :: rest => addStars n (addStar n C z ys) rest

lemma addStars_spec (n : ℕ) (stars : List (Fin n × List (Fin n))) :
    ∀ C : Circuit, IsAO2 n C → C.output < n + C.gates.length →
      (∀ p ∈ stars, p.2 ≠ []) →
      let C' := addStars n C stars
      IsAO2 n C' ∧
      C'.gates.length = C.gates.length + (stars.map fun p => p.2.length + 1).sum ∧
      C'.output < n + C'.gates.length ∧
      (∀ x : Fin n → Bool, circuitFun n C' x = true ↔
        circuitFun n C x = true ∨ ∃ p ∈ stars, x p.1 = true ∧ ∃ y ∈ p.2, x y = true) := by
  induction stars with
  | nil =>
    intro C hAO hOut _
    exact ⟨hAO, by simp [addStars], hOut, fun x => by simp [addStars]⟩
  | cons hd tl ih =>
    intro C hAO hOut hne
    rcases hd with ⟨z, ys⟩
    have hys : ys ≠ [] := hne (z, ys) (by simp)
    obtain ⟨hAO1, hlen1, hOut1, hval1⟩ := addStar_spec n C hAO hOut z ys hys
    obtain ⟨hAO2, hlen2, hOut2, hval2⟩ :=
      ih (addStar n C z ys) hAO1 hOut1 (fun p hp => hne p (List.mem_cons_of_mem _ hp))
    simp only [addStars]
    refine ⟨hAO2, ?_, hOut2, ?_⟩
    · simp only [List.map_cons, List.sum_cons, hlen2, hlen1]; omega
    · intro x
      rw [hval2 x, hval1 x]
      constructor
      · rintro ((hc | hhd) | ⟨p, hp, hpx⟩)
        · exact Or.inl hc
        · exact Or.inr ⟨(z, ys), by simp, hhd⟩
        · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hpx⟩
      · rintro (hc | ⟨p, hp, hpx⟩)
        · exact Or.inl (Or.inl hc)
        · simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact Or.inl (Or.inr hpx)
          · exact Or.inr ⟨p, hp, hpx⟩

/-! ## Section 6: Main Theorem Assembly -/

theorem main
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (col : Fin n → Bool)
    (C C0 : Circuit) (T L : Finset ℕ) (c : ℕ) (s : Fin n)
    (hBip : ∀ u v : Fin n, G.Adj u v → col u ≠ col v)
    (hC4 : NoFourCycle G)
    (hAO : IsAO2 n C) (_hRB : ReadsBack n C)
    (hFun : circuitFun n C = graphFun G ∅)
    (hOrTree : IsOrTree n C T L C.output)
    (hL : ∀ w ∈ L, n ≤ w ∧ (gateAt C (w - n)).op = GateOp.and)
    (hc : c < C.gates.length) (hcOut : InOutputCone n C c)
    (hSing : singletonSet n C c = {s})
    (hReadOr : ∀ k < C.gates.length, n + c ∈ (gateAt C k).inputs → (gateAt C k).op = GateOp.or)
    (hAbove : ∀ k < C.gates.length, InCone n C c k → InOutputCone n C k →
      k ∈ T ∨ n + k ∈ L ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ w ∈ L, ∃ a ∈ (gateAt C (w - n)).inputs, OrReaches n C a k))
    (hPriv : ∀ j < C.gates.length, InCone n C j c → ∀ k < C.gates.length,
      n + j ∈ (gateAt C k).inputs → k = c ∨ InCone n C k c)
    (hC0 : C0 = mkC0 n C c s)
    (hLeafUnit : ∀ u v : Fin n, G.Adj u v → circuitFun n C0 (pairInput u v) = false →
      ∀ w ∈ L, gateVal n C (w - n) (pairInput u v) = true →
        ∀ a b : ℕ, ((gateAt C (w - n)).inputs = [a, b] ∨ (gateAt C (w - n)).inputs = [b, a]) →
          OrReaches n C a c →
            wireVal n C b (unitInput u) = true ∨ wireVal n C b (unitInput v) = true) :
    (Finset.univ.filter fun y : Fin n =>
      ∃ z : Fin n, G.Adj z y ∧ circuitFun n C0 (pairInput z y) = false).card ≤ (coneSet n C c).card ∧
    ∃ C' : Circuit, IsAO2 n C' ∧ ReadsBack n C' ∧
      circuitFun n C' = graphFun G ∅ ∧
      C'.size + (coneSet n C c).card ≤ C.size + (Finset.univ.filter fun y2 : Fin n =>
        ∃ z2 : Fin n, G.Adj z2 y2 ∧ circuitFun n C0 (pairInput z2 y2) = false).card := by
  subst hC0
  set C0 := mkC0 n C c s
  set K := coneSet n C c
  set Y : Finset (Fin n) := Finset.univ.filter fun y : Fin n =>
    ∃ z : Fin n, G.Adj z y ∧ circuitFun n C0 (pairInput z y) = false
  have hAO0 : IsAO2 n C0 := mkC0_isAO2 n C c s hAO
  -- Basic facts about s and c
  have hc_s : gateVal n C c (unitInput s) = true := by
    have : s ∈ singletonSet n C c := by rw [hSing]; simp
    simpa [singletonSet] using this
  have hc_unit_iff : ∀ p : Fin n, gateVal n C c (unitInput p) = true ↔ p = s := by
    intro p
    have : p ∈ singletonSet n C c ↔ p = s := by rw [hSing]; simp
    simpa [singletonSet] using this
  -- C0 <= C pointwise
  have hC0_le_C : ∀ x w, wireVal n C0 w x ≤ wireVal n C w x :=
    fun x w => wireVal_C0_le_C n C hAO c s hSing x w
  have hC0_fun_le : ∀ x, circuitFun n C0 x ≤ graphFun G ∅ x := by
    intro x
    rw [← hFun, circuitFun_eq_wireVal, circuitFun_eq_wireVal]
    exact hC0_le_C x C.output
  -- Lost edge helper: for any lost edge u v, c is true at 1_uv and u ≠ s, v ≠ s
  have hLost_c_ne : ∀ u v : Fin n, G.Adj u v → circuitFun n C0 (pairInput u v) = false →
      gateVal n C c (pairInput u v) = true ∧ u ≠ s ∧ v ≠ s := by
    intro u v huv h0
    have hC_true : circuitFun n C (pairInput u v) = true := by
      rw [hFun]; exact graphFun_empty_pairInput G u v huv
    have hne : pairInput u v s ≠ gateVal n C c (pairInput u v) := by
      intro heq
      have := wireVal_C0_eq_C_of_eq_at_c n C hAO c s (pairInput u v) heq C.output
      change circuitFun n C0 (pairInput u v) = circuitFun n C (pairInput u v) at this
      rw [h0, hC_true] at this
      exact Bool.noConfusion this
    have hle := wireVal_s_le_c n C hAO c s hSing (pairInput u v)
    cases hs : pairInput u v s <;> cases hc' : gateVal n C c (pairInput u v)
    · exact (hne (by rw [hs, hc'])).elim
    · simp only [pairInput, decide_eq_false_iff_not, not_or] at hs
      exact ⟨rfl, Ne.symm hs.1, Ne.symm hs.2⟩
    · simp [hs, hc'] at hle
      exact absurd hle (by decide)
    · exact (hne (by rw [hs, hc'])).elim
  -- Every lost edge has at least one endpoint adjacent to s!
  have hLost_adj_s : ∀ u v : Fin n, G.Adj u v → circuitFun n C0 (pairInput u v) = false →
      G.Adj s u ∨ G.Adj s v := by
    intro u v huv h0
    have hC_true : circuitFun n C (pairInput u v) = true := by
      rw [hFun]; exact graphFun_empty_pairInput G u v huv
    -- Take the minimal leaf w0 ∈ L with gateVal n C (w0 - n) (pairInput u v) = true
    let Ltrue := L.filter fun w => gateVal n C (w - n) (pairInput u v) = true
    have hLne : Ltrue.Nonempty := by
      obtain ⟨w, hwL, hwt⟩ := orTree_output_true_imp_leaf n C hAO T L hOrTree (pairInput u v) hC_true
      refine ⟨w, Finset.mem_filter.mpr ⟨hwL, ?_⟩⟩
      rw [gateVal_eq_wireVal, show n + (w - n) = w by have := (hL w hwL).1; omega]
      exact hwt
    let w0 := Ltrue.min' hLne
    have hw0_mem : w0 ∈ Ltrue := Finset.min'_mem Ltrue hLne
    have hw0L : w0 ∈ L := (Finset.mem_filter.mp hw0_mem).1
    have hw0t : gateVal n C (w0 - n) (pairInput u v) = true := (Finset.mem_filter.mp hw0_mem).2
    have hw0_min : ∀ w ∈ L, gateVal n C (w - n) (pairInput u v) = true → w0 ≤ w :=
      fun w hwL hwt => Finset.min'_le Ltrue w (Finset.mem_filter.mpr ⟨hwL, hwt⟩)
    have hw0n : n ≤ w0 := (hL w0 hw0L).1
    have hw0op : (gateAt C (w0 - n)).op = GateOp.and := (hL w0 hw0L).2
    have hw0lt : w0 - n < C.gates.length := by
      by_contra hge
      have := wireVal_ge_len n C w0 (pairInput u v) (by omega)
      rw [gateVal_eq_wireVal, show n + (w0 - n) = w0 by omega] at hw0t
      rw [this] at hw0t; exact Bool.noConfusion hw0t
    have hw0_out : InOutputCone n C (w0 - n) := by
      obtain ⟨hco, _⟩ := orTree_leaf_to_output n C hAO T L hOrTree w0 hw0L hw0n
      refine ⟨hw0lt, ?_⟩
      rcases hco with ho | ⟨hn, hc'⟩
      · left; omega
      · right; exact ⟨hn, hc'⟩
    -- w0 must evaluate to false in C0!
    have hw0_false0 : gateVal n C0 (w0 - n) (pairInput u v) = false := by
      cases hval0 : gateVal n C0 (w0 - n) (pairInput u v) with
      | false => rfl
      | true =>
        -- Wait: C0 also has the same OR tree T (since n+c ∉ L and c ∉ T)!
        -- Actually even easier: prove directly that any leaf w ∈ L true in C0 makes C0 true!
        exfalso
        -- Wait: every gate in T is an OR gate; can any gate in T read n+c?
        -- If gate j ∈ T read n+c, then since gateVal n C c (unitInput s) = true,
        -- gateVal n C j (unitInput s) = true, so circuitFun n C (unitInput s) = true, contradiction!
        have hT_no_c : ∀ j ∈ T, n + c ∉ (gateAt C j).inputs := by
          intro j hjT hcin
          have hjlt := orTree_mem_lt_len n C T L C.output hOrTree j hjT
          have hjt : gateVal n C j (unitInput s) = true := by
            rw [gateVal_eval n C j hjlt hAO.2.1, (hOrTree.1 j hjT).1]
            obtain ⟨a, b, hab⟩ := list_length_two (hOrTree.1 j hjT).2.1
            rw [hab] at hcin ⊢
            simp only [List.map_cons, List.map_nil, eval_or_two, Bool.or_eq_true]
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hcin
            rcases hcin with rfl | rfl
            · left; exact hc_s
            · right; exact hc_s
          have := (orTree_ascend n C hAO T L hOrTree (C.gates.length - j) j hjT (le_refl _)).2
            (unitInput s) hjt
          rw [hFun, graphFun_empty_unitInput] at this
          exact Bool.noConfusion this
        have hOT0 : IsOrTree n C0 T L C0.output := by
          have hgT : ∀ j ∈ T, gateAt C0 j = gateAt C j := by
            intro j hjT
            have hjlt := orTree_mem_lt_len n C T L C.output hOrTree j hjT
            rw [mkC0_gateAt n C c s j hjlt]
            have hmap : (gateAt C j).inputs.map (fun ww => if ww = n + c then (s : ℕ) else ww) =
                (gateAt C j).inputs := by
              conv_rhs => rw [← List.map_id (gateAt C j).inputs]
              apply List.map_congr_left
              intro ww hww
              simp only [id_eq]
              have hne : ww ≠ n + c := fun heq => hT_no_c j hjT (heq ▸ hww)
              simp [hne]
            rw [hmap]
          have hreads : ∀ w, readsIn C0 T w = readsIn C T w := by
            intro w; unfold readsIn
            exact Finset.sum_congr rfl fun j hj => by rw [hgT j hj]
          refine ⟨fun j hj => by rw [hgT j hj]; exact hOrTree.1 j hj,
            fun w hw => ⟨(hOrTree.2.1 w hw).1, by rw [hreads]; exact (hOrTree.2.1 w hw).2⟩,
            fun j hj => by rw [hreads]; exact hOrTree.2.2.1 j hj,
            hOrTree.2.2.2⟩
        have hC0t := (orTree_leaf_to_output n C0 hAO0 T L hOT0 w0 hw0L hw0n).2 (pairInput u v) (by
          rw [show w0 = n + (w0 - n) by omega, ← gateVal_eq_wireVal]; exact hval0)
        rw [h0] at hC0t; exact Bool.noConfusion hC0t
    -- Strong induction: any gate j < w0 - n in output cone with C true and C0 false has OrReaches (n+j) c!
    have hOrReach_below : ∀ j < w0 - n, InOutputCone n C j →
        gateVal n C j (pairInput u v) = true → gateVal n C0 j (pairInput u v) = false →
        OrReaches n C (n + j) c := by
      intro j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro hjlt hjOut hCt hC0f
        have hjlen : j < C.gates.length := by omega
        by_cases hjc : j = c
        · subst hjc; exact OrReaches_self n C j hjlen
        · have hinc : InCone n C c j := by
            by_contra hnc
            have := wireVal_C0_eq_C_of_not_inCone n C hAO c s (pairInput u v) j hjlen hnc
            rw [hCt, hC0f] at this; exact Bool.noConfusion this
          have hnotL : n + j ∉ L := by
            intro hmem
            have hle := hw0_min (n + j) hmem (by rwa [Nat.add_sub_cancel_left])
            omega
          have hnotT : j ∉ T := by
            intro hmem
            obtain ⟨w', hw'L, hw'lt, hw't⟩ :=
              orTree_gate_true_imp_leaf n C hAO T L C.output hOrTree (pairInput u v) j hmem hCt
            have hw'n := (hL w' hw'L).1
            have hle := hw0_min w' hw'L (by
              rw [gateVal_eq_wireVal, show n + (w' - n) = w' by omega]; exact hw't)
            omega
          have hcases := hAbove j hjlen hinc hjOut
          rcases hcases with hT | hLm | ⟨hop, _⟩
          · exact (hnotT hT).elim
          · exact (hnotL hLm).elim
          · -- j is an OR gate, true in C, false in C0 -> one input u' is true in C, false in C0!
            rw [gateVal_eval n C j hjlen hAO.2.1, hop] at hCt
            rw [gateVal_eval n C0 j (by rw [mkC0_len]; exact hjlen) hAO0.2.1,
              mkC0_gateAt n C c s j hjlen, hop] at hC0f
            obtain ⟨a, b, hab⟩ := list_length_two (hAO.2.2 _ (gateAt_mem C j hjlen))
            rw [hab] at hCt hC0f
            simp only [List.map_cons, List.map_nil, eval_or_two, Bool.or_eq_true,
              Bool.or_eq_false_iff] at hCt hC0f
            have step : ∀ p, p ∈ (gateAt C j).inputs → wireVal n C p (pairInput u v) = true →
                wireVal n C0 (if p = n + c then (s : ℕ) else p) (pairInput u v) = false →
                OrReaches n C (n + j) c := by
              intro p hpm hpt hp0f
              have hplt := hAO.2.1 j hjlen p hpm
              by_cases hpc : p = n + c
              · subst hpc
                exact OrReaches_step n C hjlen hop hpm hplt (OrReaches_self n C c hc)
              · rw [if_neg hpc] at hp0f
                by_cases hpn : p < n
                · rw [show p = (⟨p, hpn⟩ : Fin n).val from rfl, wireVal_input] at hpt hp0f
                  rw [hpt] at hp0f; exact Bool.noConfusion hp0f
                · have hrp : OrReaches n C (n + (p - n)) c := by
                    apply ih (p - n) (by omega) (by omega)
                    · exact InOutputCone_of_InCone n C
                        (InCone_of_mem_inputs n C hjlen hAO.2.1 (by rwa [show n + (p - n) = p by omega])) hjOut
                    · rw [gateVal_eq_wireVal, show n + (p - n) = p by omega]; exact hpt
                    · rw [gateVal_eq_wireVal, show n + (p - n) = p by omega]; exact hp0f
                  rw [show n + (p - n) = p by omega] at hrp
                  exact OrReaches_step n C hjlen hop hpm hplt hrp
            rcases hCt with ha | hb
            · exact step a (by rw [hab]; simp) ha hC0f.1
            · exact step b (by rw [hab]; simp) hb hC0f.2
    -- Apply to the AND gate w0 - n!
    obtain ⟨a, b, hab⟩ := list_length_two (hAO.2.2 _ (gateAt_mem C (w0 - n) hw0lt))
    have hCt := hw0t
    have hC0f := hw0_false0
    rw [gateVal_eval n C (w0 - n) hw0lt hAO.2.1, hw0op, hab] at hCt
    rw [gateVal_eval n C0 (w0 - n) (by rw [mkC0_len]; exact hw0lt) hAO0.2.1,
      mkC0_gateAt n C c s (w0 - n) hw0lt, hw0op, hab] at hC0f
    simp only [List.map_cons, List.map_nil, eval_and_two, Bool.and_eq_true,
      Bool.and_eq_false_iff] at hCt hC0f
    -- Neither a nor b can be n + c because hReadOr says direct readers of n+c are OR gates!
    have hne_c : ∀ p, p ∈ (gateAt C (w0 - n)).inputs → p ≠ n + c := by
      intro p hpm hpc
      have := hReadOr (w0 - n) hw0lt (hpc ▸ hpm)
      rw [hw0op] at this; exact GateOp.noConfusion this
    have use_side : ∀ x1 x2, ((gateAt C (w0 - n)).inputs = [x1, x2] ∨ (gateAt C (w0 - n)).inputs = [x2, x1]) →
        wireVal n C x1 (pairInput u v) = true →
        wireVal n C0 (if x1 = n + c then (s : ℕ) else x1) (pairInput u v) = false →
        G.Adj s u ∨ G.Adj s v := by
      intro x1 x2 hord hx1t hx1f
      have hx1m : x1 ∈ (gateAt C (w0 - n)).inputs := by
        rcases hord with h | h <;> rw [h] <;> simp
      have hx1ne := hne_c x1 hx1m
      rw [if_neg hx1ne] at hx1f
      have hx1lt := hAO.2.1 (w0 - n) hw0lt x1 hx1m
      have hx1ge : n ≤ x1 := by
        by_contra hlt
        rw [show x1 = (⟨x1, by omega⟩ : Fin n).val from rfl, wireVal_input] at hx1t hx1f
        rw [hx1t] at hx1f; exact Bool.noConfusion hx1f
      have hr1 : OrReaches n C x1 c := by
        have := hOrReach_below (x1 - n) (by omega)
          (InOutputCone_of_InCone n C
            (InCone_of_mem_inputs n C hw0lt hAO.2.1 (by rwa [show n + (x1 - n) = x1 by omega])) hw0_out)
          (by rw [gateVal_eq_wireVal, show n + (x1 - n) = x1 by omega]; exact hx1t)
          (by rw [gateVal_eq_wireVal, show n + (x1 - n) = x1 by omega]; exact hx1f)
        rwa [show n + (x1 - n) = x1 by omega] at this
      have hunit := hLeafUnit u v huv h0 w0 hw0L hw0t x1 x2 hord hr1
      have make_adj : ∀ t : Fin n, wireVal n C x2 (unitInput t) = true → G.Adj s t := by
        intro t hxt
        have hx1s : wireVal n C x1 (unitInput s) = true := OrReaches_val_mono n C hAO hr1 (unitInput s) hc_s
        have hx1st : wireVal n C x1 (pairInput s t) = true := by
          have hm := wireVal_mono n C hAO (x := unitInput s) (y := pairInput s t) (fun i => by
            by_cases hi : i = s <;> simp [unitInput, pairInput, hi]) x1
          rw [hx1s] at hm; exact eq_true_of_true_le hm
        have hx2st : wireVal n C x2 (pairInput s t) = true := by
          have hm := wireVal_mono n C hAO (x := unitInput t) (y := pairInput s t) (fun i => by
            by_cases hi : i = t <;> simp [unitInput, pairInput, hi]) x2
          rw [hxt] at hm; exact eq_true_of_true_le hm
        have hw0st : gateVal n C (w0 - n) (pairInput s t) = true := by
          rw [gateVal_eval n C (w0 - n) hw0lt hAO.2.1, hw0op]
          rcases hord with h | h <;> rw [h] <;> simp [eval_and_two, hx1st, hx2st]
        have hCst := (orTree_leaf_to_output n C hAO T L hOrTree w0 hw0L hw0n).2 (pairInput s t) (by
          rw [show w0 = n + (w0 - n) by omega, ← gateVal_eq_wireVal]; exact hw0st)
        rw [hFun, graphFun_empty_true_iff] at hCst
        obtain ⟨p, q, hpq, hp, hq⟩ := hCst
        simp only [pairInput, decide_eq_true_eq] at hp hq
        rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
        · exact (G.ne_of_adj hpq rfl).elim
        · exact hpq
        · exact hpq.symm
        · exact (G.ne_of_adj hpq rfl).elim
      rcases hunit with hu | hv
      · exact Or.inl (make_adj u hu)
      · exact Or.inr (make_adj v hv)
    rcases hC0f with haf | hbf
    · exact use_side a b (Or.inl hab) hCt.1 haf
    · exact use_side b a (Or.inr hab) hCt.2 hbf
  -- Part 1: Y.card ≤ K.card
  let Vc : Finset (Fin n) := Finset.univ.filter fun v : Fin n =>
    ∃ k ∈ K, v.val ∈ (gateAt C k).inputs
  have hs_Vc : s ∈ Vc := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ s, ?_⟩
    by_contra hns
    have hEq := cone_inputs_agree n C hAO c hc (unitInput s) (fun _ => false) (fun v hv => by
      have hvs : v ≠ s := fun heq => hns (heq ▸ hv)
      simp [unitInput, hvs]) c ((mem_coneSet_iff n C c hc c).mpr (Or.inl rfl))
    rw [hc_s, gateVal_eq_wireVal, wireVal_all_false n C hAO] at hEq
    exact Bool.noConfusion hEq
  have hY_Vc : Y ⊆ Vc := by
    intro y hy
    simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨z, hzy, h0⟩ := hy
    obtain ⟨hct, hzs, hys⟩ := hLost_c_ne z y hzy h0
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ y, ?_⟩
    by_contra hny
    have hEq := cone_inputs_agree n C hAO c hc (pairInput z y) (unitInput z) (fun v hv => by
      have hvy : v ≠ y := fun heq => hny (heq ▸ hv)
      simp [pairInput, unitInput, hvy]) c ((mem_coneSet_iff n C c hc c).mpr (Or.inl rfl))
    have hcz : gateVal n C c (unitInput z) = false := by
      cases h : gateVal n C c (unitInput z) with
      | false => rfl
      | true => exact (hzs ((hc_unit_iff z).mp h)).elim
    rw [hct, hcz] at hEq
    exact Bool.noConfusion hEq
  have hs_not_Y : s ∉ Y := by
    intro hsY
    simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at hsY
    obtain ⟨z, hzs, h0⟩ := hsY
    exact (hLost_c_ne z s hzs h0).2.2 rfl
  have hVc_le : Vc.card ≤ K.card + 1 := by
    -- Map every distinct wire in (Vc.image Fin.val) ∪ ((K.erase c).image (n + ·)) into the multiset of operand slots of K
    let W_in : Finset ℕ := Vc.image Fin.val
    let W_g : Finset ℕ := (K.erase c).image (fun j => n + j)
    have hdisj : Disjoint W_in W_g := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp only [W_in, W_g, Finset.mem_image] at h1 h2
      obtain ⟨v, _, rfl⟩ := h1
      obtain ⟨j, _, hj⟩ := h2
      have := v.isLt; omega
    have hWin_card : W_in.card = Vc.card :=
      Finset.card_image_of_injective Vc Fin.val_injective
    have hWg_card : W_g.card = K.card - 1 := by
      rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
      exact Finset.card_erase_of_mem ((mem_coneSet_iff n C c hc c).mpr (Or.inl rfl))
    -- Every wire w ∈ W_in ∪ W_g has readsIn C K w ≥ 1
    have hread_ge1 : ∀ w ∈ W_in ∪ W_g, 1 ≤ readsIn C K w := by
      intro w hw
      apply Nat.succ_le_of_lt
      rw [readsIn_pos_iff]
      rcases Finset.mem_union.mp hw with h1 | h2
      · simp only [W_in, Finset.mem_image] at h1
        obtain ⟨v, hv, rfl⟩ := h1
        exact (Finset.mem_filter.mp hv).2
      · simp only [W_g, Finset.mem_image, Finset.mem_erase] at h2
        obtain ⟨j, ⟨hjc, hjK⟩, rfl⟩ := h2
        have hjinc : InCone n C j c := ((mem_coneSet_iff n C c hc j).mp hjK).resolve_left hjc
        exact InCone_has_reader n C hc hjinc
    -- Sum of readsIn over W_in ∪ W_g ≤ sum over k ∈ K of (gateAt C k).inputs.length = 2 * K.card
    have hsum_le : ∑ w ∈ W_in ∪ W_g, readsIn C K w ≤ 2 * K.card := by
      unfold readsIn
      rw [Finset.sum_comm]
      calc ∑ k ∈ K, ∑ w ∈ W_in ∪ W_g, (gateAt C k).inputs.count w
          ≤ ∑ k ∈ K, (gateAt C k).inputs.length := by
            apply Finset.sum_le_sum
            intro k _
            -- Sum of List.count over any finset ≤ list length!
            have hcnt : ∀ (l : List ℕ) (S : Finset ℕ), ∑ w ∈ S, l.count w ≤ l.length := by
              intro l S
              induction l with
              | nil => simp
              | cons a t ih =>
                simp only [List.count_cons, List.length_cons]
                rw [Finset.sum_add_distrib]
                have h1 : ∑ w ∈ S, (if a == w then 1 else 0) ≤ 1 := by
                  by_cases ha : a ∈ S
                  · rw [Finset.sum_eq_single a]
                    · simp
                    · intro b _ hba; simp [beq_eq_false_iff_ne.mpr (Ne.symm hba)]
                    · intro h; exact (h ha).elim
                  · rw [Finset.sum_eq_zero]
                    · omega
                    · intro b hb
                      have hne : a ≠ b := fun heq => ha (heq ▸ hb)
                      simp [beq_eq_false_iff_ne.mpr hne]
                omega
            exact hcnt _ _
        _ = ∑ _k ∈ K, 2 := by
            apply Finset.sum_congr rfl
            intro k hk
            have hklt := Finset.mem_range.mp (coneSet_subset_range n C c hc hk)
            exact hAO.2.2 _ (gateAt_mem C k hklt)
        _ = 2 * K.card := by simp [Nat.mul_comm]
    have hcard_le : (W_in ∪ W_g).card ≤ ∑ w ∈ W_in ∪ W_g, readsIn C K w := by
      calc (W_in ∪ W_g).card = ∑ _w ∈ W_in ∪ W_g, 1 := by simp
        _ ≤ ∑ w ∈ W_in ∪ W_g, readsIn C K w := Finset.sum_le_sum hread_ge1
    rw [Finset.card_union_of_disjoint hdisj, hWin_card, hWg_card] at hcard_le
    have hcK : 1 ≤ K.card := Finset.card_pos.mpr ⟨c, (mem_coneSet_iff n C c hc c).mpr (Or.inl rfl)⟩
    omega
  have hPart1 : Y.card ≤ K.card := by
    have hsub : insert s Y ⊆ Vc := Finset.insert_subset hs_Vc hY_Vc
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hs_not_Y] at h1
    omega
  -- Part 2: Build C1 = deleteCone n C0 K, then add stars for lost edges!
  have hClosed : ∀ j < C0.gates.length, j ∉ K → ∀ w ∈ (gateAt C0 j).inputs, n ≤ w → w - n ∉ K := by
    intro j hj hjK w hw hwn hwnK
    rw [mkC0_len] at hj
    rw [mkC0_gateAt n C c s j hj] at hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    split_ifs at hwn hwnK with hwc
    · have := s.isLt; omega
    · rcases (mem_coneSet_iff n C c hc (w0 - n)).mp hwnK with heq | hinc
      · exact hwc (by omega)
      · have hres := hPriv (w0 - n) (InCone_lt_len n C hinc) hinc j hj
          (by rwa [show n + (w0 - n) = w0 by omega])
        exact hjK ((mem_coneSet_iff n C c hc j).mpr hres)
  have hOut_not_K : n ≤ C0.output → C0.output - n < C0.gates.length → C0.output - n ∉ K := by
    intro hn hlt hmem
    rcases (mem_coneSet_iff n C c hc (C0.output - n)).mp hmem with heq | hinc
    · have ho : C.output = n + c := by
        change n ≤ C.output at hn
        change C.output - n = c at heq
        omega
      have h1 : circuitFun n C (unitInput s) = true := by
        rw [circuitFun_eq_wireVal, ho, ← gateVal_eq_wireVal]; exact hc_s
      rw [hFun, graphFun_empty_unitInput] at h1
      exact Bool.noConfusion h1
    · have hlt1 := InCone_lt n C hinc
      rcases hcOut.2 with ho | ⟨_, hinc2⟩
      · change C.output - n < c at hlt1; omega
      · have hlt2 := InCone_lt n C hinc2
        change C.output - n < c at hlt1; omega
  let C1 := deleteCone n C0 K
  have hAO1 : IsAO2 n C1 := deleteCone_isAO2 n C0 K hAO0 hClosed
  have hFun1 : circuitFun n C1 = circuitFun n C0 :=
    deleteCone_circuitFun n C0 K hAO0 hClosed hOut_not_K
  have hSize1 : C1.size + K.card = C.size := by
    have h := deleteCone_size_add n C0 K (by
      rw [mkC0_len]; exact coneSet_subset_range n C c hc)
    change C1.gates.length + K.card = C.gates.length
    change (deleteCone n C0 K).gates.length + K.card = (mkC0 n C c s).gates.length at h
    rw [mkC0_len] at h
    exact h
  refine ⟨hPart1, ?_⟩
  by_cases hYe : Y = ∅
  · -- No lost edges! C1 already computes graphFun G ∅!
    refine ⟨C1, hAO1, hAO1.2.1, ?_, by omega⟩
    funext x
    rw [hFun1]
    cases hgx : graphFun G ∅ x with
    | false =>
      have hle := hC0_fun_le x
      rw [hgx] at hle
      cases hc0 : circuitFun n C0 x with
      | false => rfl
      | true => rw [hc0] at hle; exact absurd hle (by decide)
    | true =>
      obtain ⟨u, v, huv, hxu, hxv⟩ := (graphFun_empty_true_iff G x).mp hgx
      have h0true : circuitFun n C0 (pairInput u v) = true := by
        cases h0 : circuitFun n C0 (pairInput u v) with
        | true => rfl
        | false =>
          have hvY : v ∈ Y := by
            simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨u, huv, h0⟩
          rw [hYe] at hvY; simp at hvY
      have hm := wireVal_mono n C0 hAO0 (x := pairInput u v) (y := x) (fun i => by
        by_cases h1 : i = u
        · subst h1; simp [pairInput, hxu]
        · by_cases h2 : i = v
          · subst h2; simp [pairInput, hxv]
          · simp [pairInput, h1, h2]) C0.output
      change circuitFun n C0 (pairInput u v) ≤ circuitFun n C0 x at hm
      rw [h0true] at hm; exact eq_true_of_true_le hm
  · -- Y is nonempty -> C.output < n + C.gates.length -> C1.output < n + C1.gates.length
    have hYne : Y.Nonempty := Finset.nonempty_iff_ne_empty.mpr hYe
    have hOut_lt_C : C.output < n + C.gates.length := by
      by_contra hge
      obtain ⟨y0, hy0⟩ := hYne
      simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at hy0
      obtain ⟨z0, hz0, _⟩ := hy0
      have h1 : circuitFun n C (pairInput z0 y0) = true := by
        rw [hFun]; exact graphFun_empty_pairInput G z0 y0 hz0
      rw [circuitFun_eq_wireVal, wireVal_ge_len n C C.output _ (by omega)] at h1
      exact Bool.noConfusion h1
    have hOut_lt_C1 : C1.output < n + C1.gates.length := by
      change remapWire n K C0.output < n + (deleteCone n C0 K).gates.length
      rw [deleteCone_len]
      unfold remapWire
      split_ifs with hlt
      · omega
      · have hj : C0.output - n < C0.gates.length := by
          rw [mkC0_len]; change C.output - n < C.gates.length; omega
        have hjK := hOut_not_K (by omega) hj
        have := posInKept_mono hj hjK
        omega
    -- Partition Y into centers Z (col z ≠ col s) and leaves U (col y = col s)
    let Z : Finset (Fin n) := Y.filter fun z => col z ≠ col s
    let U : Finset (Fin n) := Y.filter fun y => col y = col s
    have hZU_disj : Disjoint Z U := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [Z, U, Finset.mem_filter] at h1 h2
      exact h1.2 h2.2
    have hZU_union : Z ∪ U = Y := by
      ext x; simp only [Z, U, Finset.mem_union, Finset.mem_filter]; tauto
    have hY_card : Y.card = Z.card + U.card := by
      rw [← hZU_union, Finset.card_union_of_disjoint hZU_disj]
    -- Define lost-edge leaves of each z ∈ Z: Uz z = {y ∈ U | G.Adj z y ∧ C0(1_zy) = false}
    let Uz : Fin n → Finset (Fin n) := fun z =>
      U.filter fun y => G.Adj z y ∧ circuitFun n C0 (pairInput z y) = false
    -- For every z ∈ Z, G.Adj s z!
    have hZ_adj_s : ∀ z ∈ Z, G.Adj s z := by
      intro z hz
      simp only [Z, Y, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨⟨w, hwz, h0⟩, hcol⟩ := hz
      rcases hLost_adj_s w z hwz h0 with hsw | hsz
      · have hc1 := hBip s w hsw
        have hc2 := hBip w z hwz
        cases cs : col s <;> cases cw : col w <;> cases cz : col z <;> simp_all
      · exact hsz
    -- Every y ∈ U has a UNIQUE z ∈ Z such that y ∈ Uz z!
    have hU_unique : ∀ y ∈ U, ∃! z, z ∈ Z ∧ y ∈ Uz z := by
      intro y hy
      simp only [U, Y, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨⟨z, hzy, h0⟩, hcoly⟩ := hy
      have hcolz : col z ≠ col s := by
        rw [← hcoly]; exact hBip z y hzy
      have hzY : z ∈ Y := by
        simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y, hzy.symm, by
          have : pairInput y z = pairInput z y := by funext i; simp [pairInput, or_comm]
          rw [this]; exact h0⟩
      have hzZ : z ∈ Z := Finset.mem_filter.mpr ⟨hzY, hcolz⟩
      have hyU : y ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨z, hzy, h0⟩⟩, hcoly⟩
      refine ⟨z, ⟨hzZ, Finset.mem_filter.mpr ⟨hyU, hzy, h0⟩⟩, ?_⟩
      rintro z' ⟨hz'Z, hyUz'⟩
      have hsz := hZ_adj_s z hzZ
      have hsz' := hZ_adj_s z' hz'Z
      have hz'y : G.Adj z' y := (Finset.mem_filter.mp hyUz').2.1
      have hsy_ne : s ≠ y := Ne.symm (hLost_c_ne z y hzy h0).2.2
      have hcard := hC4 s y hsy_ne
      by_contra hne
      have hsub : ({z, z'} : Finset (Fin n)) ⊆ Finset.univ.filter (fun w => G.Adj s w ∧ G.Adj y w) := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hw with rfl | rfl
        · exact ⟨hsz, hzy.symm⟩
        · exact ⟨hsz', hz'y.symm⟩
      have hc2 := Finset.card_le_card hsub
      rw [Finset.card_pair (Ne.symm hne)] at hc2
      omega
    -- Every z ∈ Z has Uz z nonempty!
    have hUz_ne : ∀ z ∈ Z, (Uz z).Nonempty := by
      intro z hz
      simp only [Z, Y, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨⟨y, hyz, h0⟩, hcolz⟩ := hz
      have hcoly : col y = col s := by
        have h1 := hBip y z hyz
        cases cs : col s <;> cases cy : col y <;> cases cz : col z <;> simp_all
      have h0' : circuitFun n C0 (pairInput z y) = false := by
        have : pairInput z y = pairInput y z := by funext i; simp [pairInput, or_comm]
        rw [this]; exact h0
      have hyY : y ∈ Y := by
        simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨z, hyz.symm, h0'⟩
      exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyY, hcoly⟩, hyz.symm, h0'⟩⟩
    -- Disjointness of Uz z for distinct z ∈ Z, and union = U!
    have hUz_sum : ∑ z ∈ Z, (Uz z).card = U.card := by
      have hbi : Z.biUnion Uz = U := by
        ext y
        simp only [Finset.mem_biUnion]
        constructor
        · rintro ⟨z, _, hy⟩; exact (Finset.mem_filter.mp hy).1
        · intro hy
          obtain ⟨z, ⟨hzZ, hyUz⟩, _⟩ := hU_unique y hy
          exact ⟨z, hzZ, hyUz⟩
      rw [← hbi, Finset.card_biUnion]
      intro z₁ hz₁ z₂ hz₂ hne
      change Disjoint (Uz z₁) (Uz z₂)
      rw [Finset.disjoint_left]
      intro y hy₁ hy₂
      have hyU : y ∈ U := (Finset.mem_filter.mp hy₁).1
      obtain ⟨z, _, huniq⟩ := hU_unique y hyU
      have h1 := huniq z₁ ⟨hz₁, hy₁⟩
      have h2 := huniq z₂ ⟨hz₂, hy₂⟩
      exact hne (h1.trans h2.symm)
    -- Build stars list from Z.toList!
    let stars : List (Fin n × List (Fin n)) := Z.toList.map fun z => (z, (Uz z).toList)
    have hstars_ne : ∀ p ∈ stars, p.2 ≠ [] := by
      intro p hp
      simp only [stars, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨z, hzZ, rfl⟩ := hp
      intro hemp
      dsimp only at hemp
      obtain ⟨y, hy⟩ := hUz_ne z hzZ
      have : y ∈ (Uz z).toList := Finset.mem_toList.mpr hy
      rw [hemp] at this; simp at this
    let C' := addStars n C1 stars
    obtain ⟨hAO', hlen', _, hval'⟩ := addStars_spec n stars C1 hAO1 hOut_lt_C1 hstars_ne
    have hstars_sum : (stars.map fun p => p.2.length + 1).sum = Y.card := by
      have h1 : stars.map (fun p => p.2.length + 1) = Z.toList.map (fun z => (Uz z).card + 1) := by
        simp only [stars, List.map_map]
        apply List.map_congr_left
        intro z _
        simp [Finset.length_toList]
      have hsum_map : (Z.toList.map fun z => (Uz z).card + 1).sum = ∑ z ∈ Z, ((Uz z).card + 1) := by
        rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
        rfl
      rw [h1, hsum_map, Finset.sum_add_distrib,
        hUz_sum, Finset.sum_const, smul_eq_mul, mul_one, hY_card, Nat.add_comm]
    refine ⟨C', hAO', hAO'.2.1, ?_, ?_⟩
    · funext x
      rw [Bool.eq_iff_iff, hval' x, hFun1, graphFun_empty_true_iff]
      constructor
      · rintro (h0t | ⟨p, hp, hxp1, y, hy, hxy⟩)
        · have hle := hC0_fun_le x
          rw [h0t] at hle
          exact (graphFun_empty_true_iff G x).mp (eq_true_of_true_le hle)
        · simp only [stars, List.mem_map, Finset.mem_toList] at hp
          obtain ⟨z, _, rfl⟩ := hp
          simp only [Finset.mem_toList] at hy
          have hzy : G.Adj z y := (Finset.mem_filter.mp hy).2.1
          exact ⟨z, y, hzy, hxp1, hxy⟩
      · rintro ⟨u, v, huv, hxu, hxv⟩
        by_cases h0 : circuitFun n C0 (pairInput u v) = true
        · left
          have hm := wireVal_mono n C0 hAO0 (x := pairInput u v) (y := x) (fun i => by
            by_cases h1 : i = u
            · subst h1; simp [pairInput, hxu]
            · by_cases h2 : i = v
              · subst h2; simp [pairInput, hxv]
              · simp [pairInput, h1, h2]) C0.output
          change circuitFun n C0 (pairInput u v) ≤ circuitFun n C0 x at hm
          rw [h0] at hm; exact eq_true_of_true_le hm
        · right
          have h0f : circuitFun n C0 (pairInput u v) = false := by
            cases h : circuitFun n C0 (pairInput u v) <;> simp_all
          have h0f_sym : circuitFun n C0 (pairInput v u) = false := by
            have : pairInput v u = pairInput u v := by funext i; simp [pairInput, or_comm]
            rw [this]; exact h0f
          have huY : u ∈ Y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨v, huv.symm, h0f_sym⟩⟩
          have hvY : v ∈ Y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨u, huv, h0f⟩⟩
          by_cases hcu : col u = col s
          · have hcv : col v ≠ col s := by rw [← hcu]; exact (hBip u v huv).symm
            have hvZ : v ∈ Z := Finset.mem_filter.mpr ⟨hvY, hcv⟩
            have huU : u ∈ U := Finset.mem_filter.mpr ⟨huY, hcu⟩
            have huUv : u ∈ Uz v := Finset.mem_filter.mpr ⟨huU, huv.symm, h0f_sym⟩
            refine ⟨(v, (Uz v).toList), ?_, hxv, u, Finset.mem_toList.mpr huUv, hxu⟩
            simp only [stars, List.mem_map, Finset.mem_toList]
            exact ⟨v, hvZ, rfl⟩
          · have hcv : col v = col s := by
              have h1 := hBip u v huv
              cases cs : col s <;> cases cu : col u <;> cases cv : col v <;> simp_all
            have huZ : u ∈ Z := Finset.mem_filter.mpr ⟨huY, hcu⟩
            have hvU : v ∈ U := Finset.mem_filter.mpr ⟨hvY, hcv⟩
            have hvUu : v ∈ Uz u := Finset.mem_filter.mpr ⟨hvU, huv, h0f⟩
            refine ⟨(u, (Uz u).toList), ?_, hxu, v, Finset.mem_toList.mpr hvUu, hxv⟩
            simp only [stars, List.mem_map, Finset.mem_toList]
            exact ⟨u, huZ, rfl⟩
    · change C'.gates.length + K.card ≤ C.gates.length + Y.card
      change C1.gates.length + K.card = C.gates.length at hSize1
      rw [hlen', hstars_sum]
      omega

end PEqualNP.Outside.L_meta_3017

theorem PEqualNP.Outside.L_meta_3017 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (col : Fin n → Bool) (C C0 : PEqualNP.CircuitLowerBounds.Circuit) (T L : Finset ℕ) (c : ℕ) (s : Fin n),
      (∀ u v : Fin n, G.Adj u v → col u ≠ col v) →
      PEqualNP.TopForm.NoFourCycle G →
      PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.MetaComplexity.NestedCover.IsOrTree n C T L C.output →
      (∀ w ∈ L, n ≤ w ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      c < C.gates.length → PEqualNP.Core.InOutputCone n C c →
      PEqualNP.SplitCount.singletonSet n C c = {s} →
      (∀ k < C.gates.length, n + c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      (∀ k < C.gates.length, PEqualNP.EdgeOwnership.InCone n C c k → PEqualNP.Core.InOutputCone n C k →
        k ∈ T ∨ n + k ∈ L ∨ ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∃ w ∈ L, ∃ a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs, PEqualNP.CleanedNonEdge.OrReaches n C a k)) →
      (∀ j < C.gates.length, PEqualNP.EdgeOwnership.InCone n C j c → ∀ k < C.gates.length,
        n + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k = c ∨ PEqualNP.EdgeOwnership.InCone n C k c) →
      C0 = ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun ww => if ww = n + c then (s : ℕ) else ww) } : PEqualNP.CircuitLowerBounds.Gate)), output := C.output } : PEqualNP.CircuitLowerBounds.Circuit) →
      (∀ u v : Fin n, G.Adj u v → PEqualNP.MetaComplexity.circuitFun n C0 (PEqualNP.EdgeOwnership.pairInput u v) = false →
        ∀ w ∈ L, PEqualNP.EdgeOwnership.gateVal n C (w - n) (PEqualNP.EdgeOwnership.pairInput u v) = true →
          ∀ a b : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs = [a, b] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs = [b, a]) →
            PEqualNP.CleanedNonEdge.OrReaches n C a c →
              PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.SplitCount.unitInput u) = true ∨ PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.SplitCount.unitInput v) = true) →
      (Finset.univ.filter fun y : Fin n => ∃ z : Fin n, G.Adj z y ∧ PEqualNP.MetaComplexity.circuitFun n C0 (PEqualNP.EdgeOwnership.pairInput z y) = false).card ≤ (PEqualNP.Core.coneSet n C c).card ∧
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C' ∧
        PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        C'.size + (PEqualNP.Core.coneSet n C c).card ≤ C.size + (Finset.univ.filter fun y2 : Fin n => ∃ z2 : Fin n, G.Adj z2 y2 ∧ PEqualNP.MetaComplexity.circuitFun n C0 (PEqualNP.EdgeOwnership.pairInput z2 y2) = false).card :=
  fun n G _ col C C0 T L c s =>
    PEqualNP.Outside.L_meta_3017.main n G col C C0 T L c s
