import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2676

open PEqualNP.CircuitLowerBounds

def stepR {β : Type} (F : Gate → List β → β) (d : β) (R : List β) (g : Gate) : List β :=
  R ++ [F g (g.inputs.map fun i => R.getD i d)]

lemma R_length {β : Type} (F : Gate → List β → β) (d : β) (gs : List Gate) (w : List β) :
    (gs.foldl (stepR F d) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepR]
    omega

lemma R_getD_lt {β : Type} (F : Gate → List β → β) (d : β) (gs : List Gate) (w : List β)
    (i : ℕ) (hi : i < w.length) :
    (gs.foldl (stepR F d) w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepR F d w g).length := by simp [stepR]; omega
    rw [ih (stepR F d w g) hlt]
    simp [stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma R_getD_ge {β : Type} (d : β) (w : List β) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma R_getD_gate {β : Type} (F : Gate → List β → β) (d : β) (gs : List Gate) (w : List β)
    (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (stepR F d) w).getD (w.length + j) d =
      F (gs[j]) ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl (stepR F d) w).getD i d else d) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepR F d w g).length := by simp [stepR]
      rw [Nat.add_zero, R_getD_lt F d gs (stepR F d w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepR F d w g).getD w.length d =
          F g (g.inputs.map fun i => w.getD i d) := by
        simp [stepR, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, R_getD_lt F d gs (stepR F d w g) i (by simp [stepR]; omega)]
        simp [stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact R_getD_ge d w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepR F d w g) j hj'
      have hl : (stepR F d w g).length = w.length + 1 := by simp [stepR]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def FR (S : List ℕ) (k : ℕ) (g : Gate) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl PEqualNP.ReadK.insertNew acc) []
  | GateOp.and => ins.foldl (PEqualNP.ReadK.andStep k) [S.map fun _ => 0]
  | _ => []

lemma rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    PEqualNP.ReadK.readVectors C n S k =
      C.gates.foldl (stepR (FR S k) []) ((List.range n).map (PEqualNP.ReadK.leafVectors S k)) :=
  rfl

def vecs (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (PEqualNP.ReadK.readVectors C n S k).getD w []

lemma vecs_input (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : w < n) :
    vecs C n S k w = PEqualNP.ReadK.leafVectors S k w := by
  unfold vecs
  rw [rv_eq, R_getD_lt _ _ _ _ _ (by simp; exact hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma vecs_ge (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : vecs C n S k w = [] := by
  unfold vecs
  rw [rv_eq]
  apply R_getD_ge
  rw [R_length]
  simp
  omega

lemma vecs_gate' (C : Circuit) (n : ℕ) (S : List ℕ) (k j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) :
    vecs C n S k (n + j) = FR S k g (g.inputs.map fun i =>
      if i < n + j then vecs C n S k i else []) := by
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hg
  unfold vecs
  rw [rv_eq]
  have := R_getD_gate (FR S k) [] C.gates
    ((List.range n).map (PEqualNP.ReadK.leafVectors S k)) j hj
  simp only [List.length_map, List.length_range] at this
  rw [this, hgj]

lemma mem_ins_foldl (L acc : List (List ℕ)) (v : List ℕ) :
    v ∈ L.foldl PEqualNP.ReadK.insertNew acc ↔ v ∈ acc ∨ v ∈ L := by
  induction L generalizing acc with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons, ih]
    unfold PEqualNP.ReadK.insertNew
    split_ifs with h
    · simp only [List.mem_cons]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | rfl | h1)
        · exact Or.inl h1
        · exact Or.inl h
        · exact Or.inr h1
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      tauto

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) :
    v ∈ PEqualNP.ReadK.andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, PEqualNP.ReadK.capAdd k u w = v := by
  unfold PEqualNP.ReadK.andStep
  rw [mem_ins_foldl]
  simp [List.mem_flatMap]

lemma mem_or_fold (ins : List (List (List ℕ))) (acc : List (List ℕ)) (v : List ℕ) :
    v ∈ ins.foldl (fun acc A => A.foldl PEqualNP.ReadK.insertNew acc) acc ↔
      v ∈ acc ∨ ∃ A ∈ ins, v ∈ A := by
  induction ins generalizing acc with
  | nil => simp
  | cons A ins ih =>
    rw [List.foldl_cons, ih, mem_ins_foldl]
    constructor
    · rintro ((h | h) | ⟨B, hB, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨A, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact Or.inr ⟨B, List.mem_cons.mpr (Or.inr hB), h⟩
    · rintro (h | ⟨B, hB, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hB with rfl | hB
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨B, hB, h⟩

def Good (k : ℕ) (v : List ℕ) : Prop := ∀ x ∈ v, x ≤ k

def Rel (S : List ℕ) (k : ℕ) (T : List (List ℕ)) (A A' : List (List ℕ)) : Prop :=
  ∀ v ∈ A, v.length = S.length ∧ (v ∈ A' ∨ ∃ v' ∈ T, Good k v → Good k v')

lemma good_cap {k : ℕ} {a b : List ℕ} (h : a.length = b.length)
    (hg : Good k (PEqualNP.ReadK.capAdd k a b)) : Good k a ∧ Good k b := by
  constructor
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < (PEqualNP.ReadK.capAdd k a b).length := by
      simp [PEqualNP.ReadK.capAdd, List.length_zipWith]; omega
    have := hg _ (List.getElem_mem hi')
    simp only [PEqualNP.ReadK.capAdd, List.getElem_zipWith] at this
    omega
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < (PEqualNP.ReadK.capAdd k a b).length := by
      simp [PEqualNP.ReadK.capAdd, List.length_zipWith]; omega
    have := hg _ (List.getElem_mem hi')
    simp only [PEqualNP.ReadK.capAdd, List.getElem_zipWith] at this
    omega

lemma and_rel (S : List ℕ) (k : ℕ) (T A A' B B' : List (List ℕ))
    (hA : Rel S k T A A') (hB : Rel S k T B B') :
    Rel S k T (PEqualNP.ReadK.andStep k A B) (PEqualNP.ReadK.andStep k A' B') := by
  unfold Rel
  intro v hv
  rw [mem_andStep] at hv
  obtain ⟨a, ha, b, hb, rfl⟩ := hv
  obtain ⟨la, ra⟩ := hA a ha
  obtain ⟨lb, rb⟩ := hB b hb
  refine ⟨by simp [PEqualNP.ReadK.capAdd, List.length_zipWith, la, lb], ?_⟩
  rcases ra with ra | ⟨v', hv', hd⟩
  · rcases rb with rb | ⟨v', hv', hd⟩
    · left
      rw [mem_andStep]
      exact ⟨a, ra, b, rb, rfl⟩
    · exact Or.inr ⟨v', hv', fun hg => hd (good_cap (la.trans lb.symm) hg).2⟩
  · exact Or.inr ⟨v', hv', fun hg => hd (good_cap (la.trans lb.symm) hg).1⟩

lemma zero_rel (S : List ℕ) (k : ℕ) (T : List (List ℕ)) :
    Rel S k T [S.map fun _ => 0] [S.map fun _ => 0] := by
  unfold Rel
  intro v hv
  simp only [List.mem_singleton] at hv
  subst hv
  exact ⟨by simp, Or.inl (by simp)⟩

lemma and_fold (S : List ℕ) (k : ℕ) (T : List (List ℕ)) (f f' : ℕ → List (List ℕ)) :
    ∀ (L : List ℕ) (acc acc' : List (List ℕ)), Rel S k T acc acc' →
      (∀ i ∈ L, Rel S k T (f i) (f' i)) →
      Rel S k T ((L.map f).foldl (PEqualNP.ReadK.andStep k) acc)
        ((L.map f').foldl (PEqualNP.ReadK.andStep k) acc')
  | [], acc, acc', h0, _ => by
      simp only [List.map_nil, List.foldl_nil]
      exact h0
  | i :: L, acc, acc', h0, h => by
      simp only [List.map_cons, List.foldl_cons]
      exact and_fold S k T f f' L _ _
        (and_rel S k T _ _ _ _ h0 (h i (by simp)))
        (fun i' hi' => h i' (by simp [hi']))

lemma FR_rel (S : List ℕ) (k : ℕ) (T : List (List ℕ)) (g : Gate) (f f' : ℕ → List (List ℕ))
    (h : ∀ i ∈ g.inputs, Rel S k T (f i) (f' i)) :
    Rel S k T (FR S k g (g.inputs.map f)) (FR S k g (g.inputs.map f')) := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and =>
    simp only [FR]
    exact and_fold S k T f f' ins _ _ (zero_rel S k T) h
  | or =>
    simp only [FR]
    unfold Rel
    intro v hv
    rw [mem_or_fold] at hv
    rcases hv with hv | ⟨A, hA, hv⟩
    · simp at hv
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
      obtain ⟨hl, hr⟩ := h i hi v hv
      refine ⟨hl, ?_⟩
      rcases hr with hr | hr
      · left
        rw [mem_or_fold]
        exact Or.inr ⟨f' i, List.mem_map.mpr ⟨i, hi, rfl⟩, hr⟩
      · exact Or.inr hr
  | not =>
    simp only [FR]
    unfold Rel
    intro v hv
    simp at hv
  | mod m =>
    simp only [FR]
    unfold Rel
    intro v hv
    simp at hv
  | maj =>
    simp only [FR]
    unfold Rel
    intro v hv
    simp at hv

def lift (C : Circuit) (n j u t : ℕ) : Circuit :=
  { gates := C.gates.set j ⟨GateOp.or, [u]⟩ ++ [⟨GateOp.or, [C.output, t]⟩],
    output := n + C.gates.length }

lemma lift_lt (C : Circuit) (n j u t i : ℕ) (hi : i < C.gates.length) (hij : i ≠ j) :
    (lift C n j u t).gates[i]? = C.gates[i]? := by
  unfold lift
  dsimp only
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [List.getElem?_set, hij, Ne.symm hij]

lemma lift_j (C : Circuit) (n j u t : ℕ) (hj : j < C.gates.length) :
    (lift C n j u t).gates[j]? = some ⟨GateOp.or, [u]⟩ := by
  unfold lift
  dsimp only
  rw [List.getElem?_append_left (by simpa using hj)]
  simp [hj]

lemma lift_top (C : Circuit) (n j u t : ℕ) :
    (lift C n j u t).gates[C.gates.length]? = some ⟨GateOp.or, [C.output, t]⟩ := by
  unfold lift
  dsimp only
  rw [List.getElem?_append_right (by simp)]
  simp

lemma agree (C : Circuit) (n j u t : ℕ) (S : List ℕ) (k : ℕ) (hj : j < C.gates.length) :
    ∀ w, w < n + j → vecs (lift C n j u t) n S k w = vecs C n S k w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [vecs_input _ n S k w hn, vecs_input C n S k w hn]
    · obtain ⟨i, rfl⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
      have hi : i < C.gates.length := by omega
      have hgi : C.gates[i]? = some (C.gates[i]) := List.getElem?_eq_getElem hi
      rw [vecs_gate' C n S k i _ hgi,
        vecs_gate' _ n S k i _ ((lift_lt C n j u t i hi (by omega)).trans hgi)]
      congr 1
      apply List.map_congr_left
      intro i' _
      by_cases h : i' < n + i
      · rw [if_pos h, if_pos h, ih i' h (by omega)]
      · rw [if_neg h, if_neg h]

lemma inv_all (C : Circuit) (n j u t : ℕ) (S : List ℕ) (k : ℕ) (hj : j < C.gates.length)
    (hg : C.gates[j]? = some ⟨GateOp.or, [u, t]⟩) (ht : t < n + j) :
    ∀ w, Rel S k (vecs C n S k t) (vecs C n S k w) (vecs (lift C n j u t) n S k w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w < n
    · rw [vecs_input C n S k w hw, vecs_input _ n S k w hw]
      unfold Rel
      intro v hv
      refine ⟨?_, Or.inl hv⟩
      unfold PEqualNP.ReadK.leafVectors at hv
      split_ifs at hv
      · simp only [List.mem_singleton] at hv
        subst hv
        simp
      · simp at hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [vecs_ge C n S k w hlen]
        unfold Rel
        intro v hv
        simp at hv
      · obtain ⟨i, rfl⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
        have hi : i < C.gates.length := by omega
        by_cases hij : i = j
        · subst hij
          rw [vecs_gate' C n S k i _ hg, vecs_gate' _ n S k i _ (lift_j C n i u t hi)]
          unfold Rel
          intro v hv
          simp only [FR, List.map_cons, List.map_nil] at hv ⊢
          rw [mem_or_fold] at hv
          rcases hv with hv | ⟨A, hA, hv⟩
          · simp at hv
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
            rcases hA with rfl | rfl
            · by_cases hu : u < n + i
              · rw [if_pos hu] at hv
                obtain ⟨hl, hr⟩ := ih u hu v hv
                refine ⟨hl, ?_⟩
                rcases hr with hr | hr
                · left
                  rw [mem_or_fold]
                  refine Or.inr ⟨_, List.mem_singleton_self _, ?_⟩
                  rw [if_pos hu]
                  exact hr
                · exact Or.inr hr
              · rw [if_neg hu] at hv
                simp at hv
            · rw [if_pos ht] at hv
              exact ⟨(ih t ht v hv).1, Or.inr ⟨v, hv, id⟩⟩
        · have hgi : C.gates[i]? = some (C.gates[i]) := List.getElem?_eq_getElem hi
          rw [vecs_gate' C n S k i _ hgi,
            vecs_gate' _ n S k i _ ((lift_lt C n j u t i hi hij).trans hgi)]
          apply FR_rel
          intro i' _
          by_cases h : i' < n + i
          · rw [if_pos h, if_pos h]
            exact ih i' h
          · rw [if_neg h, if_neg h]
            unfold Rel
            intro v hv
            simp at hv

end PEqualNP.Outside.L_meta_2676

theorem PEqualNP.Outside.L_meta_2676 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ), PEqualNP.MetaComplexity.Monotone2 C → j < C.gates.length → C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } → t < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → ∀ (S : List ℕ) (k : ℕ), PEqualNP.ReadK.readsAtMost C n S k = true → PEqualNP.ReadK.readsAtMost { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }], output := n + C.gates.length } n S k = true := by
  open PEqualNP.Outside.L_meta_2676 in
  intro n C j u t _ hj hg ht _ S k hr
  have hr' : ∃ v ∈ vecs C n S k C.output, Good k v := by
    unfold PEqualNP.ReadK.readsAtMost at hr
    simp only [List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at hr
    exact hr
  obtain ⟨v, hv, hgood⟩ := hr'
  have hout : C.output < n + C.gates.length := by
    by_contra hc
    rw [vecs_ge C n S k _ (by omega)] at hv
    simp at hv
  obtain ⟨_, hrel⟩ := inv_all C n j u t S k hj hg ht C.output v hv
  show PEqualNP.ReadK.readsAtMost (lift C n j u t) n S k = true
  unfold PEqualNP.ReadK.readsAtMost
  simp only [List.any_eq_true, List.all_eq_true, decide_eq_true_eq]
  change ∃ x ∈ vecs (lift C n j u t) n S k (n + C.gates.length), ∀ a ∈ x, a ≤ k
  rw [vecs_gate' _ n S k _ _ (lift_top C n j u t)]
  simp only [FR, List.map_cons, List.map_nil]
  rcases hrel with hrel | ⟨v', hv', hd⟩
  · refine ⟨v, ?_, hgood⟩
    rw [mem_or_fold]
    refine Or.inr ⟨_, List.mem_cons_self .., ?_⟩
    rw [if_pos hout]
    exact hrel
  · refine ⟨v', ?_, hd hgood⟩
    rw [mem_or_fold]
    refine Or.inr ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
    rw [if_pos (by omega), agree C n j u t S k hj t ht]
    exact hv'
