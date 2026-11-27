import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7007

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.SyntacticMultilinear PEqualNP.CrossAnd

def SLe {m : ℕ} (s t : List (Finset (Fin m))) : Prop :=
  s.length = t.length ∧ ∀ w, s.getD w ∅ ⊆ t.getD w ∅

lemma supportStep_length {m : ℕ} (s : List (Finset (Fin m))) (g : Gate) :
    (supportStep s g).length = s.length + 1 := by
  simp [supportStep]

lemma fold_len {m : ℕ} : ∀ (gs : List Gate) (s : List (Finset (Fin m))),
    (gs.foldl supportStep s).length = s.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro s; simp
  | cons g gs ih => intro s; simp [List.foldl_cons, ih, supportStep_length]; omega

lemma fold_getD {m : ℕ} : ∀ (gs : List Gate) (s : List (Finset (Fin m))) (k : ℕ), k < s.length →
    (gs.foldl supportStep s).getD k ∅ = s.getD k ∅ := by
  intro gs
  induction gs with
  | nil => intro s _ _; rfl
  | cons g gs ih =>
    intro s k hk
    rw [List.foldl_cons, ih _ k (by rw [supportStep_length]; omega), supportStep,
      List.getD_append _ _ _ _ hk]

lemma foldr_mono {m : ℕ} (l : List ℕ) (f g : ℕ → Finset (Fin m)) (h : ∀ w, f w ⊆ g w) :
    l.foldr (fun w acc => f w ∪ acc) ∅ ⊆ l.foldr (fun w acc => g w ∪ acc) ∅ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact Finset.union_subset_union (h a) ih

lemma step_mono {m : ℕ} (s t : List (Finset (Fin m))) (g : Gate) (h : SLe s t) :
    SLe (supportStep s g) (supportStep t g) := by
  obtain ⟨hl, hw⟩ := h
  refine ⟨by simp [supportStep, hl], ?_⟩
  intro w
  rcases lt_trichotomy w s.length with hlt | heq | hgt
  · rw [supportStep, supportStep, List.getD_append _ _ _ _ hlt,
      List.getD_append _ _ _ _ (by omega)]
    exact hw w
  · subst heq
    rw [supportStep, supportStep, List.getD_append_right _ _ _ _ (le_refl _), hl,
      List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero,
      List.getD_cons_zero]
    exact foldr_mono _ _ _ hw
  · rw [List.getD_eq_default _ _ (by rw [supportStep_length]; omega)]
    exact Finset.empty_subset _

lemma fold_mono {m : ℕ} : ∀ (gs : List Gate) (s t : List (Finset (Fin m))), SLe s t →
    SLe (gs.foldl supportStep s) (gs.foldl supportStep t) := by
  intro gs
  induction gs with
  | nil => intro s t h; exact h
  | cons g gs ih => intro s t h; exact ih _ _ (step_mono s t g h)

theorem main (n : ℕ) (M : Finset (Fin n)) (C : Circuit) (k : Fin C.size) (L : List ℕ)
    (hcross : IsCrossAnd n M C k)
    (hsub : support n { gates := C.gates.set k { op := GateOp.or, inputs := L }, output := C.output }
        (n + k) ⊆ support n C (n + k)) :
    crossCount n M { gates := C.gates.set k { op := GateOp.or, inputs := L }, output := C.output }
      < crossCount n M C := by
  set g' : Gate := { op := GateOp.or, inputs := L } with hg'
  set C' : Circuit := { gates := C.gates.set k g', output := C.output } with hC'
  have hk : (k : ℕ) < C.gates.length := k.isLt
  have hlen' : C'.gates.length = C.gates.length := by simp [hC']
  set s0 : List (Finset (Fin n)) := List.ofFn fun i : Fin n => ({i} : Finset (Fin n))
  set P : List (Finset (Fin n)) := (C.gates.take k).foldl supportStep s0 with hP
  have hP_len : P.length = n + k := by
    rw [hP, fold_len, List.length_ofFn, List.length_take]; omega
  have hsplit : supports n C =
      (C.gates.drop (k + 1)).foldl supportStep (supportStep P C.gates[(k : ℕ)]) := by
    unfold supports
    conv_lhs => rw [← List.take_append_drop k C.gates, List.drop_eq_getElem_cons hk,
      List.foldl_append, List.foldl_cons]
  have hk' : (k : ℕ) < C'.gates.length := by rw [hlen']; exact hk
  have htake : C'.gates.take k = C.gates.take k := by
    simp [hC', List.take_set_of_le (le_refl _)]
  have hdrop : C'.gates.drop (k + 1) = C.gates.drop (k + 1) := by
    simp [hC', List.drop_set_of_lt (Nat.lt_succ_self _)]
  have hget : C'.gates[(k : ℕ)] = g' := by simp [hC']
  have hsplit' : supports n C' =
      (C.gates.drop (k + 1)).foldl supportStep (supportStep P g') := by
    unfold supports
    conv_lhs => rw [← List.take_append_drop k C'.gates, List.drop_eq_getElem_cons hk',
      List.foldl_append, List.foldl_cons]
    rw [htake, hdrop, hget]
  -- the replaced position
  have hA : SLe (supportStep P g') (supportStep P C.gates[(k : ℕ)]) := by
    refine ⟨by simp [supportStep], ?_⟩
    intro w
    rcases lt_trichotomy w P.length with hlt | heq | hgt
    · rw [supportStep, supportStep, List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
    · have e1 : support n C' (n + k) = (supportStep P g').getD w ∅ := by
        unfold support
        rw [hsplit', fold_getD _ _ _ (by rw [supportStep_length]; omega), heq, hP_len]
      have e2 : support n C (n + k) = (supportStep P C.gates[(k : ℕ)]).getD w ∅ := by
        unfold support
        rw [hsplit, fold_getD _ _ _ (by rw [supportStep_length]; omega), heq, hP_len]
      rw [← e1, ← e2]
      exact hsub
    · rw [List.getD_eq_default _ _ (by rw [supportStep_length]; omega)]
      exact Finset.empty_subset _
  have hall : ∀ w, support n C' w ⊆ support n C w := by
    intro w
    have h := (fold_mono (C.gates.drop (k + 1)) _ _ hA).2 w
    unfold support
    rw [hsplit', hsplit]
    exact h
  have hop : ∀ j w, operandSupport n C' j w ⊆ operandSupport n C j w := by
    intro j w
    unfold operandSupport
    split_ifs
    · exact hall w
    · exact Finset.empty_subset _
  have hgate : ∀ j, j ≠ (k : ℕ) → gateAt C' j = gateAt C j := by
    intro j hj
    simp only [gateAt, hC', List.getD_eq_getElem?_getD, List.getElem?_set]
    split_ifs with h
    · exact absurd h.symm hj
    · rfl
  have hgatek : gateAt C' k = g' := by
    simp only [gateAt, hC', List.getD_eq_getElem?_getD, List.getElem?_set_self hk]
    rfl
  have himp : ∀ j, IsCrossAnd n M C' j → IsCrossAnd n M C j ∧ j ≠ (k : ℕ) := by
    intro j hj
    have hne : j ≠ (k : ℕ) := by
      intro he
      subst he
      have h1 := hj.1
      rw [hgatek] at h1
      exact absurd h1 (by simp [hg'])
    refine ⟨?_, hne⟩
    obtain ⟨h1, h2, h3⟩ := hj
    rw [hgate j hne] at h1 h2 h3
    refine ⟨h1, h2, ?_⟩
    rcases h3 with ⟨a, b⟩ | ⟨a, b⟩
    · left
      exact ⟨a.mono (Finset.inter_subset_inter (hop _ _) (le_refl _)),
        b.mono (Finset.inter_subset_inter (hop _ _) (le_refl _))⟩
    · right
      exact ⟨a.mono (Finset.sdiff_subset_sdiff (hop _ _) (le_refl _)),
        b.mono (Finset.sdiff_subset_sdiff (hop _ _) (le_refl _))⟩
  unfold crossCount
  rw [hlen']
  have hmem : (k : ℕ) ∈ (Finset.range C.gates.length).filter (fun j => IsCrossAnd n M C j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hcross⟩
  have hsubset : (Finset.range C.gates.length).filter (fun j => IsCrossAnd n M C' j) ⊆
      ((Finset.range C.gates.length).filter (fun j => IsCrossAnd n M C j)).erase k := by
    intro j hj
    obtain ⟨hr, hc⟩ := Finset.mem_filter.mp hj
    obtain ⟨hc', hne⟩ := himp j hc
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨hr, hc'⟩⟩
  exact lt_of_le_of_lt (Finset.card_le_card hsubset) (Finset.card_erase_lt_of_mem hmem)

end PEqualNP.Outside.L_meta_7007

theorem PEqualNP.Outside.L_meta_7007 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin x3.size) (x5 : List ℕ), PEqualNP.CrossAnd.IsCrossAnd x1 x2 x3 ↑x4 → PEqualNP.SyntacticMultilinear.support x1 { gates := x3.gates.set ↑x4 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x5 : PEqualNP.CircuitLowerBounds.Gate }, output := x3.output : PEqualNP.CircuitLowerBounds.Circuit } (x1 + ↑x4) ⊆ PEqualNP.SyntacticMultilinear.support x1 x3 (x1 + ↑x4) → PEqualNP.CrossAnd.crossCount x1 x2 { gates := x3.gates.set ↑x4 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x5 : PEqualNP.CircuitLowerBounds.Gate }, output := x3.output : PEqualNP.CircuitLowerBounds.Circuit } < PEqualNP.CrossAnd.crossCount x1 x2 x3 :=
  fun x1 x2 x3 x4 x5 h1 h2 => PEqualNP.Outside.L_meta_7007.main x1 x2 x3 x4 x5 h1 h2
