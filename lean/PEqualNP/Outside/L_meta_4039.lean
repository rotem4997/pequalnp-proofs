import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4039_aux

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (h : Gate) (x : List Bool) :
    W (gs ++ [h]) x = W gs x ++ [h.op.eval (h.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs h ih => rw [W_snoc]; simp [ih]; omega

theorem W_low (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs h ih =>
    rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_len]; omega), ih]

theorem W_high (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (W gs x).getD i false = false := by
  apply List.getD_eq_default
  rw [W_len]; exact hi

theorem W_key (gs : List Gate) (x : List Bool) (j : ℕ) (g : Gate) (hg : gs[j]? = some g) :
    (W gs x).getD (x.length + j) false
      = g.op.eval (g.inputs.map fun i => if i < x.length + j then (W gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hg
  | append_singleton gs h ih =>
    rw [W_snoc]
    by_cases hj : j < gs.length
    · rw [List.getElem?_append_left hj] at hg
      rw [List.getD_append _ _ _ _ (by rw [W_len]; omega), ih hg]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < x.length + j
      · simp only [hi, if_true]
        rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
      · simp [hi]
    · have hlen := (List.getElem?_eq_some_iff.mp hg).1
      simp at hlen
      have hj2 : j = gs.length := by omega
      subst hj2
      simp at hg
      subst hg
      have e : x.length + gs.length = (W gs x).length := by rw [W_len]
      rw [e, List.getD_append_right _ _ _ _ (le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < (W gs x).length
      · simp only [hi, if_true]
        rw [List.getD_append _ _ _ _ hi]
      · simp only [hi, if_false]
        exact List.getD_eq_default _ _ (by omega)

def inp {n : ℕ} (S : Finset (Fin n)) : List Bool := List.ofFn fun (i : Fin n) => decide (i ∈ S)

def P {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (i : ℕ) : Prop :=
  (W gs (inp S)).getD i false = true

theorem P_low {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (i : ℕ) (hi : i < n) :
    P gs S i ↔ (⟨i, hi⟩ : Fin n) ∈ S := by
  unfold P
  rw [W_low _ _ _ (by simp [inp]; exact hi)]
  simp [inp, List.getD_eq_getElem?_getD, hi]

theorem P_and {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (j : ℕ) (g : Gate)
    (hg : gs[j]? = some g) (ho : g.op = GateOp.and) :
    P gs S (n + j) ↔ ∀ i ∈ g.inputs, i < n + j ∧ P gs S i := by
  unfold P
  have h := W_key gs (inp S) j g hg
  have e : (inp S).length = n := by simp [inp]
  rw [e] at h
  rw [h, ho]
  simp [GateOp.eval, List.all_eq_true]

theorem P_or {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (j : ℕ) (g : Gate)
    (hg : gs[j]? = some g) (ho : g.op = GateOp.or) :
    P gs S (n + j) ↔ ∃ i ∈ g.inputs, i < n + j ∧ P gs S i := by
  unfold P
  have h := W_key gs (inp S) j g hg
  have e : (inp S).length = n := by simp [inp]
  rw [e] at h
  rw [h, ho]
  simp [GateOp.eval, List.any_eq_true]

theorem P_none {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (j : ℕ)
    (hg : gs[j]? = none) : ¬ P gs S (n + j) := by
  unfold P
  rw [W_high _ _ _ (by simp [inp]; exact List.getElem?_eq_none_iff.mp hg)]
  simp

theorem P_mono {n : ℕ} (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (S T : Finset (Fin n)) (hST : S ⊆ T) : ∀ i, P gs S i → P gs T i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    by_cases hi : i < n
    · rw [P_low _ _ _ hi] at h ⊢
      exact hST h
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      cases hg : gs[j]? with
      | none => exact absurd h (P_none gs S j hg)
      | some g =>
        rcases hm g (List.mem_of_getElem? hg) with ho | ho
        · rw [P_and _ _ _ _ hg ho] at h ⊢
          intro k hk
          exact ⟨(h k hk).1, ih k (h k hk).1 (h k hk).2⟩
        · rw [P_or _ _ _ _ hg ho] at h ⊢
          obtain ⟨k, hk, hlt, hp⟩ := h
          exact ⟨k, hk, hlt, ih k hlt hp⟩

theorem P_trace {n : ℕ} (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (S : Finset (Fin n)) : ∀ i, P gs S i →
      (∃ T ⊆ S, T.card ≤ 1 ∧ P gs T i) ∨
      (∃ j g, gs[j]? = some g ∧ g.op = GateOp.and ∧ n + j ≤ i ∧ P gs S (n + j)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    by_cases hi : i < n
    · left
      refine ⟨{⟨i, hi⟩}, ?_, by simp, ?_⟩
      · rw [P_low _ _ _ hi] at h
        simpa using h
      · rw [P_low _ _ _ hi]; simp
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      cases hg : gs[j]? with
      | none => exact absurd h (P_none gs S j hg)
      | some g =>
        rcases hm g (List.mem_of_getElem? hg) with ho | ho
        · right
          exact ⟨j, g, hg, ho, le_refl _, h⟩
        · rw [P_or _ _ _ _ hg ho] at h
          obtain ⟨k, hk, hlt, hp⟩ := h
          rcases ih k hlt hp with ⟨T, hTS, hc, hT⟩ | ⟨j2, g2, h1, h2, h3, h4⟩
          · left
            refine ⟨T, hTS, hc, ?_⟩
            rw [P_or _ _ _ _ hg ho]
            exact ⟨k, hk, hlt, hT⟩
          · right
            exact ⟨j2, g2, h1, h2, by omega, h4⟩

theorem P_union {n : ℕ} (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (S : Finset (Fin n)) : ∀ l : List ℕ, (∀ i ∈ l, ∃ T ⊆ S, T.card ≤ 1 ∧ P gs T i) →
      ∃ U ⊆ S, U.card ≤ l.length ∧ ∀ i ∈ l, P gs U i := by
  classical
  intro l
  induction l with
  | nil => intro _; exact ⟨∅, by simp, by simp, by simp⟩
  | cons a l ih =>
    intro h
    obtain ⟨T, hTS, hc, hT⟩ := h a (by simp)
    obtain ⟨U, hUS, hUc, hU⟩ := ih (fun i hi => h i (by simp [hi]))
    refine ⟨T ∪ U, Finset.union_subset hTS hUS, ?_, ?_⟩
    · have := Finset.card_union_le T U
      simp only [List.length_cons]
      omega
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact P_mono gs hm T _ Finset.subset_union_left _ hT
      · exact P_mono gs hm U _ Finset.subset_union_right _ (hU i hi)

end PEqualNP.Outside.L_meta_4039_aux

open PEqualNP.Outside.L_meta_4039_aux in
theorem PEqualNP.Outside.L_meta_4039 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     have x4 : Finset (Fin x1) → Prop := fun (x4 : Finset (Fin x1)) => ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x2.wires (List.ofFn fun (x7 : Fin x1) => Decidable.decide (x7 ∈ x4))).getD (x1 + x5) Bool.false = Bool.true;     ∀ (x5 : Finset (Fin x1)), x4 x5 → ∃ x7 ⊆ x5, x7.card ≤ (2 : ℕ) ∧ x4 x7 := by
  classical
  intro n C hM
  have hm : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have := (hM g hg).1
    simpa using this
  intro x4 S hS
  have hS2 : ∃ j, ∃ g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      P C.gates S (n + j) := hS
  have hmin := @Nat.find_min _ _ hS2
  obtain ⟨g, hg, ho, hp⟩ := Nat.find_spec hS2
  generalize Nat.find hS2 = j0 at hmin hg hp
  have hin := (P_and _ _ _ _ hg ho).mp hp
  have hall : ∀ i ∈ g.inputs, ∃ T ⊆ S, T.card ≤ 1 ∧ P C.gates T i := by
    intro i hi
    rcases P_trace C.gates hm S i (hin i hi).2 with h | ⟨j, g2, h1, h2, h3, h4⟩
    · exact h
    · exfalso
      have hlt : j < j0 := by have := (hin i hi).1; omega
      exact hmin hlt ⟨g2, h1, h2, h4⟩
  obtain ⟨U, hUS, hUc, hU⟩ := P_union C.gates hm S g.inputs hall
  have hlen := (hM g (List.mem_of_getElem? hg)).2
  refine ⟨U, hUS, by omega, ?_⟩
  show ∃ j, ∃ g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      P C.gates U (n + j)
  refine ⟨j0, g, hg, ho, ?_⟩
  rw [P_and _ _ _ _ hg ho]
  intro i hi
  exact ⟨(hin i hi).1, hU i hi⟩
