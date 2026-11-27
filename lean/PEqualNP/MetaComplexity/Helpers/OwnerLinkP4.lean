import Mathlib
import PEqualNP.MetaComplexity.Helpers.OwnerLinkP3

/-!
# The owner link, step P4: the flag of a call, and `PlacedEdges` (conjecture until checked)

The flag of a call says whether its lower end is the number of a vertex of `cvcCover φ`
(`call_flag`). With P2 and P3 this gives `placedEdges : PlacedEdges`.
-/

namespace PEqualNP.MetaComplexity.Helpers.OwnerLink

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

theorem cover_inl (φ : CNF) (x : Literal) :
    Sum.inl x ∈ cvcCover φ ↔ x.1 ∈ vars (cvcFormula φ) ∧ x.2 = true := by
  simp only [cvcCover, coverOf, Finset.inl_mem_disjSum, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨hz, rfl⟩
  · rintro ⟨hz, h⟩; exact ⟨x.1, hz, by rw [← h]⟩

theorem cover_inr (φ : CNF) (i j : ℕ) :
    Sum.inr (i, j) ∈ cvcCover φ ↔ i < (cvcFormula φ).length ∧
      j < (clauseAt (cvcFormula φ) i).length ∧
      j ≠ (clauseAt (cvcFormula φ) i).findIdx (Literal.eval (fun _ => true)) := by
  simp only [cvcCover, coverOf, Finset.inr_mem_disjSum, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_image, Finset.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', j', ⟨hj', hne⟩, rfl, rfl⟩; exact ⟨hi', hj', hne⟩
  · rintro ⟨hi, hj, hne⟩; exact ⟨i, hi, j, ⟨hj, hne⟩, rfl, rfl⟩

theorem findIdx_eval_append (c : Clause) (y : ℕ) :
    (c ++ [(y, true)]).findIdx (Literal.eval (fun _ => true)) = c.findIdx (fun l : Literal => l.2) := by
  induction c with
  | nil => simp [Literal.eval]
  | cons a c ih =>
    rw [List.cons_append, List.findIdx_cons, List.findIdx_cons, ih]
    cases h : a.2 <;> simp [Literal.eval, h]

theorem cvc_length (φ : CNF) : (cvcFormula φ).length = φ.length + 1 := by simp [cvcFormula]

section
variable {φ : CNF} {E : ℕ} {num : Vertex → ℕ} (hI : itemsF φ ≤ E)
  (h1 : ∀ z ∈ vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * eF φ z + (if b then 1 else 0))
  (h2 : ∀ b : Bool, num (Sum.inl (fresh φ, b)) = 2 * E + (if b then 1 else 0))
  (h3 : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
    num (Sum.inr (i, j)) = 2 * (E + 1) + offF φ i + j)
  (h4 : num (Sum.inr (φ.length, 0)) = 3 * E + 2)
include hI h1 h2 h3 h4

/-- No cover vertex has an even number `2x` with `x ≤ E`. -/
theorem cover_not_even (u : Vertex) (hu : u ∈ cvcCover φ) (x : ℕ) (hx : x ≤ E) : num u ≠ 2 * x := by
  rcases u with ⟨z, b⟩ | ⟨i, j⟩
  · rw [cover_inl, vars_cvc] at hu
    obtain ⟨hz | rfl, hb⟩ := hu <;> simp only at hb <;> subst hb
    · rw [h1 z hz]; simp; omega
    · rw [h2]; simp; omega
  · rw [cover_inr, cvc_length] at hu
    obtain ⟨hi, hj, -⟩ := hu
    rcases Nat.lt_or_ge i φ.length with hi' | hi'
    · rw [cvc_length_lt φ i hi'] at hj
      rw [h3 i j hi' (by unfold wF at hj; omega)]; omega
    · have : i = φ.length := by omega
      subst this
      rw [clauseAt_cvc_eq] at hj
      simp at hj; subst hj
      rw [h4]; omega

/-- The flag of a call: whether its lower end numbers a cover vertex. -/
theorem call_flag (c : ℕ × ℕ × Bool) (hc : c ∈ callsF E (REN φ)) :
    (∃ u ∈ cvcCover φ, num u = c.1) ↔ c.2.2 = true := by
  have even_no : ∀ x, x ≤ E → c.1 = 2 * x → c.2.2 = false →
      ((∃ u ∈ cvcCover φ, num u = c.1) ↔ c.2.2 = true) := by
    intro x hx h1' h2'
    rw [h2']
    simp only [Bool.false_eq_true, iff_false, not_exists, not_and]
    intro u hu h
    exact cover_not_even hI h1 h2 h3 h4 u hu x hx (h.trans h1')
  rw [callsF_eq] at hc
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with ⟨i, hi, j, hj, hc⟩ | rfl | rfl
  · rw [ren_length] at hi
    rw [ren_wF] at hj
    have hoff := off_add_le φ i hi
    simp only [blkF, ren_wF, ren_posF, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_range, decide_eq_true_eq] at hc
    rcases hc with (hc | ⟨l, ⟨hl, hjl⟩, rfl⟩) | hc
    · by_cases hjw : j < wF φ i
      · rw [if_pos hjw, List.mem_singleton] at hc; subst hc
        have hz := lit_mem_vars φ i j hi hjw
        rw [ren_lit φ i j hi hjw] at even_no ⊢
        cases hb : (litF φ i j).2
        · rw [hb] at even_no
          exact even_no (eF φ (litF φ i j).1) (by have := eF_lt φ _ hz; omega) (by simp) rfl
        · simp only [hb, if_true, iff_true]
          refine ⟨Sum.inl ((litF φ i j).1, true), ?_, ?_⟩
          · rw [cover_inl, vars_cvc]; exact ⟨Or.inl hz, rfl⟩
          · rw [h1 _ hz]; simp
      · rw [if_neg hjw, List.mem_singleton] at hc; subst hc
        simp only [iff_true]
        refine ⟨Sum.inl (fresh φ, true), ?_, ?_⟩
        · rw [cover_inl, vars_cvc]; exact ⟨Or.inr rfl, rfl⟩
        · rw [h2]; simp
    · simp only
      have hfi : (clauseAt (cvcFormula φ) i).findIdx (Literal.eval (fun _ => true)) = fF (REN φ) i := by
        rw [clauseAt_cvc_lt φ i hi, findIdx_eval_append, ren_fF]
      by_cases hf : j = fF (REN φ) i
      · simp only [hf, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, iff_false,
          not_exists, not_and]
        intro u hu hnum
        rcases u with ⟨z, b⟩ | ⟨i', j'⟩
        · rw [cover_inl, vars_cvc] at hu
          obtain ⟨hz | rfl, hb⟩ := hu
          · rw [h1 z hz] at hnum; have := eF_lt φ z hz; split at hnum <;> omega
          · rw [h2] at hnum; split at hnum <;> omega
        · rw [cover_inr, cvc_length] at hu
          obtain ⟨hi', hj', hne⟩ := hu
          rcases Nat.lt_or_ge i' φ.length with hi'' | hi''
          · rw [cvc_length_lt φ i' hi''] at hj'
            rw [h3 i' j' hi'' (by unfold wF at hj'; omega)] at hnum
            obtain ⟨rfl, rfl⟩ := item_inj φ i' i j' j hi'' hi (by omega) (by omega) (by omega)
            exact hne (hfi.trans hf.symm).symm
          · have : i' = φ.length := by omega
            subst this
            rw [clauseAt_cvc_eq] at hj'
            simp at hj'; subst hj'
            rw [h4] at hnum; omega
      · simp only [ne_eq, hf, not_false_eq_true, decide_true, iff_true]
        refine ⟨Sum.inr (i, j), ?_, ?_⟩
        · rw [cover_inr, cvc_length, cvc_length_lt φ i hi, hfi]
          exact ⟨by omega, by omega, hf⟩
        · rw [h3 i j hi (by unfold wF at hj; omega)]
    · by_cases h : j < wF φ i ∧ (litF (REN φ) i j).1 = offF (REN φ) i + j
      · rw [if_pos h, List.mem_singleton] at hc; subst hc
        exact even_no _ ((ren_var_le φ i j).trans hI) rfl rfl
      · rw [if_neg h] at hc; simp at hc
  · exact even_no E le_rfl rfl rfl
  · exact even_no E le_rfl rfl rfl

end

/-- `PlacedEdges`, the first gap of the predecessor, proved (conjecture until checked). -/
theorem placedEdges : PlacedEdges := by
  intro φ E k off e hk hE hoff he num h1 h2 h3 h4 H hH T hT
  have hI : itemsF φ ≤ E := hE ▸ items_le_encode φ
  have hoffF : ∀ i, off i = offF φ i := fun i => hoff i
  have heF : ∀ z, e z = eF φ z := fun z => he z
  have h1' : ∀ z ∈ vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * eF φ z + (if b then 1 else 0) := by
    intro z hz b; rw [h1 z hz b, heF]
  have h3' : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      num (Sum.inr (i, j)) = 2 * (E + 1) + offF φ i + j := by
    intro i j hi hj; rw [h3 i j hi hj, hoffF]
  refine ⟨calls_nodup φ E hI, calls_bounds φ E hE, ?_, ?_⟩
  · intro a b hab
    exact adj_iff_call hI h1' h2 h3' h4 H hH a b hab
  · intro c hc a ha
    rw [hT, ha]
    exact call_flag hI h1' h2 h3' h4 c hc

end PEqualNP.MetaComplexity.Helpers.OwnerLink
