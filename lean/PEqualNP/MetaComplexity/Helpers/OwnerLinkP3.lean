import Mathlib
import PEqualNP.MetaComplexity.Helpers.OwnerLinkP2

/-!
# The owner link, step P3: the calls are the placed edges (conjecture until checked)

Third conjunct of `PlacedEdges`: for `a < b`, `H.Adj a b` iff `(a, b, t)` is a call for some
flag `t`. Proved from the two directions `edge_call` (an edge of `cvcGraph φ` with its ends
numbered in increasing order is a call) and `call_edge` (every call is the numbered image of
an edge), under the numbering hypotheses of G-OWN with `e = eF φ` and `off = offF φ`.
-/

namespace PEqualNP.MetaComplexity.Helpers.OwnerLink

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

theorem clauseAt_cvc_lt (φ : CNF) (i : ℕ) (hi : i < φ.length) :
    clauseAt (cvcFormula φ) i = φ.getD i [] ++ [(fresh φ, true)] := by
  simp only [clauseAt, cvcFormula, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using hi), List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

theorem clauseAt_cvc_eq (φ : CNF) : clauseAt (cvcFormula φ) φ.length = [(fresh φ, false)] := by
  simp [clauseAt, cvcFormula, List.getD_eq_getElem?_getD]

theorem clauseAt_cvc_gt (φ : CNF) (i : ℕ) (hi : φ.length < i) : clauseAt (cvcFormula φ) i = [] := by
  simp only [clauseAt, cvcFormula, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simp; omega)]
  rfl

theorem vars_cvc (φ : CNF) (z : ℕ) : z ∈ vars (cvcFormula φ) ↔ z ∈ vars φ ∨ z = fresh φ := by
  simp only [vars, cvcFormula, List.mem_toFinset, List.mem_flatMap, List.mem_map, List.mem_append,
    List.mem_singleton]
  constructor
  · rintro ⟨c, hc, l, hl, rfl⟩
    rcases hc with ⟨c', hc', rfl⟩ | rfl
    · rw [List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact Or.inl ⟨c', hc', l, hl, rfl⟩
      · exact Or.inr rfl
    · rw [List.mem_singleton] at hl; subst hl; exact Or.inr rfl
  · rintro (⟨c, hc, l, hl, rfl⟩ | rfl)
    · exact ⟨c ++ [(fresh φ, true)], Or.inl ⟨c, hc, rfl⟩, l, by simp [hl], rfl⟩
    · exact ⟨[(fresh φ, false)], Or.inr rfl, (fresh φ, false), by simp, rfl⟩

theorem fresh_not_mem (φ : CNF) : fresh φ ∉ vars φ := by
  intro h
  have := Finset.le_sup (f := id) h
  simp only [fresh, id] at this
  omega

/-- The literal at a position of a clause of `cvcFormula φ`. -/
theorem cvc_get_lt (φ : CNF) (i j : ℕ) (hi : i < φ.length) :
    (clauseAt (cvcFormula φ) i)[j]? =
      if j < wF φ i then some (litF φ i j) else if j = wF φ i then some (fresh φ, true) else none := by
  rw [clauseAt_cvc_lt φ i hi]
  unfold wF litF
  generalize φ.getD i [] = c
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]

theorem cvc_length_lt (φ : CNF) (i : ℕ) (hi : i < φ.length) :
    (clauseAt (cvcFormula φ) i).length = wF φ i + 1 := by
  rw [clauseAt_cvc_lt φ i hi]; simp [wF]

theorem ren_wF (φ : CNF) (i : ℕ) : wF (REN φ) i = wF φ i := ren_getD_length φ i

theorem ren_posF (E : ℕ) (φ : CNF) (i j : ℕ) : posF E (REN φ) i j = 2 * (E + 1) + offF φ i + j := by
  simp [posF, ren_off]

theorem ren_fF (φ : CNF) (i : ℕ) : fF (REN φ) i = (φ.getD i []).findIdx (fun l : Literal => l.2) := by
  simp only [fF, REN, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases φ[i]? <;> simp [List.findIdx_map, Function.comp_def]

theorem mem_calls_blk {E : ℕ} {ψ : CNF} {i j : ℕ} (hi : i < ψ.length) (hj : j ≤ wF ψ i)
    {c : ℕ × ℕ × Bool} (hc : c ∈ blkF E ψ i j) : c ∈ callsF E ψ := by
  rw [callsF_eq]
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
    List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (by omega), hc⟩⟩)

section
variable {φ : CNF} {E : ℕ} {num : Vertex → ℕ} (hI : itemsF φ ≤ E)
  (h1 : ∀ z ∈ vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * eF φ z + (if b then 1 else 0))
  (h2 : ∀ b : Bool, num (Sum.inl (fresh φ, b)) = 2 * E + (if b then 1 else 0))
  (h3 : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
    num (Sum.inr (i, j)) = 2 * (E + 1) + offF φ i + j)
  (h4 : num (Sum.inr (φ.length, 0)) = 3 * E + 2)
include hI h1 h2 h3 h4

/-- An edge with its ends numbered in increasing order is a call. -/
theorem edge_call (u v : Vertex) (huv : (cvcGraph φ).Adj u v) (hlt : num u < num v) :
    ∃ t, (num u, num v, t) ∈ callsF E (REN φ) := by
  change satAdj (cvcFormula φ) u v at huv
  rcases u with ⟨z, b⟩ | ⟨i, j⟩ <;> rcases v with ⟨z', b'⟩ | ⟨i', j'⟩ <;> simp only [satAdj] at huv
  · -- two literals of one variable
    obtain ⟨rfl, hb, hz⟩ := huv
    rw [vars_cvc] at hz
    rcases hz with hz | rfl
    · rw [h1 z hz, h1 z hz] at hlt ⊢
      obtain ⟨i, j, hi, hj, hzi, he⟩ := eF_spec φ z hz
      cases b <;> cases b' <;> simp at hb hlt
      refine ⟨false, mem_calls_blk (i := i) (j := j) (by rw [ren_length]; exact hi)
        (by rw [ren_wF]; omega) ?_⟩
      have hl := ren_lit φ i j hi hj
      rw [hzi] at hl
      simp only [blkF, ren_wF, hl, ren_off, he, hj, true_and, if_true, List.mem_append,
        List.mem_singleton]
      right; simp
    · rw [h2, h2] at hlt ⊢
      cases b <;> cases b' <;> simp at hb hlt
      exact ⟨false, by rw [callsF_eq]; simp⟩
  · -- a literal and an occurrence
    rcases Nat.lt_trichotomy i' φ.length with hi | rfl | hi
    · rw [cvc_get_lt φ i' j' hi] at huv
      have hj : j' ≤ wF φ i' := by split_ifs at huv <;> first | omega | simp at huv
      rw [h3 i' j' hi hj]
      split_ifs at huv with hjw hjw2
      · simp only [Option.some.injEq] at huv
        have hz := lit_mem_vars φ i' j' hi hjw
        rw [huv] at hz
        rw [h1 z hz b]
        refine ⟨b, mem_calls_blk (i := i') (j := j') (by rw [ren_length]; exact hi)
          (by rw [ren_wF]; omega) ?_⟩
        have hl := ren_lit φ i' j' hi hjw
        rw [huv] at hl
        simp only [blkF, ren_wF, hl, hjw, if_true, ren_posF, List.mem_append, List.mem_singleton]
        simp
      · simp only [Option.some.injEq, Prod.mk.injEq] at huv
        obtain ⟨rfl, rfl⟩ := huv
        rw [h2]
        refine ⟨true, mem_calls_blk (i := i') (j := j') (by rw [ren_length]; exact hi)
          (by rw [ren_wF]; omega) ?_⟩
        simp only [blkF, ren_wF, hjw, if_false, ren_posF, List.mem_append, List.mem_singleton]
        left; left; simp
    · rw [clauseAt_cvc_eq] at huv
      cases j' with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at huv
        obtain ⟨rfl, rfl⟩ := huv
        rw [h2, h4]
        exact ⟨false, by rw [callsF_eq]; simp⟩
      | succ j' => simp at huv
    · rw [clauseAt_cvc_gt φ i' hi] at huv; simp at huv
  · -- an occurrence and a literal: the occurrence has the larger number
    exfalso
    have hz : z' ∈ vars φ ∨ z' = fresh φ := by
      rw [← vars_cvc]
      simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map]
      refine ⟨clauseAt (cvcFormula φ) i, ?_, (z', b'), List.mem_of_getElem? huv, rfl⟩
      by_cases hi : i < (cvcFormula φ).length
      · simp only [clauseAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
          Option.getD_some]
        exact List.getElem_mem hi
      · simp only [clauseAt, List.getD_eq_getElem?_getD] at huv
        rw [List.getElem?_eq_none (l := cvcFormula φ) (by omega)] at huv; simp at huv
    have hv : num (Sum.inl (z', b')) ≤ 2 * E + 1 := by
      rcases hz with hz | rfl
      · rw [h1 z' hz]; have := eF_lt φ z' hz; split <;> omega
      · rw [h2]; split <;> omega
    rcases Nat.lt_trichotomy i φ.length with hi | rfl | hi
    · have hj : j ≤ wF φ i := by
        rw [cvc_get_lt φ i j hi] at huv; split_ifs at huv <;> first | omega | simp at huv
      rw [h3 i j hi hj] at hlt; omega
    · rw [clauseAt_cvc_eq] at huv
      cases j with
      | zero => rw [h4] at hlt; omega
      | succ j => simp at huv
    · rw [clauseAt_cvc_gt φ i hi] at huv; simp at huv
  · -- two occurrences of one clause
    obtain ⟨rfl, hne, hj, hj'⟩ := huv
    rcases Nat.lt_trichotomy i φ.length with hi | rfl | hi
    · rw [cvc_length_lt φ i hi] at hj hj'
      rw [h3 i j hi (by unfold wF at hj; omega), h3 i j' hi (by unfold wF at hj'; omega)] at hlt ⊢
      refine ⟨decide (j ≠ fF (REN φ) i), mem_calls_blk (i := i) (j := j)
        (by rw [ren_length]; exact hi) (by rw [ren_wF]; omega) ?_⟩
      simp only [blkF, ren_wF, ren_posF, List.mem_append, List.mem_map, List.mem_filter,
        List.mem_range, decide_eq_true_eq]
      left; right
      exact ⟨j', ⟨by omega, by omega⟩, rfl⟩
    · rw [clauseAt_cvc_eq] at hj hj'; simp at hj hj'; omega
    · rw [clauseAt_cvc_gt φ i hi] at hj; simp at hj

/-- Every call is the numbered image of an edge. -/
theorem call_edge (c : ℕ × ℕ × Bool) (hc : c ∈ callsF E (REN φ)) :
    ∃ u v, (cvcGraph φ).Adj u v ∧ num u = c.1 ∧ num v = c.2.1 := by
  rw [callsF_eq] at hc
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with ⟨i, hi, j, hj, hc⟩ | rfl | rfl
  · rw [ren_length] at hi
    rw [ren_wF] at hj
    simp only [blkF, ren_wF, ren_posF, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_range, decide_eq_true_eq] at hc
    rcases hc with (hc | ⟨l, ⟨hl, hjl⟩, rfl⟩) | hc
    · by_cases hjw : j < wF φ i
      · rw [if_pos hjw, List.mem_singleton] at hc; subst hc
        refine ⟨Sum.inl (litF φ i j), Sum.inr (i, j), ?_, ?_, ?_⟩
        · rw [show (cvcGraph φ).Adj = satAdj (cvcFormula φ) from rfl]
          simp only [satAdj]; rw [cvc_get_lt φ i j hi, if_pos hjw]
        · rw [h1 _ (lit_mem_vars φ i j hi hjw), ren_lit φ i j hi hjw]
        · rw [h3 i j hi (by unfold wF at hjw; omega)]
      · rw [if_neg hjw, List.mem_singleton] at hc; subst hc
        refine ⟨Sum.inl (fresh φ, true), Sum.inr (i, j), ?_, ?_, ?_⟩
        · rw [show (cvcGraph φ).Adj = satAdj (cvcFormula φ) from rfl]
          simp only [satAdj]; rw [cvc_get_lt φ i j hi, if_neg hjw, if_pos (by omega)]
        · rw [h2]; rfl
        · rw [h3 i j hi (by unfold wF at hj; omega)]
    · refine ⟨Sum.inr (i, j), Sum.inr (i, l), ?_, ?_, ?_⟩
      · rw [show (cvcGraph φ).Adj = satAdj (cvcFormula φ) from rfl]
        simp only [satAdj, cvc_length_lt φ i hi]
        exact ⟨trivial, by omega, by omega, by omega⟩
      · rw [h3 i j hi (by unfold wF at hj; omega)]
      · rw [h3 i l hi (by unfold wF at hl; omega)]
    · by_cases h : j < wF φ i ∧ (litF (REN φ) i j).1 = offF (REN φ) i + j
      · rw [if_pos h, List.mem_singleton] at hc; subst hc
        have hz := lit_mem_vars φ i j hi h.1
        refine ⟨Sum.inl ((litF φ i j).1, false), Sum.inl ((litF φ i j).1, true), ?_, ?_, ?_⟩
        · rw [show (cvcGraph φ).Adj = satAdj (cvcFormula φ) from rfl]
          simp only [satAdj, ne_eq, Bool.false_eq_true, not_false_eq_true, true_and]
          exact (vars_cvc φ _).mpr (Or.inl hz)
        · rw [h1 _ hz, ren_lit φ i j hi h.1]; simp
        · rw [h1 _ hz, ren_lit φ i j hi h.1]; simp
      · rw [if_neg h] at hc; simp at hc
  · refine ⟨Sum.inl (fresh φ, false), Sum.inl (fresh φ, true), ?_, ?_, ?_⟩
    · rw [show (cvcGraph φ).Adj = satAdj (cvcFormula φ) from rfl]
      simp only [satAdj, ne_eq, Bool.false_eq_true, not_false_eq_true, true_and]
      exact (vars_cvc φ _).mpr (Or.inr rfl)
    · rw [h2]; simp
    · rw [h2]; simp
  · refine ⟨Sum.inl (fresh φ, false), Sum.inr (φ.length, 0), ?_, ?_, ?_⟩
    · rw [show (cvcGraph φ).Adj = satAdj (cvcFormula φ) from rfl]
      simp only [satAdj]; rw [clauseAt_cvc_eq]; rfl
    · rw [h2]; simp
    · rw [h4]

/-- Third conjunct of `PlacedEdges`, for a graph `H` given by the numbered edges. -/
theorem adj_iff_call (H : SimpleGraph (Fin (3 * (E + 1))))
    (hH : ∀ a b : Fin (3 * (E + 1)), H.Adj a b ↔ ∃ u v, (cvcGraph φ).Adj u v ∧ num u = a.val ∧ num v = b.val)
    (a b : Fin (3 * (E + 1))) (hab : a < b) :
    H.Adj a b ↔ ∃ t : Bool, (a.val, b.val, t) ∈ callsF E (REN φ) := by
  rw [hH]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rw [← hu, ← hv]
    exact edge_call hI h1 h2 h3 h4 u v huv (by rw [hu, hv]; exact Fin.lt_def.mp hab)
  · rintro ⟨t, ht⟩
    obtain ⟨u, v, huv, hu, hv⟩ := call_edge hI h1 h2 h3 h4 _ ht
    exact ⟨u, v, huv, hu, hv⟩

end

end PEqualNP.MetaComplexity.Helpers.OwnerLink
