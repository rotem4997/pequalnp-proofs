import Mathlib
import PEqualNP.MetaComplexity.Helpers.OwnerLinkA

/-!
# The owner link, step P1: item positions and the renaming (conjecture until checked)

Items of a formula are the pairs `(i, j)`, `i < length`, `j ≤ wF i` (the literals of clause `i`
and one separator); item `(i, j)` sits at index `offF i + j` of the flattened list `itemL`.
Here: item indices are injective (`item_inj`), the value of `itemL` at an item index
(`itemL_get`), every index is an item index (`itemL_decode`), the variable of a literal of
`REN φ` is `eF φ` of the old variable (`ren_lit`), and `eF φ z` is the index of an item carrying
`z`, at most the index of every item carrying `z` (`eF_spec`, `eF_le`).
-/

namespace PEqualNP.MetaComplexity.Helpers.OwnerLink

open PEqualNP.Search

/-- The flattened item list of the renaming. -/
def itemL (ψ : CNF) : List (Option Literal) := ψ.flatMap (fun c : Clause => c.map some ++ [none])

/-- The earliest item index of a variable (the `e` of G-OWN). -/
def eF (ψ : CNF) (z : ℕ) : ℕ :=
  (itemL ψ).findIdx (fun o : Option Literal => o.any (fun l : Literal => l.1 == z))

theorem offF_zero (ψ : CNF) : offF ψ 0 = 0 := by simp [offF]

theorem offF_cons_succ (c : Clause) (ψ : CNF) (i : ℕ) :
    offF (c :: ψ) (i + 1) = c.length + 1 + offF ψ i := by
  simp [offF, List.take_succ_cons]

theorem wF_cons_zero (c : Clause) (ψ : CNF) : wF (c :: ψ) 0 = c.length := by simp [wF]

theorem wF_cons_succ (c : Clause) (ψ : CNF) (i : ℕ) : wF (c :: ψ) (i + 1) = wF ψ i := by
  simp [wF]

theorem litF_cons_zero (c : Clause) (ψ : CNF) (j : ℕ) : litF (c :: ψ) 0 j = c.getD j (0, false) := by
  simp [litF]

theorem litF_cons_succ (c : Clause) (ψ : CNF) (i j : ℕ) : litF (c :: ψ) (i + 1) j = litF ψ i j := by
  simp [litF]

theorem item_inj (ψ : CNF) : ∀ i i' j j', i < ψ.length → i' < ψ.length → j ≤ wF ψ i →
    j' ≤ wF ψ i' → offF ψ i + j = offF ψ i' + j' → i = i' ∧ j = j' := by
  induction ψ with
  | nil => intro i; simp
  | cons c ψ ih =>
    intro i i' j j' hi hi' hj hj' h
    cases i with
    | zero =>
      cases i' with
      | zero => rw [offF_zero] at h; exact ⟨rfl, by omega⟩
      | succ i' => rw [offF_zero, offF_cons_succ] at h; rw [wF_cons_zero] at hj; omega
    | succ i =>
      cases i' with
      | zero => rw [offF_zero, offF_cons_succ] at h; rw [wF_cons_zero] at hj'; omega
      | succ i' =>
        rw [offF_cons_succ, offF_cons_succ] at h
        rw [wF_cons_succ] at hj hj'
        have := ih i i' j j' (by simpa using hi) (by simpa using hi') hj hj' (by omega)
        omega

theorem itemL_cons (c : Clause) (ψ : CNF) : itemL (c :: ψ) = (c.map some ++ [none]) ++ itemL ψ := by
  simp [itemL]

theorem itemL_get (ψ : CNF) : ∀ i j, i < ψ.length → j ≤ wF ψ i →
    (itemL ψ)[offF ψ i + j]? = some (if j < wF ψ i then some (litF ψ i j) else none) := by
  induction ψ with
  | nil => intro i; simp
  | cons c ψ ih =>
    intro i j hi hj
    rw [itemL_cons]
    cases i with
    | zero =>
      rw [offF_zero, wF_cons_zero] at *
      rw [List.getElem?_append_left (by simp; omega), Nat.zero_add]
      by_cases hjc : j < c.length
      · rw [List.getElem?_append_left (by simpa using hjc)]
        simp [hjc, litF, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjc]
      · have : j = c.length := by omega
        subst this
        rw [List.getElem?_append_right (by simp)]
        simp
    | succ i =>
      rw [offF_cons_succ, wF_cons_succ, litF_cons_succ]
      rw [wF_cons_succ] at hj
      rw [List.getElem?_append_right (by simp; omega)]
      have := ih i j (by simpa using hi) hj
      simp only [List.length_append, List.length_map, List.length_singleton] at this ⊢
      rw [← this]; congr 1; omega

theorem itemL_length (ψ : CNF) : (itemL ψ).length = itemsF ψ := items_list_len ψ

theorem itemL_decode (ψ : CNF) : ∀ n, n < (itemL ψ).length →
    ∃ i j, i < ψ.length ∧ j ≤ wF ψ i ∧ n = offF ψ i + j := by
  induction ψ with
  | nil => intro n; simp [itemL]
  | cons c ψ ih =>
    intro n hn
    rw [itemL_cons] at hn
    simp only [List.length_append, List.length_map, List.length_singleton] at hn
    by_cases hc : n < c.length + 1
    · exact ⟨0, n, by simp, by rw [wF_cons_zero]; omega, by rw [offF_zero]; omega⟩
    · obtain ⟨i, j, hi, hj, hn'⟩ := ih (n - (c.length + 1)) (by omega)
      refine ⟨i + 1, j, by simpa using hi, by rw [wF_cons_succ]; exact hj, ?_⟩
      rw [offF_cons_succ]; omega

/-- A literal of the renamed formula. -/
theorem ren_lit (φ : CNF) (i j : ℕ) (hi : i < φ.length) (hj : j < wF φ i) :
    litF (REN φ) i j = (eF φ (litF φ i j).1, (litF φ i j).2) := by
  unfold wF at hj
  simp only [litF, REN, eF, itemL, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some] at hj ⊢
  rw [List.getElem?_eq_getElem hj] at *
  simp [List.getElem?_eq_getElem hj]

theorem lit_mem_vars (φ : CNF) (i j : ℕ) (hi : i < φ.length) (hj : j < wF φ i) :
    (litF φ i j).1 ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ := by
  unfold wF at hj
  simp only [PEqualNP.MetaComplexity.CoverPromise.vars, List.mem_toFinset, List.mem_flatMap,
    List.mem_map]
  refine ⟨φ[i], List.getElem_mem hi, litF φ i j, ?_, rfl⟩
  simp only [litF, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    at hj ⊢
  rw [List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

theorem vars_mem_lit (φ : CNF) (z : ℕ) (hz : z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ) :
    ∃ i j, i < φ.length ∧ j < wF φ i ∧ (litF φ i j).1 = z := by
  simp only [PEqualNP.MetaComplexity.CoverPromise.vars, List.mem_toFinset, List.mem_flatMap,
    List.mem_map] at hz
  obtain ⟨c, hc, l, hl, rfl⟩ := hz
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hl
  refine ⟨i, j, hi, by simpa [wF, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hj, ?_⟩
  simp [litF, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]

theorem eF_le (φ : CNF) (i j : ℕ) (hi : i < φ.length) (hj : j < wF φ i) :
    eF φ (litF φ i j).1 ≤ offF φ i + j := by
  have hg := itemL_get φ i j hi hj.le
  simp only [hj, if_true] at hg
  have hlt : offF φ i + j < (itemL φ).length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  by_contra hc
  have := List.not_of_lt_findIdx (p := fun o : Option Literal => o.any (fun l : Literal => l.1 == (litF φ i j).1)) (xs := itemL φ) (i := offF φ i + j) (by unfold eF at hc; omega)
  rw [List.getElem?_eq_getElem hlt] at hg
  simp only [Option.some.injEq] at hg
  rw [hg] at this
  simp at this

theorem eF_spec (φ : CNF) (z : ℕ) (hz : z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ) :
    ∃ i j, i < φ.length ∧ j < wF φ i ∧ (litF φ i j).1 = z ∧ eF φ z = offF φ i + j := by
  obtain ⟨i0, j0, hi0, hj0, hz0⟩ := vars_mem_lit φ z hz
  have hex : ∃ x ∈ itemL φ, (fun o : Option Literal => o.any (fun l : Literal => l.1 == z)) x := by
    have hg := itemL_get φ i0 j0 hi0 hj0.le
    simp only [hj0, if_true] at hg
    refine ⟨some (litF φ i0 j0), List.mem_of_getElem? hg, by simp [hz0]⟩
  have hlt := List.findIdx_lt_length_of_exists hex
  have hp := List.findIdx_getElem (w := hlt)
  obtain ⟨i, j, hi, hj, hij⟩ := itemL_decode φ _ hlt
  have hg := itemL_get φ i j hi hj
  rw [← hij, List.getElem?_eq_getElem hlt] at hg
  simp only [Option.some.injEq] at hg
  rw [hg] at hp
  by_cases hjw : j < wF φ i
  · simp only [hjw, if_true, Option.any_some, beq_iff_eq] at hp
    exact ⟨i, j, hi, hjw, hp, hij⟩
  · simp [hjw] at hp

theorem eF_lt (φ : CNF) (z : ℕ) (hz : z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ) :
    eF φ z < itemsF φ := by
  obtain ⟨i, j, hi, hj, -, h⟩ := eF_spec φ z hz
  have := off_add_le φ i hi
  omega

end PEqualNP.MetaComplexity.Helpers.OwnerLink
