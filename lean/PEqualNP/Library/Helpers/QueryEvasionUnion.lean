import Mathlib

/-!
# Query evasion across finitely many fields

Union bound step: from the single-field query evasion lemma (assumed as a
hypothesis), a Boolean point `w` that is good for every field simultaneously
exists as soon as the total number of queried points is below `2 ^ n`.
-/

namespace PEqualNP.Library.Helpers.QueryEvasionUnion

open Finset

set_option linter.unusedVariables false in
theorem of_single (h : ∀ (F : Type) [Field F] (n : ℕ) (Y : Finset (Fin n → F)), ∃ G : Finset (Fin n → Bool), 2 ^ n ≤ G.card + Y.card ∧ ∀ w ∈ G, ∃ p : MvPolynomial (Fin n) F, (∀ i : Fin n, MvPolynomial.degreeOf i p ≤ 2) ∧ (∀ y ∈ Y, MvPolynomial.eval y p = 0) ∧ ∀ z : Fin n → Bool, MvPolynomial.eval (fun i => if z i then (1 : F) else 0) p = if z = w then 1 else 0) :
    ∀ (n k : ℕ) (Fs : Fin k → Type) [inst : ∀ j, Field (Fs j)] (Y : ∀ j, Finset (Fin n → Fs j)), ∑ j, (Y j).card < 2 ^ n → ∃ w : Fin n → Bool, ∀ j, ∃ p : MvPolynomial (Fin n) (Fs j), (∀ i : Fin n, MvPolynomial.degreeOf i p ≤ 2) ∧ (∀ y ∈ Y j, MvPolynomial.eval y p = 0) ∧ ∀ z : Fin n → Bool, MvPolynomial.eval (fun i => if z i then (1 : Fs j) else 0) p = if z = w then 1 else 0 := by
  intro n k Fs inst Y hsum
  classical
  choose G hG hP using fun j => h (Fs j) n (Y j)
  have hcard : (univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
  have hB : ∀ j, (univ \ G j).card ≤ (Y j).card := by
    intro j
    have h1 := card_sdiff_add_card_eq_card (subset_univ (G j))
    have h2 := hG j
    omega
  have hU : (univ.biUnion fun j => univ \ G j).card < (univ : Finset (Fin n → Bool)).card := by
    calc _ ≤ ∑ j, (univ \ G j).card := card_biUnion_le
      _ ≤ ∑ j, (Y j).card := sum_le_sum fun j _ => hB j
      _ < 2 ^ n := hsum
      _ = _ := hcard.symm
  obtain ⟨w, -, hw⟩ := exists_mem_notMem_of_card_lt_card hU
  refine ⟨w, fun j => hP j w ?_⟩
  by_contra hc
  exact hw (mem_biUnion.2 ⟨j, mem_univ _, mem_sdiff.2 ⟨mem_univ _, hc⟩⟩)

end PEqualNP.Library.Helpers.QueryEvasionUnion
