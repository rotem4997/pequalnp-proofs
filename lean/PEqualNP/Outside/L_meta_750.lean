import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_750_aux

theorem step (n T K : ℕ) (h : Fin T → (Fin n → Bool) → Bool)
    (hm : ∀ j : Fin T, Monotone (h j)) :
    ∀ (m : ℕ) (y : Fin n → Bool) (D : Finset (Fin T)),
      (∀ j1 ∈ D, h j1 y = true) →
      (Finset.univ.filter (fun i2 : Fin n => y i2 = true)).card ≤ K * D.card →
      T - D.card ≤ m →
      ∃ (y : Fin n → Bool) (D : Finset (Fin T)), (∀ j1 ∈ D, h j1 y = true) ∧ (∀ j2 : Fin T, j2 ∉ D → ∀ x : Fin n → Bool, (∀ i : Fin n, y i = true → x i = true) → (Finset.univ.filter (fun i1 : Fin n => x i1 = true ∧ y i1 = false)).card ≤ K → h j2 x = false) ∧ (Finset.univ.filter (fun i2 : Fin n => y i2 = true)).card ≤ K * D.card := by
  intro m
  induction m with
  | zero =>
    intro y D h1 h2 h3
    refine ⟨y, D, h1, ?_, h2⟩
    intro j hj
    have hc : (insert j D).card ≤ Fintype.card (Fin T) := Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem hj, Fintype.card_fin] at hc
    omega
  | succ m ih =>
    intro y D h1 h2 h3
    by_cases hc : ∀ j2 : Fin T, j2 ∉ D → ∀ x : Fin n → Bool, (∀ i : Fin n, y i = true → x i = true) → (Finset.univ.filter (fun i1 : Fin n => x i1 = true ∧ y i1 = false)).card ≤ K → h j2 x = false
    · exact ⟨y, D, h1, hc, h2⟩
    · push_neg at hc
      obtain ⟨j, hj, x, hxy, hcard, hx⟩ := hc
      have hle : y ≤ x := by
        intro i
        have := hxy i
        revert this
        cases y i <;> cases x i <;> simp
      have hcc : (insert j D).card ≤ Fintype.card (Fin T) := Finset.card_le_univ _
      rw [Finset.card_insert_of_notMem hj, Fintype.card_fin] at hcc
      apply ih x (insert j D)
      · intro j1 hj1
        rcases Finset.mem_insert.mp hj1 with rfl | hj1
        · simpa using hx
        · have h4 := hm j1 hle
          rw [h1 j1 hj1] at h4
          revert h4
          cases h j1 x <;> simp
      · rw [Finset.card_insert_of_notMem hj]
        have hsub : (Finset.univ.filter (fun i2 : Fin n => x i2 = true)) ⊆ (Finset.univ.filter (fun i2 : Fin n => y i2 = true)) ∪ (Finset.univ.filter (fun i1 : Fin n => x i1 = true ∧ y i1 = false)) := by
          intro i hi
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          cases hy : y i <;> simp [hi]
        have h5 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have h6 : K * (D.card + 1) = K * D.card + K := by ring
        omega
      · rw [Finset.card_insert_of_notMem hj]
        omega

end PEqualNP.Outside.L_meta_750_aux

theorem PEqualNP.Outside.L_meta_750 : ∀ (n T K : ℕ) (h : Fin T → (Fin n → Bool) → Bool), 1 ≤ K → (∀ j : Fin T, Monotone (h j)) → ∃ (y : Fin n → Bool) (D : Finset (Fin T)), (∀ j1 ∈ D, h j1 y = true) ∧ (∀ j2 : Fin T, j2 ∉ D → ∀ x : Fin n → Bool, (∀ i : Fin n, y i = true → x i = true) → (Finset.univ.filter (fun i1 : Fin n => x i1 = true ∧ y i1 = false)).card ≤ K → h j2 x = false) ∧ (Finset.univ.filter (fun i2 : Fin n => y i2 = true)).card ≤ K * D.card := by
  intro n T K h _ hm
  exact PEqualNP.Outside.L_meta_750_aux.step n T K h hm T (fun _ => false) ∅ (by simp) (by simp) (by simp)
