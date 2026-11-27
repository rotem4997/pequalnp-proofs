import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5337_aux

theorem core (n k : ℕ) (E : Finset (Fin n × Fin n)) :
    ∀ N, ∀ S T : Finset (Fin n), S.card + T.card = N →
      k * (S.card + T.card) < ∑ s ∈ S, (T.filter (fun t => (s, t) ∈ E)).card →
      ∃ S' T' : Finset (Fin n), S'.Nonempty ∧ T'.Nonempty ∧
        (∀ x ∈ S', k < (T'.filter (fun y => (x, y) ∈ E)).card) ∧
        ∀ x ∈ T', k < (S'.filter (fun y => (y, x) ∈ E)).card := by
  have hswap : ∀ S T : Finset (Fin n), ∑ s ∈ S, (T.filter (fun t => (s, t) ∈ E)).card
      = ∑ t ∈ T, (S.filter (fun s => (s, t) ∈ E)).card := by
    intro S T
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro S T hN h
  by_cases hA : ∃ s ∈ S, (T.filter (fun t => (s, t) ∈ E)).card ≤ k
  · obtain ⟨s, hs, hd⟩ := hA
    have he : (T.filter (fun t => (s, t) ∈ E)).card
        + ∑ x ∈ S.erase s, (T.filter (fun t => (x, t) ∈ E)).card
        = ∑ x ∈ S, (T.filter (fun t => (x, t) ∈ E)).card :=
      Finset.add_sum_erase S (fun x => (T.filter (fun t => (x, t) ∈ E)).card) hs
    have hc := Finset.card_erase_add_one hs
    have hk : k * (S.card + T.card) = k * ((S.erase s).card + T.card) + k := by
      rw [← hc]; ring
    exact ih ((S.erase s).card + T.card) (by omega) (S.erase s) T rfl (by omega)
  by_cases hB : ∃ t ∈ T, (S.filter (fun s => (s, t) ∈ E)).card ≤ k
  · obtain ⟨t, ht, hd⟩ := hB
    have he : (S.filter (fun s => (s, t) ∈ E)).card
        + ∑ x ∈ T.erase t, (S.filter (fun s => (s, x) ∈ E)).card
        = ∑ x ∈ T, (S.filter (fun s => (s, x) ∈ E)).card :=
      Finset.add_sum_erase T (fun x => (S.filter (fun s => (s, x) ∈ E)).card) ht
    have hc := Finset.card_erase_add_one ht
    have hk : k * (S.card + T.card) = k * (S.card + (T.erase t).card) + k := by
      rw [← hc]; ring
    refine ih (S.card + (T.erase t).card) (by omega) S (T.erase t) rfl ?_
    rw [hswap]
    rw [hswap] at h
    omega
  push_neg at hA hB
  refine ⟨S, T, ?_, ?_, hA, hB⟩
  · rcases S.eq_empty_or_nonempty with h0 | h0
    · subst h0; simp at h
    · exact h0
  · rcases T.eq_empty_or_nonempty with h0 | h0
    · subst h0; simp at h
    · exact h0

end PEqualNP.Outside.L_meta_5337_aux

theorem PEqualNP.Outside.L_meta_5337 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x1)), x2 * (x1 + x1) < x3.card → ∃ (x5 : Finset (Fin x1)) (x6 : Finset (Fin x1)), x5.Nonempty ∧ x6.Nonempty ∧ (∀ x7 ∈ x5, x2 < {x9 ∈ x6 | (x7, x9) ∈ x3}.card) ∧ ∀ x7 ∈ x6, x2 < {x9 ∈ x5 | (x9, x7) ∈ x3}.card := by
  intro x1 x2 x3 h
  apply PEqualNP.Outside.L_meta_5337_aux.core x1 x2 x3 _ Finset.univ Finset.univ rfl
  have h1 : x3.card = ∑ s : Fin x1, (Finset.univ.filter (fun t => (s, t) ∈ x3)).card := by
    simp only [Finset.card_filter]
    rw [← Finset.sum_product' (f := fun s t => if (s, t) ∈ x3 then 1 else 0)]
    simp [Finset.univ_product_univ, Finset.sum_boole]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega
