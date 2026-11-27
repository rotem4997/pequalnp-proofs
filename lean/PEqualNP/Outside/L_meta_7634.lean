import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7634

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7634

theorem PEqualNP.Outside.L_meta_7634 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : Fin x2), x3 x9 x10 → ((Finset.filter (x3 x9) Finset.univ).erase x10).card = x1 ∧ ∃ (x12 : Fin x2 → Fin x2), ∀ (x13 x14 : Fin x2), x13 ≠ x9 → x3 x9 x14 → (x3 x13 x14 ↔ x12 x13 = x14) := by
  intro q n I _ hq hn hline hpt p l hpl
  classical
  let f : Fin n → Fin n := fun x => if h : x ≠ p then (hpt p x h.symm).choose else l
  have hf : ∀ x, x ≠ p → ∀ m, I p m → (I x m ↔ f x = m) := by
    intro x hx m hm
    have hs := (hpt p x hx.symm).choose_spec
    have hfx : f x = (hpt p x hx.symm).choose := by simp only [f]; rw [dif_pos hx]
    rw [hfx]
    constructor
    · intro hxm
      exact (hs.2 m ⟨hm, hxm⟩).symm
    · intro e
      rw [← e]
      exact hs.1.2
  have hf2 : ∀ x, x ≠ p → I p (f x) := by
    intro x hx
    have hs := (hpt p x hx.symm).choose_spec
    have hfx : f x = (hpt p x hx.symm).choose := by simp only [f]; rw [dif_pos hx]
    rw [hfx]
    exact hs.1.1
  refine ⟨?_, f, fun x m hx hm => hf x hx m hm⟩
  set L := Finset.filter (I p) Finset.univ with hL
  have hmaps : ∀ x ∈ (Finset.univ.erase p : Finset (Fin n)), f x ∈ L := by
    intro x hx
    rw [hL, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hf2 x (Finset.ne_of_mem_erase hx)⟩
  have hc := Finset.card_eq_sum_card_fiberwise (f := f) (s := (Finset.univ.erase p : Finset (Fin n))) (t := L) (by intro x hx; exact hmaps x hx)
  have hfib : ∀ m ∈ L, ((Finset.univ.erase p : Finset (Fin n)).filter fun x => f x = m).card = q := by
    intro m hm
    have hpm : I p m := (Finset.mem_filter.1 hm).2
    have e : ((Finset.univ.erase p : Finset (Fin n)).filter fun x => f x = m) = (Finset.univ.filter fun x => I x m).erase p := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hf x h1 m hpm).2 h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hf x h1 m hpm).1 h2⟩
    have hcard : (Finset.univ.filter fun x => I x m).card = q + 1 := by
      rw [← Fintype.card_subtype, ← hline m]
    rw [e, Finset.card_erase_of_mem (by simp [hpm]), hcard, Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin] at hc
  have hlL : l ∈ L := by rw [hL, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hpl⟩
  have hLq : L.card = q + 1 := by
    have h1 : n - 1 = (q + 1) * q := by rw [hn, Nat.add_sub_cancel]; ring
    rw [h1] at hc
    exact (Nat.eq_of_mul_eq_mul_right hq hc).symm
  rw [Finset.card_erase_of_mem hlL, hLq, Nat.add_sub_cancel]
