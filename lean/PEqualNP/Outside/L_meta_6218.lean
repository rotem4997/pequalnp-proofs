import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_6218 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → {x6 : Fin x2 × Fin x2 | x3 x6.1 x6.2}.ncard = x2 * (x1 + (1 : ℕ)) := by
  intro q n R _ h
  have h1 : {p : Fin n × Fin n | R p.1 p.2}.ncard =
      (Finset.univ.filter (fun p : Fin n × Fin n => R p.1 p.2)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p
    simp
  have h3 : ∀ b : Fin n, (∑ a : Fin n, (if R a b then 1 else 0)) = q + 1 := by
    intro b
    rw [← Finset.card_filter, ← h b, Fintype.card_subtype]
  rw [h1, Finset.card_filter, Fintype.sum_prod_type_right]
  simp only [h3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
