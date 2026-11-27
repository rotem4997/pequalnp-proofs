import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

-- Compress each set of raw input wires to its indexed points or lines.
theorem PEqualNP.Outside.R_meta_4982_219
    (compress : ∀ (p l n : ℕ) (a : Fin p ↪ Fin n) (b : Fin l ↪ Fin n) (C : Circuit),
      Monotone2 C → ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧
      ∀ X : Finset (Fin p), ∀ Y : Finset (Fin l),
        D.eval (incidenceInput X Y) = C.eval (incidenceInput (X.map a) (Y.map b)))
    (canonical : ∀ (q : ℕ) (value : Fin (q+1) → Fin (q*q) → Fin q) (D : Circuit),
      300 ≤ q →
      (∀ r s, r ≠ s → Function.Bijective fun p => (value r p, value s p)) →
      Monotone2 D →
      (∀ p r, D.eval (incidenceInput {p}
        {(finProdFinEquiv : Fin (q+1) × Fin q ≃ Fin ((q+1)*q)) (r, value r p)}) = true) →
      (∀ (X : Finset (Fin (q*q))) (Y : Finset (Fin (q+1) × Fin q)), Y.card ≤ q →
        (∀ p ∈ X, ∀ r, (r, value r p) ∉ Y) →
        D.eval (incidenceInput X (Y.map
          (finProdFinEquiv : Fin (q+1) × Fin q ≃ Fin ((q+1)*q)).toEmbedding)) = false) →
      q^2 * (q+1) ≤ 99 * D.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin (x1 * x1) ↪ Fin x2) (x4 : Fin (x1 + (1 : ℕ)) × Fin x1 ↪ Fin x2) (x5 : Fin (x1 + (1 : ℕ)) → Fin (x1 * x1) → Fin x1) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → (∀ (x8 x9 : Fin (x1 + (1 : ℕ))), x8 ≠ x9 → Function.Bijective fun (x11 : Fin (x1 * x1)) => (x5 x8 x11, x5 x9 x11)) → PEqualNP.MetaComplexity.Monotone2 x6 → (∀ (x10 : Fin (x1 * x1)) (x11 : Fin (x1 + (1 : ℕ))), x6.eval (PEqualNP.GenericRejection.incidenceInput {x3 x10} {x4 (x11, x5 x11 x10)}) = Bool.true) → (∀ (x11 : Finset (Fin (x1 * x1))) (x12 : Finset (Fin (x1 + (1 : ℕ)) × Fin x1)), x12.card ≤ x1 → (∀ x14 ∈ x11, ∀ (x16 : Fin (x1 + (1 : ℕ))), (x16, x5 x16 x14) ∉ x12) → x6.eval (PEqualNP.GenericRejection.incidenceInput (Finset.map x3 x11) (Finset.map x4 x12)) = Bool.false) → x1 ^ (2 : ℕ) * (x1 + (1 : ℕ)) ≤ (99 : ℕ) * x6.size := by
  intro q n points lines value C order orthogonal legal yes no
  let code : Fin (q+1) × Fin q ≃ Fin ((q+1)*q) := finProdFinEquiv
  let scan := code.symm.toEmbedding.trans lines
  obtain ⟨D, dlegal, size, agrees⟩ := compress (q*q) ((q+1)*q) n points scan C legal
  have same (X : Finset (Fin (q*q))) (Y : Finset (Fin (q+1) × Fin q)) :
      D.eval (incidenceInput X (Y.map code.toEmbedding)) =
        C.eval (incidenceInput (X.map points) (Y.map lines)) := by
    rw [agrees X (Y.map code.toEmbedding), Finset.map_map]
    have comp : code.toEmbedding.trans scan = lines := by
      ext t
      change (lines (code.symm (code t))).val = (lines t).val
      rw [code.symm_apply_apply]
    rw [comp]
  rw [← size]
  apply canonical q value D order orthogonal dlegal
  · intro p r
    simpa only [Finset.map_singleton, Equiv.coe_toEmbedding, code] using (same {p} {(r, value r p)}).trans (yes p r)
  · intro X Y small avoided
    exact (same X Y).trans (no X Y small avoided)
