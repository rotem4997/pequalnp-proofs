import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2577 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Sym2 (Fin x1))), PEqualNP.TopForm.NoFourCycle x2 → {x7 ∈ x5 | ∃ (x8 : Fin x1) (x9 : Fin x1), x7 = s(x8, x9) ∧ ∃ x10 < x4.gates.length, ∃ (x11 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x1 x4 (x1 + x10)).card ∧ (∀ x12 ∈ PEqualNP.TopForm.orIn x1 x4 (x1 + x10), x2.Adj x8 x12) ∧ PEqualNP.TopForm.orIn x1 x4 (PEqualNP.TopForm.opnd x4 x10 x11) = {x9}}.card ≤ (2 : ℕ) * x4.size := by
  classical
  intro n G _ C E hno
  have key : ∀ e ∈ ({x7 ∈ E | ∃ (x8 : Fin n) (x9 : Fin n), x7 = s(x8, x9) ∧ ∃ x10 < C.gates.length, ∃ (x11 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn n C (n + x10)).card ∧ (∀ x12 ∈ PEqualNP.TopForm.orIn n C (n + x10), G.Adj x8 x12) ∧ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C x10 x11) = {x9}} : Finset (Sym2 (Fin n))),
      ∃ p : ℕ × Fin 2, p ∈ Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2)) ∧
        ∃ a b : Fin n, e = s(a, b) ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + p.1)).card ∧
          (∀ x12 ∈ PEqualNP.TopForm.orIn n C (n + p.1), G.Adj a x12) ∧
          PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C p.1 p.2) = {b} := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨_, a, b, hab, j, hj, s, h1, h2, h3⟩ := he
    exact ⟨(j, s), by simp [hj], a, b, hab, h1, h2, h3⟩
  choose f hf using key
  have hle := Finset.card_le_card_of_injOn (s := Finset.attach _)
    (t := Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2)))
    (fun e => f e.1 e.2) (fun e _ => (hf e.1 e.2).1) (by
      intro e1 _ e2 _ heq
      obtain ⟨a, b, hab, hc, hadj, hb⟩ := (hf e1.1 e1.2).2
      obtain ⟨a', b', hab', hc', hadj', hb'⟩ := (hf e2.1 e2.2).2
      have heq' : f e1.1 e1.2 = f e2.1 e2.2 := heq
      rw [heq'] at hc hadj hb
      have hbb : b = b' := by
        have := hb.symm.trans hb'
        exact Finset.singleton_injective this
      obtain ⟨c, hcm, d, hdm, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 < (PEqualNP.TopForm.orIn n C (n + (f e2.1 e2.2).1)).card)
      have hcard := hno c d hcd
      have haa : a = a' := by
        refine Finset.card_le_one.mp hcard a ?_ a' ?_
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, (hadj c hcm).symm, (hadj d hdm).symm⟩
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, (hadj' c hcm).symm, (hadj' d hdm).symm⟩
      apply Subtype.ext
      rw [hab, hab', haa, hbb])
  rw [Finset.card_attach, Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin] at hle
  show _ ≤ 2 * C.gates.length
  omega
