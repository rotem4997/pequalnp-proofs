import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_1768_1
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → IsAO2 n C →
      (G.edgeFinset.filter fun e ↦
        ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
          u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
          (u ∈ side C g 0 ∨ v ∈ side C g 0) ∧
          (u ∈ side C g 1 ∨ v ∈ side C g 1)).card ≤ 27 * C.size)
    (h2 : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter fun e ↦
        (∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
          u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
          gateVal n C g (pairInput u v) = true) ∧
        ¬ (∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
          u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
          (u ∈ side C g 0 ∨ v ∈ side C g 0) ∧
          (u ∈ side C g 1 ∨ v ∈ side C g 1))).card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  obtain ⟨k, hk⟩ := h2
  refine ⟨27 + k, ?_⟩
  intro n G inst C hg hL hT
  let exposedWitness (e : Sym2 (Fin n)) : Prop :=
    ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
          u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
          (u ∈ side C g 0 ∨ v ∈ side C g 0) ∧
          (u ∈ side C g 1 ∨ v ∈ side C g 1)
  let targetWitness (e : Sym2 (Fin n)) : Prop :=
    ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
          u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
          gateVal n C g (pairInput u v) = true
  let exposedSet := G.edgeFinset.filter exposedWitness
  let targetSet := (Ustar G C).filter targetWitness
  let residualSet := (Ustar G C).filter fun e ↦ targetWitness e ∧ ¬ exposedWitness e
  change targetSet.card ≤ (27 + k) * (C.size + 1)
  have hsub : targetSet ⊆ exposedSet ∪ residualSet := by
    intro e he
    change e ∈ (Ustar G C).filter targetWitness at he
    obtain ⟨heU, htarget⟩ := Finset.mem_filter.mp he
    have heG : e ∈ G.edgeFinset :=
      (Finset.sdiff_subset : Ustar G C ⊆ G.edgeFinset) heU
    by_cases hexp : exposedWitness e
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heG, hexp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heU, htarget, hexp⟩)
  have h1c : exposedSet.card ≤ 27 * C.size := h1 n G C hg hL.1
  have h2c : residualSet.card ≤ k * (C.size + 1) := hk n G C hg hL hT
  calc
    targetSet.card ≤ (exposedSet ∪ residualSet).card := Finset.card_le_card hsub
    _ ≤ exposedSet.card + residualSet.card := Finset.card_union_le _ _
    _ ≤ 27 * C.size + k * (C.size + 1) := Nat.add_le_add h1c h2c
    _ ≤ 27 * (C.size + 1) + k * (C.size + 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 27 (Nat.le_succ C.size)) _
    _ = (27 + k) * (C.size + 1) := (Nat.add_mul _ _ _).symm
