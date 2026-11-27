import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3523

private def left (m : ℕ) {n : ℕ} (a : Fin n) : Fin (n + m) := Fin.castAdd m a
private def right (n : ℕ) {m : ℕ} (b : Fin m) : Fin (n + m) := Fin.natAdd n b

private lemma disjoint_lr {n m : ℕ} (a : Fin n) (b : Fin m) : left m a ≠ right n b := by
  intro h
  have h' := congrArg Fin.val h
  simp only [left, right, Fin.val_castAdd, Fin.val_natAdd] at h'
  have := a.isLt
  omega

private def graph (n m : ℕ) (E : Finset (Fin n × Fin m)) : SimpleGraph (Fin (n + m)) where
  Adj := fun u v => ∃ p ∈ E, u = left m p.1 ∧ v = right n p.2 ∨ v = left m p.1 ∧ u = right n p.2
  symm := ⟨by intro u v; rintro ⟨p, hp, h | h⟩; exact ⟨p, hp, Or.inr h⟩; exact ⟨p, hp, Or.inl h⟩⟩
  loopless := ⟨by
    intro u
    rintro ⟨p, hp, h | h⟩
    · exact disjoint_lr p.1 p.2 (h.1.symm.trans h.2)
    · exact disjoint_lr p.1 p.2 (h.1.symm.trans h.2)⟩

private def edge {n m : ℕ} (p : Fin n × Fin m) : Sym2 (Fin (n+m)) :=
  s(left m p.1, right n p.2)

private lemma edge_injective {n m : ℕ} : Function.Injective (@edge n m) := by
  intro p q h
  rcases Sym2.eq_iff.mp h with h | h
  · apply Prod.ext
    · apply Fin.ext
      simpa [left] using congrArg Fin.val h.1
    · apply Fin.ext
      have hh := congrArg Fin.val h.2
      simp [right] at hh
      omega
  · exact (disjoint_lr p.1 q.2 h.1).elim

private lemma edges (n m : ℕ) (E : Finset (Fin n × Fin m)) :
    (graph n m E).edgeSet = ↑(E.image edge) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeSet, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨p, hp, h | h⟩
      · exact ⟨p, hp, by simp [edge, ← h.1, ← h.2]⟩
      · exact ⟨p, hp, by simp [edge, ← h.1, ← h.2, Sym2.eq_swap]⟩
    · rintro ⟨p, hp, he⟩
      rcases Sym2.eq_iff.mp he with h | h
      · exact ⟨p, hp, Or.inl ⟨h.1.symm, h.2.symm⟩⟩
      · exact ⟨p, hp, Or.inr ⟨h.1.symm, h.2.symm⟩⟩

end PEqualNP.Outside.L_meta_3523

theorem PEqualNP.Outside.L_meta_3523 : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)), x4 ⊆ x3 → (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6.1 = x8.1 → x6 = x8) → (∀ x7 ∈ x4, ∀ x9 ∈ x4, x7.2 = x9.2 → x7 = x9) → ∃ (x8 : SimpleGraph (Fin (x1 + x2))), (∀ (x9 x10 : Fin (x1 + x2)), x8.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) ∧ x8.edgeSet.ncard = x3.card ∧ ∀ (x9 : Finset (Fin (x1 + x2))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x8 x9 → x4.card ≤ x9.card := by
  classical
  intro n m E M hME hleft hright
  let G := PEqualNP.Outside.L_meta_3523.graph n m E
  refine ⟨G, ?_, ?_, ?_⟩
  · intro u v
    rfl
  · rw [PEqualNP.Outside.L_meta_3523.edges, Set.ncard_coe_finset]
    exact Finset.card_image_iff.mpr PEqualNP.Outside.L_meta_3523.edge_injective.injOn
  · intro S hS
    let f : Fin n × Fin m → Fin (n+m) := fun p =>
      if PEqualNP.Outside.L_meta_3523.left m p.1 ∈ S then PEqualNP.Outside.L_meta_3523.left m p.1 else PEqualNP.Outside.L_meta_3523.right n p.2
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      have hadj : G.Adj (PEqualNP.Outside.L_meta_3523.left m p.1) (PEqualNP.Outside.L_meta_3523.right n p.2) :=
        ⟨p, hME hp, Or.inl ⟨rfl, rfl⟩⟩
      have hc := hS _ _ hadj
      dsimp [f]
      split_ifs <;> tauto
    · intro p hp q hq he
      dsimp [f] at he
      split_ifs at he with hpS hqS
      · apply hleft p hp q hq
        apply Fin.ext
        simpa [PEqualNP.Outside.L_meta_3523.left] using congrArg Fin.val he
      · exact (PEqualNP.Outside.L_meta_3523.disjoint_lr p.1 q.2 he).elim
      · exact (PEqualNP.Outside.L_meta_3523.disjoint_lr q.1 p.2 he.symm).elim
      · apply hright p hp q hq
        apply Fin.ext
        have hh := congrArg Fin.val he
        simp [PEqualNP.Outside.L_meta_3523.right] at hh
        omega
