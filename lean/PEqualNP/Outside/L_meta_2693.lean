import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2693

open PEqualNP.EdgeOwnership

def El : List (ℕ × ℕ) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8),
  (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

-- a set of vertices covers every listed edge
abbrev cov (T : Finset (Fin 11)) : Prop :=
  ∀ e ∈ El, (∃ v ∈ T, v.val = e.1) ∨ (∃ v ∈ T, v.val = e.2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tau_dec : ∀ T : Finset (Fin 11), ¬ (T.card ≤ 6 ∧ cov T) := by
  decide +kernel

theorem tau (T : Finset (Fin 11)) (h : cov T) : 7 ≤ T.card := by
  by_contra hc
  exact tau_dec T ⟨by omega, h⟩

theorem hEl : ∀ e ∈ El, e.1 < 11 ∧ e.2 < 11 ∧ e.1 ≠ e.2 := by decide

theorem main : ∀ (D : Finset (Sym2 (Fin 11))) (S : Finset (Fin 11)),
    ((edgeGraph 11 El).deleteEdges ↑D).IsVertexCover ↑S → 7 ≤ S.card + D.card := by
  intro D S hS
  classical
  let T : Finset (Fin 11) := S ∪ D.image (fun e => (Quot.out e).1)
  have hT : cov T := by
    intro e he
    obtain ⟨h1, h2, h3⟩ := hEl e he
    let a : Fin 11 := ⟨e.1, h1⟩
    let b : Fin 11 := ⟨e.2, h2⟩
    have hab : (edgeGraph 11 El).Adj a b := by
      refine ⟨fun h => h3 (congrArg Fin.val h), Or.inl ?_⟩
      exact he
    by_cases hd : s(a, b) ∈ D
    · -- the chosen endpoint of this deleted edge is in T
      obtain ⟨p, hp⟩ : ∃ p : Fin 11 × Fin 11, p = Quot.out (s(a, b) : Sym2 (Fin 11)) := ⟨_, rfl⟩
      have hq : s(p.1, p.2) = s(a, b) := by
        rw [hp]; exact Quot.out_eq (s(a, b) : Sym2 (Fin 11))
      have hmem : p.1 ∈ T :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hd, by rw [hp]⟩)
      rcases Sym2.eq_iff.mp hq with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl ⟨_, hmem, by rw [h]⟩
      · exact Or.inr ⟨_, hmem, by rw [h]⟩
    · have hadj : ((edgeGraph 11 El).deleteEdges ↑D).Adj a b :=
        (SimpleGraph.deleteEdges_adj).mpr ⟨hab, hd⟩
      rcases hS hadj with h | h
      · exact Or.inl ⟨a, Finset.mem_union_left _ h, rfl⟩
      · exact Or.inr ⟨b, Finset.mem_union_left _ h, rfl⟩
  have h7 := tau T hT
  have hc : T.card ≤ S.card + D.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  omega

end PEqualNP.Outside.L_meta_2693

theorem PEqualNP.Outside.L_meta_2693 : have x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Finset (Sym2 (Fin (11 : ℕ)))) (x3 : Finset (Fin (11 : ℕ))), (x1.deleteEdges ↑x2).IsVertexCover ↑x3 → (7 : ℕ) ≤ x3.card + x2.card :=
  PEqualNP.Outside.L_meta_2693.main
