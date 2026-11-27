import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6836

theorem pairG (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] :
    (if ¬A then (1 : ℕ) else 0) + (if ¬B then (1 : ℕ) else 0) + (if ¬C ∧ A ∧ B then (1 : ℕ) else 0)
      + (if A ∨ B then (1 : ℕ) else 0) + (if A ∧ B ∧ C then (1 : ℕ) else 0) = 2 := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC]

theorem fin (p0 p1 p2 p4 p5 p6 p7 c14 c25 c67 : Prop) [Decidable p0] [Decidable p1] [Decidable p2]
    [Decidable p4] [Decidable p5] [Decidable p6] [Decidable p7] [Decidable c14] [Decidable c25]
    [Decidable c67] :
    ((((if ¬p0 then (1 : ℕ) else 0) + ((if ¬p1 then (1 : ℕ) else 0) + ((if ¬p2 then (1 : ℕ) else 0)
      + ((if ¬p4 then (1 : ℕ) else 0) + ((if ¬p5 then (1 : ℕ) else 0) + ((if ¬p6 then (1 : ℕ) else 0)
      + (if ¬p7 then (1 : ℕ) else 0)))))))
      + ((if ¬c14 ∧ p1 ∧ p4 then (1 : ℕ) else 0) + ((if ¬c25 ∧ p2 ∧ p5 then (1 : ℕ) else 0)
        + (if ¬c67 ∧ p6 ∧ p7 then (1 : ℕ) else 0)))
      + (if p0 then (1 : ℕ) else 0))
      + ((if p1 ∨ p4 then (1 : ℕ) else 0) + ((if p2 ∨ p5 then (1 : ℕ) else 0)
        + (if p6 ∨ p7 then (1 : ℕ) else 0))))
      + ((if p1 ∧ p4 ∧ c14 then (1 : ℕ) else 0) + ((if p2 ∧ p5 ∧ c25 then (1 : ℕ) else 0)
        + (if p6 ∧ p7 ∧ c67 then (1 : ℕ) else 0))) = 7 := by
  have a := pairG p1 p4 c14
  have b := pairG p2 p5 c25
  have c := pairG p6 p7 c67
  have d : (if ¬p0 then (1 : ℕ) else 0) + (if p0 then (1 : ℕ) else 0) = 1 := by
    by_cases h : p0 <;> simp [h]
  omega

theorem sum7 (f : Fin 11 → ℕ) :
    ∑ a ∈ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)), f a
      = f 0 + (f 1 + (f 2 + (f 4 + (f 5 + (f 6 + f 7))))) := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem sum3 (f : Fin 11 × Fin 11 → ℕ) :
    ∑ a ∈ ({((1 : Fin 11), (4 : Fin 11)), ((2 : Fin 11), (5 : Fin 11)),
      ((6 : Fin 11), (7 : Fin 11))} : Finset (Fin 11 × Fin 11)), f a
      = f (1, 4) + (f (2, 5) + f (6, 7)) := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]

end PEqualNP.Outside.L_meta_6836

theorem PEqualNP.Outside.L_meta_6836 : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : Finset (Sym2 (Fin (11 : ℕ)))),   have x4 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};   have x5 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};   (∀ x6 ∈ x5, x1.Adj x6.1 x6.2) →     let x7 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x3;     have x8 : Finset (Fin (11 : ℕ)) := {x8 ∈ Finset.univ \ x4 | ∃ x9 ∈ x4, x7.Adj x9 x8};     let x9 : Fin (11 : ℕ) → Prop := fun (x9 : Fin (11 : ℕ)) => ∀ x10 ∈ x4, x1.Adj x10 x9 → s(x10, x9) ∈ x3;     (x8.card + {x10 ∈ x5 | x7.Adj x10.1 x10.2 ∧ x10.1 ∉ x8 ∧ x10.2 ∉ x8}.card + if x9 (0 : Fin (11 : ℕ)) then (1 : ℕ) else (0 : ℕ)) + {x10 ∈ x5 | x9 x10.1 ∨ x9 x10.2}.card + {x10 ∈ x5 | x9 x10.1 ∧ x9 x10.2 ∧ s(x10.1, x10.2) ∈ x3}.card = (7 : ℕ) := by
  intro x1 x2 x3
  dsimp only
  intro h
  have h14 : x1.Adj 1 4 := h (1, 4) (by decide)
  have h25 : x1.Adj 2 5 := h (2, 5) (by decide)
  have h67 : x1.Adj 6 7 := h (6, 7) (by decide)
  have hadj : ∀ u v : Fin 11, (x1.deleteEdges (↑x3 : Set (Sym2 (Fin 11)))).Adj u v
      ↔ x1.Adj u v ∧ s(u, v) ∉ x3 := by
    intro u v
    simp [SimpleGraph.deleteEdges_adj]
  have hT : ∀ v : Fin 11, v ∈ (Finset.univ \ {3, 8, 9, 10} : Finset (Fin 11))
      ↔ v ∈ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)) := by decide
  have hX8 : {x8 ∈ Finset.univ \ ({3, 8, 9, 10} : Finset (Fin 11)) |
        ∃ x9 ∈ ({3, 8, 9, 10} : Finset (Fin 11)), (x1.deleteEdges (↑x3 : Set (Sym2 (Fin 11)))).Adj x9 x8}
      = {v ∈ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)) |
        ¬ ∀ u ∈ ({3, 8, 9, 10} : Finset (Fin 11)), x1.Adj u v → s(u, v) ∈ x3} := by
    ext v
    simp only [Finset.mem_filter, hT, hadj]
    constructor
    · rintro ⟨hv, u, hu, h1, h2⟩
      exact ⟨hv, fun H => h2 (H u hu h1)⟩
    · rintro ⟨hv, H⟩
      simp only [not_forall] at H
      obtain ⟨u, hu, h1, h2⟩ := H
      exact ⟨hv, u, hu, h1, h2⟩
  have m1 : (1 : Fin 11) ∈ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)) := by decide
  have m2 : (2 : Fin 11) ∈ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)) := by decide
  have m4 : (4 : Fin 11) ∈ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)) := by decide
  have m5 : (5 : Fin 11) ∈ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)) := by decide
  have m6 : (6 : Fin 11) ∈ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)) := by decide
  have m7 : (7 : Fin 11) ∈ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)) := by decide
  rw [hX8]
  simp only [Finset.card_filter]
  rw [PEqualNP.Outside.L_meta_6836.sum7, PEqualNP.Outside.L_meta_6836.sum3, PEqualNP.Outside.L_meta_6836.sum3, PEqualNP.Outside.L_meta_6836.sum3]
  simp only [Finset.mem_filter, hadj, h14, h25, h67, m1, m2, m4, m5, m6, m7, true_and, not_not]
  convert PEqualNP.Outside.L_meta_6836.fin
    (∀ u ∈ ({3, 8, 9, 10} : Finset (Fin 11)), x1.Adj u 0 → s(u, 0) ∈ x3)
    (∀ u ∈ ({3, 8, 9, 10} : Finset (Fin 11)), x1.Adj u 1 → s(u, 1) ∈ x3)
    (∀ u ∈ ({3, 8, 9, 10} : Finset (Fin 11)), x1.Adj u 2 → s(u, 2) ∈ x3)
    (∀ u ∈ ({3, 8, 9, 10} : Finset (Fin 11)), x1.Adj u 4 → s(u, 4) ∈ x3)
    (∀ u ∈ ({3, 8, 9, 10} : Finset (Fin 11)), x1.Adj u 5 → s(u, 5) ∈ x3)
    (∀ u ∈ ({3, 8, 9, 10} : Finset (Fin 11)), x1.Adj u 6 → s(u, 6) ∈ x3)
    (∀ u ∈ ({3, 8, 9, 10} : Finset (Fin 11)), x1.Adj u 7 → s(u, 7) ∈ x3)
    (s((1 : Fin 11), (4 : Fin 11)) ∈ x3) (s((2 : Fin 11), (5 : Fin 11)) ∈ x3)
    (s((6 : Fin 11), (7 : Fin 11)) ∈ x3)
