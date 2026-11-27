import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8421

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8421

theorem PEqualNP.Outside.L_meta_8421 : let x1 : Type := Fin (21 : ℕ); have x2 : x1 → Finset x1 := fun (x2 : x1) => {x3 : x1 | (↑x2 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]}; have x3 : (Fin (42 : ℕ) → Bool) → Prop := fun (x3 : Fin (42 : ℕ) → Bool) => ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true; ∀ (x4 : Fin (42 : ℕ) → Bool),   ¬x3 x4 →     (∀ (x6 : Fin (42 : ℕ) → Bool), (∀ (x7 : Fin (42 : ℕ)), x4 x7 = Bool.true → x6 x7 = Bool.true) → ¬x3 x6 → x6 = x4) →       ∃ (x7 : Finset x1),         have x8 : Finset (Fin (21 : ℕ)) := PEqualNP.HeptadCover.missLines x2 x7;         PEqualNP.GenericRejection.zeroSet x2 x8 = x7 ∧ List.ofFn x4 = PEqualNP.GenericRejection.incidenceInput x7 x8 := by
  intro X S F x hx hmax
  classical
  have up : ∀ i : Fin 42, (∀ p l : Fin 42, ((p : ℕ) < 21 ∧ 21 ≤ (l : ℕ) ∧ ((l : ℕ) + 21 - (p : ℕ)) % 21 ∈ [0, 5, 7, 17, 20]) → Function.update x i true p = true → Function.update x i true l = true → False) → x i = true := by
    intro i h
    have := hmax (Function.update x i true) (by
      intro j hj
      by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji]; exact hj) (by rintro ⟨p, l, h1, h2, h3⟩; exact h p l h1 h2 h3)
    rw [← this]; simp
  have inc : ∀ p l : Fin 21, p ∈ S l ↔ ((l : ℕ) + 21 - (p : ℕ)) % 21 ∈ [0, 5, 7, 17, 20] := by
    intro p l
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have edge : ∀ p l : Fin 21, p ∈ S l → x (Fin.castAdd 21 p) = true → x (Fin.natAdd 21 l) = true → False := by
    intro p l h h1 h2
    refine hx ⟨Fin.castAdd 21 p, Fin.natAdd 21 l, ⟨by simp, by simp, ?_⟩, h1, h2⟩
    have := (inc p l).1 h
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    have e : (21 + (l : ℕ) + 21 - (p : ℕ)) % 21 = ((l : ℕ) + 21 - (p : ℕ)) % 21 := by have := p.isLt; omega
    rw [e]; exact this
  have dec : ∀ p l : Fin 42, ((p : ℕ) < 21 ∧ 21 ≤ (l : ℕ) ∧ ((l : ℕ) + 21 - (p : ℕ)) % 21 ∈ [0, 5, 7, 17, 20]) → ∃ p' l' : Fin 21, p = Fin.castAdd 21 p' ∧ l = Fin.natAdd 21 l' ∧ p' ∈ S l' := by
    rintro p l ⟨h1, h2, h3⟩
    refine ⟨⟨p, h1⟩, ⟨(l : ℕ) - 21, by have := l.isLt; omega⟩, Fin.ext rfl, Fin.ext (by simp only [Fin.val_natAdd]; omega), ?_⟩
    rw [inc]
    have e : ((l : ℕ) - 21 + 21 - (p : ℕ)) % 21 = ((l : ℕ) + 21 - (p : ℕ)) % 21 := by omega
    simp only [e]; exact h3
  have ne1 : ∀ p l : Fin 21, (Fin.castAdd 21 p : Fin 42) ≠ Fin.natAdd 21 l := by
    intro p l e
    have := congrArg Fin.val e
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := p.isLt
    omega
  let A : Finset (Fin 21) := Finset.univ.filter fun p => x (Fin.castAdd 21 p) = true
  have hA : ∀ p, p ∈ A ↔ x (Fin.castAdd 21 p) = true := by intro p; simp [A]
  have hM : ∀ l, l ∈ PEqualNP.HeptadCover.missLines S A ↔ x (Fin.natAdd 21 l) = true := by
    intro l
    simp only [PEqualNP.HeptadCover.missLines, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hd
      refine up _ fun p l' h h1 h2 => ?_
      obtain ⟨p', l'', rfl, rfl, hpl⟩ := dec p l' h
      rw [Function.update_of_ne (ne1 p' l)] at h1
      by_cases hll : l'' = l
      · subst hll
        exact Finset.disjoint_left.1 hd hpl ((hA p').2 h1)
      · have hne : (Fin.natAdd 21 l'' : Fin 42) ≠ Fin.natAdd 21 l := fun e => hll (Fin.natAdd_injective _ _ e)
        rw [Function.update_of_ne hne] at h2
        exact edge p' l'' hpl h1 h2
    · intro h
      rw [Finset.disjoint_left]
      intro p hp hpA
      exact edge p l hp ((hA p).1 hpA) h
  refine ⟨A, ?_, ?_⟩
  · ext p
    rw [hA]
    simp only [PEqualNP.GenericRejection.zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine up _ fun p' l' hpl h1 h2 => ?_
      obtain ⟨p'', l, rfl, rfl, hin⟩ := dec p' l' hpl
      rw [Function.update_of_ne (fun e => ne1 p l e.symm)] at h2
      by_cases hpp : p'' = p
      · subst hpp
        exact h l ((hM l).2 h2) hin
      · have hne : (Fin.castAdd 21 p'' : Fin 42) ≠ Fin.castAdd 21 p := fun e => hpp (Fin.castAdd_injective _ _ e)
        rw [Function.update_of_ne hne] at h1
        exact edge p'' l hin h1 h2
    · intro hp l hl hin
      exact edge p l hin hp ((hM l).1 hl)
  · unfold PEqualNP.GenericRejection.incidenceInput
    rw [← List.ofFn_fin_append]
    congr 1
    funext i
    refine Fin.addCases (m := 21) (n := 21) (motive := fun i => x i = Fin.append (fun p : Fin 21 => decide (p ∈ A)) (fun l : Fin 21 => decide (l ∈ PEqualNP.HeptadCover.missLines S A)) i) (fun p => ?_) (fun l => ?_) i
    · rw [Fin.append_left]
      cases h : x (Fin.castAdd 21 p)
      · symm; rw [decide_eq_false_iff_not, hA, h]; simp
      · symm; rw [decide_eq_true_eq, hA, h]
    · rw [Fin.append_right]
      cases h : x (Fin.natAdd 21 l)
      · symm; rw [decide_eq_false_iff_not, hM, h]; simp
      · symm; rw [decide_eq_true_eq, hM, h]
