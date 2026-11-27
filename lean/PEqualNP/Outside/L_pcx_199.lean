import Mathlib
import PEqualNP.Defs

-- An explicit Res(2) refutation (138 lines), checked by a verified checker (chkK, chkK_sound) run in the kernel.

namespace PEqualNP.Outside.L_pcx_199_aux

open PEqualNP.ProofComplexity

theorem memD {α : Type} (l : List α) (d : α) (i : ℕ) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

-- Res(k) lines, newest first; premises are entries i, j of the tail
inductive KStep (V : Type) where
  | ax : Clause V → KStep V
  | wk : ℕ → KStep V
  | ai : ℕ → ℕ → KTerm V → KTerm V → KStep V
  | ae : ℕ → KTerm V → KTerm V → KStep V
  | cut : ℕ → ℕ → KTerm V → KStep V

def chkK {V : Type} [DecidableEq V] (k : ℕ) (ax : Clause V → Bool) :
    List (KLine V × KStep V) → Bool
  | [] => true
  | (R, .ax C) :: t => ax C && decide (kLineOfClause C = R) && decide (∀ T ∈ R, T.card ≤ k) && chkK k ax t
  | (R, .wk i) :: t => decide (i < t.length) && decide ((t.map Prod.fst).getD i ∅ ⊆ R) &&
      decide (∀ T ∈ R, T.card ≤ k) && chkK k ax t
  | (R, .ai i j T₁ T₂) :: t => decide (i < t.length) && decide (j < t.length) &&
      decide (T₁ ∈ (t.map Prod.fst).getD i ∅ ∧ T₂ ∈ (t.map Prod.fst).getD j ∅ ∧
        R = (((t.map Prod.fst).getD i ∅).erase T₁ ∪ ((t.map Prod.fst).getD j ∅).erase T₂) ∪ {T₁ ∪ T₂}) &&
      decide (∀ T ∈ R, T.card ≤ k) && chkK k ax t
  | (R, .ae i T T') :: t => decide (i < t.length) &&
      decide (T ∈ (t.map Prod.fst).getD i ∅ ∧ T' ⊆ T ∧ T'.Nonempty ∧
        R = ((t.map Prod.fst).getD i ∅).erase T ∪ {T'}) && chkK k ax t
  | (R, .cut i j T) :: t => decide (i < t.length) && decide (j < t.length) &&
      decide (T ∈ (t.map Prod.fst).getD i ∅ ∧ T.Nonempty ∧
        (∀ l ∈ T, ({(l.1, !l.2)} : KTerm V) ∈ (t.map Prod.fst).getD j ∅) ∧
        R = ((t.map Prod.fst).getD i ∅).erase T ∪
          ((t.map Prod.fst).getD j ∅ \ T.image (fun l => ({(l.1, !l.2)} : KTerm V)))) && chkK k ax t

theorem chkK_sound {V : Type} [DecidableEq V] (k : ℕ) (F : Set (Clause V)) (ax : Clause V → Bool)
    (hax : ∀ C, ax C = true → C ∈ F) :
    ∀ l, chkK k ax l = true → IsResKDerivation k ((fun C => kLineOfClause C) '' F) (l.map Prod.fst)
  | [], _ => IsResKDerivation.nil
  | (R, .ax C) :: t, h => by
    simp only [chkK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, ht⟩ := h
    exact IsResKDerivation.ax (chkK_sound k F ax hax t ht) ⟨C, hax C h1, h2⟩ h3
  | (R, .wk i) :: t, h => by
    simp only [chkK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, h1⟩, h2⟩, ht⟩ := h
    exact IsResKDerivation.weak (chkK_sound k F ax hax t ht) (memD _ _ _ (by simpa using hi)) h1 h2
  | (R, .ai i j T₁ T₂) :: t, h => by
    simp only [chkK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hi, hj⟩, h1, h2, h3⟩, h4⟩, ht⟩ := h
    exact IsResKDerivation.andIntro (chkK_sound k F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (memD _ _ _ (by simpa using hj)) ⟨T₁, T₂, h1, h2, h3⟩ h4
  | (R, .ae i T T') :: t, h => by
    simp only [chkK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h1, h2, h3, h4⟩, ht⟩ := h
    exact IsResKDerivation.andElim (chkK_sound k F ax hax t ht) (memD _ _ _ (by simpa using hi))
      ⟨T, T', h1, h2, h3, h4⟩
  | (R, .cut i j T) :: t, h => by
    simp only [chkK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, h1, h2, h3, h4⟩, ht⟩ := h
    exact IsResKDerivation.cut (chkK_sound k F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (memD _ _ _ (by simpa using hj)) ⟨T, h1, h2, h3, h4⟩

def axPHP (m n : ℕ) (C : Clause (Fin m × Fin n)) : Bool :=
  decide (∃ i : Fin m, C = Finset.univ.image (fun j : Fin n => ((i, j), true))) ||
  decide (∃ i : Fin m, ∃ i' : Fin m, ∃ j : Fin n, i ≠ i' ∧ C = {((i, j), false), ((i', j), false)})

theorem axPHP_sound (m n : ℕ) : ∀ C, axPHP m n C = true → C ∈ PHP m n := by
  intro C h
  simp only [axPHP, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨i, hi⟩ | ⟨i, i', j, hne, hC⟩
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr ⟨i, i', j, hne, hC⟩

def cert : List (KLine (Fin 5 × Fin 4) × KStep (Fin 5 × Fin 4)) := [
  (∅, .cut 8 0 {((4, 3), true)}),
  ({{((4, 3), false)}}, .cut 0 3 {((2, 3), false), ((3, 3), false)}),
  ({{((2, 3), false), ((3, 3), false)}, {((4, 3), false)}}, .ai 1 0 {((2, 3), false)} {((3, 3), false)}),
  ({{((3, 3), false)}, {((4, 3), false)}}, .ax {((3, 3), false), ((4, 3), false)}),
  ({{((2, 3), false)}, {((4, 3), false)}}, .ax {((2, 3), false), ((4, 3), false)}),
  ({{((2, 3), true)}, {((3, 3), true)}, {((4, 3), false)}}, .cut 0 31 {((0, 3), false), ((1, 3), false)}),
  ({{((0, 3), false), ((1, 3), false)}, {((4, 3), false)}}, .ai 1 0 {((0, 3), false)} {((1, 3), false)}),
  ({{((1, 3), false)}, {((4, 3), false)}}, .ax {((1, 3), false), ((4, 3), false)}),
  ({{((0, 3), false)}, {((4, 3), false)}}, .ax {((0, 3), false), ((4, 3), false)}),
  ({{((4, 3), true)}}, .cut 8 0 {((4, 2), true)}),
  ({{((4, 2), false)}}, .cut 0 3 {((2, 2), false), ((3, 2), false)}),
  ({{((2, 2), false), ((3, 2), false)}, {((4, 2), false)}}, .ai 1 0 {((2, 2), false)} {((3, 2), false)}),
  ({{((3, 2), false)}, {((4, 2), false)}}, .ax {((3, 2), false), ((4, 2), false)}),
  ({{((2, 2), false)}, {((4, 2), false)}}, .ax {((2, 2), false), ((4, 2), false)}),
  ({{((2, 2), true)}, {((3, 2), true)}, {((4, 2), false)}}, .cut 0 31 {((0, 2), false), ((1, 2), false)}),
  ({{((0, 2), false), ((1, 2), false)}, {((4, 2), false)}}, .ai 1 0 {((0, 2), false)} {((1, 2), false)}),
  ({{((1, 2), false)}, {((4, 2), false)}}, .ax {((1, 2), false), ((4, 2), false)}),
  ({{((0, 2), false)}, {((4, 2), false)}}, .ax {((0, 2), false), ((4, 2), false)}),
  ({{((4, 2), true)}, {((4, 3), true)}}, .cut 8 0 {((4, 1), true)}),
  ({{((4, 1), false)}}, .cut 0 3 {((2, 1), false), ((3, 1), false)}),
  ({{((2, 1), false), ((3, 1), false)}, {((4, 1), false)}}, .ai 1 0 {((2, 1), false)} {((3, 1), false)}),
  ({{((3, 1), false)}, {((4, 1), false)}}, .ax {((3, 1), false), ((4, 1), false)}),
  ({{((2, 1), false)}, {((4, 1), false)}}, .ax {((2, 1), false), ((4, 1), false)}),
  ({{((2, 1), true)}, {((3, 1), true)}, {((4, 1), false)}}, .cut 0 31 {((0, 1), false), ((1, 1), false)}),
  ({{((0, 1), false), ((1, 1), false)}, {((4, 1), false)}}, .ai 1 0 {((0, 1), false)} {((1, 1), false)}),
  ({{((1, 1), false)}, {((4, 1), false)}}, .ax {((1, 1), false), ((4, 1), false)}),
  ({{((0, 1), false)}, {((4, 1), false)}}, .ax {((0, 1), false), ((4, 1), false)}),
  ({{((4, 1), true)}, {((4, 2), true)}, {((4, 3), true)}}, .cut 8 0 {((4, 0), true)}),
  ({{((4, 0), false)}}, .cut 0 3 {((2, 0), false), ((3, 0), false)}),
  ({{((2, 0), false), ((3, 0), false)}, {((4, 0), false)}}, .ai 1 0 {((2, 0), false)} {((3, 0), false)}),
  ({{((3, 0), false)}, {((4, 0), false)}}, .ax {((3, 0), false), ((4, 0), false)}),
  ({{((2, 0), false)}, {((4, 0), false)}}, .ax {((2, 0), false), ((4, 0), false)}),
  ({{((2, 0), true)}, {((3, 0), true)}, {((4, 0), false)}}, .cut 0 35 {((0, 0), false), ((1, 0), false)}),
  ({{((0, 0), false), ((1, 0), false)}, {((4, 0), false)}}, .ai 1 0 {((0, 0), false)} {((1, 0), false)}),
  ({{((1, 0), false)}, {((4, 0), false)}}, .ax {((1, 0), false), ((4, 0), false)}),
  ({{((0, 0), false)}, {((4, 0), false)}}, .ax {((0, 0), false), ((4, 0), false)}),
  ({{((4, 0), true)}, {((4, 1), true)}, {((4, 2), true)}, {((4, 3), true)}}, .ax {((4, 0), true), ((4, 1), true), ((4, 2), true), ((4, 3), true)}),
  ({{((0, 3), true)}, {((1, 3), true)}, {((2, 3), true)}, {((3, 3), true)}}, .cut 2 0 {((3, 2), true)}),
  ({{((0, 3), true)}, {((1, 3), true)}, {((2, 3), true)}, {((3, 2), false)}}, .cut 0 38 {((2, 2), true)}),
  ({{((0, 3), true)}, {((1, 3), true)}, {((2, 2), true)}, {((2, 3), true)}, {((3, 2), false)}}, .cut 39 50 {((0, 2), false), ((1, 2), false)}),
  ({{((0, 3), true)}, {((1, 3), true)}, {((2, 3), true)}, {((3, 2), true)}, {((3, 3), true)}}, .cut 2 0 {((3, 1), true)}),
  ({{((0, 3), true)}, {((1, 3), true)}, {((2, 3), true)}, {((3, 1), false)}}, .cut 0 42 {((2, 1), true)}),
  ({{((0, 3), true)}, {((1, 3), true)}, {((2, 1), true)}, {((2, 3), true)}, {((3, 1), false)}}, .cut 43 50 {((0, 1), false), ((1, 1), false)}),
  ({{((0, 3), true)}, {((1, 3), true)}, {((2, 3), true)}, {((3, 1), true)}, {((3, 2), true)}, {((3, 3), true)}}, .cut 45 0 {((3, 0), true)}),
  ({{((0, 3), true)}, {((1, 3), true)}, {((2, 3), true)}, {((3, 0), false)}}, .cut 0 18 {((2, 0), true)}),
  ({{((0, 3), true)}, {((1, 3), true)}, {((2, 0), true)}, {((2, 3), true)}, {((3, 0), false)}}, .cut 19 57 {((0, 0), false), ((1, 0), false)}),
  ({{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((3, 2), true)}}, .cut 2 0 {((3, 3), true)}),
  ({{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((3, 3), false)}}, .cut 0 22 {((2, 3), true)}),
  ({{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((2, 3), true)}, {((3, 3), false)}}, .cut 23 41 {((0, 3), false), ((1, 3), false)}),
  ({{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((3, 2), true)}, {((3, 3), true)}}, .cut 2 0 {((3, 1), true)}),
  ({{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((3, 1), false)}}, .cut 0 33 {((2, 1), true)}),
  ({{((0, 2), true)}, {((1, 2), true)}, {((2, 1), true)}, {((2, 2), true)}, {((3, 1), false)}}, .cut 34 44 {((0, 1), false), ((1, 1), false)}),
  ({{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((3, 1), true)}, {((3, 2), true)}, {((3, 3), true)}}, .cut 36 0 {((3, 0), true)}),
  ({{((0, 2), true)}, {((1, 2), true)}, {((2, 2), true)}, {((3, 0), false)}}, .cut 0 9 {((2, 0), true)}),
  ({{((0, 2), true)}, {((1, 2), true)}, {((2, 0), true)}, {((2, 2), true)}, {((3, 0), false)}}, .cut 10 51 {((0, 0), false), ((1, 0), false)}),
  ({{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((3, 1), true)}}, .cut 2 0 {((3, 3), true)}),
  ({{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((3, 3), false)}}, .cut 0 13 {((2, 3), true)}),
  ({{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((2, 3), true)}, {((3, 3), false)}}, .cut 14 35 {((0, 3), false), ((1, 3), false)}),
  ({{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((3, 1), true)}, {((3, 3), true)}}, .cut 2 0 {((3, 2), true)}),
  ({{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((3, 2), false)}}, .cut 0 17 {((2, 2), true)}),
  ({{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((2, 2), true)}, {((3, 2), false)}}, .cut 18 35 {((0, 2), false), ((1, 2), false)}),
  ({{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((3, 1), true)}, {((3, 2), true)}, {((3, 3), true)}}, .cut 27 0 {((3, 0), true)}),
  ({{((0, 1), true)}, {((1, 1), true)}, {((2, 1), true)}, {((3, 0), false)}}, .cut 1 0 {((2, 0), true)}),
  ({{((2, 0), false)}, {((3, 0), false)}}, .ax {((2, 0), false), ((3, 0), false)}),
  ({{((0, 1), true)}, {((1, 1), true)}, {((2, 0), true)}, {((2, 1), true)}, {((3, 0), false)}}, .cut 0 48 {((0, 0), false), ((1, 0), false)}),
  ({{((0, 0), false), ((1, 0), false)}, {((3, 0), false)}}, .ai 1 0 {((0, 0), false)} {((1, 0), false)}),
  ({{((1, 0), false)}, {((3, 0), false)}}, .ax {((1, 0), false), ((3, 0), false)}),
  ({{((0, 0), false)}, {((3, 0), false)}}, .ax {((0, 0), false), ((3, 0), false)}),
  ({{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((3, 0), true)}}, .cut 6 0 {((3, 3), true)}),
  ({{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((3, 3), false)}}, .cut 1 0 {((2, 3), true)}),
  ({{((2, 3), false)}, {((3, 3), false)}}, .ax {((2, 3), false), ((3, 3), false)}),
  ({{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((2, 3), true)}, {((3, 3), false)}}, .cut 0 31 {((0, 3), false), ((1, 3), false)}),
  ({{((0, 3), false), ((1, 3), false)}, {((3, 3), false)}}, .ai 1 0 {((0, 3), false)} {((1, 3), false)}),
  ({{((1, 3), false)}, {((3, 3), false)}}, .ax {((1, 3), false), ((3, 3), false)}),
  ({{((0, 3), false)}, {((3, 3), false)}}, .ax {((0, 3), false), ((3, 3), false)}),
  ({{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((3, 0), true)}, {((3, 3), true)}}, .cut 6 0 {((3, 2), true)}),
  ({{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((3, 2), false)}}, .cut 1 0 {((2, 2), true)}),
  ({{((2, 2), false)}, {((3, 2), false)}}, .ax {((2, 2), false), ((3, 2), false)}),
  ({{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((2, 2), true)}, {((3, 2), false)}}, .cut 0 27 {((0, 2), false), ((1, 2), false)}),
  ({{((0, 2), false), ((1, 2), false)}, {((3, 2), false)}}, .ai 1 0 {((0, 2), false)} {((1, 2), false)}),
  ({{((1, 2), false)}, {((3, 2), false)}}, .ax {((1, 2), false), ((3, 2), false)}),
  ({{((0, 2), false)}, {((3, 2), false)}}, .ax {((0, 2), false), ((3, 2), false)}),
  ({{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((3, 0), true)}, {((3, 2), true)}, {((3, 3), true)}}, .cut 6 0 {((3, 1), true)}),
  ({{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((3, 1), false)}}, .cut 1 0 {((2, 1), true)}),
  ({{((2, 1), false)}, {((3, 1), false)}}, .ax {((2, 1), false), ((3, 1), false)}),
  ({{((0, 0), true)}, {((1, 0), true)}, {((2, 0), true)}, {((2, 1), true)}, {((3, 1), false)}}, .cut 0 27 {((0, 1), false), ((1, 1), false)}),
  ({{((0, 1), false), ((1, 1), false)}, {((3, 1), false)}}, .ai 1 0 {((0, 1), false)} {((1, 1), false)}),
  ({{((1, 1), false)}, {((3, 1), false)}}, .ax {((1, 1), false), ((3, 1), false)}),
  ({{((0, 1), false)}, {((3, 1), false)}}, .ax {((0, 1), false), ((3, 1), false)}),
  ({{((3, 0), true)}, {((3, 1), true)}, {((3, 2), true)}, {((3, 3), true)}}, .ax {((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)}),
  ({{((0, 2), true)}, {((0, 3), true)}, {((1, 2), true)}, {((1, 3), true)}, {((2, 2), true)}, {((2, 3), true)}}, .cut 0 33 {((0, 1), false), ((1, 1), false)}),
  ({{((0, 1), false), ((1, 1), false)}, {((0, 2), true)}, {((0, 3), true)}, {((1, 2), true)}, {((1, 3), true)}, {((2, 2), true)}, {((2, 3), true)}}, .cut 0 35 {((0, 0), false), ((1, 0), false)}),
  ({{((0, 0), false), ((1, 0), false)}, {((0, 1), false), ((1, 1), false)}, {((2, 2), true)}, {((2, 3), true)}}, .cut 6 17 {((2, 1), true)}),
  ({{((0, 1), true)}, {((0, 3), true)}, {((1, 1), true)}, {((1, 3), true)}, {((2, 1), true)}, {((2, 3), true)}}, .cut 0 30 {((0, 2), false), ((1, 2), false)}),
  ({{((0, 1), true)}, {((0, 2), false), ((1, 2), false)}, {((0, 3), true)}, {((1, 1), true)}, {((1, 3), true)}, {((2, 1), true)}, {((2, 3), true)}}, .cut 0 35 {((0, 0), false), ((1, 0), false)}),
  ({{((0, 0), false), ((1, 0), false)}, {((0, 2), false), ((1, 2), false)}, {((2, 1), true)}, {((2, 3), true)}}, .cut 3 24 {((2, 2), true)}),
  ({{((0, 1), true)}, {((0, 2), true)}, {((1, 1), true)}, {((1, 2), true)}, {((2, 1), true)}, {((2, 2), true)}}, .cut 0 27 {((0, 3), false), ((1, 3), false)}),
  ({{((0, 1), true)}, {((0, 2), true)}, {((0, 3), false), ((1, 3), false)}, {((1, 1), true)}, {((1, 2), true)}, {((2, 1), true)}, {((2, 2), true)}}, .cut 0 35 {((0, 0), false), ((1, 0), false)}),
  ({{((0, 0), false), ((1, 0), false)}, {((0, 3), false), ((1, 3), false)}, {((2, 1), true)}, {((2, 2), true)}}, .cut 0 17 {((2, 3), true)}),
  ({{((0, 0), false), ((1, 0), false)}, {((2, 1), true)}, {((2, 2), true)}, {((2, 3), true)}}, .cut 23 0 {((2, 0), true)}),
  ({{((0, 0), false), ((1, 0), false)}, {((2, 0), false)}}, .ai 1 0 {((0, 0), false)} {((1, 0), false)}),
  ({{((1, 0), false)}, {((2, 0), false)}}, .ax {((1, 0), false), ((2, 0), false)}),
  ({{((0, 0), false)}, {((2, 0), false)}}, .ax {((0, 0), false), ((2, 0), false)}),
  ({{((0, 0), true)}, {((0, 3), true)}, {((1, 0), true)}, {((1, 3), true)}, {((2, 0), true)}, {((2, 3), true)}}, .cut 0 23 {((0, 2), false), ((1, 2), false)}),
  ({{((0, 0), true)}, {((0, 2), false), ((1, 2), false)}, {((0, 3), true)}, {((1, 0), true)}, {((1, 3), true)}, {((2, 0), true)}, {((2, 3), true)}}, .cut 0 25 {((0, 1), false), ((1, 1), false)}),
  ({{((0, 1), false), ((1, 1), false)}, {((0, 2), false), ((1, 2), false)}, {((2, 0), true)}, {((2, 3), true)}}, .cut 3 14 {((2, 2), true)}),
  ({{((0, 0), true)}, {((0, 2), true)}, {((1, 0), true)}, {((1, 2), true)}, {((2, 0), true)}, {((2, 2), true)}}, .cut 0 20 {((0, 3), false), ((1, 3), false)}),
  ({{((0, 0), true)}, {((0, 2), true)}, {((0, 3), false), ((1, 3), false)}, {((1, 0), true)}, {((1, 2), true)}, {((2, 0), true)}, {((2, 2), true)}}, .cut 0 25 {((0, 1), false), ((1, 1), false)}),
  ({{((0, 1), false), ((1, 1), false)}, {((0, 3), false), ((1, 3), false)}, {((2, 0), true)}, {((2, 2), true)}}, .cut 0 7 {((2, 3), true)}),
  ({{((0, 1), false), ((1, 1), false)}, {((2, 0), true)}, {((2, 2), true)}, {((2, 3), true)}}, .cut 13 0 {((2, 1), true)}),
  ({{((0, 1), false), ((1, 1), false)}, {((2, 1), false)}}, .ai 1 0 {((0, 1), false)} {((1, 1), false)}),
  ({{((1, 1), false)}, {((2, 1), false)}}, .ax {((1, 1), false), ((2, 1), false)}),
  ({{((0, 1), false)}, {((2, 1), false)}}, .ax {((0, 1), false), ((2, 1), false)}),
  ({{((0, 0), true)}, {((0, 1), true)}, {((1, 0), true)}, {((1, 1), true)}, {((2, 0), true)}, {((2, 1), true)}}, .cut 0 16 {((0, 3), false), ((1, 3), false)}),
  ({{((0, 0), true)}, {((0, 1), true)}, {((0, 3), false), ((1, 3), false)}, {((1, 0), true)}, {((1, 1), true)}, {((2, 0), true)}, {((2, 1), true)}}, .cut 0 18 {((0, 2), false), ((1, 2), false)}),
  ({{((0, 2), false), ((1, 2), false)}, {((0, 3), false), ((1, 3), false)}, {((2, 0), true)}, {((2, 1), true)}}, .cut 3 0 {((2, 3), true)}),
  ({{((0, 3), false), ((1, 3), false)}, {((2, 3), false)}}, .ai 1 0 {((0, 3), false)} {((1, 3), false)}),
  ({{((1, 3), false)}, {((2, 3), false)}}, .ax {((1, 3), false), ((2, 3), false)}),
  ({{((0, 3), false)}, {((2, 3), false)}}, .ax {((0, 3), false), ((2, 3), false)}),
  ({{((0, 2), false), ((1, 2), false)}, {((2, 0), true)}, {((2, 1), true)}, {((2, 3), true)}}, .cut 3 0 {((2, 2), true)}),
  ({{((0, 2), false), ((1, 2), false)}, {((2, 2), false)}}, .ai 1 0 {((0, 2), false)} {((1, 2), false)}),
  ({{((1, 2), false)}, {((2, 2), false)}}, .ax {((1, 2), false), ((2, 2), false)}),
  ({{((0, 2), false)}, {((2, 2), false)}}, .ax {((0, 2), false), ((2, 2), false)}),
  ({{((2, 0), true)}, {((2, 1), true)}, {((2, 2), true)}, {((2, 3), true)}}, .ax {((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)}),
  ({{((0, 1), true)}, {((0, 2), true)}, {((0, 3), true)}, {((1, 1), true)}, {((1, 2), true)}, {((1, 3), true)}}, .cut 0 12 {((0, 0), false)}),
  ({{((0, 0), false)}, {((1, 1), true)}, {((1, 2), true)}, {((1, 3), true)}}, .cut 10 0 {((1, 0), true)}),
  ({{((0, 0), false)}, {((1, 0), false)}}, .ax {((0, 0), false), ((1, 0), false)}),
  ({{((0, 0), true)}, {((0, 2), true)}, {((0, 3), true)}, {((1, 0), true)}, {((1, 2), true)}, {((1, 3), true)}}, .cut 0 9 {((0, 1), false)}),
  ({{((0, 1), false)}, {((1, 0), true)}, {((1, 2), true)}, {((1, 3), true)}}, .cut 7 0 {((1, 1), true)}),
  ({{((0, 1), false)}, {((1, 1), false)}}, .ax {((0, 1), false), ((1, 1), false)}),
  ({{((0, 0), true)}, {((0, 1), true)}, {((0, 3), true)}, {((1, 0), true)}, {((1, 1), true)}, {((1, 3), true)}}, .cut 0 6 {((0, 2), false)}),
  ({{((0, 2), false)}, {((1, 0), true)}, {((1, 1), true)}, {((1, 3), true)}}, .cut 4 0 {((1, 2), true)}),
  ({{((0, 2), false)}, {((1, 2), false)}}, .ax {((0, 2), false), ((1, 2), false)}),
  ({{((0, 0), true)}, {((0, 1), true)}, {((0, 2), true)}, {((1, 0), true)}, {((1, 1), true)}, {((1, 2), true)}}, .cut 0 3 {((0, 3), false)}),
  ({{((0, 3), false)}, {((1, 0), true)}, {((1, 1), true)}, {((1, 2), true)}}, .cut 1 0 {((1, 3), true)}),
  ({{((0, 3), false)}, {((1, 3), false)}}, .ax {((0, 3), false), ((1, 3), false)}),
  ({{((1, 0), true)}, {((1, 1), true)}, {((1, 2), true)}, {((1, 3), true)}}, .ax {((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)}),
  ({{((0, 0), true)}, {((0, 1), true)}, {((0, 2), true)}, {((0, 3), true)}}, .ax {((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)})]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hc : chkK 2 (axPHP 5 4) cert = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hm : (∅ : KLine (Fin 5 × Fin 4)) ∈ cert.map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
theorem hl : (cert.map Prod.fst).length ≤ 140 := by decide +kernel

end PEqualNP.Outside.L_pcx_199_aux

theorem PEqualNP.Outside.L_pcx_199 : ∃ π : List (PEqualNP.ProofComplexity.KLine (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsResKRefutation 2 (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 140 := by
  exact ⟨PEqualNP.Outside.L_pcx_199_aux.cert.map Prod.fst, ⟨PEqualNP.Outside.L_pcx_199_aux.chkK_sound 2 _ (PEqualNP.Outside.L_pcx_199_aux.axPHP 5 4) (PEqualNP.Outside.L_pcx_199_aux.axPHP_sound 5 4) _ PEqualNP.Outside.L_pcx_199_aux.hc, PEqualNP.Outside.L_pcx_199_aux.hm⟩, PEqualNP.Outside.L_pcx_199_aux.hl⟩
