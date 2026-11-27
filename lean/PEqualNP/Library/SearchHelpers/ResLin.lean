import PEqualNP.Defs

/-!
# Helpers: soundness of Res(lin)

Used by `L-lib-054`.
-/

namespace PEqualNP.Library.SearchHelpers

open PEqualNP.Search

/-- Every line of a Res(lin) derivation holds under an assignment satisfying the axioms. -/
theorem resLin_lines_hold {n : ℕ} (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    (a : Fin n → Bool) (ha : PEqualNP.ProofComplexity.Satisfies a F) :
    ∀ π : List (LinClause n), IsResLinDerivation F π → ∀ L ∈ π, LinClause.Holds a L := by
  intro π h
  induction h with
  | nil => intro L hL; simp at hL
  | ax C _ hC hL ih =>
    intro L' hL'
    rcases List.mem_cons.mp hL' with rfl | hL'
    · obtain ⟨l, hl, hal⟩ := ha C hC
      refine ⟨({l.1}, l.2), (hL _).mpr ⟨l, hl, rfl⟩, ?_⟩
      simp only [LinEq.Holds, Finset.filter_singleton]
      cases h1 : a l.1 <;> cases h2 : l.2 <;> simp_all
    · exact ih L' hL'
  | @res π e e' C D _ h1 h2 hv hb ih =>
    intro L' hL'
    rcases List.mem_cons.mp hL' with rfl | hL'
    · obtain ⟨f, hf, hfa⟩ := ih _ h1
      obtain ⟨g, hg, hga⟩ := ih _ h2
      rcases List.mem_cons.mp hf with rfl | hf
      · rcases List.mem_cons.mp hg with rfl | hg
        · exfalso
          simp only [LinEq.Holds] at hfa hga
          rw [hv] at hfa
          apply hb
          cases hx : f.2 <;> cases hy : g.2 <;> simp_all
        · exact ⟨g, List.mem_append_right _ hg, hga⟩
      · exact ⟨f, List.mem_append_left _ hf, hfa⟩
    · exact ih L' hL'
  | weaken _ hC himp ih =>
    intro L' hL'
    rcases List.mem_cons.mp hL' with rfl | hL'
    · exact himp a (ih _ hC)
    · exact ih L' hL'

end PEqualNP.Library.SearchHelpers

namespace PEqualNP.Library.SearchHelpers

open PEqualNP.Search

/-- A clause read as a linear clause: each literal `(v, b)` becomes the equation `{v} = b`. -/
noncomputable def lin {n : ℕ} (C : PEqualNP.ProofComplexity.Clause (Fin n)) : LinClause n :=
  C.toList.map fun l => ({l.1}, l.2)

theorem holds_single {n : ℕ} (a : Fin n → Bool) (v : Fin n) (b : Bool) :
    LinEq.Holds a ({v}, b) ↔ a v = b := by
  simp only [LinEq.Holds, Finset.filter_singleton]
  cases h1 : a v <;> cases b <;> simp

theorem holds_lin {n : ℕ} (a : Fin n → Bool) (C : PEqualNP.ProofComplexity.Clause (Fin n)) :
    LinClause.Holds a (lin C) ↔ ∃ l ∈ C, a l.1 = l.2 := by
  simp only [LinClause.Holds, lin, List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨e, ⟨l, hl, rfl⟩, h⟩
    exact ⟨l, hl, (holds_single a l.1 l.2).mp h⟩
  · rintro ⟨l, hl, h⟩
    exact ⟨_, ⟨l, hl, rfl⟩, (holds_single a l.1 l.2).mpr h⟩

theorem resLin_simulates {n : ℕ} (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) :
    ∀ π : List (PEqualNP.ProofComplexity.Clause (Fin n)),
    PEqualNP.ProofComplexity.IsDerivation F π →
    ∃ π' : List (LinClause n), IsResLinDerivation F π' ∧ π'.length ≤ 4 * π.length ∧
      ∀ D ∈ π, lin D ∈ π' := by
  intro π h
  induction h with
  | nil => exact ⟨[], IsResLinDerivation.nil, by simp, by simp⟩
  | @ax π C _ hC ih =>
    obtain ⟨π', hd, hlen, hmem⟩ := ih
    refine ⟨lin C :: π', IsResLinDerivation.ax C hd hC ?_, by simp; omega, ?_⟩
    · intro e
      simp [lin, eq_comm]
    · intro D hD
      rcases List.mem_cons.mp hD with rfl | hD
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hmem D hD)
  | @res π C D R _ hC hD hR ih =>
    obtain ⟨π', hd, hlen, hmem⟩ := ih
    obtain ⟨v, hv1, hv2, rfl⟩ := hR
    set X1 : LinClause n := ({v}, true) :: lin (C.erase (v, true))
    set X2 : LinClause n := ({v}, false) :: lin (D.erase (v, false))
    have h1 : IsResLinDerivation F (X1 :: π') := by
      refine IsResLinDerivation.weaken hd (hmem C hC) fun a ha => ?_
      obtain ⟨l, hl, hal⟩ := (holds_lin a C).mp ha
      by_cases hlv : l = (v, true)
      · subst hlv; exact ⟨_, List.mem_cons_self, (holds_single a v true).mpr hal⟩
      · obtain ⟨e, he, hea⟩ := (holds_lin a _).mpr ⟨l, Finset.mem_erase.mpr ⟨hlv, hl⟩, hal⟩
        exact ⟨e, List.mem_cons_of_mem _ he, hea⟩
    have h2 : IsResLinDerivation F (X2 :: X1 :: π') := by
      refine IsResLinDerivation.weaken h1 (List.mem_cons_of_mem _ (hmem D hD)) fun a ha => ?_
      obtain ⟨l, hl, hal⟩ := (holds_lin a D).mp ha
      by_cases hlv : l = (v, false)
      · subst hlv; exact ⟨_, List.mem_cons_self, (holds_single a v false).mpr hal⟩
      · obtain ⟨e, he, hea⟩ := (holds_lin a _).mpr ⟨l, Finset.mem_erase.mpr ⟨hlv, hl⟩, hal⟩
        exact ⟨e, List.mem_cons_of_mem _ he, hea⟩
    have h3 : IsResLinDerivation F
        ((lin (C.erase (v, true)) ++ lin (D.erase (v, false))) :: X2 :: X1 :: π') :=
      IsResLinDerivation.res h2 (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
        rfl (by simp)
    have h4 : IsResLinDerivation F (lin (C.erase (v, true) ∪ D.erase (v, false)) ::
        (lin (C.erase (v, true)) ++ lin (D.erase (v, false))) :: X2 :: X1 :: π') := by
      refine IsResLinDerivation.weaken h3 List.mem_cons_self fun a ha => ?_
      rw [holds_lin]
      obtain ⟨e, he, hea⟩ := ha
      rcases List.mem_append.mp he with he | he
      · obtain ⟨l, hl, hal⟩ := (holds_lin a _).mp ⟨e, he, hea⟩
        exact ⟨l, Finset.mem_union_left _ hl, hal⟩
      · obtain ⟨l, hl, hal⟩ := (holds_lin a _).mp ⟨e, he, hea⟩
        exact ⟨l, Finset.mem_union_right _ hl, hal⟩
    refine ⟨_, h4, by simp; omega, ?_⟩
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (hmem E hE))))

end PEqualNP.Library.SearchHelpers
