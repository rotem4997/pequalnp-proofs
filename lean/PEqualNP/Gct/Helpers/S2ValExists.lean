import Mathlib

/-!
# Lemma V for Lemma S2 (L-gct-086)

Over an algebraically closed field `k`, an element `y` of a field extension `K` that is not in
the image of `k` lies in the maximal ideal of some valuation subring of `K` containing `k`.
-/

namespace PEqualNP.Gct.Helpers.S2ValExists

open Polynomial

theorem exists_valuationSubring (k K : Type*) [Field k] [IsAlgClosed k] [Field K]
    [Algebra k K] (y : K) (hy : y ∉ Set.range (algebraMap k K)) :
    ∃ O : ValuationSubring K, (∀ r : k, algebraMap k K r ∈ O) ∧ y ∈ O.nonunits := by
  -- `y` is transcendental over `k`.
  have htr : Transcendental k y := by
    intro halg
    have hint : IsIntegral k y := halg.isIntegral
    exact hy (minpoly.mem_range_of_degree_eq_one k y
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)))
  let A : Subring K := (Algebra.adjoin k {y}).toSubring
  let yA : A := ⟨y, Algebra.subset_adjoin rfl⟩
  have hI : Ideal.span {yA} ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ Ideal.span {yA} := htop ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    have ha' : (a : K) * y = 1 := congrArg Subtype.val ha
    have hamem : (a : K) ∈ Algebra.adjoin k {y} := a.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hamem
    obtain ⟨p, hp⟩ := hamem
    apply htr
    refine ⟨X * p - 1, ?_, ?_⟩
    · intro h0
      have := congrArg (fun f : k[X] => f.coeff 0) h0
      simp at this
    · have hp' : aeval y p = (a : K) := hp
      simp only [map_sub, map_mul, aeval_X, hp', map_one]
      rw [mul_comm, ha', sub_self]
  obtain ⟨B, hAB, hsub⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  refine ⟨B, fun r => hAB (Subalgebra.algebraMap_mem _ r), ?_⟩
  exact hsub ⟨yA, Ideal.subset_span rfl, rfl⟩

theorem exists_valuationSubring' (k K : Type*) [Field k] [IsAlgClosed k] [Field K]
    [Algebra k K] (q : ℕ) (lam : Fin q → K) (hlam : ∀ j, lam j ≠ 0)
    (h : ∃ j, lam j ∉ Set.range (algebraMap k K)) :
    ∃ O : ValuationSubring K, (∀ r : k, algebraMap k K r ∈ O) ∧
      ∃ j, lam j ∈ O.nonunits ∨ (lam j)⁻¹ ∈ O.nonunits := by
  obtain ⟨j, hj⟩ := h
  obtain ⟨O, hO, hy⟩ := exists_valuationSubring k K (lam j) hj
  exact ⟨O, hO, j, Or.inl hy⟩

end PEqualNP.Gct.Helpers.S2ValExists
