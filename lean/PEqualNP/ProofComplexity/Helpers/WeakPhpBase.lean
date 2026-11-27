import PEqualNP.ProofComplexity.L046
import PEqualNP.ProofComplexity.L047
import PEqualNP.ProofComplexity.Helpers.PhpFinal

/-!
# The base bound for the pigeonhole formula with any number of pigeons (L-pcx-053)

A Res(⊕) refutation of `PHP m N` restricts to one of the pigeonhole formula on a graph `G`
(L-pcx-047), which has no low degree polynomial calculus refutation when `G` is a boundary
expander (L-pcx-046); the degree to size theorem then bounds the length from below in terms of
the number of edges, at most `b * m` for left degree at most `b`.

With no pigeons the exponent is `0` and the bound reads `1 ≤ 2 * π.length`. With a pigeon the
expansion of a single pigeon gives the graph an edge, so the number of edges is positive.
-/

namespace PEqualNP.ProofComplexity.WeakPhpBase

open PEqualNP.ProofComplexity PEqualNP.Expanders

/-- A boundary expander with a left vertex and `1 ≤ s` has an edge. -/
theorem card_gedge_pos {m N : ℕ} (G : BipGraph m N) (s : ℕ) (hE : IsBdryExpander G s 2)
    (hs : 1 ≤ s) (i₀ : Fin m) : 0 < Fintype.card (GEdge G) := by
  have h := hE {i₀} (by rw [Finset.card_singleton]; exact hs)
  rw [Finset.card_singleton] at h
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) h)
  unfold uniqueNbrs at hj
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hj).2
  have hi' : i ∈ Finset.filter (fun i => j ∈ G i) {i₀} := by
    rw [hi]; exact Finset.mem_singleton_self i
  exact Fintype.card_pos_iff.mpr ⟨⟨(i, j), (Finset.mem_filter.mp hi').2⟩⟩

/-- The base bound. -/
theorem weak_php_base (m N : ℕ) (G : BipGraph m N) (s b D : ℕ)
    (π : List (LinClause (Fin m × Fin N))) (hE : IsBdryExpander G s 2) (hL : LeftDegLe G b)
    (hs : 2 * (D + 1) ≤ s) (hD : 32 ≤ D) (hb : 2 * b ≤ D)
    (hπ : IsLinRefutation (PHP m N) π) :
    Real.exp (((D : ℝ) ^ 2) / (256 * ((b : ℝ) * (m : ℝ)))) ≤ 2 * (π.length : ℝ) := by
  obtain ⟨π', hπ', hlen⟩ := PEqualNP.ProofComplexity.L047 m N G π hπ
  have hnr := PEqualNP.ProofComplexity.L046 m N G s D hE hs
  have hsize := DegSizeAssembly.degree_to_size_256 (GEdge G) (graphPHP G) π' (max b 2) D
    (PhpFinal.graphPHP_width G b hL) (by omega) hD hπ' hnr
  have hlenR : (π'.length : ℝ) ≤ 2 * (π.length : ℝ) := by exact_mod_cast hlen
  refine le_trans (le_trans (Real.exp_le_exp.mpr ?_) hsize) hlenR
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have hpos : 0 < Fintype.card (GEdge G) := card_gedge_pos G s hE (by omega) ⟨0, hm⟩
    have hcard : Fintype.card (GEdge G) ≤ m * b := PhpFinal.card_gedge_le G b hL
    have hposR : (0 : ℝ) < (Fintype.card (GEdge G) : ℝ) := by exact_mod_cast hpos
    have hcardR : (Fintype.card (GEdge G) : ℝ) ≤ (b : ℝ) * (m : ℝ) := by
      rw [mul_comm]; exact_mod_cast hcard
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hcardR (by norm_num))

end PEqualNP.ProofComplexity.WeakPhpBase
