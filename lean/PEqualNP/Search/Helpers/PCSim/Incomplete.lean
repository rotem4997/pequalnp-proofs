import PEqualNP.Library.L109
import PEqualNP.ProofComplexity.Helpers.ThreeCnfFamily
import PEqualNP.ProofComplexity.L046

/-!
# Helpers for L-lib-110: bounded-width Res(⊕) is incomplete on 3-CNFs

For a width bound `k`, let `D = max (2 * k + 2) (k + 3)`. The 3-CNF `to3 (graphPHP G) w` on an
expander `G` (L-pcx-043) with enough pigeons has no polynomial calculus refutation of degree
`D` (L-pcx-046 carried by `to3_pc_lower`). Renamed to the variables `Fin n`, a Res(⊕)
refutation with every line of at most `k` equations pulls back line by line (an image, so the
number of equations does not grow) to one of the original formula, and L-lib-109 turns that
into a polynomial calculus refutation of degree `D`: a contradiction.
-/

namespace PEqualNP.Search.Helpers.PCSim

open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.ProofComplexity.Helpers.ThreeCnf
  PEqualNP.ProofComplexity.ThreeCnfFamily

theorem incomplete (k : ℕ) :
    ∃ (n : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))),
      (∀ C ∈ F, C.card ≤ 3) ∧
      ¬ PEqualNP.ProofComplexity.Satisfiable
        (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧
      ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin n)),
        IsLinRefutation (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π →
        ∃ L ∈ π, k < L.card := by
  classical
  obtain ⟨b, s₀, n₀, hs₀, hG⟩ := PEqualNP.ProofComplexity.L043
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w = max b 2 := ⟨_, rfl⟩
  have hw2 : 2 ≤ w := hw ▸ le_max_right _ _
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = max (2 * k + 2) (k + 3) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = max n₀ (s₀ * (2 * (w * D + 2 * w + 1))) := ⟨_, rfl⟩
  obtain ⟨G, hL, _, hE⟩ := hG N (hN ▸ le_max_left _ _)
  have hdeg : 2 * (w * D + 2 * w + 1) ≤ N / s₀ := by
    rw [Nat.le_div_iff_mul_le hs₀, Nat.mul_comm, hN]
    exact le_max_right _ _
  have hnr := L046 (N + 1) N G (N / s₀) (w * D + 2 * w) hE hdeg
  have hwid : ∀ C ∈ graphPHP G, C.card ≤ w := fun C hC =>
    hw ▸ PhpFinal.graphPHP_width G b hL C hC
  have hnr3 : ¬ PCRefutable (cnfSystem (to3 (graphPHP G) w)) D :=
    to3_pc_lower (graphPHP G) w D (by omega) hwid hnr
  have instF : Fintype ↥(graphPHP G) := Fintype.ofFinite _
  have hun : ¬ PEqualNP.ProofComplexity.Satisfiable (to3 (graphPHP G) w) :=
    to3_unsat _ _ (graphPHP_unsat G (Nat.lt_succ_self N))
  have hfin : (ren (Fintype.equivFin (GEdge G ⊕ (↥(graphPHP G) × Fin (w + 1))))
      '' to3 (graphPHP G) w).Finite := Set.toFinite _
  refine ⟨_, hfin.toFinset, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨C0, hC0, rfl⟩ := hfin.mem_toFinset.mp hC
    exact le_trans Finset.card_image_le (to3_width _ _ C0 hC0)
  · rw [Set.Finite.coe_toFinset]
    exact ren_unsat _ _ hun
  · intro π hπ
    rw [Set.Finite.coe_toFinset] at hπ
    by_contra hcon
    push Not at hcon
    have hback := back_refutation _ _ π hπ
    apply hnr3
    have h := PEqualNP.Library.L109 _ _ _ 3 k (to3_width _ _) hback (by
      intro L hL
      obtain ⟨L0, hL0, rfl⟩ := List.mem_map.mp hL
      exact le_trans Finset.card_image_le (hcon L0 hL0))
    rw [hD]
    exact h

end PEqualNP.Search.Helpers.PCSim
