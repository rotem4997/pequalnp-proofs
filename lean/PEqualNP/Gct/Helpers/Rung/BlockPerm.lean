import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.Helpers.Rung.Statements
import PEqualNP.Gct.Helpers.Rung.BlockPermA4

/-!
# Helper module (proofs only): Theorem C, the block sum as a restriction of the permanent

`blockPerm : BlockPerm`. The matrix is the one of `BlockPermA4` (rows `BPA.Row`, columns
`BPA.Col`), transported to `Fin (a + N * (b + r) - r)` along two bijections; its permanent is
computed by `BPA.pm_block`. The constant is
`stab (grp) * (-1) ^ (r + 1) * stab (pad)`, a product of two positive integers (the numbers
of permutations of the rows preserving the groups) and a sign.
-/

namespace PEqualNP.Gct.Rung

open MvPolynomial Finset BPA

namespace BPA

theorem entry_totalDegree_le (N a b r : ℕ) (ζ₀ : ℂ) (γ : Grp N a) (j : Col N a b r) :
    (entry N a b r (fun h i j => (X (h, i, j) : MvPolynomial (Fin N × Fin a × Fin b) ℂ))
      (C ζ₀) γ j).totalDegree ≤ 1 := by
  rcases γ with (i | u) | h <;> rcases j with p | ⟨h', j⟩ | ⟨h', l⟩ <;> simp only [entry] <;>
    (try split_ifs) <;> first | (rw [← C_pow, totalDegree_C]; exact Nat.zero_le 1) | simp

theorem blockPoly_eq (N a b r : ℕ) :
    blockPoly N a b r = ∑ h : Fin N, ∑ J : {J : Finset (Fin b) // J.card = r},
      ∑ I : {I : Finset (Fin a) // I.card = r},
        Matrix.permanent (Matrix.of fun m n : Fin r =>
          (X (h, I.1.orderEmbOfFin I.2 m, J.1.orderEmbOfFin J.2 n) :
            MvPolynomial (Fin N × Fin a × Fin b) ℂ)) := by
  unfold blockPoly gadgetPoly sumSubperm
  refine sum_congr rfl fun h _ => ?_
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun J _ => sum_congr rfl fun I _ => ?_
  simp only [Matrix.permanent, map_sum, map_prod, Matrix.of_apply, Matrix.mvPolynomialX_apply,
    rename_X]

end BPA

theorem blockPerm : BlockPerm := by
  intro N a b r hN hr hra hrb
  classical
  obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ₀ : ℂ, IsPrimitiveRoot ζ₀ r :=
    ⟨_, Complex.isPrimitiveRoot_exp r (by omega)⟩
  have hζ : IsPrimitiveRoot (C ζ₀ : MvPolynomial (Fin N × Fin a × Fin b) ℂ) r :=
    hζ₀.map_of_injective (C_injective (Fin N × Fin a × Fin b) ℂ)
  have hNr : N * (b + r) = (N - 1) * r + r + N * b := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    simp only [Nat.add_sub_cancel_left]
    ring
  have hcr : Fintype.card (Row N a b r) = a + N * (b + r) - r := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega
  have hcc : Fintype.card (Col N a b r) = a + N * (b + r) - r := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    have : N * (b + r) = N * b + N * r := Nat.mul_add _ _ _
    omega
  set x : Fin N → Fin a → Fin b → MvPolynomial (Fin N × Fin a × Fin b) ℂ :=
    fun h i j => X (h, i, j) with hx
  set M : Row N a b r → Col N a b r → MvPolynomial (Fin N × Fin a × Fin b) ℂ :=
    fun i j => entry N a b r x (C ζ₀) (grp N a b r i) j with hM
  refine ⟨(stab (grp N a b r) : ℂ) * ((-1) ^ (r + 1) * (stab (pad a r) : ℂ)),
    fun p => M ((Fintype.equivFinOfCardEq hcr).symm p.1) ((Fintype.equivFinOfCardEq hcc).symm p.2),
    ?_, ?_, ?_⟩
  · exact mul_ne_zero (Nat.cast_ne_zero.2 (stab_pos _).ne')
      (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
        (Nat.cast_ne_zero.2 (stab_pos _).ne'))
  · intro p
    exact entry_totalDegree_le N a b r ζ₀ _ _
  · have h1 : bind₁ (fun p : Fin (a + N * (b + r) - r) × Fin (a + N * (b + r) - r) =>
          M ((Fintype.equivFinOfCardEq hcr).symm p.1) ((Fintype.equivFinOfCardEq hcc).symm p.2))
          (PEqualNP.Gct.permPoly ℂ (a + N * (b + r) - r)) =
        pm (fun (i j : Fin (a + N * (b + r) - r)) =>
          M ((Fintype.equivFinOfCardEq hcr).symm i) ((Fintype.equivFinOfCardEq hcc).symm j)) := by
      unfold PEqualNP.Gct.permPoly pm Matrix.permanent
      simp only [map_sum, map_prod, Matrix.mvPolynomialX_apply, bind₁_X_right]
    rw [h1, pm_reindex (Fintype.equivFinOfCardEq hcr).symm (Fintype.equivFinOfCardEq hcc).symm M,
      hM, pm_block x (C ζ₀) hN hr hra hζ, blockPoly_eq]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, hx]
    ring
