import Mathlib

/-!
# Three-row level spaces: the centred bound implies the full bound

`ls3_of_centred` derives the statement of row L-gct-156 (`StmtLS3`) from the statement of row
L-gct-157 (`StmtCentred`). The latter is a conjecture; this is a helper only.
-/

namespace PEqualNP.Gct.Helpers.ThreeRow

open Module

/-- Statement of row L-gct-157. -/
def StmtCentred : Prop :=
  ∀ (q : ℕ) (L : Submodule ℂ (Fin 3 × Fin q → ℂ)), 1 ≤ q → (∀ t ∈ L, (∀ i : Fin 3, ∑ j, t (i, j) = 0) ∧ (∑ j, ∑ l, if j = l then 0 else (t (0, j) * t (1, l) + t (0, j) * t (2, l) + t (1, j) * t (2, l))) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * t (2, m)) = 0) → Module.finrank ℂ L + 1 ≤ q

/-- Statement of row L-gct-156. -/
def StmtLS3 : Prop :=
  ∀ (q : ℕ) (L : Submodule ℂ (Fin 3 × Fin q → ℂ)), (∀ t ∈ L, (∑ i : Fin 3, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else (t (0, j) * t (1, l) + t (0, j) * t (2, l) + t (1, j) * t (2, l))) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * t (2, m)) = 0) → Module.finrank ℂ L ≤ q + 1

/-- The row-sum map. -/
def rowSum (q : ℕ) : (Fin 3 × Fin q → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun t i := ∑ j, t (i, j)
  map_add' a b := by ext i; simp [Finset.sum_add_distrib]
  map_smul' c a := by ext i; simp [Finset.mul_sum]

theorem ls3_of_centred : StmtCentred → StmtLS3 := by
  intro hA q L hL
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have h1 := Submodule.finrank_le L
    have h2 : finrank ℂ (Fin 3 × Fin 0 → ℂ) = 0 := by simp
    omega
  · set f := (rowSum q).comp L.subtype with hf
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    -- the range is proper: it misses `Pi.single 0 1`
    have hne : LinearMap.range f ≠ ⊤ := by
      intro htop
      have hmem : (Pi.single 0 1 : Fin 3 → ℂ) ∈ LinearMap.range f := htop ▸ Submodule.mem_top
      obtain ⟨x, hx⟩ := hmem
      have h0 : ∑ i : Fin 3, f x i = 0 := (hL x.1 x.2).1
      rw [hx] at h0
      simp at h0
    have hr : finrank ℂ (LinearMap.range f) < 3 := by
      have := Submodule.finrank_lt hne
      simpa using this
    set K : Submodule ℂ (Fin 3 × Fin q → ℂ) := (LinearMap.ker f).map L.subtype with hKdef
    have hK : finrank ℂ K = finrank ℂ (LinearMap.ker f) :=
      (LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective L.subtype L.injective_subtype (LinearMap.ker f))).symm
    have hKA := hA q K hq (by
      intro t ht
      obtain ⟨x, hxk, rfl⟩ := Submodule.mem_map.mp ht
      obtain ⟨_, h2, h3⟩ := hL x.1 x.2
      refine ⟨?_, h2, h3⟩
      intro i
      exact congrFun (LinearMap.mem_ker.mp hxk) i)
    omega

end PEqualNP.Gct.Helpers.ThreeRow
