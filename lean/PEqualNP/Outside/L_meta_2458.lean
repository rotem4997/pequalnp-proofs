import Mathlib
import PEqualNP.Defs

open scoped LinearAlgebra.Projectivization

namespace PEqualNP.Outside.L_meta_2458

theorem card_plane [Fact (Nat.Prime 211)] :
    Nat.card (ℙ (ZMod 211) (Fin 3 → ZMod 211)) = 211 ^ 2 + 211 + 1 := by
  rw [Projectivization.card_of_finrank (ZMod 211) (Fin 3 → ZMod 211) (n := 3) (by simp)]
  simp [Finset.sum_range_succ]

theorem order_eq [Fact (Nat.Prime 211)] :
    Configuration.ProjectivePlane.order (ℙ (ZMod 211) (Fin 3 → ZMod 211))
      (ℙ (ZMod 211) (Fin 3 → ZMod 211)) = 211 := by
  classical
  letI : Fintype (ℙ (ZMod 211) (Fin 3 → ZMod 211)) := Fintype.ofFinite _
  have h := Configuration.ProjectivePlane.card_points (ℙ (ZMod 211) (Fin 3 → ZMod 211))
    (ℙ (ZMod 211) (Fin 3 → ZMod 211))
  rw [Fintype.card_eq_nat_card, card_plane] at h
  set o := Configuration.ProjectivePlane.order (ℙ (ZMod 211) (Fin 3 → ZMod 211))
    (ℙ (ZMod 211) (Fin 3 → ZMod 211))
  rcases lt_trichotomy o 211 with hlt | heq | hgt
  · have : o ^ 2 + o + 1 < 211 ^ 2 + 211 + 1 := by
      have := Nat.pow_lt_pow_left hlt (by norm_num : (2 : ℕ) ≠ 0)
      omega
    omega
  · exact heq
  · have : 211 ^ 2 + 211 + 1 < o ^ 2 + o + 1 := by
      have := Nat.pow_lt_pow_left hgt (by norm_num : (2 : ℕ) ≠ 0)
      omega
    omega

end PEqualNP.Outside.L_meta_2458

theorem PEqualNP.Outside.L_meta_2458 : ∃ (x1 : ℕ) (x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : DecidableRel x3), (201 : ℕ) ≤ x1 ∧ x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) ∧ (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) ∧ ∀ (x5 x6 : Fin x2), x5 ≠ x6 → ∃! x8 : Fin x2, x3 x5 x8 ∧ x3 x6 x8 := by
  classical
  haveI : Fact (Nat.Prime 211) := ⟨by norm_num⟩
  letI : Fintype (ℙ (ZMod 211) (Fin 3 → ZMod 211)) := Fintype.ofFinite _
  let e := Fintype.equivFin (ℙ (ZMod 211) (Fin 3 → ZMod 211))
  refine ⟨Configuration.ProjectivePlane.order (ℙ (ZMod 211) (Fin 3 → ZMod 211))
      (ℙ (ZMod 211) (Fin 3 → ZMod 211)),
    Fintype.card (ℙ (ZMod 211) (Fin 3 → ZMod 211)),
    fun i j => e.symm i ∈ e.symm j, Classical.decRel _, ?_, ?_, ?_, ?_⟩
  · rw [PEqualNP.Outside.L_meta_2458.order_eq]; norm_num
  · exact Configuration.ProjectivePlane.card_points _ _
  · intro l
    have h := Configuration.ProjectivePlane.pointCount_eq
      (ℙ (ZMod 211) (Fin 3 → ZMod 211)) (e.symm l)
    unfold Configuration.pointCount at h
    rw [Fintype.card_eq_nat_card, ← h]
    exact Nat.card_congr (Equiv.subtypeEquiv e.symm (fun _ => Iff.rfl))
  · intro a b hab
    have hne : e.symm a ≠ e.symm b := e.symm.injective.ne hab
    obtain ⟨l, hl, huniq⟩ := Configuration.HasLines.existsUnique_line
      (ℙ (ZMod 211) (Fin 3 → ZMod 211)) (ℙ (ZMod 211) (Fin 3 → ZMod 211))
      (e.symm a) (e.symm b) hne
    refine ⟨e l, by simpa using hl, fun y hy => ?_⟩
    have := huniq (e.symm y) hy
    rw [← this]; simp
