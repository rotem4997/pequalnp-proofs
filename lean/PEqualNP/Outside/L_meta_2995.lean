import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2995

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm

open Configuration Configuration.ProjectivePlane in
open scoped LinearAlgebra.Projectivization in
theorem plane : ∃ (q N : ℕ) (I : Fin N → Fin N → Prop), 201 ≤ q ∧ N = q ^ 2 + q + 1 ∧ q % 2 = 1 ∧
    (∀ l, Nat.card {p // I p l} = q + 1) ∧ (∀ p, Nat.card {l // I p l} = q + 1) ∧
    (∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) := by
  classical
  have : Fact (Nat.Prime 211) := ⟨by norm_num⟩
  let K := ZMod 211
  have : Finite K := inferInstanceAs (Finite (ZMod 211))
  have hK : Nat.card K = 211 := Nat.card_zmod 211
  let P := ℙ K (Fin 3 → K)
  have : Finite P := inferInstance
  have : Fintype P := Fintype.ofFinite P
  have hP : Nat.card P = 211 ^ 2 + 211 + 1 := by
    have h := Projectivization.card_of_finrank K (Fin 3 → K) (n := 3) (by simp)
    rw [hK] at h
    rw [h]
    simp [Finset.sum_range_succ]
  have ho : order P P = 211 := by
    have h := card_points P P
    rw [← Nat.card_eq_fintype_card, hP] at h
    nlinarith [h]
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = 211 := ⟨_, rfl⟩
  have hP : Nat.card P = q ^ 2 + q + 1 := by rw [hq]; exact hP
  have ho : order P P = q := by rw [hq]; exact ho
  let e : Fin (Nat.card P) ≃ P := (Finite.equivFin P).symm
  refine ⟨q, Nat.card P, fun p l => e p ∈ e l, by omega, hP, by omega, ?_, ?_, ?_⟩
  · intro l
    have h := pointCount_eq (P := P) (L := P) (e l)
    rw [ho] at h
    rw [← h]
    exact Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl)
  · intro p
    have h := lineCount_eq (P := P) (L := P) (e p)
    rw [ho] at h
    rw [← h]
    exact Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl)
  · intro p p' hne
    obtain ⟨l, hl, hu⟩ := HasLines.existsUnique_line P P (e p) (e p') (fun h => hne (e.injective h))
    refine ⟨e.symm l, by simpa using hl, ?_⟩
    intro m hm
    rw [Equiv.eq_symm_apply]
    exact hu _ hm

-- The circuit without gates whose output is input 0.
def C0 : Circuit := ⟨[], 0⟩

lemma C0_ao (n : ℕ) : IsAO2 n C0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg; cases hg
  · intro j hj; exact absurd hj (Nat.not_lt_zero _)
  · intro g hg; cases hg

lemma C0_val (n : ℕ) (h : 0 < n) (x : Fin n → Bool) : circuitFun n C0 x = x ⟨0, h⟩ := by
  change (List.ofFn x).getD 0 false = _
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

lemma C0_read (n : ℕ) (h : 0 < n) : IsReadK n C0 2 := by
  intro S hS
  have h0 : setInput S ⟨0, h⟩ = true := (C0_val n h (setInput S)).symm.trans hS.1
  have hm : (⟨0, h⟩ : Fin n) ∈ S := of_decide_eq_true h0
  have hl : 0 ∈ setList S := by
    unfold setList
    refine List.mem_map.mpr ⟨⟨0, h⟩, ?_, rfl⟩
    simpa using hm
  unfold readsAtMost
  change (((List.range n).map (leafVectors (setList S) 2)).getD 0 []).any _ = true
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp only [List.getElem_map, List.getElem_range]
  unfold leafVectors
  rw [ite_eq_left hl]
  simp only [List.any_cons, List.any_nil, Bool.or_false, List.all_eq_true]
  intro a ha
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
  refine decide_eq_true ?_
  split_ifs <;> omega

end PEqualNP.Outside.L_meta_2995

theorem PEqualNP.Outside.L_meta_2995 : ¬ (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (201 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x9 → PEqualNP.ReadK.IsReadK (x2 + x2) x9 (2 : ℕ) → x9.size ≤ (2 : ℕ) * x2 → ∀ (x13 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x9 x13 = Bool.true → ∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) := by
  classical
  intro H
  obtain ⟨q, N, I, hq, hN, _, hpl, _, hu⟩ := PEqualNP.Outside.L_meta_2995.plane
  have hpos : 0 < N + N := by rw [hN]; omega
  have hNp : 0 < N := by omega
  obtain ⟨p, l, _, h1, h2⟩ := H q N I hq hN (fun l => by rw [← Nat.card_eq_fintype_card]; exact hpl l) hu
    PEqualNP.Outside.L_meta_2995.C0 (PEqualNP.Outside.L_meta_2995.C0_ao _)
    (PEqualNP.Outside.L_meta_2995.C0_read _ hpos) (Nat.zero_le _)
    (fun i => decide (i = ⟨0, hpos⟩)) (by rw [PEqualNP.Outside.L_meta_2995.C0_val _ hpos]; simp)
  have e : Fin.natAdd N l = ⟨0, hpos⟩ := of_decide_eq_true h2
  have := congrArg Fin.val e
  simp only [Fin.val_natAdd] at this
  omega
