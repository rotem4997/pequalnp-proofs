import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6949

-- The inclusion-minimal members of a family.
def mn {n : ℕ} (F : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  {A ∈ F | ∀ B ∈ F, B ⊆ A → A ⊆ B}

theorem mem_mn {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) :
    A ∈ mn F ↔ A ∈ F ∧ ∀ B ∈ F, B ⊆ A → A ⊆ B := by
  unfold mn
  rw [Finset.mem_filter]

-- Every member contains a minimal member.
theorem below {n : ℕ} (F : Finset (Finset (Fin n))) :
    ∀ (k : ℕ) (A : Finset (Fin n)), A ∈ F → A.card ≤ k → ∃ B ∈ mn F, B ⊆ A := by
  intro k
  induction k with
  | zero =>
    intro A hA hk
    refine ⟨A, (mem_mn F A).mpr ⟨hA, fun B _ _ => ?_⟩, Finset.Subset.refl A⟩
    have : A = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [this]
    exact Finset.empty_subset B
  | succ k ih =>
    intro A hA hk
    by_cases hmin : ∀ B ∈ F, B ⊆ A → A ⊆ B
    · exact ⟨A, (mem_mn F A).mpr ⟨hA, hmin⟩, Finset.Subset.refl A⟩
    · have hex : ∃ B ∈ F, B ⊆ A ∧ ¬A ⊆ B := by
        by_contra hcon
        apply hmin
        intro B hB hBA
        by_contra hAB
        exact hcon ⟨B, hB, hBA, hAB⟩
      obtain ⟨B, hB, hBA, hAB⟩ := hex
      have hlt : B.card < A.card := Finset.card_lt_card ⟨hBA, hAB⟩
      obtain ⟨C, hC, hCB⟩ := ih B hB (by omega)
      exact ⟨C, hC, hCB.trans hBA⟩

-- A subfamily meeting every member from below has the same minimal members.
theorem mn_eq {n : ℕ} (F G : Finset (Finset (Fin n))) (hsub : G ⊆ F)
    (hd : ∀ A ∈ F, ∃ B ∈ G, B ⊆ A) : mn F = mn G := by
  ext A
  rw [mem_mn, mem_mn]
  constructor
  · rintro ⟨hA, hmin⟩
    obtain ⟨B, hB, hBA⟩ := hd A hA
    have hAB : A ⊆ B := hmin B (hsub hB) hBA
    have hEq : A = B := Finset.Subset.antisymm hAB hBA
    rw [hEq]
    refine ⟨hB, fun C hC hCB => ?_⟩
    rw [← hEq] at hCB ⊢
    exact hmin C (hsub hC) hCB
  · rintro ⟨hA, hmin⟩
    refine ⟨hsub hA, fun B hB hBA => ?_⟩
    obtain ⟨C, hC, hCB⟩ := hd B hB
    exact (hmin C hC (hCB.trans hBA)).trans hCB

theorem main {n : ℕ} (F G : Finset (Finset (Fin n))) :
    mn (F ∪ G) = mn (mn F ∪ mn G) ∧
    mn (F.biUnion fun A => Finset.image (fun B => A ∪ B) G) =
      mn ((mn F).biUnion fun A => Finset.image (fun B => A ∪ B) (mn G)) := by
  constructor
  · apply mn_eq
    · intro A hA
      rcases Finset.mem_union.mp hA with h | h
      · exact Finset.mem_union_left _ ((mem_mn F A).mp h).1
      · exact Finset.mem_union_right _ ((mem_mn G A).mp h).1
    · intro A hA
      rcases Finset.mem_union.mp hA with h | h
      · obtain ⟨B, hB, hBA⟩ := below F A.card A h (le_refl _)
        exact ⟨B, Finset.mem_union_left _ hB, hBA⟩
      · obtain ⟨B, hB, hBA⟩ := below G A.card A h (le_refl _)
        exact ⟨B, Finset.mem_union_right _ hB, hBA⟩
  · apply mn_eq
    · intro C hC
      obtain ⟨A, hA, hC⟩ := Finset.mem_biUnion.mp hC
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
      exact Finset.mem_biUnion.mpr ⟨A, ((mem_mn F A).mp hA).1,
        Finset.mem_image.mpr ⟨B, ((mem_mn G B).mp hB).1, rfl⟩⟩
    · intro C hC
      obtain ⟨A, hA, hC⟩ := Finset.mem_biUnion.mp hC
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨A', hA', hAA⟩ := below F A.card A hA (le_refl _)
      obtain ⟨B', hB', hBB⟩ := below G B.card B hB (le_refl _)
      exact ⟨A' ∪ B', Finset.mem_biUnion.mpr ⟨A', hA', Finset.mem_image.mpr ⟨B', hB', rfl⟩⟩,
        Finset.union_subset_union hAA hBB⟩

end PEqualNP.Outside.L_meta_6949

theorem PEqualNP.Outside.L_meta_6949 : ∀ (x1 : ℕ) (x2 x3 : Finset (Finset (Fin x1))),   have x4 : Finset (Finset (Fin x1)) → Finset (Finset (Fin x1)) := fun (x4 : Finset (Finset (Fin x1))) => {x5 ∈ x4 | ∀ x6 ∈ x4, x6 ⊆ x5 → x5 ⊆ x6};   x4 (x2 ∪ x3) = x4 (x4 x2 ∪ x4 x3) ∧ x4 (x2.biUnion fun (x5 : Finset (Fin x1)) => Finset.image (fun (x6 : Finset (Fin x1)) => x5 ∪ x6) x3) = x4 ((x4 x2).biUnion fun (x5 : Finset (Fin x1)) => Finset.image (fun (x6 : Finset (Fin x1)) => x5 ∪ x6) (x4 x3)) := by
  intro n F G
  exact PEqualNP.Outside.L_meta_6949.main F G
