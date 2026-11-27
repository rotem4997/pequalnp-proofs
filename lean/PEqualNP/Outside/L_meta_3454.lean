import Mathlib
import PEqualNP.Defs
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_3454 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ g ∈ F, g < C.gates.length) → ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => w < n)).card + ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => n ≤ w ∧ w - n ∉ F)).card + (F.filter (fun g => n + g ∈ F.biUnion (fun g' => (PEqualNP.MetaComplexity.NestedCover.gateAt C g').inputs.toFinset))).card ≤ 2 * F.card := by
  intro n C F hC hF
  classical
  let R := F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)
  let Q := R.filter (fun w => n ≤ w)
  have hlen : ∀ g ∈ F, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.length = 2 := by
    intro g hg
    apply hC.2.2
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ (hF g hg)]
    apply List.getElem_mem
  have hbound : R.card ≤ 2 * F.card := by
    calc
      R.card ≤ ∑ g ∈ F, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ g ∈ F, 2 := by
        apply Finset.sum_le_sum
        intro g hg
        exact (List.toFinset_card_le _).trans (hlen g hg).le
      _ = 2 * F.card := by simp [Nat.mul_comm]
  have hparts : (R.filter (fun w => w < n)).card + Q.card = R.card := by
    simpa [Q, Nat.not_lt] using (Finset.card_filter_add_card_filter_not (s:=R) (fun w => w<n))
  have hsplit := Finset.card_filter_add_card_filter_not (s:=Q) (fun w => w-n ∉ F)
  simp only [not_not] at hsplit
  have hout : Q.filter (fun w => w-n ∉ F) = R.filter (fun w => n ≤ w ∧ w-n ∉ F) := by
    ext w
    simp [Q,and_assoc]
  have hin : (F.filter (fun g => n+g ∈ R)).card = (Q.filter (fun w => w-n ∈ F)).card := by
    refine Finset.card_bij (fun g _ => n+g) ?_ ?_ ?_
    · intro g hg
      simp only [Finset.mem_filter] at hg
      simp [Q,hg.1,hg.2]
    · intro a ha b hb he
      omega
    · intro w hw
      have hh : (w ∈ R ∧ n ≤ w) ∧ w-n ∈ F := by simpa [Q] using hw
      refine ⟨w-n, ?_, by omega⟩
      simp only [Finset.mem_filter]
      exact ⟨hh.2, by simpa [Nat.add_sub_of_le hh.1.2] using hh.1.1⟩
  change (R.filter (fun w => w<n)).card + (R.filter (fun w => n ≤ w ∧ w-n ∉ F)).card +
    (F.filter (fun g => n+g ∈ R)).card ≤ 2 * F.card
  rw [← hout, hin]
  omega
