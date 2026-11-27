import Mathlib
import PEqualNP.Defs

-- Delete points and lines with few remaining unexplained incidences.
-- Any counterexample leaves a nonempty subgraph with large degree on both sides.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3254_1
    (peel : ∀ (N k : ℕ) (E : Finset (Fin N × Fin N)), k*(N+N) < E.card →
      ∃ A B : Finset (Fin N), A.Nonempty ∧ B.Nonempty ∧
        (∀ p ∈ A, k < (B.filter fun l => (p,l) ∈ E).card) ∧
        (∀ l ∈ B, k < (A.filter fun p => (p,l) ∈ E).card))
    (coreBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      100 < q → N=q^2+q+1 → (∀ l, Fintype.card {p : Fin N // I p l}=q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
      let m := N+N
      let one := fun (a b : Fin N) => decide (b=a)
      let R := {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ k < s, W (m+k) ⊆ W o ∧
        (one e.1,one e.2) ∈ W (m+k) ∧ ∃ a b, max a b < m+k ∧
        W (m+k) = W a ∩ W b ∧ ∃ A B, W a = A ×ˢ Set.univ ∧ W b = Set.univ ×ˢ B}
      o < m+s →
      (∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true}) →
      (∀ k < s, ∃ a b, max a b < m+k ∧ W (m+k) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
      (∀ p l, I p l → (one p,one l) ∈ W o) →
      (∀ T : Fin N → Bool, Fintype.card {l : Fin N // T l = true} ≤ q →
        ((fun p => decide (¬∃ l, I p l ∧ T l = true)),T) ∉ W o) →
      R.ncard ≤ 4*s →
      ∀ (E : Finset (Fin N × Fin N)), (∀ e, e ∈ E ↔ I e.1 e.2 ∧ e ∉ R) →
      ∀ (A B : Finset (Fin N)), A.Nonempty → B.Nonempty →
        (∀ p ∈ A, 12*q/25 < (B.filter fun l => (p,l) ∈ E).card) →
        (∀ l ∈ B, 12*q/25 < (A.filter fun p => (p,l) ∈ E).card) →
        N*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 → (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) → (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) → (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) → (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) → {x19 : Fin x2 × Fin x2 | x3 x19.1 x19.2 ∧ ∃ x20 < x9, x11 (x12 + x20) ⊆ x11 x10 ∧ (x13 x19.1, x13 x19.2) ∈ x11 (x12 + x20) ∧ ∃ (x21 : ℕ) (x22 : ℕ), Max.max x21 x22 < x12 + x20 ∧ x11 (x12 + x20) = x11 x21 ∩ x11 x22 ∧ ∃ (x23 : Set (Fin x2 → Bool)) (x24 : Set (Fin x2 → Bool)), x11 x21 = x23 ×ˢ Set.univ ∧ x11 x22 = Set.univ ×ˢ x24}.ncard ≤ (4 : ℕ) * x9 → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I inst hq hN hcol hplane s o W m one hout hin hg pos neg hcount
  let edges := (Finset.univ : Finset (Fin N × Fin N)).filter (fun e => I e.1 e.2)
  let covered : Set (Fin N × Fin N) := {e | I e.1 e.2 ∧ ∃ k < s, W (m+k) ⊆ W o ∧
    (one e.1,one e.2) ∈ W (m+k) ∧ ∃ a b, max a b < m+k ∧ W (m+k) = W a ∩ W b ∧
    ∃ A B, W a = A ×ˢ Set.univ ∧ W b = Set.univ ×ˢ B}
  let U := edges.filter fun e => e ∉ covered
  have memU (e : Fin N × Fin N) : e ∈ U ↔ I e.1 e.2 ∧ e ∉ covered := by simp [U,edges]
  have edgeCount : edges.card = N*(q+1) := by
    have count (l : Fin N) : (edges.filter fun e => e.2 = l).card = q+1 := by
      rw [←hcol l,Fintype.card_subtype]
      apply Finset.card_bij (fun e _ => e.1)
      · intro e he
        obtain ⟨he,hl⟩ := Finset.mem_filter.mp he
        have hI := (Finset.mem_filter.mp he).2
        simpa [hl] using hI
      · intro a ha b hb heq
        exact Prod.ext heq ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
      · intro p hp
        exact ⟨(p,l), by simpa [edges] using hp,rfl⟩
    calc
      edges.card = ∑ l : Fin N, (edges.filter fun e => e.2=l).card := by
        symm
        simpa using Finset.sum_card_fiberwise_eq_card_filter edges (Finset.univ : Finset (Fin N)) Prod.snd
      _ = N*(q+1) := by simp [count]
  have hcovered : (edges.filter fun e => e ∈ covered).card ≤ 4*s := by
    have sub : (edges.filter fun e => e ∈ covered) ⊆ covered.toFinset := by
      intro e he
      simpa only [Set.mem_toFinset] using (Finset.mem_filter.mp he).2
    have hc : covered.ncard ≤ 4*s := hcount
    rw [Set.ncard_eq_toFinset_card'] at hc
    exact (Finset.card_le_card sub).trans hc
  have splitCount : U.card + (edges.filter fun e => e ∈ covered).card = edges.card := by
    simpa only [U,add_comm] using edges.card_filter_add_card_filter_not (fun e => e ∈ covered)
  by_contra! small
  have frac : 25*(12*q/25) ≤ 12*q := Nat.mul_div_le _ _
  have scale := Nat.mul_le_mul_right (N+N) frac
  have dense : (12*q/25)*(N+N) < U.card := by
    nlinarith only [scale, hcovered, splitCount, edgeCount, small]
  obtain ⟨A,B,hA,hB,hrow,hline⟩ := peel N (12*q/25) U dense
  apply (Nat.not_le_of_lt small)
  exact coreBound q N I hq hN hcol hplane s o W hout hin hg pos neg hcount U memU A B hA hB hrow hline
