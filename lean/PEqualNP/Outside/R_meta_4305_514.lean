import Mathlib
import PEqualNP.Defs

-- Peel the incidences that no rectangle gate inside the output explains: if the circuit
-- were small, a nonempty core remains in which every point and every line keeps more than
-- 12q/25 such incidences. The first statement is the peeling count, the second bounds the
-- circuit by its dense core, now with only union and intersection gates, none of them empty.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4305_514
    (peel : ∀ (N k : ℕ) (E : Finset (Fin N × Fin N)), k*(N+N) < E.card →
      ∃ A B : Finset (Fin N), A.Nonempty ∧ B.Nonempty ∧
        (∀ p ∈ A, k < (B.filter fun l => (p,l) ∈ E).card) ∧
        (∀ l ∈ B, k < (A.filter fun p => (p,l) ∈ E).card))
    (coreClean : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   let x5 : Type := Fin x2 → Bool;   ∀ (x6 x7 : ℕ) (x8 : ℕ → Set (x5 × x5)),     have x9 : ℕ := x2 + x2;     have x10 : Fin x2 → Fin x2 → Bool := fun (x10 x11 : Fin x2) => Decidable.decide (x11 = x10);     have x11 : Set (Fin x2 × Fin x2) := {x11 : Fin x2 × Fin x2 | x3 x11.1 x11.2 ∧ ∃ x12 < x6, x8 (x9 + x12) ⊆ x8 x7 ∧ (x10 x11.1, x10 x11.2) ∈ x8 (x9 + x12) ∧ ∃ (x13 : ℕ) (x14 : ℕ), Max.max x13 x14 < x9 + x12 ∧ x8 (x9 + x12) = x8 x13 ∩ x8 x14 ∧ ∃ (x15 : Set x5) (x16 : Set x5), x8 x13 = x15 ×ˢ Set.univ ∧ x8 x14 = Set.univ ×ˢ x16};     (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x14 : Fin x2), Fintype.card { x15 : Fin x2 // x3 x15 x14 } = x1 + (1 : ℕ)) → (∀ (x15 x16 : Fin x2), x15 ≠ x16 → ∃! x18 : Fin x2, x3 x15 x18 ∧ x3 x16 x18) → x7 < x9 + x6 → (∀ (x17 : ℕ), x8 x17 ≠ ∅) → (∀ (x18 : Fin x2), x8 ↑x18 = {x19 : x5 × x5 | x19.1 x18 = Bool.true} ∧ x8 (x2 + ↑x18) = {x19 : x5 × x5 | x19.2 x18 = Bool.true}) → (∀ x19 < x6, ∃ (x21 : ℕ) (x22 : ℕ), Max.max x21 x22 < x9 + x19 ∧ (x8 (x9 + x19) = x8 x21 ∪ x8 x22 ∨ x8 (x9 + x19) = x8 x21 ∩ x8 x22)) → (∀ (x20 x21 : Fin x2), x3 x20 x21 → (x10 x20, x10 x21) ∈ x8 x7) → (∀ (x21 : x5), Fintype.card { x22 : Fin x2 // x21 x22 = Bool.true } ≤ x1 → (fun (x23 : Fin x2) => Decidable.decide ¬∃ (x24 : Fin x2), x3 x23 x24 ∧ x21 x24 = Bool.true, x21) ∉ x8 x7) → x11.ncard ≤ (4 : ℕ) * x6 → ∀ (x23 : Finset (Fin x2 × Fin x2)), (∀ (x24 : Fin x2 × Fin x2), x24 ∈ x23 ↔ x3 x24.1 x24.2 ∧ x24 ∉ x11) → ∀ (x25 x26 : Finset (Fin x2)), x25.Nonempty → x26.Nonempty → (∀ x29 ∈ x25, (12 : ℕ) * x1 / (25 : ℕ) < {x31 ∈ x26 | (x29, x31) ∈ x23}.card) → (∀ x30 ∈ x26, (12 : ℕ) * x1 / (25 : ℕ) < {x32 ∈ x25 | (x32, x30) ∈ x23}.card) → x2 * x1 ≤ (100 : ℕ) * x6) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   let x5 : Type := Fin x2 → Bool;   have x6 : ℕ := x2 + x2;   have x7 : Fin x2 → Fin x2 → Bool := fun (x7 x8 : Fin x2) => Decidable.decide (x8 = x7);   (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x10 : Fin x2), Fintype.card { x11 : Fin x2 // x3 x11 x10 } = x1 + (1 : ℕ)) → (∀ (x11 x12 : Fin x2), x11 ≠ x12 → ∃! x14 : Fin x2, x3 x11 x14 ∧ x3 x12 x14) → ∀ (x12 x13 : ℕ) (x14 : ℕ → Set (x5 × x5)), x13 < x6 + x12 → (∀ (x16 : ℕ), x14 x16 ≠ ∅) → (∀ (x17 : Fin x2), x14 ↑x17 = {x18 : x5 × x5 | x18.1 x17 = Bool.true} ∧ x14 (x2 + ↑x17) = {x18 : x5 × x5 | x18.2 x17 = Bool.true}) → (∀ x18 < x12, ∃ (x20 : ℕ) (x21 : ℕ), Max.max x20 x21 < x6 + x18 ∧ (x14 (x6 + x18) = x14 x20 ∪ x14 x21 ∨ x14 (x6 + x18) = x14 x20 ∩ x14 x21)) → (∀ (x19 x20 : Fin x2), x3 x19 x20 → (x7 x19, x7 x20) ∈ x14 x13) → (∀ (x20 : x5), Fintype.card { x21 : Fin x2 // x20 x21 = Bool.true } ≤ x1 → (fun (x22 : Fin x2) => Decidable.decide ¬∃ (x23 : Fin x2), x3 x22 x23 ∧ x20 x23 = Bool.true, x20) ∉ x14 x13) → {x21 : Fin x2 × Fin x2 | x3 x21.1 x21.2 ∧ ∃ x22 < x12, x14 (x6 + x22) ⊆ x14 x13 ∧ (x7 x21.1, x7 x21.2) ∈ x14 (x6 + x22) ∧ ∃ (x23 : ℕ) (x24 : ℕ), Max.max x23 x24 < x6 + x22 ∧ x14 (x6 + x22) = x14 x23 ∩ x14 x24 ∧ ∃ (x25 : Set x5) (x26 : Set x5), x14 x23 = x25 ×ˢ Set.univ ∧ x14 x24 = Set.univ ×ˢ x26}.ncard ≤ (4 : ℕ) * x12 → x2 * x1 ≤ (100 : ℕ) * x12 := by
  classical
  intro q N I inst X m one hq hN hcol hplane s o W hout hlive hin hg pos neg hcount
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
  exact coreClean q N I s o W hq hN hcol hplane hout hlive hin hg pos neg hcount U memU A B hA hB hrow hline
