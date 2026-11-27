import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1955

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

theorem cardL {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ p ∈ A, (B.filter (fun w => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

theorem cardR {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ w ∈ B, (A.filter (fun p => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.card_filter]

theorem cover {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpt : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (A B : Finset (Fin N)) (hc : ∀ p w : Fin N, I p w → p ∈ A ∨ w ∈ B) :
    N ≤ A.card + B.card := by
  have hE : (((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = N * (q + 1) := by
    rw [cardR, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hA : ((A ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = A.card * (q + 1) := by
    rw [cardL, Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_const, smul_eq_mul]
  have hB : (((Finset.univ : Finset (Fin N)) ×ˢ B).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = B.card * (q + 1) := by
    rw [cardR, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, smul_eq_mul]
  have hsub : ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)
      ⊆ ((A ×ˢ (Finset.univ : Finset (Fin N))).filter (fun pw : Fin N × Fin N => I pw.1 pw.2))
        ∪ (((Finset.univ : Finset (Fin N)) ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)) := by
    rintro ⟨p, w⟩ h
    have hI : I p w := (Finset.mem_filter.mp h).2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product]
    rcases hc p w hI with h1 | h1
    · exact Or.inl ⟨⟨h1, Finset.mem_univ _⟩, hI⟩
    · exact Or.inr ⟨⟨Finset.mem_univ _, h1⟩, hI⟩
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hE, hA, hB, ← Nat.add_mul] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.succ_pos q)

theorem count {N : ℕ} (q k : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (lps pps : Fin N → Fin N → Prop)
    (hpt : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1) (hkq : k ≤ q)
    (hL : ∀ p w : Fin N, I p w → lps p w ∨ pps p w) :
    (k + 1) * N ≤ ∑ w : Fin N, Set.ncard {p : Fin N | lps p w}
      + ∑ p : Fin N, min (k + 1) (Set.ncard {w : Fin N | pps p w}) := by
  classical
  have e1 : ∀ w : Fin N, Set.ncard {p : Fin N | lps p w}
      = (Finset.univ.filter (fun p : Fin N => lps p w)).card := by
    intro w
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p
    simp
  have e2 : ∀ p : Fin N, Set.ncard {w : Fin N | pps p w}
      = (Finset.univ.filter (fun w : Fin N => pps p w)).card := by
    intro p
    rw [← Set.ncard_coe_finset]
    congr 1
    ext w
    simp
  have e3 : ∑ w : Fin N, (Finset.univ.filter (fun p : Fin N => lps p w)).card
      = ∑ p : Fin N, (Finset.univ.filter (fun w : Fin N => lps p w)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hp : ∀ p : Fin N, k + 1 ≤ (Finset.univ.filter (fun w : Fin N => lps p w)).card
      + min (k + 1) (Set.ncard {w : Fin N | pps p w}) := by
    intro p
    rw [e2 p]
    have hsub : Finset.univ.filter (fun l => I p l)
        ⊆ Finset.univ.filter (fun w : Fin N => lps p w)
          ∪ Finset.univ.filter (fun w : Fin N => pps p w) := by
      intro w hw
      have hI : I p w := (Finset.mem_filter.mp hw).2
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases hL p w hI with h1 | h1
      · exact Or.inl ⟨Finset.mem_univ _, h1⟩
      · exact Or.inr ⟨Finset.mem_univ _, h1⟩
    have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [hpt p] at h
    omega
  rw [Finset.sum_congr rfl (fun w _ => e1 w), e3, ← Finset.sum_add_distrib]
  calc (k + 1) * N = ∑ _p : Fin N, (k + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun p _ => hp p)

end PEqualNP.Outside.L_meta_1955

theorem PEqualNP.Outside.L_meta_1955 : (∀ (N260 k260 t260 : ℕ) (I260 : Fin N260 → Fin N260 → Prop) [DecidableRel I260] (C260 : PEqualNP.CircuitLowerBounds.Circuit), (∀ p260 p260x1 w260 w260x1 : Fin N260, p260 ≠ p260x1 → w260 ≠ w260x1 → I260 p260 w260 → I260 p260x1 w260 → I260 p260 w260x1 → I260 p260x1 w260x1 → False) → (∃ p260x2 w260x2 : Fin N260, I260 p260x2 w260x2) → 1 ≤ k260 → ((∀ g260 ∈ C260.gates, (g260.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g260.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g260.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N260 + N260) C260) → (∀ j260 < C260.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i260 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).inputs, (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 + N260))).getD i260 0 = 0) ∨ (∀ h260 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).inputs, (C260.lineDegrees (N260 + N260) (Finset.range N260)).getD h260 0 = 0)) → (∀ p260x3 w260x3 : Fin N260, I260 p260x3 w260x3 → PEqualNP.MetaComplexity.circuitFun (N260 + N260) C260 (Fin.append (fun a260 : Fin N260 => decide (a260 = p260x3)) (fun a260x1 : Fin N260 => decide (a260x1 = w260x3))) = true) → (∀ x260 y260 : Fin N260 → Bool, (Finset.univ.filter (fun l260 : Fin N260 => y260 l260 = true)).card ≤ k260 → (¬ ∃ p260x4 w260x4 : Fin N260, I260 p260x4 w260x4 ∧ x260 p260x4 = true ∧ y260 w260x4 = true) → PEqualNP.MetaComplexity.circuitFun (N260 + N260) C260 (Fin.append x260 y260) = false) → (∀ A260 B260 : Finset (Fin N260), (∀ p260x5 w260x5 : Fin N260, I260 p260x5 w260x5 → p260x5 ∈ A260 ∨ w260x5 ∈ B260) → t260 ≤ A260.card + B260.card) → ∀ mixed260 : ℕ → Prop, mixed260 = (fun i260x1 : ℕ => 0 < (C260.lineDegrees (N260 + N260) (Finset.range N260)).getD i260x1 0 ∧ 0 < (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 + N260))).getD i260x1 0) → ∀ cone260 : ℕ → Prop, cone260 = (fun j260x1 : ℕ => j260x1 < C260.gates.length ∧ mixed260 (N260 + N260 + j260x1) ∧ Relation.ReflTransGen (fun a260x2 b260 : ℕ => a260x2 < b260 ∧ ∃ f260 : Fin C260.gates.length, b260 = N260 + N260 + f260.val ∧ a260x2 ∈ (C260.gates.get f260).inputs) (N260 + N260 + j260x1) C260.output) → ∀ gok260 : (Fin N260 → Bool) → ℕ → Prop, gok260 = (fun (x260x1 : Fin N260 → Bool) (j260x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i260x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x2).inputs, (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 + N260))).getD i260x2 0 = 0 ∧ (C260.wires (List.ofFn (Fin.append x260x1 (fun u260 : Fin N260 => false)))).getD i260x2 false = true) → ∀ step260 : (Fin N260 → Bool) → ℕ → ℕ → Prop, step260 = (fun (x260x2 : Fin N260 → Bool) (j260x3 j260x4 : ℕ) => cone260 j260x4 ∧ N260 + N260 + j260x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x4).inputs ∧ gok260 x260x2 j260x4) → ∀ lvx260 : (Fin N260 → Bool) → ℕ → Prop, lvx260 = (fun (x260x3 : Fin N260 → Bool) (j260x5 : ℕ) => cone260 j260x5 ∧ gok260 x260x3 j260x5 ∧ ∃ j260x6 : ℕ, N260 + N260 + j260x6 = C260.output ∧ Relation.ReflTransGen (step260 x260x3) j260x5 j260x6) → ∀ slot260 : ℕ → ℕ → Prop, slot260 = (fun h260x1 j260x7 : ℕ => cone260 j260x7 ∧ h260x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x7).inputs ∧ (C260.lineDegrees (N260 + N260) (Finset.range N260)).getD h260x1 0 = 0) → ∀ ap260 : ℕ → Fin N260 → Prop, ap260 = (fun (h260x2 : ℕ) (p260x6 : Fin N260) => ∃ j260x8 : ℕ, slot260 h260x2 j260x8 ∧ lvx260 (fun a260x3 : Fin N260 => decide (a260x3 = p260x6)) j260x8) → ∀ lh260 : ℕ → Fin N260 → Prop, lh260 = (fun (h260x3 : ℕ) (w260x6 : Fin N260) => (C260.wires (List.ofFn (Fin.append (fun u260x1 : Fin N260 => false) (fun a260x4 : Fin N260 => decide (a260x4 = w260x6))))).getD h260x3 false = true) → ∀ lpw260 : ℕ → Fin N260 → Prop, lpw260 = (fun (h260x4 : ℕ) (w260x7 : Fin N260) => ∀ w260x8 : Fin N260, lh260 h260x4 w260x8 ↔ w260x8 = w260x7) → ∀ ppw260 : ℕ → Fin N260 → Prop, ppw260 = (fun (h260x5 : ℕ) (p260x7 : Fin N260) => (∃ w260x9 w260x10 : Fin N260, w260x9 ≠ w260x10 ∧ lh260 h260x5 w260x9 ∧ lh260 h260x5 w260x10) ∧ ∀ p260x8 : Fin N260, ap260 h260x5 p260x8 ↔ p260x8 = p260x7) → ∀ lps260 : Fin N260 → Fin N260 → Prop, lps260 = (fun p260x9 w260x11 : Fin N260 => ∃ h260x6 : ℕ, lpw260 h260x6 w260x11 ∧ ap260 h260x6 p260x9) → ∀ pps260 : Fin N260 → Fin N260 → Prop, pps260 = (fun p260x10 w260x12 : Fin N260 => ∃ h260x7 : ℕ, ppw260 h260x7 p260x10 ∧ lh260 h260x7 w260x12) → ∑ w260x13 : Fin N260, Set.ncard {p260x11 : Fin N260 | lps260 p260x11 w260x13} + ∑ p260x12 : Fin N260, min (k260 + 1) (Set.ncard {w260x14 : Fin N260 | pps260 p260x12 w260x14}) + t260 ≤ C260.size + 1) → (∀ (N231 : ℕ) (I231 : Fin N231 → Fin N231 → Prop) [DecidableRel I231] (C231 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g231 ∈ C231.gates, (g231.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g231.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g231.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N231 + N231) C231) → (∀ j231 < C231.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231 0 = 0) ∨ (∀ h231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231 0 = 0)) → (∀ p231 p231x1 w231 w231x1 : Fin N231, p231 ≠ p231x1 → w231 ≠ w231x1 → I231 p231 w231 → I231 p231x1 w231 → I231 p231 w231x1 → I231 p231x1 w231x1 → False) → (∃ p231x2 w231x2 : Fin N231, I231 p231x2 w231x2) → (∀ p231x3 w231x3 : Fin N231, I231 p231x3 w231x3 → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append (fun a231 : Fin N231 => decide (a231 = p231x3)) (fun a231x1 : Fin N231 => decide (a231x1 = w231x3))) = true) → (∀ x231 y231 : Fin N231 → Bool, (Finset.univ.filter (fun l231 : Fin N231 => y231 l231 = true)).card ≤ 1 → (¬ ∃ p231x4 w231x4 : Fin N231, I231 p231x4 w231x4 ∧ x231 p231x4 = true ∧ y231 w231x4 = true) → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231 y231) = false) → ∀ mixed231 : ℕ → Prop, mixed231 = (fun i231x1 : ℕ => 0 < (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD i231x1 0 ∧ 0 < (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x1 0) → ∀ cone231 : ℕ → Prop, cone231 = (fun j231x1 : ℕ => j231x1 < C231.gates.length ∧ mixed231 (N231 + N231 + j231x1) ∧ Relation.ReflTransGen (fun a231x2 b231 : ℕ => a231x2 < b231 ∧ ∃ f231 : Fin C231.gates.length, b231 = N231 + N231 + f231.val ∧ a231x2 ∈ (C231.gates.get f231).inputs) (N231 + N231 + j231x1) C231.output) → ∀ gok231 : (Fin N231 → Bool) → ℕ → Prop, gok231 = (fun (x231x1 : Fin N231 → Bool) (j231x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i231x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x2 0 = 0 ∧ (C231.wires (List.ofFn (Fin.append x231x1 (fun u231 : Fin N231 => false)))).getD i231x2 false = true) → ∀ step231 : (Fin N231 → Bool) → ℕ → ℕ → Prop, step231 = (fun (x231x2 : Fin N231 → Bool) (j231x3 j231x4 : ℕ) => cone231 j231x4 ∧ N231 + N231 + j231x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x4).inputs ∧ gok231 x231x2 j231x4) → ∀ lvx231 : (Fin N231 → Bool) → ℕ → Prop, lvx231 = (fun (x231x3 : Fin N231 → Bool) (j231x5 : ℕ) => cone231 j231x5 ∧ gok231 x231x3 j231x5 ∧ ∃ j231x6 : ℕ, N231 + N231 + j231x6 = C231.output ∧ Relation.ReflTransGen (step231 x231x3) j231x5 j231x6) → ∀ slot231 : ℕ → ℕ → Prop, slot231 = (fun h231x1 j231x7 : ℕ => cone231 j231x7 ∧ h231x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x7).inputs ∧ (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231x1 0 = 0) → ∀ ap231 : ℕ → Fin N231 → Prop, ap231 = (fun (h231x2 : ℕ) (p231x5 : Fin N231) => ∃ j231x8 : ℕ, slot231 h231x2 j231x8 ∧ lvx231 (fun a231x3 : Fin N231 => decide (a231x3 = p231x5)) j231x8) → ∀ lh231 : ℕ → Fin N231 → Prop, lh231 = (fun (h231x3 : ℕ) (w231x5 : Fin N231) => (C231.wires (List.ofFn (Fin.append (fun u231x1 : Fin N231 => false) (fun a231x4 : Fin N231 => decide (a231x4 = w231x5))))).getD h231x3 false = true) → ∀ lpw231 : ℕ → Fin N231 → Prop, lpw231 = (fun (h231x4 : ℕ) (w231x6 : Fin N231) => ∀ w231x7 : Fin N231, lh231 h231x4 w231x7 ↔ w231x7 = w231x6) → ∀ ppw231 : ℕ → Fin N231 → Prop, ppw231 = (fun (h231x5 : ℕ) (p231x6 : Fin N231) => (∃ w231x8 w231x9 : Fin N231, w231x8 ≠ w231x9 ∧ lh231 h231x5 w231x8 ∧ lh231 h231x5 w231x9) ∧ ∀ p231x7 : Fin N231, ap231 h231x5 p231x7 ↔ p231x7 = p231x6) → ∀ lps231 : Fin N231 → Fin N231 → Prop, lps231 = (fun p231x8 w231x10 : Fin N231 => ∃ h231x6 : ℕ, lpw231 h231x6 w231x10 ∧ ap231 h231x6 p231x8) → ∀ pps231 : Fin N231 → Fin N231 → Prop, pps231 = (fun p231x9 w231x11 : Fin N231 => ∃ h231x7 : ℕ, ppw231 h231x7 p231x9 ∧ lh231 h231x7 w231x11) → (∃ j231x9 : ℕ, N231 + N231 + j231x9 = C231.output ∧ cone231 j231x9) ∧ (∀ (x231x4 y231x1 : Fin N231 → Bool) (h231x8 j231x10 : ℕ), slot231 h231x8 j231x10 → lvx231 x231x4 j231x10 → (C231.wires (List.ofFn (Fin.append (fun u231x2 : Fin N231 => false) y231x1))).getD h231x8 false = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x4 y231x1) = true) ∧ (∀ x231x5 y231x2 : Fin N231 → Bool, PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 y231x2) = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 (fun u231x3 : Fin N231 => false)) = false → ∃ h231x9 j231x11 : ℕ, slot231 h231x9 j231x11 ∧ lvx231 x231x5 j231x11 ∧ (C231.wires (List.ofFn (Fin.append (fun u231x4 : Fin N231 => false) y231x2))).getD h231x9 false = true) ∧ (∀ (h231x10 j231x12 : ℕ) (w231x12 : Fin N231), slot231 h231x10 j231x12 → lh231 h231x10 w231x12 → ¬ lvx231 (fun a231x5 : Fin N231 => decide (¬ I231 a231x5 w231x12)) j231x12) ∧ (∀ (h231x11 : ℕ) (p231x10 w231x13 : Fin N231), ap231 h231x11 p231x10 → lh231 h231x11 w231x13 → I231 p231x10 w231x13) ∧ (∀ p231x11 w231x14 : Fin N231, I231 p231x11 w231x14 → lps231 p231x11 w231x14 ∨ pps231 p231x11 w231x14)) → ∀ (q261 N261 k261 : ℕ) (I261 : Fin N261 → Fin N261 → Prop) [DecidableRel I261] (C261 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q261 → N261 = q261 ^ 2 + q261 + 1 → (∀ l261 : Fin N261, (Finset.univ.filter (fun p261 => I261 p261 l261)).card = q261 + 1) → (∀ pa261 pb261 : Fin N261, pa261 ≠ pb261 → ∃! lb261 : Fin N261, I261 pa261 lb261 ∧ I261 pb261 lb261) → 1 ≤ k261 → k261 ≤ q261 → ((∀ g261 ∈ C261.gates, (g261.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g261.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g261.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N261 + N261) C261) → (∀ j261 < C261.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C261 j261).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i261 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C261 j261).inputs, (C261.lineDegrees (N261 + N261) (Finset.Ico N261 (N261 + N261))).getD i261 0 = 0) ∨ (∀ h261 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C261 j261).inputs, (C261.lineDegrees (N261 + N261) (Finset.range N261)).getD h261 0 = 0)) → (∀ p261x1 l261x1 : Fin N261, I261 p261x1 l261x1 → PEqualNP.MetaComplexity.circuitFun (N261 + N261) C261 (fun i261x1 => decide (i261x1 = Fin.castAdd N261 p261x1 ∨ i261x1 = Fin.natAdd N261 l261x1)) = true) → (∀ z261 : Fin (N261 + N261) → Bool, (Finset.univ.filter (fun l261x2 : Fin N261 => z261 (Fin.natAdd N261 l261x2) = true)).card ≤ k261 → (¬ ∃ p261x2 l261x3 : Fin N261, I261 p261x2 l261x3 ∧ z261 (Fin.castAdd N261 p261x2) = true ∧ z261 (Fin.natAdd N261 l261x3) = true) → PEqualNP.MetaComplexity.circuitFun (N261 + N261) C261 z261 = false) → (k261 + 2) * N261 ≤ C261.size + 1 := by
  intro H1 H2 q N k I inst C hq hN hl hu hk1 hkq hshape hkm hcomp hsound
  have hpt := PEqualNP.Outside.L_meta_1955.lines_through q N I hq hN hl hu
  have h4 : ∀ p p' w w' : Fin N, p ≠ p' → w ≠ w' → I p w → I p' w → I p w' → I p' w' → False := by
    intro p p' w w' hp hw a b c d
    exact hw ((hu p p' hp).unique ⟨a, b⟩ ⟨c, d⟩)
  have hne : ∃ p w : Fin N, I p w := by
    have hpos : 0 < N := by
      rw [hN]
      exact Nat.succ_pos _
    have hc : 0 < (Finset.univ.filter (fun p => I p (⟨0, hpos⟩ : Fin N))).card := by
      rw [hl]
      exact Nat.succ_pos _
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hc
    exact ⟨p, ⟨0, hpos⟩, (Finset.mem_filter.mp hp).2⟩
  have hcomp' : ∀ p w : Fin N, I p w → PEqualNP.MetaComplexity.circuitFun (N + N) C
      (Fin.append (fun a : Fin N => decide (a = p)) (fun a : Fin N => decide (a = w))) = true := by
    intro p w hI
    have e : Fin.append (fun a : Fin N => decide (a = p)) (fun a : Fin N => decide (a = w))
        = (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N w)) := by
      funext i
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i
      · rw [Fin.append_left, decide_eq_decide]
        have h1 := a.isLt
        simp only [Fin.ext_iff, Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      · rw [Fin.append_right, decide_eq_decide]
        have h1 := p.isLt
        simp only [Fin.ext_iff, Fin.coe_castAdd, Fin.coe_natAdd]
        omega
    rw [e]
    exact hcomp p w hI
  have hsound' : ∀ x y : Fin N → Bool,
      (Finset.univ.filter (fun l : Fin N => y l = true)).card ≤ k →
      (¬ ∃ p w : Fin N, I p w ∧ x p = true ∧ y w = true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C (Fin.append x y) = false := by
    intro x y hy hno
    have h := hsound (Fin.append x y)
    simp only [Fin.append_left, Fin.append_right] at h
    exact h hy hno
  have hsound1 : ∀ x y : Fin N → Bool,
      (Finset.univ.filter (fun l : Fin N => y l = true)).card ≤ 1 →
      (¬ ∃ p w : Fin N, I p w ∧ x p = true ∧ y w = true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C (Fin.append x y) = false :=
    fun x y hy hno => hsound' x y (hy.trans hk1) hno
  have hcov := PEqualNP.Outside.L_meta_1955.cover q I hl hpt
  have T := H1 N k N I C h4 hne hk1 hshape hkm hcomp' hsound' hcov
    _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
  have L := (H2 N I C hshape hkm h4 hne hcomp' hsound1
    _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl).2.2.2.2.2
  have hc := PEqualNP.Outside.L_meta_1955.count q k I _ _ hpt hkq L
  have e : (k + 2) * N = (k + 1) * N + N := by ring
  rw [e]
  exact le_trans (Nat.add_le_add_right hc N) T
