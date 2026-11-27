import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2714_1
    (short : ∃ (N : ℕ) (S : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ i : Fin N, i ∈ S i) ∧
      (∀ i j : Fin N, i ≠ j → (S i ∩ S j).card ≤ 1) ∧ PEqualNP.TopForm.IsAO2 (N+N) C ∧
      (∀ z : Fin (N+N) → Bool, PEqualNP.MetaComplexity.circuitFun (N+N) C z =
        decide (∃ p l : Fin N, p ∈ S l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧ C.size + 1 < (PEqualNP.HeptadCover.incidences S).card + N)
    (bound : ∀ (N : ℕ) (S : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (W : Finset ℕ), (∀ i : Fin N, i ∈ S i) →
      (∀ i j : Fin N, i ≠ j → (S i ∩ S j).card ≤ 1) → PEqualNP.TopForm.IsAO2 (N+N) C →
      (∀ z : Fin (N+N) → Bool, PEqualNP.MetaComplexity.circuitFun (N+N) C z =
        decide (∃ p l : Fin N, p ∈ S l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      let g := PEqualNP.MetaComplexity.NestedCover.gateAt C
      (∀ w ∈ W, w < N+N ∨ ∃ i < C.size, w=N+N+i ∧ (g i).op=.or ∧ ∀ u ∈ (g i).inputs, u ∈ W) →
      (∀ i < C.size, (g i).op=.and → ∀ u ∈ (g i).inputs, u ∈ W) →
      (PEqualNP.HeptadCover.incidences S).card + N ≤ C.size + 1) :
    ¬ (∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  intro normalize
  obtain ⟨N,S,C,diag,linear,model,works,small⟩ := short
  have sq (p q l m : Fin N) (pq : p ≠ q) (lm : l ≠ m) :
      ¬ (p ∈ S l ∧ p ∈ S m ∧ q ∈ S l ∧ q ∈ S m) := by
    rintro ⟨a,b,c,d⟩
    exact pq (Finset.card_le_one.mp (linear _ _ lm) p (Finset.mem_inter.mpr ⟨a,b⟩)
      q (Finset.mem_inter.mpr ⟨c,d⟩))
  obtain ⟨D,P,L,md,wd,budget,hp,hl,ha⟩ := normalize N N (fun p l => p ∈ S l) C sq model works
  have closed (w : ℕ) (hw : w ∈ P ∪ L) : w < N+N ∨ ∃ i < D.size, w=N+N+i ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op=.or ∧
      ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P ∪ L := by
    rcases Finset.mem_union.mp hw with h|h
    · rcases hp w h with input|⟨i,hi,eq,op,parents⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨i,hi,eq,op,fun u hu => Finset.mem_union_left L (parents u hu)⟩
    · rcases hl w h with input|⟨i,hi,eq,op,parents⟩
      · exact Or.inl input.2
      · exact Or.inr ⟨i,hi,eq,op,fun u hu => Finset.mem_union_right P (parents u hu)⟩
  have count := bound N S D (P ∪ L) diag linear md wd closed (by
    intro i hi op u hu
    obtain ⟨a,b,eq,h⟩ := ha i hi op
    rw [eq,List.mem_pair] at hu
    rcases h with ⟨pa,lb⟩|⟨la,pb⟩ <;> rcases hu with rfl|rfl
    · exact Finset.mem_union_left _ pa
    · exact Finset.mem_union_right _ lb
    · exact Finset.mem_union_right _ la
    · exact Finset.mem_union_left _ pb)
  omega
