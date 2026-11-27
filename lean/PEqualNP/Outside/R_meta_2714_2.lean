import Mathlib.Data.Fin.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Separate the short unrestricted witness from extracting and counting its normalized star cover.
theorem PEqualNP.Outside.R_meta_2714_2
    (short : ∃ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit),
      M ⊆ E ∧ (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) ∧
      (∀ p q l r, p ≠ q → l ≠ r → ¬ ((p,l) ∈ E ∧ (p,r) ∈ E ∧ (q,l) ∈ E ∧ (q,r) ∈ E)) ∧
      IsAO2 (n+m) C ∧
      (∀ z, circuitFun (n+m) C z = decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) ∧
      C.size + 1 < E.card + M.card)
    (parts : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (D : Circuit) (U : Finset ℕ),
      (∀ p q l r, p ≠ q → l ≠ r → ¬ ((p,l) ∈ E ∧ (p,r) ∈ E ∧ (q,l) ∈ E ∧ (q,r) ∈ E)) →
      IsAO2 (n+m) D →
      (∀ z, circuitFun (n+m) D z = decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      let g := NestedCover.gateAt D
      (∀ w ∈ U, w < n+m ∨
        ∃ i < D.size, w = n+m+i ∧ (g i).op = .or ∧ ∀ u ∈ (g i).inputs, u ∈ U) →
      (∀ i < D.size, (g i).op = .and → ∀ u ∈ (g i).inputs, u ∈ U) →
      let k := n+m+D.size
      ∃ (A : Finset (Fin n ⊕ Fin m)) (R T : (Fin n ⊕ Fin m) → Finset ℕ)
        (F : (Fin n ⊕ Fin m) → ℕ → Finset (Fin n × Fin m)) (a b : ℕ → ℕ) (t : ℕ),
        let W := fun c => (R c).biUnion (F c)
        (∀ e ∈ E, ∃ c ∈ A, e ∈ W c) ∧
        (∀ c ∈ A, ∀ e ∈ W c, c = Sum.inl e.1 ∨ c = Sum.inr e.2) ∧
        (∀ c ∈ A, R c ⊆ Finset.range k ∧ T c ⊆ Finset.range k ∧
          (∀ x < k, x ∉ T c → (F c x).card ≤ 1) ∧
          ∀ x ∈ T c, a x < x ∧ b x < x ∧ F c x = F c (a x) ∪ F c (b x)) ∧
        A.card ≤ t ∧ (∑ c ∈ A, (R c).card) ≤ t ∧ 2*t+(∑ c ∈ A, (T c).card) ≤ D.size+1)
    (forest : ∀ (n m k : ℕ) (T R : Finset ℕ) (S : ℕ → Finset (Fin n × Fin m))
      (a b : ℕ → ℕ), T ⊆ Finset.range k → R ⊆ Finset.range k →
      (∀ x < k, x ∉ T → (S x).card ≤ 1) →
      (∀ x ∈ T, a x < x ∧ b x < x ∧ S x = S (a x) ∪ S (b x)) →
      (R.biUnion S).card ≤ R.card + T.card)
    (count : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m))
      (A : Finset (Fin n ⊕ Fin m)) (W : (Fin n ⊕ Fin m) → Finset (Fin n × Fin m)) (b q : ℕ),
      M ⊆ E → (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) →
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
      (∀ e ∈ E, ∃ c ∈ A, e ∈ W c) →
      (∀ c ∈ A, ∀ e ∈ W c, c = Sum.inl e.1 ∨ c = Sum.inr e.2) →
      (∑ c ∈ A, (W c).card) ≤ b+q → A.card ≤ b → E.card + M.card ≤ 2*b+q) : ¬ (∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  intro normalize
  obtain ⟨n,m,E,M,C,sub,left,right,square,ao,eval,small⟩ := short
  obtain ⟨D,P,L,dao,deval,dsize,typedP,typedL,typedAND⟩ :=
    normalize n m (fun p l => (p,l) ∈ E) C square ao eval
  have pure (w : ℕ) (hw : w ∈ P ∪ L) : w < n+m ∨
      ∃ i < D.size, w = n+m+i ∧ (NestedCover.gateAt D i).op = .or ∧
        ∀ u ∈ (NestedCover.gateAt D i).inputs, u ∈ P ∪ L := by
    rcases Finset.mem_union.mp hw with hp | hl
    · rcases typedP w hp with h | ⟨i,hi,eq,op,hs⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨i,hi,eq,op,fun u hu => Finset.mem_union_left _ (hs u hu)⟩
    · rcases typedL w hl with h | ⟨i,hi,eq,op,hs⟩
      · exact Or.inl h.2
      · exact Or.inr ⟨i,hi,eq,op,fun u hu => Finset.mem_union_right _ (hs u hu)⟩
  have factors (i : ℕ) (hi : i < D.size) (op : (NestedCover.gateAt D i).op = .and) :
      ∀ u ∈ (NestedCover.gateAt D i).inputs, u ∈ P ∪ L := by
    obtain ⟨a,b,eq,⟨aP,bL⟩|⟨aL,bP⟩⟩ := typedAND i hi op
    · rw [eq]
      intro u hu
      rcases List.mem_pair.mp hu with rfl | rfl
      · exact Finset.mem_union_left _ aP
      · exact Finset.mem_union_right _ bL
    · rw [eq]
      intro u hu
      rcases List.mem_pair.mp hu with rfl | rfl
      · exact Finset.mem_union_right _ aL
      · exact Finset.mem_union_left _ bP
  obtain ⟨A,R,T,F,a,b,t,cover,star,localCert,centers,rootCount,budget⟩ :=
    parts n m E D (P ∪ L) square dao deval pure factors
  let W := fun c => (R c).biUnion (F c)
  have leaves : (∑ c ∈ A, (W c).card) ≤ t + (∑ c ∈ A, (T c).card) := by
    calc
      (∑ c ∈ A, (W c).card) ≤ ∑ c ∈ A, ((R c).card + (T c).card) := by
        apply Finset.sum_le_sum
        intro c hc
        obtain ⟨rBound,tBound,terminal,branching⟩ := localCert c hc
        exact forest n m _ _ _ _ a b tBound rBound terminal branching
      _ ≤ _ := by
        rw [Finset.sum_add_distrib]
        omega
  have lower := count n m E M A W t (∑ c ∈ A, (T c).card) sub left right cover star leaves centers
  omega
