import Mathlib
import PEqualNP.Defs

-- Separate the case controlled by singleton and two-input activation tests.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_4869_857
  (hClean :
    have S := PEqualNP.HeptadCover.singerLines3
    have A : (Fin 26 → Bool) → Prop := fun x =>
      ∃ p l : Fin 13, p ∈ S l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
    have short : (Fin 26 → Bool) → Prop := fun x =>
      x = (fun _ => false) ∨ (∃ u : Fin 26, x = fun z => decide (z = u)) ∨
      (∃ u v : Fin 26, x = fun z => decide (z = u ∨ z = v))
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 26 C →
      (∀ u : Fin 26, C.eval (List.ofFn fun z => decide (z = u)) = false) →
      (∀ u v : Fin 26, A (fun z => decide (z = u ∨ z = v)) →
        C.eval (List.ofFn fun z => decide (z = u ∨ z = v)) = true) →
      (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and →
        ∀ x : Fin 26 → Bool, short x → (C.wires (List.ofFn x)).getD (26+j) false = true → A x) →
      64 ≤ C.size)
  (hDirty :
    have r : Finset (Fin 13) → Finset (Fin 13) → List Bool := fun P L =>
      (List.ofFn fun p : Fin 13 => decide (p ∈ P)) ++ List.ofFn fun l : Fin 13 => decide (l ∈ L)
    have S := PEqualNP.HeptadCover.singerLines3
    have A : (Fin 26 → Bool) → Prop := fun x =>
      ∃ p l : Fin 13, p ∈ S l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
    have short : (Fin 26 → Bool) → Prop := fun x =>
      x = (fun _ => false) ∨ (∃ u : Fin 26, x = fun z => decide (z = u)) ∨
      (∃ u v : Fin 26, x = fun z => decide (z = u ∨ z = v))
    have qrow := fun Q => r Q (PEqualNP.HeptadCover.missLines S Q)
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 26 C →
      (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
      2 ≤ PEqualNP.TopForm.andPairs 26 C →
      (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and →
        ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
          ∃ Q ∈ PEqualNP.HeptadCover.quadrangles S,
            (C.wires (qrow Q)).getD (26+j) false ≠ (C.wires (qrow Q)).getD w false) →
      (∀ p l : Fin 13, p ∈ S l → C.eval (r {p} {l}) = true) →
      (∀ Q ∈ PEqualNP.HeptadCover.quadrangles S, C.eval (qrow Q) = false) →
      (∃ j < C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and ∧
        ∃ x : Fin 26 → Bool, short x ∧ ¬ A x ∧
          (C.wires (List.ofFn x)).getD (26+j) false = true) → 64 ≤ C.size) :
  have x1 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x1 x2 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x1)) ++ List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x2); have x2 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → (∀ x5 ∈ x3.gates, x5.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x5.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 → (∀ x7 < x3.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).inputs, ∃ x12 ∈ PEqualNP.HeptadCover.quadrangles x2, (x3.wires (x1 x12 (PEqualNP.HeptadCover.missLines x2 x12))).getD ((26 : ℕ) + x7) Bool.false ≠ (x3.wires (x1 x12 (PEqualNP.HeptadCover.missLines x2 x12))).getD x10 Bool.false) → (∀ (x8 x9 : Finset (Fin (13 : ℕ))), x8.card ≤ (4 : ℕ) → x9.card ≤ (3 : ℕ) → (∀ (x12 : Fin (13 : ℕ)), (x8 ∩ x2 x12).card ≤ (2 : ℕ)) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x9 | x13 ∈ x2 x14}.card ≤ (2 : ℕ)) → x3.eval (x1 x8 x9) = Decidable.decide ¬x9 ⊆ PEqualNP.HeptadCover.missLines x2 x8) → (64 : ℕ) ≤ x3.size := by
  classical
  dsimp only
  intro C wf distinct pairs switches verified
  let S := PEqualNP.HeptadCover.singerLines3
  let r : Finset (Fin 13) → Finset (Fin 13) → List Bool :=
    fun P L => (List.ofFn fun (p : Fin 13) => decide (p ∈ P)) ++
      List.ofFn fun (l : Fin 13) => decide (l ∈ L)
  let A : (Fin 26 → Bool) → Prop := fun x =>
    ∃ p l : Fin 13, p ∈ S l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  let short : (Fin 26 → Bool) → Prop := fun x =>
    x = (fun _ => false) ∨ (∃ u : Fin 26, x = fun z => decide (z = u)) ∨
    (∃ u v : Fin 26, x = fun z => decide (z = u ∨ z = v))
  have testedSmall (P L : Finset (Fin 13)) (hp : P.card ≤ 1) (hl : L.card ≤ 1) :
      C.eval (r P L) = decide (¬ L ⊆ PEqualNP.HeptadCover.missLines S P) := by
    apply verified P L (by omega) (by omega)
    · intro l
      change (P ∩ S l).card ≤ 2
      exact (Finset.card_le_card (Finset.inter_subset_left : P ∩ S l ⊆ P)).trans
        (hp.trans (by decide))
    · intro p
      change {l ∈ L | p ∈ S l}.card ≤ 2
      exact (Finset.card_filter_le L (fun l => p ∈ S l)).trans (hl.trans (by decide))
  have positive (p l : Fin 13) (edge : p ∈ S l) :
      C.eval (r {p} {l}) = true := by
    rw [testedSmall _ _ (by simp) (by simp)]
    apply decide_eq_true
    intro included
    have miss : l ∈ PEqualNP.HeptadCover.missLines S {p} :=
      included (Finset.mem_singleton_self _)
    have apart := (Finset.mem_filter.mp miss).2
    exact Finset.disjoint_left.mp apart edge (Finset.mem_singleton_self _)
  by_cases bad : ∃ j < C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and ∧
      ∃ x : Fin 26 → Bool, short x ∧ ¬ A x ∧
        (C.wires (List.ofFn x)).getD (26+j) false = true
  · apply hDirty C wf distinct pairs switches positive ?_ bad
    intro Q hQ
    let badQuad : Finset (Fin 13) → Prop := fun T =>
      3 < (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 T).card ∨
      ∃ p : Fin 13, 2 < {l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 T |
        p ∈ PEqualNP.HeptadCover.singerLines3 l}.card
    letI (Q : Finset (Fin 13)) : Decidable (badQuad Q) := by
      unfold badQuad
      infer_instance
    have certification :
        ((PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3).filter badQuad).card = 0 := by
      decide +kernel
    have noBad : ¬ badQuad Q := by
      intro h
      have inBad : Q ∈ (PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3).filter badQuad :=
        Finset.mem_filter.mpr ⟨hQ,h⟩
      rw [Finset.card_eq_zero.mp certification] at inBad
      exact Finset.notMem_empty Q inBad
    change Q ∈ (Finset.univ.powersetCard 4).filter
      (fun T => ∀ l : Fin 13, (T ∩ PEqualNP.HeptadCover.singerLines3 l).card ≤ 2) at hQ
    obtain ⟨qc,pc⟩ := Finset.mem_filter.mp hQ
    have four : Q.card = 4 := (Finset.mem_powersetCard.mp qc).2
    have lc : (PEqualNP.HeptadCover.missLines S Q).card ≤ 3 :=
      Nat.le_of_not_gt (fun h => noBad (Or.inl h))
    have cap (p : Fin 13) :
        {l ∈ PEqualNP.HeptadCover.missLines S Q | p ∈ S l}.card ≤ 2 :=
      Nat.le_of_not_gt (fun h => noBad (Or.inr ⟨p,h⟩))
    rw [verified Q (PEqualNP.HeptadCover.missLines S Q) (le_of_eq four) lc pc cap]
    simp [S]
  · apply hClean C wf ?_ ?_ ?_
    · have lhs : ∀ p : Fin 13,
          List.ofFn (fun z : Fin 26 => decide (z = Fin.castAdd 13 p)) = r {p} ∅ := by
        decide +kernel
      have rhs : ∀ l : Fin 13,
          List.ofFn (fun z : Fin 26 => decide (z = Fin.natAdd 13 l)) = r ∅ {l} := by
        decide +kernel
      intro u
      refine Fin.addCases (m := 13) (n := 13) ?_ ?_ u
      · intro p
        rw [lhs p,testedSmall _ _ (by simp) (by simp)]
        simp
      · intro l
        rw [rhs l,testedSmall _ _ (by simp) (by simp)]
        have included : ({l} : Finset (Fin 13)) ⊆ PEqualNP.HeptadCover.missLines S ∅ := by
          intro t _
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp⟩
        simp [included]
    · intro u v hits
      obtain ⟨p,l,edge,hp,hl⟩ := hits
      simp only [decide_eq_true_eq] at hp hl
      have disjointHalves : ∀ p l : Fin 13, Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
        decide +kernel
      have edgeRow : ∀ p l : Fin 13,
          List.ofFn (fun z : Fin 26 => decide (z = Fin.castAdd 13 p ∨ z = Fin.natAdd 13 l)) =
            r {p} {l} := by
        decide +kernel
      rcases hp with e | e <;> rcases hl with f | f
      · exact (disjointHalves p l (e.trans f.symm)).elim
      · subst u
        subst v
        rw [edgeRow]
        exact positive _ _ edge
      · subst u
        subst v
        have reorder (z : Fin 26) :
            (z = Fin.natAdd 13 l ∨ z = Fin.castAdd 13 p) ↔
            (z = Fin.castAdd 13 p ∨ z = Fin.natAdd 13 l) := or_comm
        simp only [reorder]
        rw [edgeRow]
        exact positive _ _ edge
      · exact (disjointHalves p l (e.trans f.symm)).elim
    · intro j hj andGate x hx on
      by_contra inactive
      exact bad ⟨j,hj,andGate,x,hx,inactive,on⟩
