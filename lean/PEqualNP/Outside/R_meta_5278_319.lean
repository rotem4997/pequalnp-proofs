import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.LowMerge

-- A zero certificate is a mask of inputs allowed to be on.
-- False certificates of an AND are pooled, and those of an OR are intersected.
-- Every maximal independent quadrangle must occur literally at the output.
set_option maxRecDepth 2048 in
theorem PEqualNP.Outside.R_meta_5278_319
    (compile :
      let bits (V : Finset (Fin 13 ⊕ Fin 13)) :=
        List.ofFn (fun p : Fin 13 => decide (Sum.inl p ∈ V)) ++
        List.ofFn (fun l : Fin 13 => decide (Sum.inr l ∈ V))
      ∀ C : Circuit, IsAO2 26 C → (∃ V, C.eval (bits V) = true) →
        ∃ (F : ℕ → Finset (Finset (Fin 13 ⊕ Fin 13))) (o : ℕ),
          o < 26 + C.size ∧
          (∀ i < 26, ∃ v, F i = {Finset.univ.erase v}) ∧
          (∀ j < C.size, ∃ a < 26+j, ∃ b < 26+j,
            F (26+j) = F a ∪ F b ∨ F (26+j) = Finset.image₂ (· ∩ ·) (F a) (F b)) ∧
          ∀ V, C.eval (bits V) = false ↔ ∃ W ∈ F o, V ⊆ W)
    (outside : ∀ Q ∈ quadrangles singerLines3, ∀ p : Fin 13, p ∉ Q →
      ∃ l ∈ missLines singerLines3 Q, p ∈ singerLines3 l)
    (synthesis : ∀ (s o : ℕ) (F : ℕ → Finset (Finset (Fin 13 ⊕ Fin 13))),
      o < 26+s →
      (∀ i < 26, ∃ v, F i = {Finset.univ.erase v}) →
      (∀ j < s, ∃ a < 26+j, ∃ b < 26+j,
        F (26+j) = F a ∪ F b ∨ F (26+j) = Finset.image₂ (· ∩ ·) (F a) (F b)) →
      (∀ V ∈ F o, IsFree (incidences singerLines3) V) →
      (∀ Q ∈ quadrangles singerLines3, supp singerLines3 Q ∈ F o) → 64 ≤ s) :
have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : Finset (Finset (Fin (13 : ℕ))) := PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ),   have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x3;   have x6 : List Bool → ℕ → Bool := PEqualNP.LowMerge.wireVal x3;   PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → (38 : ℕ) ≤ x3.size → x3.size < (64 : ℕ) → (8 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x3 ∧ (18 : ℕ) ≤ PEqualNP.ReadTwo.nOr x3 → (∀ x11 ∈ x3.gates, x11.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x11.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 → (∀ x13 < x3.size, (x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x16 ∈ (x5 x13).inputs, ∃ x18 ∈ x2, x6 (x1 x18) ((26 : ℕ) + x13) ≠ x6 (x1 x18) x16) → (∀ x14 ∈ x4, x14 < x3.size ∧ (x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ x16 ∈ x2, x6 (x1 x16) ((26 : ℕ) + x14) = Bool.false) → (2 : ℕ) * x4.card ≤ x3.size + (1 : ℕ) → (∀ (x16 : List Bool), x16.length = (26 : ℕ) → (x3.eval x16 = Bool.true ↔ ∃ x18 ∈ x4, x6 x16 ((26 : ℕ) + x18) = Bool.true)) → (∀ (x17 x18 : Fin (13 : ℕ)), x17 ∈ PEqualNP.HeptadCover.singerLines3 x18 → ∃ x20 ∈ x4, x6 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x17 x18) ((26 : ℕ) + x20) = Bool.true) → False := by
  classical
  have maximal : ∀ Q ∈ quadrangles singerLines3, ∀ V, supp singerLines3 Q ⊆ V →
      IsFree (incidences singerLines3) V → V = supp singerLines3 Q := by
    intro Q hQ V sub free
    have incompatible (p l : Fin 13) (h : p ∈ singerLines3 l) :
        ¬ (Sum.inl p ∈ V ∧ Sum.inr l ∈ V) :=
      free (p,l) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    apply Finset.Subset.antisymm _ sub
    intro u hu
    change u ∈ Q.disjSum (missLines singerLines3 Q)
    cases u with
    | inl p =>
      simp only [Finset.inl_mem_disjSum]
      by_contra absent
      obtain ⟨l,hl,inc⟩ := outside Q hQ p absent
      exact incompatible p l inc ⟨hu,sub (Finset.inr_mem_disjSum.mpr hl)⟩
    | inr l =>
      apply Finset.inr_mem_disjSum.mpr
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,Finset.disjoint_left.mpr ?_⟩
      intro p inc hp
      exact incompatible p l inc ⟨sub (Finset.inl_mem_disjSum.mpr hp),hu⟩
  intro N qs C J G W ao _ small _ _ _ _ clean _ output cover
  let bits (V : Finset (Fin 13 ⊕ Fin 13)) :=
    List.ofFn (fun p : Fin 13 => decide (Sum.inl p ∈ V)) ++
    List.ofFn (fun l : Fin 13 => decide (Sum.inr l ∈ V))
  have bitsLength (V) : (bits V).length = 26 := by simp [bits]
  have pairBits (p l : Fin 13) : bits {Sum.inl p, Sum.inr l} = pointLineInput 13 13 p l := by
    change bits _ = List.ofFn (fun q : Fin 13 => decide (q = p)) ++
      List.ofFn (fun k : Fin 13 => decide (k = l))
    simp [bits]
  have heptadBits (Q) : bits (supp singerLines3 Q) = N Q := by
    change _ = List.ofFn _ ++ List.ofFn _
    change bits (Q.disjSum (missLines singerLines3 Q)) = _
    simp [bits]
  have yes (p l : Fin 13) (h : p ∈ singerLines3 l) : C.eval (bits {Sum.inl p, Sum.inr l}) = true := by
    apply (output _ (bitsLength _)).mpr
    rw [pairBits]
    exact cover p l h
  obtain ⟨F, o, ho, seeds, steps, hF⟩ := compile C ao ⟨_, yes 0 0 (by decide)⟩
  have freeness (V) (mem : V ∈ F o) : IsFree (incidences singerLines3) V := by
    intro pl inc pair
    obtain ⟨p, l⟩ := pl
    have incident : p ∈ singerLines3 l := (Finset.mem_filter.mp inc).2
    have sub : ({Sum.inl p, Sum.inr l} : Finset (Fin 13 ⊕ Fin 13)) ⊆ V :=
      Finset.insert_subset_iff.mpr ⟨pair.1, Finset.singleton_subset_iff.mpr pair.2⟩
    have off := (hF _).mpr ⟨V, mem, sub⟩
    change C.eval (bits _) = false at off
    have on := yes p l incident
    exact Bool.noConfusion (on.symm.trans off)
  apply (Nat.not_le_of_gt small) (synthesis C.size o F ho seeds steps freeness ?_)
  intro Q hQ
  have nq : (N Q).length = 26 := by rw [← heptadBits]; apply bitsLength
  have off : C.eval (N Q) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨j, hj, on⟩ := (output _ nq).mp h
    have hOff := (clean j hj).2.2 Q hQ
    exact Bool.noConfusion (hOff.symm.trans on)
  have equation : C.eval (bits (supp singerLines3 Q)) = false := (congrArg C.eval (heptadBits Q)).trans off
  obtain ⟨V, mem, sub⟩ := (hF _).mp equation
  rw [maximal Q hQ V sub (freeness V mem)] at mem
  exact mem
