import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4833_584
    (removeInput : ∀ (n : ℕ) (v : Fin (n + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
        D.size ≤ C.size ∧ ∀ x : Fin n → Bool,
          PEqualNP.MetaComplexity.circuitFun n D x =
            PEqualNP.MetaComplexity.circuitFun (n + 1) C (v.insertNth false x))
    (normalize :
      ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 →
      (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x4 : Fin x1) => Bool.false) = Bool.false → ∃ (x5 :
      PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x5 ∧ x5.size ≤ x2.size ∧
      PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2)
    (lower :
      let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)];
      ∀ (v : Fin 11) (D : PEqualNP.CircuitLowerBounds.Circuit), v.val < 4 →
        PEqualNP.TopForm.IsAO2 10 D →
        (∀ x : Fin 10 → Bool, PEqualNP.MetaComplexity.circuitFun 10 D x =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (v.insertNth false x)) → 19 ≤ D.size) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)),
      ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 :
      ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8
      : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ),
      (9 : ℕ))];
    ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) →
      PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false →
      PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1
      ∅ x6) → (19 : ℕ) ≤ x3.size := by
  intro G v C hv ao agree
  have mono : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    have hop := ao.1 g hg
    have hlen := ao.2.2 g hg
    exact ⟨by simpa using hop, by omega⟩
  obtain ⟨D, dmono, dsize, eval⟩ := removeInput 10 v C mono
  have computes (x : Fin 10 → Bool) : PEqualNP.MetaComplexity.circuitFun 10 D x =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (v.insertNth false x) :=
    (eval x).trans (agree _ (Fin.insertNth_apply_same _ _ _))
  have zero : v.insertNth false (fun _ : Fin 10 => false) = (fun _ : Fin 11 => false) := by
    funext i
    induction i using Fin.succAboveCases v
    · exact Fin.insertNth_apply_same _ _ _
    · exact Fin.insertNth_apply_succAbove _ _ _ _
  have outFalse : PEqualNP.MetaComplexity.circuitFun 10 D (fun _ => false) = false := by
    rw [computes, zero]
    delta PEqualNP.MetaComplexity.NestedCover.graphFun
    simp
  obtain ⟨E, eao, esize, same⟩ := normalize 10 D dmono outFalse
  exact (lower v E hv eao (fun x => (congrFun same x).trans (computes x))).trans (esize.trans dsize)
