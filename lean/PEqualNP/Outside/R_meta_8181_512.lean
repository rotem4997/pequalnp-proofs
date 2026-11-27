import Mathlib
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_8181_512
    (charge : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n+m) C →
      (∀ z, circuitFun (n+m) C z = decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      ∃ T : Finset (Fin (n+m)),
        (∀ e ∈ E, Fin.castAdd m e.1 ∈ T ∨ Fin.natAdd n e.2 ∈ T) ∧
        E.card + T.card ≤ C.size + 1)
    (stars : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (T : Finset (Fin (n+m))),
      E.Nonempty →
      (∀ e ∈ E, Fin.castAdd m e.1 ∈ T ∨ Fin.natAdd n e.2 ∈ T) →
      ∃ D : Circuit, IsAO2 (n+m) D ∧
        (∀ z, circuitFun (n+m) D z = decide (∃ p l, (p,l) ∈ E ∧
          z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) ∧
        D.size + 1 ≤ E.card + T.card) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))),   have x7 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true);   have x8 : Prop :=     ∃ (x8 : Fin (x1 + x2)),       have x9 : ℕ := (x6.neighborSet x8).ncard;       have x10 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x5 ↑x8;       (2 : ℕ) ≤ x9 ∧ (x9 < x10.card ∨ x9 = x10.card ∧ ∃ x11 ∈ x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.readers (x1 + x2) x5 x11 ⊆ x10);   (∀ (x9 x10 : Fin (x1 + x2)), x6.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) → ¬x6.IsAcyclic → x7 x3 x5 → (∀ x12 ∈ x4, ∀ x14 ∈ x4, x12.1 = x14.1 → x12 = x14) → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.2 = x15.2 → x13 = x15) → x4 ⊆ x3 → (∀ (x15 x16 : Fin x1) (x17 x18 : Fin x2), x15 ≠ x16 → x17 ≠ x18 → ¬((x15, x17) ∈ x3 ∧ (x15, x18) ∈ x3 ∧ (x16, x17) ∈ x3 ∧ (x16, x18) ∈ x3)) → (∀ x16 ∈ x3, ((∀ x18 ∈ x3, x18.1 = x16.1 → x18 = x16) ∨ ∀ x18 ∈ x3, x18.2 = x16.2 → x18 = x16) → (x3.erase x16).Nonempty → x16 ∈ x4) → ¬x8 → ∃ x18 ∈ x3, x18 ∉ x4 ∧ ∃ (x19 : PEqualNP.CircuitLowerBounds.Circuit), x19.size < x5.size ∧ x7 (x3.erase x18) x19 := by
  classical
  intro n m E M C G ok overflow adj cycle realizes left right Msub square pendant quiet
  obtain ⟨v, w, hw⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp cycle
  let edge : Fin n × Fin m → Sym2 (Fin (n+m)) :=
    fun e => s(Fin.castAdd m e.1, Fin.natAdd n e.2)
  have sub : G.edgeFinset ⊆ E.image edge := by
    intro z hz
    rw [SimpleGraph.mem_edgeFinset] at hz
    induction z using Sym2.inductionOn with
    | _ i j =>
      obtain ⟨e, he, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adj i j).1 hz
      · exact Finset.mem_image_of_mem edge he
      · rw [Sym2.eq_swap]
        exact Finset.mem_image_of_mem edge he
  have three : 3 ≤ E.card := by
    calc
      3 ≤ w.length := hw.three_le_length
      _ ≤ G.edgeSet.ncard := hw.isTrail.length_le_ncard_edgeSet
      _ = G.edgeFinset.card := by
        simpa only [SimpleGraph.edgeFinset] using Set.ncard_eq_toFinset_card' G.edgeSet
      _ ≤ (E.image edge).card := Finset.card_le_card sub
      _ ≤ E.card := Finset.card_image_le
  have unmatched : ∃ e ∈ E, e ∉ M := by
    classical
    by_contra! allM
    have sep (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
      intro eq
      have h := congrArg Fin.val eq
      change a.val = n + b.val at h
      omega
    have unique (v u w : Fin (n+m)) (hu : G.Adj v u) (hv : G.Adj v w) : u = w := by
      obtain ⟨e, he, ⟨ve,ue⟩ | ⟨ue,ve⟩⟩ := (adj _ _).mp hu <;>
        obtain ⟨f, hf, ⟨vf,wf⟩ | ⟨wf,vf⟩⟩ := (adj _ _).mp hv
      · have ef := left e (allM e he) f (allM f hf)
          (Fin.castAdd_inj.mp (ve.symm.trans vf))
        simp [ue,wf,ef]
      · exact (sep _ _ (ve.symm.trans vf)).elim
      · exact (sep _ _ (vf.symm.trans ve)).elim
      · have eq := congrArg Fin.val (ve.symm.trans vf)
        have ef := right e (allM e he) f (allM f hf) (by simpa [Fin.ext_iff] using eq)
        simp [ue,wf,ef]
    obtain ⟨v,w,hw⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp cycle
    have h3 := hw.three_le_length
    have eq := unique (w.getVert 1) (w.getVert 0) (w.getVert 2)
      (w.adj_getVert_succ (i:=0) (by omega)).symm (w.adj_getVert_succ (i:=1) (by omega))
    have bad := hw.getVert_injOn' (x₁:=0) (x₂:=2) (by change 0 ≤ w.length-1; omega)
      (by change 2 ≤ w.length-1; omega) eq
    contradiction
  obtain ⟨e, he, heM⟩ := unmatched
  obtain ⟨T, cover, bound⟩ := charge n m E C square realizes.1 realizes.2
  have erase_nonempty : (E.erase e).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem he]
    omega
  have erase_cover : ∀ f ∈ E.erase e,
      Fin.castAdd m f.1 ∈ T ∨ Fin.natAdd n f.2 ∈ T := by
    intro f hf
    exact cover f (Finset.mem_of_mem_erase hf)
  obtain ⟨D, hDao, hDeval, hDsize⟩ := stars n m (E.erase e) T erase_nonempty erase_cover
  refine ⟨e, he, heM, D, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem he] at hDsize
    omega
  · exact ⟨hDao, hDeval⟩
