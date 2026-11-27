import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2872_3
    (graph : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)), M ⊆ E → (∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d) → (∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) →
      ∃ G : SimpleGraph (Fin (n+m)), (∀ u v, G.Adj u v ↔ ∃ e ∈ E, (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨ (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2)) ∧ G.edgeSet.ncard = E.card ∧
        ∀ S : Finset (Fin (n+m)), CoverPromise.IsVertexCover G S → M.card ≤ S.card)
    (forest : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit), G.IsAcyclic →
      (∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → k ≤ S.card) → Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      G.edgeSet.ncard + k ≤ C.size + 1)
    (peel : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit) (G : SimpleGraph (Fin (n+m))),
      (∀ u v, G.Adj u v ↔ ∃ e ∈ E, (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨ (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2)) → ¬ G.IsAcyclic → (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) → IsAO2 (n+m) C →
      (∀ x : Fin (n+m) → Bool, circuitFun (n+m) C x = decide (∃ p l, (p,l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) → M ⊆ E → (∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d) → (∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) →
      ∃ e ∈ E, e ∉ M ∧ ∃ D : Circuit, D.size < C.size ∧ IsAO2 (n+m) D ∧
        (∀ x : Fin (n+m) → Bool, circuitFun (n+m) D x = decide (∃ p l, (p,l) ∈ (E.erase e) ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true))) :
∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x4 ⊆ x3 → (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) → (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) → x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
  classical
  intro n m E
  induction E using Finset.strongInductionOn with
  | _ E ih =>
    intro M C square ao val sub rows cols
    obtain ⟨G,adj,card,cover⟩ := graph n m E M sub rows cols
    by_cases ac : G.IsAcyclic
    · have mono : Monotone2 C := fun g hg => ⟨ao.1 g hg, (ao.2.2 g hg).le⟩
      have evalG (x : Fin (n+m) → Bool) : C.eval (List.ofFn x) = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
        change circuitFun (n+m) C x = true ↔ _
        rw [val, decide_eq_true_eq]
        constructor
        · rintro ⟨p,l,he,hp,hl⟩
          exact ⟨_,_,(adj _ _).mpr ⟨(p,l),he,Or.inl ⟨rfl,rfl⟩⟩,hp,hl⟩
        · rintro ⟨u,v,h,hx,hy⟩
          obtain ⟨e,he,h | h⟩ := (adj _ _).mp h
          · obtain ⟨rfl,rfl⟩ := h
            exact ⟨e.1,e.2,he,hx,hy⟩
          · obtain ⟨rfl,rfl⟩ := h
            exact ⟨e.1,e.2,he,hy,hx⟩
      simpa only [card] using forest (n+m) M.card G C ac cover mono evalG
    · obtain ⟨e,he,nm,D,save,dAO,dEval⟩ := peel n m E M C G adj ac square ao val sub rows cols
      have into : E.erase e ⊆ E := Finset.erase_subset _ _
      have smaller := ih (E.erase e) (Finset.erase_ssubset he) M D (by
        intro p q l s hp hl h
        exact square p q l s hp hl ⟨into h.1, into h.2.1, into h.2.2.1, into h.2.2.2⟩)
        dAO dEval (fun d hd => Finset.mem_erase.mpr ⟨fun eq => nm (eq ▸ hd), sub hd⟩) rows cols
      have drop := Finset.card_erase_add_one he
      omega

