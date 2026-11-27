import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5759_617
    (trace : ∃ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
    let F := fun p l : Fin n => PEqualNP.MetaComplexity.circuitFun (n+n) C
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n p) (Fin.natAdd n l))
    PEqualNP.TopForm.IsAO2 (n+n) C ∧ (∀ p, F p p = true) ∧
    (∀ p q j k, p ≠ q → j ≠ k → ¬ (F p j = true ∧ F p k = true ∧ F q j = true ∧ F q k = true)) ∧
    (∀ X : Finset (Fin n), PEqualNP.MetaComplexity.circuitFun (n+n) C
      (Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (∀ p ∈ X, F p l = false))) = false) ∧
    C.size + 1 < ({e : Fin n × Fin n | F e.1 e.2 = true} : Set _).ncard + n)
    (boundary : ∀ (n : ℕ) (F : Fin n → Fin n → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.TopForm.IsAO2 (n+n) C →
    (∀ p l, F p l = true → PEqualNP.MetaComplexity.circuitFun (n+n) C
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n p) (Fin.natAdd n l)) = true) →
    (∀ X : Finset (Fin n), PEqualNP.MetaComplexity.circuitFun (n+n) C
      (Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (∀ p ∈ X, F p l = false))) = false) →
    ∀ z, PEqualNP.MetaComplexity.circuitFun (n+n) C z =
      decide (∃ p l, F p l = true ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true)) :
    ∃ (x1 : ℕ) (x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x4 ⊆ x3 ∧ (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6.1 = x8.1 → x6 = x8) ∧ (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6.2 = x8.2 → x6 = x8) ∧ (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x5 ∧ (∀ (x6 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x6 = Decidable.decide (∃ (x7 : Fin x1) (x8 : Fin x2), (x7, x8) ∈ x3 ∧ x6 (Fin.castAdd x2 x7) = Bool.true ∧ x6 (Fin.natAdd x1 x8) = Bool.true)) ∧ x5.size + (1 : ℕ) < x3.card + x4.card := by
  obtain ⟨n,C,h⟩ := trace
  let F := fun p l : Fin n => PEqualNP.MetaComplexity.circuitFun (n+n) C
    (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n p) (Fin.natAdd n l))
  let E := Finset.univ.filter (fun e : Fin n × Fin n => F e.1 e.2 = true)
  let M := Finset.univ.image (fun p : Fin n => (p,p))
  obtain ⟨ao,diag,sq,neg,cost⟩ := h
  have memE (p l) : (p,l) ∈ E ↔ F p l = true := by simp [E]
  have cardM : M.card=n := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
    simp
  refine ⟨n,n,E,M,C,?_,?_,?_,?_,ao,?_,?_⟩
  · intro e he
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp he
    exact (memE p p).mpr (diag p)
  · intro e he f hf eq
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hf
    exact congrArg (fun i => (i,i)) eq
  · intro e he f hf eq
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hf
    exact congrArg (fun i => (i,i)) eq
  · intro p q j k hp hl h
    exact sq p q j k hp hl ⟨(memE _ _).mp h.1,(memE _ _).mp h.2.1,
      (memE _ _).mp h.2.2.1,(memE _ _).mp h.2.2.2⟩
  · intro z
    simpa only [memE] using boundary n F C ao (fun _ _ ok => ok) neg z
  · have eq : (E : Set (Fin n × Fin n)) = {e | F e.1 e.2 = true} := by
      ext e
      exact memE e.1 e.2
    have cardE : E.card = ({e | F e.1 e.2 = true} : Set (Fin n × Fin n)).ncard := by
      rw [← eq, Set.ncard_coe_finset]
    simpa only [cardM,cardE] using cost
