import PEqualNP.Defs

set_option maxRecDepth 22000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_17924_733 :
(∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
 PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.range 13) C 1 →
 ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size = C.size ∧
 PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) D 1 ∧
 ∀ P L : Finset (Fin 13), D.eval (PEqualNP.GenericRejection.incidenceInput P L) =
 C.eval (PEqualNP.GenericRejection.incidenceInput (L.image (fun z : Fin 13 => -z)) (P.image (fun z : Fin 13 => -z)))) →
(let S := fun l : Fin 13 => ({l,l+1,l+3,l+9} : Finset (Fin 13))
 let masks : List ℕ := [8191,15860,31200,46544,77220,107904,146756,277652,292992,539952,1093712,1124388,1996800,3060736,3338304,4942080,5711876,10268688,12513280,67100672]
 let select := fun (m : ℕ) (t : Fin 13) (o : ℕ) =>
   Finset.univ.filter (fun i : Fin 13 => m.testBit (o + (i - t).val))
 ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 63 →
 ¬ PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.range 13) C 1 →
 ¬ PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 →
 (∀ p l, p ∈ S l → C.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true) →
 ∃ m ∈ masks, ∃ t : Fin 13, C.eval (PEqualNP.GenericRejection.incidenceInput (select m t 0) (select m t 13)) = true) →
(have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := fun (x1 : Fin (13 : ℕ)) => {x1, x1 + (1 : Fin (13 : ℕ)), x1 + (3 : Fin (13 : ℕ)), x1 + (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ x1 x4 → x2.eval (PEqualNP.GenericRejection.incidenceInput {x3} {x4}) = Bool.true) ∧ x2.eval (PEqualNP.GenericRejection.incidenceInput (x1 (0 : Fin (13 : ℕ)) ∪ (x1 (0 : Fin (13 : ℕ)))ᶜ) (x1 (0 : Fin (13 : ℕ)) \ x1 (0 : Fin (13 : ℕ)))) = Bool.false ∧ ∀ (x3 : Fin (13 : ℕ)), x2.eval (PEqualNP.GenericRejection.incidenceInput (x1 x3)ᶜ {x3}) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ (63 : ℕ) → (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∈ x1 x7 → x3.eval (PEqualNP.GenericRejection.incidenceInput {x6} {x7}) = Bool.true) → (∀ (x7 x8 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse x1 x7 x8 → ¬PEqualNP.GenericRejection.IsGeneric x1 (0 : ℕ) x7 x8 → x3.eval (PEqualNP.GenericRejection.incidenceInput x7 x8) = Bool.false) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x3.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x8 (1 : ℕ) ∧ x2 x8) := by
  intro dual obstruct
  dsimp only
  let S := fun l : Fin 13 => ({l,l+1,l+3,l+9} : Finset (Fin 13))
  let mirror := fun (U : Finset (Fin 13)) => U.image (fun z : Fin 13 => -z)
  let A := fun P L : Finset (Fin 13) =>
    PEqualNP.GenericRejection.IsMaximalFalse S P L ∧ ¬ PEqualNP.GenericRejection.IsGeneric S 0 P L
  intro C hm hs hp hn
  change (∀ p l, p ∈ S l → C.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true) at hp
  have reject (P L : Finset (Fin 13)) (h : A P L) : C.eval (PEqualNP.GenericRejection.incidenceInput P L) = false := hn P L h.1 h.2
  have boundary : A ((S 0) ∪ (S 0)ᶜ) ((S 0) \ (S 0)) ∧
      (∀ l, A (S l)ᶜ {l}) := by decide +kernel
  by_cases hline : PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1
  · exact ⟨C,hm,le_rfl,hline,hp,reject _ _ boundary.1,fun l => reject _ _ (boundary.2 l)⟩
  by_cases hpoint : PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.range 13) C 1
  · obtain ⟨D,hd,sz,lin,transfer⟩ := dual C hm hpoint
    have mirrored : A (mirror ((S 0) \ (S 0))) (mirror ((S 0) ∪ (S 0)ᶜ)) ∧
        (∀ l, A (mirror {l}) (mirror (S l)ᶜ)) := by decide +kernel
    have flipFlag : ∀ p l : Fin 13, p ∈ S l → -l ∈ S (-p) := by decide +kernel
    refine ⟨D,hd,sz.le,lin,?_,?_,?_⟩
    · intro p l h
      rw [transfer]
      simpa using hp (-l) (-p) (flipFlag p l h)
    · rw [transfer]
      exact reject _ _ mirrored.1
    · intro l
      rw [transfer]
      exact reject _ _ (mirrored.2 l)
  · let masks : List ℕ := [8191,15860,31200,46544,77220,107904,146756,277652,292992,539952,1093712,1124388,1996800,3060736,3338304,4942080,5711876,10268688,12513280,67100672]
    let select := fun (m : ℕ) (t : Fin 13) (o : ℕ) =>
      Finset.univ.filter (fun i : Fin 13 => m.testBit (o + (i-t).val))
    have legal : ∀ m ∈ masks, ∀ t : Fin 13, A (select m t 0) (select m t 13) := by decide +kernel
    obtain ⟨m,mem,t,bad⟩ := obstruct C hm hs hpoint hline hp
    have no := reject _ _ (legal m mem t)
    change C.eval (PEqualNP.GenericRejection.incidenceInput (select m t 0) (select m t 13)) = true at bad
    rw [no] at bad
    contradiction
