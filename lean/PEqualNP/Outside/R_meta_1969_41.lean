import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Normalize the first raw pair using incident-flag stabilizers of the Fano plane.
theorem PEqualNP.Outside.R_meta_1969_41
    (normal : let F := fun (x : Fin 14 → Bool) => decide (∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l)=true)
      let W := fun (C : Circuit) (g : ℕ) (p : Fin 14) => let V := wireVal 14 C; let P := @pairInput 14; (gateAt C g).op = .and ∧ (14+g=C.output ∨ InCone 14 C g (C.output-14)) ∧ V (14+g) (P 0 7) = true ∧ ∀ b, V (opnd C g b) (P p p) = false
      let bad := fun (C : Circuit) => C.size≤27 ∧ IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧ circuitFun 14 C = F ∧ ∃ a b : ℕ, a≠b ∧ ¬ InCone 14 C a b ∧ ¬ InCone 14 C b a ∧ W C a 0 ∧ W C b 7
      let canonical := fun (C : Circuit) => let a := opnd C 0 0; let b := opnd C 0 1; (([2438,2956,11728,0,0,0,0,2304,6656,0,0,8192] : List ℕ).getD (min a b) 0).testBit (max a b)=true
      (∃ C, bad C) → ∃ C, bad C ∧ canonical C)
    (limited : let F := fun (x : Fin 14 → Bool) => decide (∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l)=true)
      let W := fun (C : Circuit) (g : ℕ) (p : Fin 14) => let V := wireVal 14 C; let P := @pairInput 14; (gateAt C g).op = .and ∧ (14+g=C.output ∨ InCone 14 C g (C.output-14)) ∧ V (14+g) (P 0 7) = true ∧ ∀ b, V (opnd C g b) (P p p) = false
      let bad := fun (C : Circuit) => C.size≤27 ∧ IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧ circuitFun 14 C = F ∧ ∃ a b : ℕ, a≠b ∧ ¬ InCone 14 C a b ∧ ¬ InCone 14 C b a ∧ W C a 0 ∧ W C b 7
      let canonical := fun (C : Circuit) => let a := opnd C 0 0; let b := opnd C 0 1; (([2438,2956,11728,0,0,0,0,2304,6656,0,0,8192] : List ℕ).getD (min a b) 0).testBit (max a b)=true
      ¬ ∃ C, bad C ∧ canonical C) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ) (x3 : ℕ), x2 ≠ x3 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 x2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ (∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x4) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x4) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  rintro ⟨C,sz,shape,ok,a,b,diff,nab,nba,wa,al,ap,ad,wb,bl,bp,bd⟩
  have data (g : Gate) (hg : g ∈ C.gates) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ i j : ℕ, g.inputs=[i,j] ∧ i≠j := by
    obtain ⟨k,hk⟩ := List.getElem?_of_mem hg
    obtain ⟨op,i,j,eq,ne,_,_⟩ := shape k g hk
    exact ⟨op,i,j,eq,ne⟩
  have ao : IsAO2 14 C := by
    refine ⟨fun g hg => (data g hg).1,?_,?_⟩
    · intro k hk i hi
      have get : C.gates[k]? = some (gateAt C k) := by
        change C.gates[k]? = some (C.gates.getD k ⟨.or,[]⟩)
        simp [List.getD_eq_getElem?_getD,hk]
      obtain ⟨_,u,v,e,_,hu,hv⟩ := shape k (gateAt C k) get
      rw [e] at hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl <;> assumption
    · intro g hg
      obtain ⟨_,i,j,eq,_⟩ := data g hg
      simp [eq]
  have nd : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨_,i,j,eq,ne⟩ := data g hg
    simp [eq,ne]
  apply limited
  apply normal
  refine ⟨C,sz,ao,nd,funext (fun x => ?_),a,b,diff,nab,nba,⟨wa,al,ap,ad⟩,wb,bl,bp,bd⟩
  apply Bool.eq_iff_iff.mpr
  have rows : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p=l ∨ p=l+1 ∨ p=l+3 := by decide +kernel
  change (C.eval (List.ofFn x) = true) ↔ decide (∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l)=true) = true
  simpa only [decide_eq_true_eq,rows] using ok x
