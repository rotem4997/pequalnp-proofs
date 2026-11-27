import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.GenericRejection

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2418_648
    (patch : ∀ (n : ℕ) (M : Finset ℕ) (V : Set (Fin n → Bool)) (C : Circuit), Monotone2 C →
      (∀ i a b, C.gates[i]? = some ⟨.and,[a,b]⟩ →
        let P : Circuit := ⟨C.gates.take i,0⟩
        0 < (P.lineDegrees n M).getD a 0 → 0 < (P.lineDegrees n M).getD b 0 →
        ∃ rs : List ℕ, rs.length ≤ 2 ∧ ∀ x ∈ V,
          let w := P.wires (List.ofFn x)
          (w.getD a false && w.getD b false) = rs.any (fun j => w.getD j false)) →
      ∃ D, Monotone2 D ∧ D.size ≤ C.size ∧ HasLineDegree n M D 1 ∧
        ∀ x ∈ V, circuitFun n D x = circuitFun n C x)
    (represent : let S := fun l : Fin 13 => ({l,l+1,l+3,l+9} : Finset (Fin 13))
      let thin := fun x : Fin 26 → Bool => ∃ l : Fin 13, ∀ k : Fin 13,
        x (Fin.natAdd 13 k) = true → k=l
      ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
      (∀ p l, p ∈ S l → C.eval (incidenceInput {p} {l}) = true) →
      (∀ P L, IsMaximalFalse S P L → ¬ IsGeneric S 0 P L →
        C.eval (incidenceInput P L) = false) →
      ∃ B : Circuit, Monotone2 B ∧ B.size ≤ C.size ∧
      (∀ x, thin x → circuitFun 26 B x = circuitFun 26 C x) ∧
      ∀ i a b, B.gates[i]? = some ⟨.and,[a,b]⟩ →
        let P : Circuit := ⟨B.gates.take i,0⟩
        let d := P.lineDegrees 26 (Finset.Ico 13 26)
        0 < min (d.getD a 0) (d.getD b 0) →
        ∃ r s : ℕ, ∀ x, thin x →
          let w := P.wires (List.ofFn x)
          (w.getD a false && w.getD b false) = (w.getD r false || w.getD s false)) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x3 x5 x8 → x2 x7 x8) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x5, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x3 x5 x9)) = Bool.false; have x5 : (Fin (26 : ℕ) → Bool) → Prop := fun (x5 : Fin (26 : ℕ) → Bool) => ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x7 = x6; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → x6.size ≤ (63 : ℕ) → x4 x6 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x6.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x10 (1 : ℕ) ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), x5 x11 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x10 x11 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 x11 := by
  dsimp only
  intro C mono size checks
  let S := fun l : Fin 13 => ({l,l+1,l+3,l+9} : Finset (Fin 13))
  let I := fun p l : Fin 13 => ∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p=l+d
  have sameInc : ∀ p l, p ∈ S l ↔ I p l := by
    dsimp [S,I]
    decide +kernel
  have apart (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
    intro e
    have h : p.val = 13+l.val := congrArg (fun i : Fin 26 => i.val) e
    have hp := p.isLt
    omega
  have row (P L : Finset (Fin 13)) :
      List.ofFn (fun k : Fin 26 => decide ((∃ p ∈ P, k=Fin.castAdd 13 p) ∨
        ∃ l ∈ L, k=Fin.natAdd 13 l)) = incidenceInput P L := by
    let f := fun k : Fin (13+13) => decide ((∃ p ∈ P, k=Fin.castAdd 13 p) ∨
      ∃ l ∈ L, k=Fin.natAdd 13 l)
    have left (p : Fin 13) : f (Fin.castAdd 13 p) = decide (p ∈ P) := by
      unfold f
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro (⟨a,ha,e⟩ | ⟨l,_,e⟩)
        · exact ((Fin.castAdd_injective 13 13) e).symm ▸ ha
        · exact (apart p l e).elim
      · exact fun h => Or.inl ⟨p,h,rfl⟩
    have right (l : Fin 13) : f (Fin.natAdd 13 l) = decide (l ∈ L) := by
      unfold f
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro (⟨p,_,e⟩ | ⟨b,hb,e⟩)
        · exact (apart p l e.symm).elim
        · exact ((Fin.natAdd_injective 13 13) e).symm ▸ hb
      · exact fun h => Or.inr ⟨l,h,rfl⟩
    change List.ofFn f = _
    rw [List.ofFn_add]
    exact congrArg₂ List.append (congrArg List.ofFn (funext left)) (congrArg List.ofFn (funext right))
  have yes (p l : Fin 13) (inc : p ∈ S l) : C.eval (incidenceInput {p} {l}) = true := by
    rw [← row {p} {l}]
    have test := checks.1 p l ((sameInc p l).mp inc)
    change C.eval (List.ofFn (fun k : Fin 26 => decide (k=Fin.castAdd 13 p ∨ k=Fin.natAdd 13 l))) = true at test
    simpa only [Finset.mem_singleton,exists_eq_left] using test
  have no (P L : Finset (Fin 13)) (largest : IsMaximalFalse S P L)
      (degenerate : (∃ l, P ⊆ S l) ∨ ∃ p, ∀ l ∈ L, p ∈ S l) : C.eval (incidenceInput P L) = false := by
    have disj (l : Fin 13) : l ∈ L ↔ ∀ p ∈ P, ¬I p l := by
      constructor
      · intro hl p hp inc
        exact Finset.disjoint_left.mp (largest.1 l hl) ((sameInc p l).mpr inc) hp
      · intro hl
        by_contra missing
        apply largest.2.2 l missing
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | old
        · exact Finset.disjoint_left.mpr fun p hs hp => hl p hp ((sameInc p k).mp hs)
        · exact largest.1 k old
    have maxPoints (p : Fin 13) (hp : p ∉ P) : ∃ l, (∀ r ∈ P, ¬I r l) ∧ I p l := by
      classical
      by_contra fail
      apply largest.2.1 p hp
      intro l hl
      apply Finset.disjoint_left.mpr
      intro r hr hIn
      rcases Finset.mem_insert.mp hIn with rfl | old
      · exact fail ⟨l,(disj l).mp hl,(sameInc r l).mp hr⟩
      · exact Finset.disjoint_left.mp (largest.1 l hl) hr old
    have kind : (∃ l, ∀ p ∈ P, I p l) ∨ ∃ p, ∀ l, (∀ r ∈ P, ¬I r l) → I p l := by
      rcases degenerate with ⟨l,h⟩ | ⟨p,h⟩
      · exact Or.inl ⟨l,fun p hp => (sameInc p l).mp (h hp)⟩
      · exact Or.inr ⟨p,fun l hl => (sameInc p l).mp (h l ((disj l).mpr hl))⟩
    rw [← row P L]
    have hh := checks.2 P maxPoints kind
    change C.eval (List.ofFn (fun k : Fin 26 => decide ((∃ p ∈ P, k=Fin.castAdd 13 p) ∨
      ∃ l, k=Fin.natAdd 13 l ∧ ∀ r ∈ P, ¬I r l))) = false at hh
    have agree : (fun k : Fin 26 => decide ((∃ p ∈ P, k=Fin.castAdd 13 p) ∨
        ∃ l ∈ L, k=Fin.natAdd 13 l)) =
        (fun k : Fin 26 => decide ((∃ p ∈ P, k=Fin.castAdd 13 p) ∨
          ∃ l, k=Fin.natAdd 13 l ∧ ∀ r ∈ P, ¬I r l)) := by
      funext k
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,← disj,and_comm]
    rwa [agree]
  let thin : Set (Fin 26 → Bool) := {x | ∃ l : Fin 13, ∀ k : Fin 13,
    x (Fin.natAdd 13 k) = true → k=l}
  have noGeneric (P L : Finset (Fin 13)) (largest : IsMaximalFalse S P L)
      (generic : ¬ IsGeneric S 0 P L) : C.eval (incidenceInput P L) = false := by
    classical
    apply no P L largest
    by_contra h
    apply generic
    refine ⟨Nat.zero_le _,Nat.zero_le _,?_,?_⟩
    · exact fun l hl => h (Or.inl ⟨l,hl⟩)
    · exact fun p hp => h (Or.inr ⟨p,hp⟩)
  obtain ⟨B,mb,sb,eqB,localPatch⟩ := represent C mono size yes noGeneric
  have listPatch (i a b : ℕ) (shape : B.gates[i]? = some ⟨.and,[a,b]⟩) :
      let P : Circuit := ⟨B.gates.take i,0⟩
      0 < (P.lineDegrees 26 (Finset.Ico 13 26)).getD a 0 →
      0 < (P.lineDegrees 26 (Finset.Ico 13 26)).getD b 0 →
      ∃ rs : List ℕ, rs.length ≤ 2 ∧ ∀ x ∈ thin,
        let w := P.wires (List.ofFn x)
        (w.getD a false && w.getD b false) = rs.any (fun j => w.getD j false) := by
    intro P ha hb
    obtain ⟨r,s,h⟩ := localPatch i a b shape (lt_min ha hb)
    refine ⟨[r,s],by exact le_rfl,fun x hx => ?_⟩
    simpa only [List.any_cons,List.any_nil,Bool.or_false] using h x hx
  obtain ⟨D,md,sd,deg,eqD⟩ := patch 26 (Finset.Ico 13 26) thin B mb listPatch
  exact ⟨D,md,sd.trans sb,deg,fun x hx => (eqD x hx).trans (eqB x hx)⟩
