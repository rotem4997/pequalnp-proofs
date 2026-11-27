import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover
open PEqualNP.AndCount PEqualNP.GenericRejection

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_5075_418
    (compress : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      ∃ D : AndCountCircuit (n+1), D.WellFormed ∧
        D.size ≤ {i : Fin C.gates.length | (C.gates.get i).op = GateOp.and}.ncard ∧
        ∀ U : Finset (Fin n), D.eval (insert (Fin.last n) (U.map Fin.castSuccEmb)) =
          circuitFun n C (fun i => decide (i∈U)))
    (obstruction : ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)), x1.WellFormed → (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x1.eval (Insert.insert (Fin.last (26 : ℕ)) (Finset.map Fin.castSuccEmb {Fin.castAdd (13 : ℕ) x3, Fin.natAdd (13 : ℕ) x4})) = Bool.true) → (∀ (x4 x5 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse PEqualNP.HeptadCover.singerLines3 x4 x5 → PEqualNP.GenericRejection.IsGeneric PEqualNP.HeptadCover.singerLines3 (3 : ℕ) x4 x5 → x1.eval (Insert.insert (Fin.last (26 : ℕ)) (Finset.map Fin.castSuccEmb (Finset.map (Fin.castAddEmb (13 : ℕ)) x4 ∪ Finset.map (Fin.natAddEmb (13 : ℕ)) x5))) = Bool.false) → (13 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → ∃ (x5 : Finset (Fin ((13 : ℕ) + (13 : ℕ)))), (∀ (x6 x7 : Fin (13 : ℕ)), x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ)) → Fin.castAdd (13 : ℕ) x6 ∈ x5 ∨ Fin.natAdd (13 : ℕ) x7 ∈ x5) ∧ x5.card ≤ {x6 : Fin x1.gates.length | (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro C mono yes no
  obtain ⟨D,wf,budget,evals⟩ := compress 26 C mono
  have inc : ∀ p l : Fin 13, p∈singerLines3 l ↔ p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9 := by decide
  have lower : 13 ≤ D.size := by
    apply obstruction D wf
    · intro p l h
      rw [evals]
      simpa only [Finset.mem_insert,Finset.mem_singleton] using yes p l ((inc p l).mp h)
    · intro X Y maximal generic
      have disj : ∀ l∈Y, ∀ p∈X, p ∉ singerLines3 l :=
        fun l hl p hp hin => Finset.disjoint_left.mp (maximal.1 l hl) hin hp
      have missing (l : Fin 13) : l∈Y ↔ ∀ p∈X, ¬(p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) := by
        constructor
        · intro hl p hp h
          exact disj l hl p hp ((inc p l).mpr h)
        · intro h
          by_contra hn
          apply maximal.2.2 l hn
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl|hj
          · exact Finset.disjoint_left.mpr fun p hp hx => h p hx ((inc p _).mp hp)
          · exact maximal.1 j hj
      have closed (p : Fin 13) (hp : p∉X) : ∃ l ∈ Y, p∈singerLines3 l := by
        by_contra! none
        apply maximal.2.1 p hp
        intro l hl
        apply Finset.disjoint_left.mpr
        intro a ha hm
        rcases Finset.mem_insert.mp hm with rfl|hm
        · exact none l hl ha
        · exact disj l hl a hm ha
      have hneg := no X (fun p hp => by
        obtain ⟨l,hl,on⟩ := closed p hp
        exact ⟨l,(missing l).mp hl,(inc p l).mp on⟩) ⟨by
          rintro ⟨l,h⟩
          exact generic.2.2.1 l (fun p hp => (inc p l).mpr (h p hp)),by
          rintro ⟨p,h⟩
          exact generic.2.2.2 p (fun l hl => (inc p l).mpr (h l ((missing l).mp hl)))⟩
      rw [evals]
      convert hneg using 2
      funext i
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      simp only [Finset.mem_union,Finset.mem_map]
      constructor
      · rintro (⟨p,hp,h⟩|⟨l,hl,h⟩)
        · exact Or.inl ⟨p,hp,h.symm⟩
        · exact Or.inr ⟨l,h.symm,(missing l).mp hl⟩
      · rintro (⟨p,hp,h⟩|⟨l,h,hl⟩)
        · exact Or.inl ⟨p,hp,h.symm⟩
        · exact Or.inr ⟨l,(missing l).mpr hl,h.symm⟩
  refine ⟨Finset.univ.map (Fin.castAddEmb 13),?_,?_⟩
  · intro p l _
    exact Or.inl (Finset.mem_map.mpr ⟨p,Finset.mem_univ _,rfl⟩)
  · simpa using lower.trans budget
