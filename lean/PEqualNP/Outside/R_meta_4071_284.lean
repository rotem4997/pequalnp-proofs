import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.HeptadCover PEqualNP.NotPremium

-- The score counts two units per accepted flag and subtracts one per gate.
-- Pinning a gate to false preserves rejection on every negative input.
-- If it loses exactly one flag and other flags survive, both the pinned gate
-- and a reader can be removed. Iteration leaves a circuit where every gate is
-- needed for at least two flags, unless at most one flag survives.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_4071_284
    (peel : ∀ (n m : ℕ) (E : Finset (Fin m × Fin m)) (row : Fin m × Fin m → Fin n → Bool),
      let hits := fun B : Circuit => E.filter fun e => circuitFun n B (row e) = true
      ∀ C : Circuit, Monotone2 C → ∃ D : Circuit, Monotone2 D ∧
        circuitFun n D ≤ circuitFun n C ∧ D.size ≤ C.size ∧
        2*(hits C).card + D.size ≤ 2*(hits D).card + C.size ∧
        ((hits D).card ≤ 1 ∨ ∀ j < D.size, 2 ≤ (hits D \ hits ⟨replaceByConst D.gates j false,D.output⟩).card))
    (core : let I := fun p l : Fin 13 => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
      let S := fun (d : Bool) (l : Fin 13) => Finset.univ.filter (fun p => if d then I l p else I p l)
      let hits := fun B : Circuit => (incidences (S false)).filter (fun e =>
        circuitFun 26 B (pairInput (Fin.castAdd 13 e.1) (Fin.natAdd 13 e.2)) = true)
      ∀ C : Circuit, Monotone2 C → 40+C.size < 2*(hits C).card →
        (∀ j < C.size, 2 ≤ (hits C \ hits ⟨replaceByConst C.gates j false,C.output⟩).card) →
        ∃ (d : Bool) (Q : Finset (Fin 13)), IsQuadrangle (S d) Q ∧
          circuitFun 26 C (fun i => let v := finSumFinEquiv.symm i
            decide ((if d then v.swap else v) ∈ supp (S d) Q)) = true) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5}; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ); have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ); have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x7)) x8; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (63 : ℕ) → (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) → (∃ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) ∧ x4 x11 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 x11 (x2 x11)) = Bool.true) ∨ ∃ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) ∧ x5 x11 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 (x3 x11) x11) = Bool.true := by
  classical
  dsimp only
  intro C mono size flags
  let I := fun p l : Fin 13 => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
  let S := fun (d : Bool) (l : Fin 13) => Finset.univ.filter (fun p => if d then I l p else I p l)
  let E := incidences (S false)
  let row := fun e : Fin 13 × Fin 13 => pairInput (Fin.castAdd 13 e.1) (Fin.natAdd 13 e.2)
  let hits := fun B : Circuit => E.filter fun e => circuitFun 26 B (row e) = true
  have full : hits C = E := by
    apply Finset.filter_eq_self.mpr
    intro e he
    have inc : I e.1 e.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp he).2).2
    exact flags e.1 e.2 inc
  have count : E.card = 52 := by decide +kernel
  obtain ⟨D,dm,below,_,save,branch⟩ := peel 26 13 E row C mono
  change 2*(hits C).card + D.size ≤ 2*(hits D).card + C.size at save
  rw [full,count] at save
  have high : 40+D.size < 2*(hits D).card := by omega
  rcases branch with low | critical
  · change (hits D).card ≤ 1 at low
    omega
  obtain ⟨d,Q,quad,yes⟩ := core D dm high critical
  have memS (d : Bool) (p l : Fin 13) : p ∈ S d l ↔ (if d then I l p else I p l) := by
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
  have miss (b : Bool) (Q : Finset (Fin 13)) (v : Fin 13) :
      v ∈ missLines (S b) Q ↔ ∀ q ∈ Q, ¬(if b then I v q else I q v) := by
    change v ∈ Finset.univ.filter (fun l => Disjoint (S b l) Q) ↔ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [disjoint_comm,Finset.disjoint_left]
    simp only [memS]
  have cap (t : Fin 13) : (Q ∩ S d t).card ≤ 2 := quad.2 t
  have hit := Bool.le_iff_imp.mp (below _) yes
  cases d with
  | false =>
    left
    refine ⟨Q,quad.1,fun t => ?_,?_⟩
    · have eq : Q.filter (fun p => I p t) = Q ∩ S false t := by
        ext z
        simp only [Finset.mem_filter,Finset.mem_inter,memS,Bool.false_eq_true,if_false]
      change (Q.filter (fun p => I p t)).card ≤ 2
      rw [eq]
      exact cap t
    · convert hit using 2
      funext i
      refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
      · simp only [Fin.addCases_left,Fin.addCases_right,finSumFinEquiv_symm_apply_castAdd,
          finSumFinEquiv_symm_apply_natAdd,Bool.false_eq_true,ite_false,ite_true,Sum.swap_inl,Sum.swap_inr]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        change (p ∈ Q) ↔ Sum.inl p ∈ Q.disjSum (missLines (S false) Q)
        simp only [Finset.inl_mem_disjSum,Finset.mem_filter,Finset.mem_univ,true_and,miss,
          Bool.false_eq_true,ite_false,ite_true]
      · simp only [Fin.addCases_left,Fin.addCases_right,finSumFinEquiv_symm_apply_castAdd,
          finSumFinEquiv_symm_apply_natAdd,Bool.false_eq_true,ite_false,ite_true,Sum.swap_inl,Sum.swap_inr]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        change (l ∈ Finset.univ.filter (fun t => ∀ q ∈ Q, ¬ I q t)) ↔ Sum.inr l ∈ Q.disjSum (missLines (S false) Q)
        simp only [Finset.inr_mem_disjSum,Finset.mem_filter,Finset.mem_univ,true_and,miss,
          Bool.false_eq_true,ite_false,ite_true]
  | true =>
    right
    refine ⟨Q,quad.1,fun t => ?_,?_⟩
    · have eq : Q.filter (I t) = Q ∩ S true t := by
        ext z
        simp only [Finset.mem_filter,Finset.mem_inter,memS,if_true]
      change (Q.filter (I t)).card ≤ 2
      rw [eq]
      exact cap t
    · convert hit using 2
      funext i
      refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
      · simp only [Fin.addCases_left,Fin.addCases_right,finSumFinEquiv_symm_apply_castAdd,
          finSumFinEquiv_symm_apply_natAdd,Bool.false_eq_true,ite_false,ite_true,Sum.swap_inl,Sum.swap_inr]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        change (p ∈ Finset.univ.filter (fun t => ∀ q ∈ Q, ¬ I t q)) ↔ Sum.inr p ∈ Q.disjSum (missLines (S true) Q)
        simp only [Finset.inr_mem_disjSum,Finset.mem_filter,Finset.mem_univ,true_and,miss,
          Bool.false_eq_true,ite_false,ite_true]
      · simp only [Fin.addCases_left,Fin.addCases_right,finSumFinEquiv_symm_apply_castAdd,
          finSumFinEquiv_symm_apply_natAdd,Bool.false_eq_true,ite_false,ite_true,Sum.swap_inl,Sum.swap_inr]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        change (l ∈ Q) ↔ Sum.inl l ∈ Q.disjSum (missLines (S true) Q)
        simp only [Finset.inl_mem_disjSum,Finset.mem_filter,Finset.mem_univ,true_and,miss,
          Bool.false_eq_true,ite_false,ite_true]
