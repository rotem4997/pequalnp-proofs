
import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.GenericRejection
open PEqualNP.MetaComplexity PEqualNP.HeptadCover

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_4604_677
    (transport : ∀ (p l k : ℕ) (S : Fin l → Finset (Fin p)) (C : Circuit)
      (hp : k ≤ p) (hl : k ≤ l),
      (∀ i : Fin k, Fin.castLE hp i ∈ S (Fin.castLE hl i)) →
      (∀ a b : Fin l, a ≠ b → (S a ∩ S b).card ≤ 1) →
      IsAO2 (p+l) C → C.output < p+l+C.size → ComputesIncidence S C →
      let N := p+(l-k)
      ∃ T : Fin N → Finset (Fin N), ∃ D : Circuit,
        (∀ i, i ∈ T i) ∧ (∀ a b, a ≠ b → (T a ∩ T b).card ≤ 1) ∧
        IsAO2 (N+N) D ∧ ComputesIncidence T D ∧
        (incidences T).card = (incidences S).card+(N-k) ∧ D.size = C.size+2*(N-k))
    (rectangle : ∃ (p l k : ℕ) (S : Fin l → Finset (Fin p)) (C : Circuit)
      (hp : k ≤ p) (hl : k ≤ l),
      (∀ i : Fin k, Fin.castLE hp i ∈ S (Fin.castLE hl i)) ∧
      (∀ a b : Fin l, a ≠ b → (S a ∩ S b).card ≤ 1) ∧
      IsAO2 (p+l) C ∧ C.output < p+l+C.size ∧
      ComputesIncidence S C ∧ C.size+1 < (incidences S).card+k) :
    ∃ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin x1), x4 ∈ x2 x4) ∧ (∀ (x4 x5 : Fin x1), x4 ≠ x5 → (x2 x4 ∩ x2 x5).card ≤ (1 : ℕ)) ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) x3 ∧ (∀ (x4 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x4 = Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x5 ∈ x2 x6 ∧ x4 (Fin.castAdd x1 x5) = Bool.true ∧ x4 (Fin.natAdd x1 x6) = Bool.true)) ∧ x3.size + (1 : ℕ) < (PEqualNP.HeptadCover.incidences x2).card + x1 := by
  obtain ⟨p,l,k,S,C,hp,hl,matched,linear,model,out,correct,small⟩ := rectangle
  obtain ⟨T,D,diag,free,ao,eval,edges,size⟩ := transport p l k S C hp hl matched linear model out correct
  let N := p+(l-k)
  refine ⟨N,T,D,diag,free,ao,?_,?_⟩
  · intro z
    let X : Finset (Fin N) := Finset.univ.filter fun p => z (Fin.castAdd N p) = true
    let Y : Finset (Fin N) := Finset.univ.filter fun l => z (Fin.natAdd N l) = true
    have split : Fin.append (fun p : Fin N => decide (p ∈ X))
        (fun l : Fin N => decide (l ∈ Y)) = z := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro p
        rw [Fin.append_left]
        cases h : z (Fin.castAdd N p) <;> simp [X,h]
      · intro l
        rw [Fin.append_right]
        cases h : z (Fin.natAdd N l) <;>
          simp only [Y,Finset.mem_filter,Finset.mem_univ,true_and,h] <;> rfl
    have row : incidenceInput X Y = List.ofFn z := by
      change List.ofFn (fun p : Fin N => decide (p ∈ X)) ++
        List.ofFn (fun l : Fin N => decide (l ∈ Y)) = _
      rw [← List.ofFn_fin_append,split]
    change D.eval (List.ofFn z) = _
    rw [← row, eval X Y]
    apply Bool.eq_iff_iff.mpr
    change decide (∃ p ∈ X, ∃ l ∈ Y, p ∈ T l) = true ↔ _
    simp only [decide_eq_true_eq, X, Y, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p,hp,l,hl,h⟩
      exact ⟨p,l,h,hp,hl⟩
    · rintro ⟨p,l,h,hp,hl⟩
      exact ⟨p,hp,l,hl,h⟩
  · dsimp only [N]
    rw [size,edges]
    omega
