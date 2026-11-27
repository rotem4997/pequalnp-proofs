import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3527_642
    (pinZero : ∀ (n : ℕ) (p : Fin n), ∀ k (C : Circuit), C.size = k → IsAO2 n C →
      (∃ x y : Fin n → Bool, C.eval (List.ofFn (Function.update x p false)) ≠
        C.eval (List.ofFn (Function.update y p false))) →
      ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
        ((∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠
          C.eval (List.ofFn (Function.update x p false))) → D.size < C.size) ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x p false)))
    (core : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) → ¬x6.IsAcyclic → (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) → x4 ⊆ x3 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) → (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) → (∀ e ∈ x3, ((∀ d ∈ x3, d.1 = e.1 → d = e) ∨ (∀ d ∈ x3, d.2 = e.2 → d = e)) → (x3.erase e).Nonempty → e ∈ x4) → ∃ x15 ∈ x3, x15 ∉ x4 ∧ ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit), x16.size < x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x16 ∧ ∀ (x17 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x16 x17 = Decidable.decide (∃ (x18 : Fin x1) (x19 : Fin x2), (x18, x19) ∈ x3.erase x15 ∧ x17 (Fin.castAdd x2 x18) = Bool.true ∧ x17 (Fin.natAdd x1 x19) = Bool.true)) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) → ¬x6.IsAcyclic → (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) → x4 ⊆ x3 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) → (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) → ∃ x15 ∈ x3, x15 ∉ x4 ∧ ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit), x16.size < x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x16 ∧ ∀ (x17 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x16 x17 = Decidable.decide (∃ (x18 : Fin x1) (x19 : Fin x2), (x18, x19) ∈ x3.erase x15 ∧ x17 (Fin.castAdd x2 x18) = Bool.true ∧ x17 (Fin.natAdd x1 x19) = Bool.true) := by
  classical
  intro n m E M C G adj cyc hSquare hAO hEval hSub hMatchP hMatchL
  let left : Fin n → Fin (n+m) := Fin.castAdd m
  let right : Fin m → Fin (n+m) := Fin.natAdd n
  let target (A : Finset (Fin n × Fin m)) (z : Fin (n+m) → Bool) : Bool :=
    decide (∃ p l, (p,l) ∈ A ∧ z (left p) = true ∧ z (right l) = true)
  let leaf (A : Finset (Fin n × Fin m)) (e : Fin n × Fin m) : Prop :=
    (∀ d ∈ A, d.1 = e.1 → d = e) ∨ (∀ d ∈ A, d.2 = e.2 → d = e)
  let squareFree (A : Finset (Fin n × Fin m)) : Prop :=
    ∀ (p q : Fin n) (l s : Fin m), p ≠ q → l ≠ s →
      ¬ ((p,l) ∈ A ∧ (p,s) ∈ A ∧ (q,l) ∈ A ∧ (q,s) ∈ A)
  have leftInj : Function.Injective left := by
    intro p q eq
    have h := congrArg (fun i : Fin (n+m) => i.val) eq
    exact Fin.ext h
  have rightInj : Function.Injective right := by
    intro p q eq
    apply Fin.ext
    have k := congrArg Fin.val eq
    change n+p.val = n+q.val at k
    omega
  have sides (p : Fin n) (l : Fin m) : left p ≠ right l := by
    intro e
    have h := congrArg Fin.val e
    change p.val = n+l.val at h
    omega
  have pinPoint (A : Finset (Fin n × Fin m)) (e : Fin n × Fin m) (h : leaf A e) :
      ∃ a : Fin (n+m), (a = left e.1 ∨ a = right e.2) ∧
        ∀ d ∈ A, (a = left d.1 ∨ a = right d.2) → d = e := by
    rcases h with h | h
    · refine ⟨left e.1,Or.inl rfl,?_⟩
      intro d hd hh
      rcases hh with hh | hh
      · exact h d hd (leftInj hh).symm
      · exact (sides _ _ hh).elim
    · refine ⟨right e.2,Or.inr rfl,?_⟩
      intro d hd hh
      rcases hh with hh | hh
      · exact (sides _ _ hh.symm).elim
      · exact h d hd (rightInj hh).symm
  have project (A : Finset (Fin n × Fin m)) (e : Fin n × Fin m) (a : Fin (n+m))
      (ha : a = left e.1 ∨ a = right e.2)
      (unique : ∀ d ∈ A, (a = left d.1 ∨ a = right d.2) → d = e)
      (z : Fin (n+m) → Bool) : target A (Function.update z a false) = target (A.erase e) z := by
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨p,l,he,hp,hl⟩
      have dp : left p ≠ a := by
        intro eq
        rw [eq,Function.update_self] at hp
        cases hp
      have dl : right l ≠ a := by
        intro eq
        rw [eq,Function.update_self] at hl
        cases hl
      have neq : (p,l) ≠ e := by
        intro ee
        rw [← ee] at ha
        exact ha.elim (fun h => dp h.symm) (fun h => dl h.symm)
      rw [Function.update_of_ne dp] at hp
      rw [Function.update_of_ne dl] at hl
      exact ⟨p,l,Finset.mem_erase.mpr ⟨neq,he⟩,hp,hl⟩
    · rintro ⟨p,l,he,hp,hl⟩
      obtain ⟨neq,he⟩ := Finset.mem_erase.mp he
      have dp : left p ≠ a := fun eq => neq (unique (p,l) he (Or.inl eq.symm))
      have dl : right l ≠ a := fun eq => neq (unique (p,l) he (Or.inr eq.symm))
      exact ⟨p,l,he,by rwa [Function.update_of_ne dp],by rwa [Function.update_of_ne dl]⟩
  have sensitive (A : Finset (Fin n × Fin m)) (e : Fin n × Fin m) (he : e ∈ A) :
      ∃ z : Fin (n+m) → Bool, target A z ≠ target (A.erase e) z := by
    let z := fun i : Fin (n+m) => decide (i = left e.1 ∨ i = right e.2)
    have yes : target A z = true := by
      apply decide_eq_true_eq.mpr
      exact ⟨e.1,e.2,he,by simp (config := {congrConsts := false}) [z],by simp (config := {congrConsts := false}) [z]⟩
    have no : target (A.erase e) z = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p,l,he',hp,hl⟩ := decide_eq_true_eq.mp h
      have pe : p = e.1 := by
        simp (config := {congrConsts := false}) only [z,decide_eq_true_eq] at hp
        exact hp.elim (fun v => leftInj v) (fun v => (sides _ _ v).elim)
      have le : l = e.2 := by
        simp (config := {congrConsts := false}) only [z,decide_eq_true_eq] at hl
        exact hl.elim (fun v => (sides _ _ v.symm).elim) (fun v => rightInj v)
      exact (Finset.mem_erase.mp he').1 (Prod.ext pe le)
    exact ⟨z,by rw [yes,no]; decide⟩
  by_cases removable : ∃ e ∈ E, e ∉ M ∧ leaf E e ∧ (E.erase e).Nonempty
  · obtain ⟨e,he,heM,hLeaf,hasEdge⟩ := removable
    obtain ⟨a,ha,alone⟩ := pinPoint E e hLeaf
    have cofactor (z : Fin (n+m) → Bool) :
        C.eval (List.ofFn (Function.update z a false)) = target (E.erase e) z :=
      (hEval (Function.update z a false)).trans (project E e a ha alone z)
    have hn : ∃ x y : Fin (n+m) → Bool, C.eval (List.ofFn (Function.update x a false)) ≠
        C.eval (List.ofFn (Function.update y a false)) := by
      have no : target (E.erase e) (fun _ => false) = false := by simp (config := {congrConsts := false}) [target]
      obtain ⟨d,hd⟩ := hasEdge
      have yes : target (E.erase e) (fun _ => true) = true :=
        decide_eq_true_eq.mpr ⟨d.1,d.2,hd,rfl,rfl⟩
      exact ⟨fun _ => false,fun _ => true,by rw [cofactor,cofactor,no,yes]; decide⟩
    have needsPin : ∃ z : Fin (n+m) → Bool, C.eval (List.ofFn z) ≠
        C.eval (List.ofFn (Function.update z a false)) := by
      obtain ⟨z,hz⟩ := sensitive E e he
      refine ⟨z,?_⟩
      rw [cofactor]
      change circuitFun (n+m) C z ≠ target (E.erase e) z
      rw [hEval z]
      exact hz
    obtain ⟨D,hD,_,saved,models⟩ := pinZero (n+m) a C.size C rfl hAO hn
    have small := saved needsPin
    have hDModel (z : Fin (n+m) → Bool) : circuitFun (n+m) D z = target (E.erase e) z :=
      (models z).trans (cofactor z)
    exact ⟨e,he,heM,D,small,hD,hDModel⟩
  · apply core n m E M C G adj cyc hSquare hAO hEval hSub hMatchP hMatchL
    intro e he hl hr
    by_contra hm
    exact removable ⟨e,he,hm,hl,hr⟩
