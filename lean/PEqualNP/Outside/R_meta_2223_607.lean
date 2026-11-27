import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_2223_607
    (compile :
      let branch := fun (a b : DMFormula 14) (ha hb : Prop) =>
        ha ∧ hb ∧ ¬ ∃ i, a = DMFormula.lit i true ∧ b = DMFormula.lit i true
      let good := fun (t : DMFormula 14) => DMFormula.rec (motive := fun _ : DMFormula 14 => Prop)
        (fun _ sign => sign = true) branch branch t
      let deg := fun (k : ℕ) (t : DMFormula 14) =>
        DMFormula.rec (motive := fun _ : DMFormula 14 => ℕ)
          (fun i _ => if i.val = k then 1 else 0)
          (fun _ _ a b => a+b) (fun _ _ a b => max a b) t
      ∀ t : DMFormula 14, good t → ∃ D : Circuit,
        IsAO2 14 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧ D.size+1 = t.leaves ∧
        ((D.output :: D.gates.flatMap Gate.inputs).filter (fun w => decide (14≤w))).Nodup ∧
        (∀ x, D.eval (List.ofFn x) = t.eval x) ∧
        ∀ k, D.lineDeg 14 {k} = deg k t)
    (unfoldFit :
      let branch := fun (a b : DMFormula 14) (ha hb : Prop) =>
        ha ∧ hb ∧ ¬ ∃ i, a = DMFormula.lit i true ∧ b = DMFormula.lit i true
      let good := fun (t : DMFormula 14) => DMFormula.rec (motive := fun _ : DMFormula 14 => Prop)
        (fun _ sign => sign = true) branch branch t
      let deg := fun (k : ℕ) (t : DMFormula 14) =>
        DMFormula.rec (motive := fun _ : DMFormula 14 => ℕ)
          (fun i _ => if i.val = k then 1 else 0)
          (fun _ _ a b => a+b) (fun _ _ a b => max a b) t
      ∀ (C : Circuit) (p l : Fin 7), C.size ≤ 27 → IsAO2 14 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) → ComputesIncidence fanoLines C →
        p ∈ fanoLines l → 2 ≤ C.lineDeg 14 {p.val} → 2 ≤ C.lineDeg 14 {7+l.val} →
        ∃ t : DMFormula 14, good t ∧ t.leaves ≤ 28 ∧
          (∀ x, t.eval x = C.eval (List.ofFn x)) ∧ 2 ≤ deg p.val t ∧ 2 ≤ deg (7+l.val) t) :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x2 x4 → x1 x5 x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x2 x11 ∧ x3 x11 ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {↑x5} ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} := by
  dsimp only
  intro C p l eligible flag dp dl
  have fanoPoint (p l : Fin 7) : p ∈ fanoLines l ↔
      p = l ∨ p = l + 1 ∨ p = l + 3 := by
    revert p l
    decide +kernel
  have cb : IsAO2 14 C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.1 hg
      exact (eligible.2.1 j g hj).1
    · intro j hj i hi
      have lookup : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
      rw [lookup] at hi
      obtain ⟨_,a,b,eq,_,ha,hb⟩ := eligible.2.1 j C.gates[j] (List.getElem?_eq_getElem hj)
      simp only [eq,List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.1 hg
      obtain ⟨_,a,b,eq,_,_,_⟩ := eligible.2.1 j g hj
      simp [eq]
  have nd : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.1 hg
    obtain ⟨_,a,b,eq,ne,_,_⟩ := eligible.2.1 j g hj
    simp [eq,ne]
  have incidence : ComputesIncidence fanoLines C := by
    intro X Y
    let x : Fin 14 → Bool := Fin.append (fun u => decide (u ∈ X)) (fun v => decide (v ∈ Y))
    have eq : List.ofFn x = incidenceInput X Y := List.ofFn_fin_append _ _
    rw [← eq]
    apply Bool.eq_iff_iff.mpr
    rw [eligible.2.2 x]
    have result : incidenceFun fanoLines X Y = true ↔
        ∃ p ∈ X, ∃ l ∈ Y, p ∈ fanoLines l := by
      change decide (∃ p ∈ X, ∃ l ∈ Y, p ∈ fanoLines l) = true ↔ _
      constructor
      · intro h; exact of_decide_eq_true h
      · intro h; exact decide_eq_true h
    rw [result]
    simp only [x, Fin.append_left, Fin.append_right, decide_eq_true_eq, fanoPoint]
    constructor
    · rintro ⟨u,v,hit,hu,hv⟩
      exact ⟨u,hu,v,hv,hit⟩
    · rintro ⟨u,hu,v,hv,hit⟩
      exact ⟨u,v,hit,hu,hv⟩
  obtain ⟨t,good,leaf,agree,pDegree,lDegree⟩ := unfoldFit C p l eligible.1 cb nd incidence
    ((fanoPoint p l).mpr flag) dp dl
  obtain ⟨D,interpreted,distinct,size,tree,eval,degree⟩ := compile t good
  refine ⟨D,⟨by omega,?_,?_⟩,tree,?_,?_⟩
  · intro j g hit
    have mem := List.mem_of_getElem? hit
    have earlier (i : ℕ) (hi : i ∈ g.inputs) : i < 14+j := by
      have valid : j < D.gates.length := (List.getElem?_eq_some_iff.mp hit).1
      have eq : gateAt D j = g := by
        unfold gateAt
        rw [List.getD_eq_getElem?_getD,hit]
        rfl
      exact interpreted.2.1 j valid i (eq.symm ▸ hi)
    have hlen := interpreted.2.2 g mem
    obtain ⟨a,b,slots⟩ : ∃ a b, g.inputs = [a,b] := by
      cases h : g.inputs with
      | nil => simp [h] at hlen
      | cons a mid => cases mid with
        | nil => simp [h] at hlen
        | cons b tail =>
          have empty : tail = [] := by
            apply List.length_eq_zero_iff.mp
            simpa [h] using hlen
          subst tail
          exact ⟨a,b,rfl⟩
    have ne : a ≠ b := by simpa [slots] using distinct g mem
    exact ⟨interpreted.1 g mem,a,b,slots,ne,earlier a (by simp [slots]),earlier b (by simp [slots])⟩
  · intro x
    rw [eval x, agree x]
    exact eligible.2.2 x
  · rw [degree]
    exact pDegree
  · rw [degree]
    exact lDegree
