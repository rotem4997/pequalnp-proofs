import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5888_1
    (nestedShare : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      let uses := C.output :: C.gates.flatMap Gate.inputs
      let shared (i : ℕ) := 2 ≤ uses.count (14+i)
      let raw (i : ℕ) := ∀ v ∈ (gateAt C i).inputs, v < 14
      let cone := InCone 14 C
      let witness (i : ℕ) (v : Fin 14) := (gateAt C i).op = GateOp.and ∧
        (14+i = C.output ∨ cone i (C.output-14)) ∧ gateVal 14 C i (pairInput 0 7) = true ∧
        ∀ b : Fin 2, wireVal 14 C (opnd C i b) (pairInput v v) = false
      (∃ i, shared i ∧ ¬raw i) → ∀ i j, i ≠ j → ¬cone i j → ¬cone j i → witness i 0 → witness j 7 → False)
    (twoRawShares : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      let uses := C.output :: C.gates.flatMap Gate.inputs
      let shared (i : ℕ) := 2 ≤ uses.count (14+i)
      let raw (i : ℕ) := ∀ v ∈ (gateAt C i).inputs, v < 14
      let cone := InCone 14 C
      let witness (i : ℕ) (v : Fin 14) := (gateAt C i).op = GateOp.and ∧
        (14+i = C.output ∨ cone i (C.output-14)) ∧ gateVal 14 C i (pairInput 0 7) = true ∧
        ∀ b : Fin 2, wireVal 14 C (opnd C i b) (pairInput v v) = false
      (∃ i j, i ≠ j ∧ shared i ∧ raw i ∧ shared j ∧ raw j) → ∀ i j, i ≠ j → ¬cone i j → ¬cone j i → witness i 0 → witness j 7 → False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List ℕ := List.filter (fun (x2 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x2)) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates);   have x3 : ℕ → Prop := fun (x3 : ℕ) => x3 < x1.gates.length ∧ (∀ x4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).inputs, x4 < (14 : ℕ)) ∧ (List.filter (fun (x4 : ℕ) => x4 != (14 : ℕ) + x3) x2).Nodup;   have x4 : ℕ → Fin (14 : ℕ) → Prop := fun (x4 : ℕ) (x5 : Fin (14 : ℕ)) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x4 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x4 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x6 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x4 x6) (PEqualNP.EdgeOwnership.pairInput x5 x5) = Bool.false;   x1.size ≤ (27 : ℕ) → (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 ≠ x10 ∧ x9 < (14 : ℕ) + x6 ∧ x10 < (14 : ℕ) + x6) → (∀ (x7 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (7 : ℕ)) (x9 : Fin (7 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (7 : ℕ)) ∨ x8 = x9 + (3 : Fin (7 : ℕ))) ∧ x7 (Fin.castAdd (7 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (7 : ℕ) x9) = Bool.true) → ¬x2.Nodup → (¬∃ (x9 : ℕ), x3 x9) → ∀ (x10 x11 : ℕ), x10 ≠ x11 → ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x10 x11 → ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x11 x10 → x4 x10 (0 : Fin (14 : ℕ)) → x4 x11 (7 : Fin (14 : ℕ)) → False) := by
  intro C used first witness size shape correct repeats noFirst
  let uses := C.output :: C.gates.flatMap Gate.inputs
  let shared (i : ℕ) := 2 ≤ uses.count (14+i)
  let raw (i : ℕ) := ∀ v ∈ (gateAt C i).inputs, v < 14
  have ops (g : Gate) (hg : g ∈ C.gates) :
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b := by
    obtain ⟨j, hj, h⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨hop,a,b,hs,hab,_⟩ := shape j g (by simp [hj, h])
    exact ⟨hop,a,b,hs,hab⟩
  have ao : IsAO2 14 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      exact (ops g hg).1
    · intro j hj t ht
      obtain ⟨_, a,b, hs,_,ha,hb⟩ := shape j C.gates[j] (by simp [hj])
      change t ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs at ht
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
        Option.getD_some] at ht
      rw [hs] at ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨_,a,b, hs, _⟩ := ops g hg
      simp [hs]
  have distinct (g : Gate) (hg : g ∈ C.gates) : g.inputs.Nodup := by
    obtain ⟨_,a,b,hs,hab⟩ := ops g hg
    simp [hs, hab]
  have inc : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p=l ∨ p=l+1 ∨ p=l+3 := by decide
  have corr (x : Fin 14 → Bool) := correct x
  simp_rw [← inc] at corr
  by_cases hn : ∃ i, shared i ∧ ¬raw i
  · exact nestedShare C size ao distinct corr hn
  have allRaw (i) (h : shared i) : raw i := by by_contra h'; exact hn ⟨i,h,h'⟩
  have findDup (l : List ℕ) (h : ¬l.Nodup) : ∃ w, 2 ≤ l.count w := by
    by_contra! h'
    exact h (List.nodup_iff_count.mpr fun w => by have := h' w; omega)
  have locate (w : ℕ) (hw : 2 ≤ used.count w) :
      ∃ i, w = 14+i ∧ i < C.gates.length ∧ shared i := by
    have mem := List.count_pos_iff.mp (by omega : 0 < used.count w)
    have low : 14 ≤ w := by simpa using (List.mem_filter.mp mem).2
    have hcnt : 2 ≤ uses.count w := by
      simpa [used, uses, List.count_filter (p := fun t : ℕ => decide (14 ≤ t)) (by simpa using low : decide (14 ≤ w) = true)] using hw
    have inside : w ∈ C.gates.flatMap Gate.inputs := by
      by_contra h
      have hz := List.count_eq_zero_of_not_mem h
      simp only [uses, List.count_cons, hz] at hcnt
      split at hcnt <;> omega
    obtain ⟨g,hg,hmem⟩ := List.mem_flatMap.mp inside
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨_,a,b,hs,_,ha,hb⟩ := shape j g (by simp [hj, he])
    rw [hs] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    have eq : w = 14+(w-14) := by omega
    refine ⟨w-14,eq,by rcases hmem with rfl | rfl <;> omega,?_⟩
    simpa only [shared, ← eq] using hcnt
  obtain ⟨w,hw⟩ := findDup used repeats
  obtain ⟨i,rfl,hi,hsi⟩ := locate w hw
  have remaining : ¬(used.filter (fun v => v != 14+i)).Nodup :=
    fun h => noFirst ⟨i, hi, allRaw i hsi, h⟩
  obtain ⟨v,hv⟩ := findDup _ remaining
  have hm := List.count_pos_iff.mp (by omega : 0 < (used.filter (fun t => t != 14+i)).count v)
  have test := (List.mem_filter.mp hm).2
  rw [List.count_filter (p := fun t : ℕ => t != 14+i) (a := v) test] at hv
  obtain ⟨j,rfl,_,hsj⟩ := locate v hv
  have ne : i ≠ j := by rintro rfl; simp at test
  exact twoRawShares C size ao distinct corr ⟨i,j,ne,hsi,allRaw i hsi,hsj,allRaw j hsj⟩
