import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1700000 in
theorem PEqualNP.Outside.R_meta_7700_71
    (peel : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) → (gateAt C 0).op = GateOp.and →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      (let profile := fun (j v : ℕ) => gateVal 14 C j (fun i => decide (i.val = v))
       ∃ a b : Fin C.size, (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧
        profile a 7 = true ∧ profile a 0 = false ∧ profile b 0 = true ∧ profile b 7 = false) →
      ∃ moves : List (ℕ × ℕ), moves.length = 7 ∧
        (∀ i : Fin moves.length, (moves.get i).1 < C.size - i.val) ∧
        let D := moves.foldl (fun A e => eraseGate 14 A e.1 e.2) C
        ∀ x : Fin 14 → Bool, x 0 = false → x 7 = false → D.eval (List.ofFn x) = C.eval (List.ofFn x))
    (residual : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 14 → Bool, x 0 = false → x 7 = false → (D.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
      21 ≤ D.size) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∃ x7 < x1.size,                 ∃ x8 < x1.size,                   (0 : ℕ) < x7 ∧                     (0 : ℕ) < x8 ∧                       x7 ≠ x8 ∧                         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧                           (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧                             have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = (0 : Fin (14 : ℕ))));                             have x10 : List Bool := x1.wires (List.ofFn fun (x10 : Fin (14 : ℕ)) => Decidable.decide (x10 = (7 : Fin (14 : ℕ))));                             x10.getD ((14 : ℕ) + x7) Bool.false = Bool.true ∧ x9.getD ((14 : ℕ) + x7) Bool.false = Bool.false ∧ x9.getD ((14 : ℕ) + x8) Bool.false = Bool.true ∧ x10.getD ((14 : ℕ) + x8) Bool.false = Bool.false) →               False := by
  intro C size legal distinct first computes pair
  have inc : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p = l ∨ p = l+1 ∨ p = l+3 := by decide +kernel
  have comp (x : Fin 14 → Bool) : C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    simpa only [inc] using computes x
  obtain ⟨a,ha,b,hb,_,_,_,oa,ob,ta,fa,tb,fb⟩ := pair
  have atZero : (fun i : Fin 14 => decide (i.val = 0)) = (fun i => decide (i = 0)) := by decide +kernel
  have atSeven : (fun i : Fin 14 => decide (i.val = 7)) = (fun i => decide (i = 7)) := by decide +kernel
  obtain ⟨moves,len,valid,agree⟩ := peel C size legal distinct first comp (by
    refine ⟨⟨a,ha⟩,⟨b,hb⟩,oa,ob,?_,?_,?_,?_⟩
    all_goals unfold gateVal; simp only [atZero,atSeven]; assumption)
  have mono : Monotone2 C := by
    intro g hg
    refine ⟨?_,by have h := legal.2.2 g hg; omega⟩
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal.1 g hg
  let edit := fun (A : Circuit) (e : ℕ × ℕ) => eraseGate 14 A e.1 e.2
  have erase {A : Circuit} (g t : ℕ) (hg : g < A.size) (hA : Monotone2 A) :
      (eraseGate 14 A g t).size + 1 = A.size ∧ Monotone2 (eraseGate 14 A g t) := by
    change g < A.gates.length at hg
    unfold eraseGate
    rw [if_pos hg]
    constructor
    · change (A.gates.take g ++ (A.gates.drop (g+1)).map _).length + 1 = A.gates.length
      rw [List.length_append,List.length_take,List.length_map,List.length_drop,Nat.min_eq_left (Nat.le_of_lt hg)]
      omega
    · intro z hz
      simp only [List.mem_append,List.mem_map] at hz
      rcases hz with before | ⟨a,ha,rfl⟩
      · exact hA _ (List.mem_of_mem_take before)
      · obtain ⟨ops,len⟩ := hA _ (List.mem_of_mem_drop ha)
        exact ⟨ops,by simpa using len⟩
  have account (ms : List (ℕ × ℕ)) (A : Circuit) (ok : Monotone2 A)
      (bounds : ∀ i : Fin ms.length, (ms.get i).1 < A.size - i.val) :
      (ms.foldl edit A).size + ms.length = A.size ∧ Monotone2 (ms.foldl edit A) := by
    induction ms generalizing A with
    | nil => exact ⟨rfl,ok⟩
    | cons e es ih =>
      have h0 := bounds ⟨0,by simp⟩
      have one := erase (A:=A) e.1 e.2 (by simpa using h0) ok
      change (edit A e).size + 1 = A.size ∧ Monotone2 (edit A e) at one
      have tail (i : Fin es.length) : (es.get i).1 < (edit A e).size - i.val := by
        have b := bounds ⟨i.val+1,by simp <;> omega⟩
        change (es.get i).1 < A.size - (i.val+1) at b
        have sz := one.1
        omega
      obtain ⟨cost,legalTail⟩ := ih (edit A e) one.2 tail
      exact ⟨by simpa only [List.foldl_cons,List.length_cons] using (show (es.foldl edit (edit A e)).size + (es.length+1) = A.size by omega),legalTail⟩
  obtain ⟨cost,legalD⟩ := account moves C mono valid
  have h := residual (moves.foldl edit C) legalD (by
    intro x hx hy
    have e : (moves.foldl edit C).eval (List.ofFn x) = C.eval (List.ofFn x) := agree x hx hy
    rw [e]; exact comp x)
  omega
