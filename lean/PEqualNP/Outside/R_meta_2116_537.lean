import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2116_537
    (forced : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v w : Fin n)
      (i : Fin C.size), v ≠ w → (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      ((C.gates.get i).inputs = [v.val, w.val] ∨ (C.gates.get i).inputs = [w.val, v.val]) →
      (∀ j : Fin C.size, v.val ∈ (C.gates.get j).inputs → j = i) →
      PEqualNP.MetaComplexity.circuitFun n C (fun j => decide (j = v)) = false →
      ∀ x : Fin n → Bool, x w = true →
        PEqualNP.MetaComplexity.circuitFun n C (Function.update x v true) =
        PEqualNP.MetaComplexity.circuitFun n C (Function.update x v false))
    (internal : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.IsMinimalCircuit 9 C → C.size ≤ 15 →
      PEqualNP.MetaComplexity.circuitFun 9 C =
        (fun x : Fin 9 → Bool =>
          ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
            (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any
              (fun e => x e.1 && x e.2)) →
      (∀ i : Fin C.size, (∀ w ∈ (C.gates.get i).inputs, w < 9 + i.val) ∧
        (C.gates.get i).inputs.Nodup ∧
        ((C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          (C.gates.get i).inputs.length = 1 ∨
        (C.gates.get i).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
          (C.gates.get i).inputs.length = 2)) →
      (∀ v ∈ ([4, 6, 7] : List (Fin 9)), ∃ i : Fin C.size,
        (∀ j : Fin C.size, v.val ∈ (C.gates.get j).inputs ↔ j = i) ∧
        (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ∃ w ∈ (C.gates.get i).inputs, 9 ≤ w) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x6).card = (1 : ℕ) ∧ ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  dsimp only
  intro C hP hS
  obtain ⟨hmin, hsize, hfun, hnorm, -⟩ := hP
  let f (x : Fin 9 → Bool) : Bool :=
    ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
      (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any
        (fun e => x e.1 && x e.2)
  have hfun' : PEqualNP.MetaComplexity.circuitFun 9 C = f := by
    rw [hfun]
    funext x
    dsimp only [f]
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  have singleton_false : ∀ v : Fin 9, f (fun j => decide (j = v)) = false := by decide
  have witness : ∀ (v w : Fin 9), v ∈ ([4, 6, 7] : List (Fin 9)) → v ≠ w →
      ∃ z : Fin 9, f (Function.update (fun j => decide (j = w ∨ j = z)) v true) = true ∧
        f (Function.update (fun j => decide (j = w ∨ j = z)) v false) = false := by decide
  apply internal C hmin hsize hfun' hnorm
  intro v hv
  obtain ⟨hcard, hOr⟩ := hS v hv
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have hUnique (j : Fin C.size) : v.val ∈ (C.gates.get j).inputs ↔ j = i := by
    have heq := Finset.ext_iff.mp hi j
    simpa using heq
  have hOp : (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    apply hOr
    rw [hi]
    exact Finset.mem_singleton_self i
  refine ⟨i, hUnique, hOp, ?_⟩
  have hLen : (C.gates.get i).inputs.length = 2 := by
    rcases (hnorm i).2.2 with h | h
    · rw [hOp] at h
      cases h.1
    · exact h.2
  have hNoRaw (w : Fin 9) (hne : v ≠ w)
      (hargs : (C.gates.get i).inputs = [v.val, w.val] ∨
        (C.gates.get i).inputs = [w.val, v.val]) : False := by
    obtain ⟨z, hYes, hNo⟩ := witness v w hv hne
    have he := forced 9 C v w i hne hOp hargs (fun j => (hUnique j).1)
      (by rw [hfun']; exact singleton_false v) (fun j => decide (j = w ∨ j = z)) (by simp)
    rw [hfun', hYes, hNo] at he
    contradiction
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hLen
  have hvab := (hUnique i).2 rfl
  rw [hab] at hvab
  have habNe : a ≠ b := by
    have h := (hnorm i).2.1
    rw [hab] at h
    simpa using h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hvab
  rcases hvab with hav | hbv
  · by_cases h : 9 ≤ b
    · exact ⟨b, by simp [hab], h⟩
    · apply False.elim
      exact hNoRaw ⟨b, Nat.lt_of_not_ge h⟩
        (fun he => habNe (hav.symm.trans (congrArg Fin.val he))) (Or.inl (by simpa [hav] using hab))
  · by_cases h : 9 ≤ a
    · exact ⟨a, by simp [hab], h⟩
    · apply False.elim
      exact hNoRaw ⟨a, Nat.lt_of_not_ge h⟩
        (fun he => habNe ((congrArg Fin.val he).symm.trans hbv))
        (Or.inr (by simpa [hbv] using hab))
