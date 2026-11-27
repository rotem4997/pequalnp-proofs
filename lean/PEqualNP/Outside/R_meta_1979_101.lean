import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1979_101
    (classify :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let reps : List (ℕ × ℕ) := [(7, 904), (13, 2848), (19, 708), (21, 2720), (25, 2656), (37, 2440), (41, 2370), (133, 808)]
      let row := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
        let bit := fun (a b : ℕ) (i : Fin 13) =>
          if dual then b.testBit (-(m * i + t)).val else a.testBit (m * i + t).val
        Fin.append (bit z.1 z.2) (bit z.2 z.1)
      ∀ (P L : Finset (Fin 13)),
        (∀ p ∈ P, ∀ l ∈ L, p - l ∉ D) →
        (∀ l : Fin 13, (P.filter fun p => p - l ∈ D).card ≤ 2) →
        (∀ p : Fin 13, (L.filter fun l => p - l ∈ D).card ≤ 2) →
        ∃ z ∈ reps, ∃ m ∈ ([1, 3, 9] : List (Fin 13)), ∃ t : Fin 13, ∃ dual : Bool,
          ∀ k : Fin 26,
            decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨ (∃ l ∈ L, k = Fin.natAdd 13 l)) = true →
            row z m t dual k = true)
    (synthesize :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let reps : List (ℕ × ℕ) := [(7, 904), (13, 2848), (19, 708), (21, 2720), (25, 2656), (37, 2440), (41, 2370), (133, 808)]
      let row := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
        let bit := fun (a b : ℕ) (i : Fin 13) =>
          if dual then b.testBit (-(m * i + t)).val else a.testBit (m * i + t).val
        Fin.append (bit z.1 z.2) (bit z.2 z.1)
      ∃ C : Circuit, PEqualNP.TopForm.IsAO2 26 C ∧ C.size ≤ 63 ∧
        (∀ p l : Fin 13, p - l ∈ D →
          circuitFun 26 C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)) = true) ∧
        (∀ z ∈ reps, ∀ m ∈ ([1, 3, 9] : List (Fin 13)), ∀ t : Fin 13, ∀ dual : Bool,
          circuitFun 26 C (row z m t dual) = false)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∈ x3, ∀ x7 ∈ x4, x5 - x7 ∉ x1) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x7 - x6 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 - x8 ∈ x1}.card ≤ (2 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x9 ∈ x3, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ x9 ∈ x4, x8 = Fin.natAdd (13 : ℕ) x9)) = Bool.false := by
  classical
  dsimp only
  obtain ⟨C, hAO, hSize, hPos, hNeg⟩ := synthesize
  have hMono : Monotone2 C := fun g hg => ⟨hAO.1 g hg, (hAO.2.2 g hg).le⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have propagate (gs : List Gate) (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (u v : List Bool) (len : u.length = v.length)
      (sub : ∀ i, u.getD i false = true → v.getD i false = true) :
      ∀ i, (gs.foldl step u).getD i false = true → (gs.foldl step v).getD i false = true := by
    induction gs generalizing u v with
    | nil => exact sub
    | cons g gs ih =>
      apply ih (fun a ha => ops a (List.mem_cons_of_mem _ ha)) (step u g) (step v g)
        (by simp [step, len])
      intro i h
      change (v ++ [_]).getD i false = true
      change (u ++ [_]).getD i false = true at h
      by_cases hi : i < u.length
      · rw [List.getD_append _ _ _ _ hi] at h
        rw [List.getD_append _ _ _ _ (hi.trans_eq len)]
        exact sub i h
      · rw [List.getD_append_right _ _ _ _ (by omega)] at h ⊢
        rw [← len]
        cases hidx : i - u.length with
        | zero =>
          rw [hidx] at h
          simp only [List.getD_cons_zero] at h ⊢
          rcases ops g List.mem_cons_self with op | op <;> rw [op] at h ⊢
          · change (g.inputs.map fun j => u.getD j false).all id = true at h
            change (g.inputs.map fun j => v.getD j false).all id = true
            simp only [List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
              forall_apply_eq_imp_iff₂] at h ⊢
            exact fun j hj => sub j (h j hj)
          · change (g.inputs.map fun j => u.getD j false).any id = true at h
            change (g.inputs.map fun j => v.getD j false).any id = true
            rw [List.any_eq_true] at h ⊢
            obtain ⟨b, hb, hbeq⟩ := h
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
            exact ⟨true, List.mem_map.mpr ⟨j, hj, sub j (by simpa only [id_eq] using hbeq)⟩, rfl⟩
        | succ t => simp [hidx, List.getD_eq_getElem?_getD] at h
  refine ⟨C, hMono, hSize, hPos, ?_⟩
  intro P L hDisj hArcP hArcL
  obtain ⟨z, hz, m, hm, t, dual, hDom⟩ := classify P L hDisj hArcP hArcL
  let uFn : Fin 26 → Bool := fun x8 => decide ((∃ x9 ∈ P, x8 = Fin.castAdd 13 x9) ∨ ∃ x9 ∈ L, x8 = Fin.natAdd 13 x9)
  let bit := fun (a b : ℕ) (i : Fin 13) => if dual then b.testBit (-(m * i + t)).val else a.testBit (m * i + t).val
  let vFn : Fin 26 → Bool := Fin.append (bit z.1 z.2) (bit z.2 z.1)
  have hFalse : C.eval (List.ofFn vFn) = false := hNeg z hz m hm t dual
  apply Bool.eq_false_iff.mpr
  intro hTrue
  have hSub : ∀ i, (List.ofFn uFn).getD i false = true → (List.ofFn vFn).getD i false = true := by
    intro i hi
    by_cases hilt : i < 26
    · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hilt, Option.getD_some] at hi ⊢
      exact hDom ⟨i, hilt⟩ hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg hilt, Option.getD_none] at hi
      exact Bool.noConfusion hi
  have hvTrue : C.eval (List.ofFn vFn) = true :=
    propagate C.gates (fun g hg => (hAO.1 g hg)) (List.ofFn uFn) (List.ofFn vFn)
      (by simp) hSub C.output hTrue
  exact Bool.noConfusion (hvTrue.symm.trans hFalse)
