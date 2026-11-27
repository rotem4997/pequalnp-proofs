import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.ReadTwo PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_6068_613
    (save : ∀ C : Circuit, 63 ≤ C.size → C.size ≤ 64 → PEqualNP.TopForm.IsAO2 26 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      let V := fun s : Finset ℕ => wval C (indW 26 s)
      let A := fun (u j : ℕ) => isAnd C j ∧
        ∀ i ∈ (gateAt C j).inputs, V {0,13} i = true ∧ V {u} i = false
      (∃ j k, j ≠ k ∧ A 0 j ∧ A 13 k ∧ V {13} (26+j) ≠ V {0} (26+k)) →
      ∃ (s : Fin 26) (D : Circuit), (s = 0 ∨ s = 13) ∧ PEqualNP.TopForm.IsAO2 26 D ∧
        D.size + 6 ≤ C.size ∧ ∀ x : Fin 26 → Bool,
          D.eval (List.ofFn x) = C.eval (List.ofFn (fun i => if i = s then false else x i)))
    (punctured : ∀ (s : Fin 26) (D : Circuit), (s = 0 ∨ s = 13) →
      PEqualNP.TopForm.IsAO2 26 D →
      (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧
        Fin.castAdd 13 p ≠ s ∧ Fin.natAdd 13 l ≠ s ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) → 59 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →               PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →                 have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);                 have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 : ℕ) (x15 : ℕ), x1.gates[x12]? = Option.some x13 ∧ x11 = (26 : ℕ) + x12 ∧ x13.inputs = [x14, x15] ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x10 = x14 ∨ x10 = x15) ∨ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x10 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x15) ∧ x9 {(0 : ℕ), (13 : ℕ)} x10 = Bool.true ∧ x9 {(0 : ℕ), (13 : ℕ)} x11 = Bool.true;                 have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) => Relation.ReflTransGen x10 ((26 : ℕ) + x12) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x12 ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs, x9 {(0 : ℕ), (13 : ℕ)} x13 = Bool.true ∧ x9 {x11} x13 = Bool.false;                 (∃ (x12 : ℕ) (x13 : ℕ), x12 ≠ x13 ∧ x11 (0 : ℕ) x12 ∧ x11 (13 : ℕ) x13 ∧ x9 {(13 : ℕ)} ((26 : ℕ) + x12) ≠ x9 {(0 : ℕ)} ((26 : ℕ) + x13)) → False := by
  intro C lo hi ao nodup correct _ _
  intro V path blocked witness
  obtain ⟨j,k,hne,hj,hk,hval⟩ := witness
  obtain ⟨s,D,hs,hD,hsize,hfun⟩ := save C lo hi ao nodup correct ⟨j,k,hne,hj.2,hk.2,hval⟩
  have hmin := punctured s D hs hD (by
    intro x
    rw [hfun,correct]
    constructor
    · rintro ⟨p,l,inc,hp,hl⟩
      by_cases ep : Fin.castAdd 13 p = s
      · simp only [if_pos ep, Bool.false_eq_true] at hp
      by_cases el : Fin.natAdd 13 l = s
      · simp only [if_pos el, Bool.false_eq_true] at hl
      exact ⟨p,l,inc,ep,el,by simpa only [if_neg ep] using hp,by simpa only [if_neg el] using hl⟩
    · rintro ⟨p,l,inc,ep,el,hp,hl⟩
      exact ⟨p,l,inc,by simpa only [if_neg ep] using hp,by simpa only [if_neg el] using hl⟩)
  omega
