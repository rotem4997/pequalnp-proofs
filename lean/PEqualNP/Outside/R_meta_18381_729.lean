import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_18381_729
    (trim : ∀ (n : ℕ) (C : Circuit) (s : Fin n) (U : ℕ → Bool), TopForm.IsAO2 n C →
      let T := ReadTwo.wval C (fun i : Fin n => decide (i ≠ s))
      U C.output = true →
      (∀ j < C.size, U (n+j) = true → T (n+j) = true →
        ∀ i ∈ (gateAt C j).inputs, T i = true → U i = true) →
      ∃ D : Circuit, TopForm.IsAO2 n D ∧
        D.size ≤ ((List.range C.size).filter (fun j => U (n+j) && (gateAt C j).inputs.all T)).length ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn fun i => if i=s then false else x i))
    (count : ∀ C : Circuit, 63 ≤ C.size → C.size ≤ 64 → TopForm.IsAO2 26 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
        (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true) →
      let V := fun S : Finset ℕ => ReadTwo.wval C (ReadTwo.indW 26 S)
      let A := fun v j : ℕ => ReadTwo.isAnd C j ∧ ∀ i ∈ (gateAt C j).inputs, V {0,13} i=true ∧ V {v} i=false
      (∃ j k, j≠k ∧ A 0 j ∧ A 13 k ∧ V {13} (26+j) ≠ V {0} (26+k)) →
      ∃ (s : Fin 26) (U : ℕ → Bool), (s=0 ∨ s=13) ∧
        let T := ReadTwo.wval C (fun i : Fin 26 => decide (i ≠ s))
        U C.output = true ∧ (∀ j < C.size, U (26+j)=true → T (26+j)=true →
          ∀ i ∈ (gateAt C j).inputs, T i=true → U i=true) ∧
        ((List.range C.size).filter (fun j => U (26+j) && (gateAt C j).inputs.all T)).length + 6 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             have x7 : Finset ℕ → ℕ → Bool := fun (x7 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x7);             have x8 : ℕ → ℕ → Prop := fun (x8 x9 : ℕ) => PEqualNP.ReadTwo.isAnd x1 x9 ∧ ∀ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).inputs, x7 {(0 : ℕ), (13 : ℕ)} x10 = Bool.true ∧ x7 {x8} x10 = Bool.false;             (∃ (x9 : ℕ) (x10 : ℕ), x9 ≠ x10 ∧ x8 (0 : ℕ) x9 ∧ x8 (13 : ℕ) x10 ∧ x7 {(13 : ℕ)} ((26 : ℕ) + x9) ≠ x7 {(0 : ℕ)} ((26 : ℕ) + x10)) → ∃ (x10 : Fin (26 : ℕ)) (x11 : PEqualNP.CircuitLowerBounds.Circuit), (x10 = (0 : Fin (26 : ℕ)) ∨ x10 = (13 : Fin (26 : ℕ))) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x11 ∧ x11.size + (6 : ℕ) ≤ x1.size ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), x11.eval (List.ofFn x12) = x1.eval (List.ofFn fun (x13 : Fin (26 : ℕ)) => if x13 = x10 then Bool.false else x12 x13) := by
  intro C lo hi ao nd spec V A wit
  obtain ⟨s,U,hs,ho,closed,ns⟩ := count C lo hi ao nd spec wit
  obtain ⟨D,good,size,ev⟩ := trim 26 C s U ao ho closed
  exact ⟨s,D,hs,good,le_trans (Nat.add_le_add_right size 6) ns,ev⟩
