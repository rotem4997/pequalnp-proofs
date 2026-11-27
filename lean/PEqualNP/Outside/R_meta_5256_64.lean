import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- Separate removing false positives at AND gates, extending the quadrangle tests,
-- and counting the gates of a circuit that is clean on all independent inputs.
theorem PEqualNP.Outside.R_meta_5256_64
    (repair : let S : Finset (Fin 13) := {0,1,3,9}
      let T := fun (b : Bool) (x : List Bool) => if b = true then
        ∃ p l : Fin 13, p-l ∈ S ∧ x = (List.ofFn fun u : Fin 13 => decide (u=p)) ++
          List.ofFn fun u : Fin 13 => decide (u=l)
        else ∃ Q : Finset (Fin 13), Q.card = 4 ∧ (∀ l : Fin 13, (Q.filter (fun p => p-l ∈ S)).card ≤ 2) ∧
          x = (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++ List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ S)
      ∀ C : Circuit, Monotone2 C → ReadsBack 26 C →
        (∀ b x, T b x → C.eval x = b) → 2 ≤ C.lineDeg 26 (Finset.Ico 13 26) →
        (∀ j < C.size, ∀ i ≤ 26+j, ∃ b x, T b x ∧ (C.wires x).getD (26+j) false = b ∧
          (if i=26+j then false else (C.wires x).getD i false) = !b) →
        (∃ j k, (∀ i ∈ [j,k], (gateAt C i).op = .and) ∧ PEqualNP.EdgeOwnership.InCone 26 C j k) →
        ∃ D : Circuit, D.size ≤ C.size ∧ IsAO2 26 D ∧
          (∀ i < D.size, 26+i = D.output ∨ ∃ j < D.size, 26+i ∈ (gateAt D j).inputs) ∧
          (∀ b x, T b x → D.eval x = b) ∧
          ∀ j < D.size, (gateAt D j).op = .and → ∀ x, T false x →
            (D.wires x).getD (26+j) false = false)
    (extendTests : let S : Finset (Fin 13) := {0,1,3,9}
      let T := fun (b : Bool) (x : List Bool) => if b = true then
        ∃ p l : Fin 13, p-l ∈ S ∧ x = (List.ofFn fun u : Fin 13 => decide (u=p)) ++
          List.ofFn fun u : Fin 13 => decide (u=l)
        else ∃ Q : Finset (Fin 13), Q.card = 4 ∧ (∀ l : Fin 13, (Q.filter (fun p => p-l ∈ S)).card ≤ 2) ∧
          x = (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++ List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ S)
      let F := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13, p-l ∈ S ∧
        x (p.castAdd 13) = true ∧ x (Fin.natAdd 13 l) = true
      ∀ D : Circuit, (IsAO2 26 D ∧
          (∀ i < D.size, 26+i = D.output ∨ ∃ j < D.size, 26+i ∈ (gateAt D j).inputs) ∧
          (∀ b x, T b x → D.eval x = b) ∧
          ∀ j < D.size, (gateAt D j).op = .and → ∀ x, T false x →
            (D.wires x).getD (26+j) false = false) → (∀ x, D.eval (List.ofFn x) = true ↔ F x) ∧
        ∀ j < D.size, (gateAt D j).op = .and → ∀ x : Fin 26 → Bool,
          (D.wires (List.ofFn x)).getD (26+j) false = true → F x)
    (count : let S : Finset (Fin 13) := {0,1,3,9}
      let F := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13, p-l ∈ S ∧
        x (p.castAdd 13) = true ∧ x (Fin.natAdd 13 l) = true
      ∀ D : Circuit, IsAO2 26 D →
        (∀ i < D.size, 26+i = D.output ∨ ∃ j < D.size, 26+i ∈ (gateAt D j).inputs) →
        ((∀ x, D.eval (List.ofFn x) = true ↔ F x) ∧
        ∀ j < D.size, (gateAt D j).op = .and → ∀ x : Fin 26 → Bool,
          (D.wires (List.ofFn x)).getD (26+j) false = true → F x) → 64 ≤ D.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → (∀ (x6 : Bool) (x7 : List Bool), x2 x6 x7 → x3.eval x7 = x6) → (2 : ℕ) ≤ x3.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) → (∀ x8 < x3.size, ∀ x10 ≤ (26 : ℕ) + x8, ∃ (x12 : Bool) (x13 : List Bool), x2 x12 x13 ∧ (x3.wires x13).getD ((26 : ℕ) + x8) Bool.false = x12 ∧ (if x10 = (26 : ℕ) + x8 then Bool.false else (x3.wires x13).getD x10 Bool.false) = !x12) → (∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x9 x10) → (64 : ℕ) ≤ x3.size := by
  dsimp only at repair extendTests count ⊢
  intro C hm hr tests degree separates nested
  obtain ⟨j,k,hj,hk,path⟩ := nested
  have both : ∀ i ∈ [j,k], (gateAt C i).op = .and := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    · exact hj
    · exact hk
  obtain ⟨D,small,model,used,correct,quiet⟩ := repair C hm hr tests degree separates ⟨j,k,both,path⟩
  exact (count D model used (extendTests D ⟨model,used,correct,quiet⟩)).trans small
