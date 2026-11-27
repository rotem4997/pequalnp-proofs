import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4678_292
    (h1 :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let good := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (s : List ℕ) =>
        let extend := fun (x : List Bool) => x ++ [s.any (fun i => x.getD i false)]
        (∀ p l : Fin 13, p - l ∈ D → C.eval (extend (P p l)) = true) ∧
        (∀ Q, good Q → C.eval (extend (N Q)) = false)
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (s : List ℕ),
        s ∈ ([[0, 2], [13, 15], [0, 15], [0, 17], [0, 20]] : List (List ℕ)) →
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val) → fits C s →
        ∃ (B : PEqualNP.CircuitLowerBounds.Circuit) (t : List ℕ),
          t ∈ ([[], [0], [13], [0, 1], [13, 14], [0, 13], [0, 14]] : List (List ℕ)) ∧
          B.size = C.size ∧ PEqualNP.MetaComplexity.Monotone2 B ∧
          (∀ i : Fin B.gates.length, ∀ w ∈ (B.gates.get i).inputs, w < 27 + i.val) ∧ fits B t)
    (h2 :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let good := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (s : List ℕ) =>
        let extend := fun (x : List Bool) => x ++ [s.any (fun i => x.getD i false)]
        (∀ p l : Fin 13, p - l ∈ D → C.eval (extend (P p l)) = true) ∧
        (∀ Q, good Q → C.eval (extend (N Q)) = false)
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (t : List ℕ),
        t ∈ ([[], [0], [13], [0, 1], [13, 14], [0, 13], [0, 14]] : List (List ℕ)) →
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val) →
        fits C t → 63 ≤ C.size) : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List ℕ) => x2 fun (x5 : List Bool) => x3.eval (x5 ++ [x4.any fun (x6 : ℕ) => x5.getD x6 Bool.false]); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin x4.gates.length), ∀ x6 ∈ (x4.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5; have x5 : List (List ℕ) := [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (2 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)], [(0 : ℕ), (15 : ℕ)], [(0 : ℕ), (17 : ℕ)], [(0 : ℕ), (20 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(13 : ℕ), (15 : ℕ)]]; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ x5, PEqualNP.MetaComplexity.Monotone2 x6 → x4 x6 → x3 x6 x7 → (63 : ℕ) ≤ x6.size := by
  intro x1 x2 x3 x4 x5 C t ht hm hb hfit
  have hf : (∀ p l : Fin 13, p - l ∈ x1 →
        C.eval ((List.ofFn (fun u : Fin 13 => decide (u = p)) ++
          List.ofFn (fun v : Fin 13 => decide (v = l))) ++
          [t.any (fun i => (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))).getD i false)]) = true) ∧
      (∀ Q : Finset (Fin 13), (Q.card = 4 ∧
          ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ x1)).card ≤ 2) →
        C.eval ((List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
          List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ x1))) ++
          [t.any (fun i => (List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
            List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ x1))).getD i false)]) = false) :=
    ⟨hfit.1, fun Q hQ => hfit.2 Q hQ.1 hQ.2⟩
  have hdir : t ∈ ([[], [0], [13], [0, 1], [13, 14], [0, 13], [0, 14]] : List (List ℕ)) →
      63 ≤ C.size := fun h => h2 C t h hm hb hf
  have hvia : t ∈ ([[0, 2], [13, 15], [0, 15], [0, 17], [0, 20]] : List (List ℕ)) →
      63 ≤ C.size := by
    intro h
    obtain ⟨B, t', ht', hsize, hmB, hbB, hfB⟩ := h1 C t h hm hb hf
    rw [← hsize]
    exact h2 B t' ht' hmB hbB hfB
  have hcase : t ∈ ([[], [0], [13], [0, 1], [13, 14], [0, 13], [0, 14]] : List (List ℕ)) ∨
      t ∈ ([[0, 2], [13, 15], [0, 15], [0, 17], [0, 20]] : List (List ℕ)) := by
    have ht' : t ∈ ([[], [0], [13], [0, 1], [0, 2], [0, 13], [0, 14], [0, 15], [0, 17],
        [0, 20], [13, 14], [13, 15]] : List (List ℕ)) := ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht' ⊢
    rcases ht' with h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  rcases hcase with h | h
  · exact hdir h
  · exact hvia h
