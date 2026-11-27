import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Normalize the free OR under incidence-preserving permutations on the two input blocks.
-- Empty, singletons, same-side pairs, flags, and nonflags give seven representatives.
theorem PEqualNP.Outside.R_meta_2343_1
    (normalize :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let good := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let fits := fun (C : Circuit) (s : List ℕ) =>
        let extend := fun (x : List Bool) => x ++ [s.any (fun i => x.getD i false)]
        (∀ p l : Fin 13, p - l ∈ D → C.eval (extend (P p l)) = true) ∧
        (∀ Q, good Q → C.eval (extend (N Q)) = false)
      ∀ (C : Circuit) (s : List ℕ), s.length ≤ 2 → Monotone2 C →
        (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val) → fits C s →
        ∃ (B : Circuit) (t : List ℕ), t ∈ ([[], [0], [13], [0,1], [13,14], [0,13], [0,14]] : List (List ℕ)) ∧
          B.size = C.size ∧ Monotone2 B ∧ (∀ i : Fin B.gates.length, ∀ w ∈ (B.gates.get i).inputs, w < 27 + i.val) ∧ fits B t)
    (representatives :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let good := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let fits := fun (C : Circuit) (s : List ℕ) =>
        let extend := fun (x : List Bool) => x ++ [s.any (fun i => x.getD i false)]
        (∀ p l : Fin 13, p - l ∈ D → C.eval (extend (P p l)) = true) ∧
        (∀ Q, good Q → C.eval (extend (N Q)) = false)
      ∀ (C : Circuit) (t : List ℕ), t ∈ ([[], [0], [13], [0,1], [13,14], [0,13], [0,14]] : List (List ℕ)) →
        Monotone2 C → (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val) → fits C t → 63 ≤ C.size) :
    ∀ (C : Circuit) (s : List ℕ), s.length ≤ 2 → Monotone2 C →
      (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val) →
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let good := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let extend := fun (x : List Bool) => x ++ [s.any (fun i => x.getD i false)]
      (∀ p l : Fin 13, p - l ∈ D → C.eval (extend (P p l)) = true) →
      (∀ Q, good Q → C.eval (extend (N Q)) = false) →
      63 ≤ C.size := by
  intro C s hs hm hb
  dsimp only
  intro hpos hneg
  obtain ⟨B, t, ht, hsize, hmono, hback, hrows⟩ :=
    normalize C s hs hm hb ⟨hpos, hneg⟩
  exact hsize ▸ representatives B t ht hmono hback hrows
