import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_4727_53
    (compile : ∀ C : Circuit, FanInTwo C →
      ∃ (D : BinaryCircuit) (N : Finset ℕ) (s : Bool),
        (∀ i : Fin D.gates.length, let q := D.gates.get i
          q.left < 11 + i.val ∧ q.right < 11 + i.val ∧
          ∃ a b : Bool, (a = true → q.left ∈ N) ∧ (b = true → q.right ∈ N) ∧
            Monotone (fun t : Bool × Bool => q.op (t.1 != a) (t.2 != b))) ∧
        D.output < 11 + D.size ∧ (s = true → D.output ∈ N) ∧
        N.card ≤ notCount C ∧ D.size + notCount C ≤ C.size ∧
        ∀ x : List Bool, x.length = 10 → (D.eval (x ++ [false]) != s) = C.eval x)
    (signedBound : ∀ (D : BinaryCircuit) (N : Finset ℕ) (s : Bool),
      (∀ i : Fin D.gates.length, let q := D.gates.get i
        q.left < 11 + i.val ∧ q.right < 11 + i.val ∧
        ∃ a b : Bool, (a = true → q.left ∈ N) ∧ (b = true → q.right ∈ N) ∧
          Monotone (fun t : Bool × Bool => q.op (t.1 != a) (t.2 != b))) →
      D.output < 11 + D.size → (s = true → D.output ∈ N) →
      N.card ≤ 4 → D.size + max 1 N.card ≤ 19 →
      ∃ x : Fin 10 → Bool, (D.eval (List.ofFn x ++ [false]) != s) ≠
        ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (19 : ℕ) → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x2 → PEqualNP.NotBracket.notCount x2 ≤ (4 : ℕ) → ¬∀ (x7 : Fin (10 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7 := by
  intro f C fan cost low high correct
  obtain ⟨D, N, s, gates, out, sign, marks, small, run⟩ := compile C fan
  obtain ⟨x, hx⟩ := signedBound D N s gates out sign (by omega) (by omega)
  apply hx
  rw [run _ List.length_ofFn, correct x]
  dsimp only [f, List.any_cons, List.any_nil]
  simp only [Bool.or_false]
  change _ = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) ||
    ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) ||
    ((x 2 && x 7) || ((x 3 && x 8) || ((x 4 && x 9) || ((x 5 && x 7) ||
    ((x 7 && x 9) || ((x 9 && x 6) || ((x 6 && x 8) || (x 8 && x 5)))))))))))))))
  ac_rfl
