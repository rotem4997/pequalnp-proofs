import PEqualNP.Defs

-- On the chosen input slice each marked gate agrees with an earlier wire.
-- Earlier representatives can themselves be marked: their indices decrease.
theorem PEqualNP.Outside.R_meta_7217_71
    (findCopies :
      let target := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
      let inputs := fun (p : Fin 10 → Fin 10) (x : Fin 10 → Bool) => List.ofFn (x ∘ p) ++ [x 0 && x 2]
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin 10 → Fin 10),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 18 →
        (∀ x, C.eval (inputs p x) = target x) →
        ∃ (v : Fin 10) (S : Finset (Fin C.size)), 4 ≤ S.card ∧
          ∀ i ∈ S, ∃ j < 11 + i.val, ∀ x : Fin 10 → Bool, x v = false →
            let w := C.wires (inputs p x)
            w.getD (11 + i.val) false = w.getD j false)
    (eraseCopies :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (n : ℕ) (A : Set (List Bool))
        (S : Finset (Fin C.size)), PEqualNP.MetaComplexity.FanInTwo C →
        (∀ x ∈ A, List.length x = n) →
        (∀ i ∈ S, ∃ j < n + i.val, ∀ x ∈ A,
          (C.wires x).getD (n + i.val) false = (C.wires x).getD j false) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
          D.size + S.card ≤ C.size ∧ ∀ x ∈ A, D.eval x = C.eval x) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (10 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (10 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (10 : ℕ) → Fin (10 : ℕ)) → (Fin (10 : ℕ) → Bool) → List Bool := fun (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Fin (10 : ℕ) → Bool) => List.ofFn (x3 ∘ x2) ++ [x3 (0 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (18 : ℕ) → (∀ (x7 : Fin (10 : ℕ) → Bool), x3.eval (x2 x4 x7) = x1 x7) → ∃ (x8 : Fin (10 : ℕ)) (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x9 ∧ x9.size + (4 : ℕ) ≤ x3.size ∧ ∀ (x10 : Fin (10 : ℕ) → Bool), x10 x8 = Bool.false → x9.eval (x2 x4 x10) = x3.eval (x2 x4 x10) := by
  dsimp only at findCopies ⊢
  intro C p hfan hsize hfun
  obtain ⟨v, S, hfour, hw⟩ := findCopies C p hfan hsize hfun
  let inputs := (fun (p : Fin 10 → Fin 10) (x : Fin 10 → Bool) => List.ofFn (x ∘ p) ++ [x 0 && x 2]) p
  let A : Set (List Bool) := {ys | ∃ x : Fin 10 → Bool, x v = false ∧ ys = inputs x}
  obtain ⟨D, hD, hlen, heval⟩ := eraseCopies C 11 A S hfan (by
    rintro ys ⟨x, _, rfl⟩
    simp [inputs]) (by
    intro i hi
    obtain ⟨j, hj, h⟩ := hw i hi
    refine ⟨j, hj, ?_⟩
    rintro ys ⟨x, hx, rfl⟩
    exact h x hx)
  exact ⟨v, D, hD, by omega, fun x hx => heval (inputs x) ⟨x, hx, rfl⟩⟩
