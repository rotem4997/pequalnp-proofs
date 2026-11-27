import PEqualNP.Defs

-- The symmetry in the conclusion is bookkeeping: it is enough to fix ANY vertex u to v (core),
-- because the Petersen graph is vertex-transitive (transitive) and renaming the inputs of a
-- circuit keeps its size (relabel). The core lets a gate-elimination argument choose its vertex.
theorem PEqualNP.Outside.R_meta_3821_642
    (relabel : ∀ (n : ℕ) (π : Fin n → Fin n) (E : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo E → ∃ F : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo F ∧ F.size = E.size ∧
          ∀ y : Fin n → Bool, F.eval (List.ofFn y) = E.eval (List.ofFn (y ∘ π)))
    (transitive : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ))));
      ∀ u : Fin 10, ∃ s : Equiv.Perm (Fin 10), s u = 9 ∧ ∀ x : Fin 10 → Bool, x1 (x ∘ s) = x1 x)
    (core : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ))));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (18 : ℕ) →
        have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;
        have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 || x7 x8 x4;
        (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) →
        ∃ (u : Fin 10) (v : Bool) (E : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo E ∧
          (E.size ≤ if v = true then 10 else 15) ∧
          ∀ x : Fin 10 → Bool, x u = v → E.eval (List.ofFn fun j : Fin 9 => x (u.succAbove j)) = x8 x) :
    (have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (18 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 || x7 x8 x4;       (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) → ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧ PEqualNP.MetaComplexity.FanInTwo x14 ∧ (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧ ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12)) := by
  intro x1 D a b fan small x7 x8 h1 h2 h3
  obtain ⟨u, v, E, fanE, sizeE, evalE⟩ := core D a b fan small h1 h2 h3
  obtain ⟨s, su, inv⟩ := transitive u
  have su' : s u = Fin.last 9 := su
  have ne : ∀ j : Fin 9, s (u.succAbove j) ≠ Fin.last 9 := by
    intro j h
    exact Fin.succAbove_ne u j (s.injective (h.trans su'.symm))
  let π : Fin 9 → Fin 9 := fun j => (s (u.succAbove j)).castPred (ne j)
  obtain ⟨F, fanF, sizeF, evalF⟩ := relabel 9 π E fanE
  refine ⟨s, v, F, inv, fanF, sizeF ▸ sizeE, ?_⟩
  intro y
  let x : Fin 10 → Bool := (fun i : Fin (9 + 1) => Fin.lastCases v y i) ∘ s
  have hx : x u = v := by
    show Fin.lastCases v y (s u) = v
    rw [su']
    exact Fin.lastCases_last
  have key : y ∘ π = fun j : Fin 9 => x (u.succAbove j) := by
    funext j
    show y ((s (u.succAbove j)).castPred (ne j)) = Fin.lastCases v y (s (u.succAbove j))
    conv_rhs => rw [← Fin.castSucc_castPred (s (u.succAbove j)) (ne j)]
    rw [Fin.lastCases_castSucc]
  rw [evalF, key]
  exact evalE x hx
