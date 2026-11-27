import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3136_39
    (h1 : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), gs.length = 13 → PEqualNP.MetaComplexity.FanInTwo { gates := gs, output := 0 } → gs.countP (fun z => z.op.eval [false]) ≤ 1 → ∀ a b : Nat,
      let w := fun (x : Fin 9 → Bool) (i : Nat) => (({ gates := gs, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
      let f := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
      (∀ x, (w x a && w x b) = f x) → ((a = 22 ∧ 10 ≤ b ∧ b < 22) ∨ (b = 22 ∧ 10 ≤ a ∧ a < 22)) ∧
      (∀ j ∈ [a,b], (gs.getD (j-10) ⟨.or,[]⟩).op ≠ .not))
    (h2 : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), gs.length = 13 → PEqualNP.MetaComplexity.FanInTwo { gates := gs, output := 0 } → ∀ j : Nat,
      let w := fun (x : Fin 9 → Bool) (i : Nat) => (({ gates := gs, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
      let f := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
      (∀ x, f x = true → w x j = true) → (∃ y, w y j = false) → 12 ≤ j)
    (h3 : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), gs.length = 13 → PEqualNP.MetaComplexity.FanInTwo { gates := gs, output := 0 } → ∀ a b : Nat,
      let w := fun (x : Fin 9 → Bool) (i : Nat) => (({ gates := gs, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
      let f := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
      (∀ x, (w x a && w x b) = f x) → ∃ x, w x a = true ∧ w x b = false)
    (h4 : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), gs.length = 13 → PEqualNP.MetaComplexity.FanInTwo { gates := gs, output := 0 } → gs.countP (fun g => g.op.eval [false]) ≤ 1 → ∀ r : Nat, 12 ≤ r → r < 22 →
      let w := fun (x : Fin 9 → Bool) (i : Nat) => (({ gates := gs, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
      let f := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
      (∀ j ∈ ([r,22] : List Nat), (gs.getD (j-10) ⟨.or,[]⟩).op ≠ .not) →
      (∃ x, w x r = true ∧ w x 22 = false) → (∃ y, w y r = false ∧ w y 22 = true) →
      ∃ x, (w x r && w x 22) ≠ f x) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             ∃ (x9 : Fin (9 : ℕ) → Bool),               have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ))]);               (x10.getD x2 Bool.false && x10.getD x3 Bool.false) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro gs a b hs hf cnt _ _
  let w := fun (x : Fin 9 → Bool) (i : Nat) => (({ gates := gs, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
  let f := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  by_contra! h
  have good (x : Fin 9 → Bool) : (w x a && w x b) = f x := by
    simpa only [w,f,not_ne_iff] using h x
  obtain ⟨positions,safe⟩ := h1 gs hs hf cnt a b good
  have finish (j : Nat) (lo : 10 ≤ j) (hi : j < 22) (ev : ∀ x, (w x j && w x 22) = f x)
      (noNot : ∀ k ∈ [j,22], (gs.getD (k-10) ⟨.or,[]⟩).op ≠ .not) : False := by
    obtain ⟨x,p,q⟩ := h3 gs hs hf j 22 ev
    obtain ⟨y,p',q'⟩ := h3 gs hs hf 22 j (fun z => (Bool.and_comm _ _).trans (ev z))
    have enough := h2 gs hs hf j (fun z hit => by have t := (ev z).trans hit; rw [Bool.and_eq_true] at t; exact t.1) ⟨y,q'⟩
    obtain ⟨z,no⟩ := h4 gs hs hf cnt j enough hi noNot ⟨x,p,q⟩ ⟨y,q',p'⟩
    exact no (ev z)
  rcases positions with ⟨rfl,lo,hi⟩ | ⟨rfl,lo,hi⟩
  · apply finish b lo hi (fun x => (Bool.and_comm _ _).trans (good x))
    intro j hj
    exact safe j (by simpa [or_comm] using hj)
  · exact finish a lo hi good safe
