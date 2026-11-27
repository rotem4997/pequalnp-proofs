import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2301_1
    (hsmall : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
      (∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 2 && y 6 || y 3 && y 7 || y 5 && y 6 || y 7 && y 5)) → 13 ≤ D.size)
    (hrestrict : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      let plug := fun (y : Fin 8 → Bool) (b : Bool) (i : Fin 9) => if i.val = 6 then b else y (Fin.ofNat 8 (if i.val < 6 then i.val else i.val - 1))
      let f := fun (y : Fin 8 → Bool) (b : Bool) => C.eval (List.ofFn (plug y b) ++ [y 0])
      (∃ y, f y true ≠ f y false) → (∃ y z, f y false ≠ f z false) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
        D.size + 1 ≤ C.size ∧ ∀ y, D.eval (List.ofFn y) = f y false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x3 (0 : Fin (9 : ℕ)) = Bool.true ∨ x3 (6 : Fin (9 : ℕ)) = Bool.false → x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C hfan hcorrect
  let plug := fun (y : Fin 8 → Bool) (b : Bool) (i : Fin 9) => if i.val = 6 then b else y (Fin.ofNat 8 (if i.val < 6 then i.val else i.val - 1))
  let f := fun (y : Fin 8 → Bool) (b : Bool) => C.eval (List.ofFn (plug y b) ++ [y 0])
  let target := fun (x : Fin 9 → Bool) => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  have calcOn (y : Fin 8 → Bool) (b : Bool) (hp : y 0 = true ∨ b = false) : f y b = target (plug y b) := by
    have hz : plug y b 0 = y 0 := rfl
    have hb : plug y b 6 = b := rfl
    exact (show C.eval (List.ofFn (plug y b) ++ [y 0]) = _ by
      rw [← hz]
      exact hcorrect _ (by simpa only [hz, hb] using hp))
  let a : Fin 8 → Bool := fun i => decide (i = 0 ∨ i = 7)
  let b : Fin 8 → Bool := fun i => decide (i = 0 ∨ i = 1)
  let z : Fin 8 → Bool := fun _ => false
  have hdep : f a true ≠ f a false := by
    rw [calcOn a true (Or.inl rfl), calcOn a false (Or.inr rfl)]
    change true ≠ false
    decide
  have hnon : f b false ≠ f z false := by
    rw [calcOn b false (Or.inr rfl), calcOn z false (Or.inr rfl)]
    change true ≠ false
    decide
  obtain ⟨D, hD, hlt, hval⟩ := hrestrict C hfan ⟨a, hdep⟩ ⟨b, z, hnon⟩
  have hs := hsmall D hD (by
    intro y
    rw [hval]
    change f y false = _
    rw [calcOn y false (Or.inr rfl)]
    simp [target, plug, Fin.ofNat])
  omega
