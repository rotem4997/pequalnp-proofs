import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8776

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem fuelS {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) : ∀ (k : ℕ) (i : Fin C.size), (i : ℕ) < k → ∀ d e : ℕ, (i : ℕ) < d → (i : ℕ) < e → gateValFuel C U d i = gateValFuel C U e i := by
  intro k
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi d e hd he
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    have hs : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)), sideTrue U B F i (gateValFuel C U d) = sideTrue U B F i (gateValFuel C U e) := by
      intro B F
      unfold sideTrue
      congr 1
      apply propext
      refine or_congr_right (exists_congr fun j => and_congr_right fun _ => and_congr_right fun hj => ?_)
      have hj' : (j : ℕ) < (i : ℕ) := hj
      rw [ih j (by omega) d e (by omega) (by omega)]
    simp only [Nat.succ_eq_add_one, gateValFuel]
    rw [hs, hs]

theorem gv {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) && sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h : C.gateVal U i = gateValFuel C U (C.size + 1) i := fuelS C U (i + 1) i (by omega) _ _ i.isLt (by have := i.isLt; omega)
  rw [h]
  rfl


def stp (a b : Fin 6 → ℕ) (x : ℕ) (g : Fin 6) : ℕ := if x &&& a g ≠ 0 ∧ x &&& b g ≠ 0 then x ||| 2 ^ (10 + (g : ℕ)) else x

theorem andne (x y : ℕ) : x &&& y ≠ 0 ↔ ∃ t, x.testBit t = true ∧ y.testBit t = true := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Nat.exists_testBit_of_ne_zero h
    rw [Nat.testBit_and, Bool.and_eq_true] at ht
    exact ⟨t, ht⟩
  · rintro ⟨t, h1, h2⟩ h
    have : (x &&& y).testBit t = true := by rw [Nat.testBit_and, h1, h2]; rfl
    rw [h, Nat.zero_testBit] at this
    cases this

def Inv (z : ℕ) (V : Fin 6 → Bool) (k x : ℕ) : Prop := (∀ t < 10, x.testBit t = z.testBit t) ∧ ∀ j : Fin 6, x.testBit (10 + (j : ℕ)) = (decide ((j : ℕ) < k) && V j)

theorem sd (z : ℕ) (V : Fin 6 → Bool) (g : Fin 6) (x a : ℕ) (h : Inv z V g x) (ha : a < 2 ^ (10 + (g : ℕ))) :
    x &&& a ≠ 0 ↔ (∃ v : Fin 10, a.testBit v = true ∧ z.testBit v = true) ∨ ∃ j : Fin 6, j < g ∧ a.testBit (10 + (j : ℕ)) = true ∧ V j = true := by
  rw [andne]
  constructor
  · rintro ⟨t, h1, h2⟩
    have ht : t < 10 + (g : ℕ) := by
      by_contra hc
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega)))] at h2
      cases h2
    by_cases h10 : t < 10
    · exact Or.inl ⟨⟨t, h10⟩, h2, by rw [← h.1 t h10]; exact h1⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h10)
      have hj : j < 6 := by have := g.isLt; omega
      have h3 := h.2 ⟨j, hj⟩
      simp only at h3
      rw [h1] at h3
      have h3 := h3.symm
      rw [Bool.and_eq_true] at h3
      refine Or.inr ⟨⟨j, hj⟩, ?_, h2, h3.2⟩
      change j < (g : ℕ)
      omega
  · rintro (⟨v, h1, h2⟩ | ⟨j, h1, h2, h3⟩)
    · exact ⟨v, by rw [h.1 v v.isLt]; exact h2, h1⟩
    · refine ⟨10 + (j : ℕ), ?_, h2⟩
      have h1 : (j : ℕ) < (g : ℕ) := h1
      rw [h.2 j, h3, decide_eq_true h1]
      rfl

theorem stpI (z : ℕ) (V : Fin 6 → Bool) (g : Fin 6) (x : ℕ) (a b : Fin 6 → ℕ) (h : Inv z V g x) (ha : a g < 2 ^ (10 + (g : ℕ))) (hb : b g < 2 ^ (10 + (g : ℕ)))
    (hV : V g = true ↔ ((∃ v : Fin 10, (a g).testBit v = true ∧ z.testBit v = true) ∨ ∃ j : Fin 6, j < g ∧ (a g).testBit (10 + (j : ℕ)) = true ∧ V j = true) ∧
      ((∃ v : Fin 10, (b g).testBit v = true ∧ z.testBit v = true) ∨ ∃ j : Fin 6, j < g ∧ (b g).testBit (10 + (j : ℕ)) = true ∧ V j = true)) :
    Inv z V ((g : ℕ) + 1) (stp a b x g) := by
  rw [← sd z V g x _ h ha, ← sd z V g x _ h hb] at hV
  unfold stp
  split_ifs with hc
  · refine ⟨fun t ht => ?_, fun j => ?_⟩
    · rw [Nat.testBit_or, h.1 t ht, Nat.testBit_two_pow, decide_eq_false (by omega), Bool.or_false]
    · rw [Nat.testBit_or, h.2 j, Nat.testBit_two_pow]
      by_cases hj : j = g
      · subst hj
        rw [hV.2 hc]
        simp
      · have hj' : (j : ℕ) ≠ (g : ℕ) := fun e => hj (Fin.ext e)
        rw [decide_eq_false (p := 10 + (g : ℕ) = 10 + (j : ℕ)) (by omega), Bool.or_false]
        congr 1
        exact decide_eq_decide.2 (by omega)
  · refine ⟨h.1, fun j => ?_⟩
    rw [h.2 j]
    by_cases hj : j = g
    · subst hj
      have : V j = false := by
        by_contra hv
        exact hc (hV.1 (by simpa using hv))
      rw [this, Bool.and_false, Bool.and_false]
    · have hj' : (j : ℕ) ≠ (g : ℕ) := fun e => hj (Fin.ext e)
      congr 1
      exact decide_eq_decide.2 (by omega)

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8776

theorem PEqualNP.Outside.L_meta_8776 : ∀ (x1 x2 : Fin (6 : ℕ) → ℕ) (x3 : Finset (Fin (6 : ℕ))),   (∀ (x4 : Fin (6 : ℕ)), x1 x4 < (2 : ℕ) ^ ((10 : ℕ) + ↑x4) ∧ x2 x4 < (2 : ℕ) ^ ((10 : ℕ) + ↑x4)) →     have x5 : PEqualNP.AndCount.AndCountCircuit (10 : ℕ) := { size := (6 : ℕ), leftVars := fun (x5 : Fin (6 : ℕ)) => {x6 : Fin (10 : ℕ) | (x1 x5).testBit ↑x6 = Bool.true}, leftGates := fun (x5 : Fin (6 : ℕ)) => {x6 : Fin (6 : ℕ) | x6 < x5 ∧ (x1 x5).testBit ((10 : ℕ) + ↑x6) = Bool.true}, rightVars := fun (x5 : Fin (6 : ℕ)) => {x6 : Fin (10 : ℕ) | (x2 x5).testBit ↑x6 = Bool.true}, rightGates := fun (x5 : Fin (6 : ℕ)) => {x6 : Fin (6 : ℕ) | x6 < x5 ∧ (x2 x5).testBit ((10 : ℕ) + ↑x6) = Bool.true}, outVars := ∅, outGates := x3 : PEqualNP.AndCount.AndCountCircuit (10 : ℕ) };     have x6 : ℕ → ℕ := fun (x6 : ℕ) => List.foldl (fun (x7 : ℕ) (x8 : Fin (6 : ℕ)) => if x7 &&& x1 x8 ≠ (0 : ℕ) ∧ x7 &&& x2 x8 ≠ (0 : ℕ) then x7 ||| (2 : ℕ) ^ ((10 : ℕ) + ↑x8) else x7) (x6 % (1024 : ℕ)) (List.finRange (6 : ℕ));     ∀ (x7 : ℕ), x5.eval {x8 : Fin (10 : ℕ) | x7.testBit ↑x8 = Bool.true} = Decidable.decide (∃ x8 ∈ x3, (x6 x7).testBit ((10 : ℕ) + ↑x8) = Bool.true) := by
  intro a b S hab
  intro C f z
  let U : Finset (Fin 10) := {x8 : Fin 10 | z.testBit ↑x8 = true}
  let V : Fin 6 → Bool := fun j => C.gateVal U j
  have hV : ∀ g : Fin 6, V g = true ↔ ((∃ v : Fin 10, (a g).testBit v = true ∧ z.testBit v = true) ∨ ∃ j : Fin 6, j < g ∧ (a g).testBit (10 + (j : ℕ)) = true ∧ V j = true) ∧
      ((∃ v : Fin 10, (b g).testBit v = true ∧ z.testBit v = true) ∨ ∃ j : Fin 6, j < g ∧ (b g).testBit (10 + (j : ℕ)) = true ∧ V j = true) := by
    intro g
    have e := PEqualNP.Outside.L_meta_8776.gv C U g
    change V g = _ at e
    rw [e, Bool.and_eq_true]
    refine and_congr ?_ ?_
    · simp only [PEqualNP.AndCount.AndCountCircuit.sideTrue, decide_eq_true_eq]
      refine or_congr (exists_congr fun v => ?_) (exists_congr fun j => ?_)
      · simp [C, U]
      · simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h4⟩
        · rintro ⟨h1, h2, h4⟩; exact ⟨⟨h1, h2⟩, h1, h4⟩
    · simp only [PEqualNP.AndCount.AndCountCircuit.sideTrue, decide_eq_true_eq]
      refine or_congr (exists_congr fun v => ?_) (exists_congr fun j => ?_)
      · simp [C, U]
      · simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h4⟩
        · rintro ⟨h1, h2, h4⟩; exact ⟨⟨h1, h2⟩, h1, h4⟩
  have h0 : PEqualNP.Outside.L_meta_8776.Inv z V 0 (z % 1024) := by
    refine ⟨fun t ht => ?_, fun j => ?_⟩
    · rw [show (1024 : ℕ) = 2 ^ 10 by norm_num, Nat.testBit_mod_two_pow, decide_eq_true ht, Bool.true_and]
    · rw [show (1024 : ℕ) = 2 ^ 10 by norm_num, Nat.testBit_mod_two_pow, decide_eq_false (by omega), Bool.false_and]
      simp
  have st := fun g x h => PEqualNP.Outside.L_meta_8776.stpI z V g x a b h (hab g).1 (hab g).2 (hV g)
  have h6 := st 5 _ (st 4 _ (st 3 _ (st 2 _ (st 1 _ (st 0 _ h0)))))
  have ef : f z = PEqualNP.Outside.L_meta_8776.stp a b (PEqualNP.Outside.L_meta_8776.stp a b (PEqualNP.Outside.L_meta_8776.stp a b (PEqualNP.Outside.L_meta_8776.stp a b (PEqualNP.Outside.L_meta_8776.stp a b (PEqualNP.Outside.L_meta_8776.stp a b (z % 1024) 0) 1) 2) 3) 4) 5 := by
    simp only [f]
    rw [show List.finRange 6 = [0, 1, 2, 3, 4, 5] by decide]
    simp only [List.foldl_cons, List.foldl_nil]
    rfl
  have hb : ∀ j : Fin 6, (f z).testBit (10 + (j : ℕ)) = V j := by
    intro j
    rw [ef]
    refine (h6.2 j).trans ?_
    rw [decide_eq_true (by have := j.isLt; simpa using this), Bool.true_and]
  change C.eval U = _
  simp only [PEqualNP.AndCount.AndCountCircuit.eval, hb]
  simp [C, V]
