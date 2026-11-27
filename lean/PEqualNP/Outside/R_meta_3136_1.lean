import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3136_1
    (withoutNot : ∀ (gs : List Gate) (a b : ℕ),
      gs.length = 13 → FanInTwo ⟨gs, 0⟩ →
      gs.countP (fun g => g.op.eval [false]) = 0 →
      10 ≤ a → a ≤ b → b < 23 →
      ∃ x : Fin 9 → Bool,
        let w := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 3])
        (w.getD a false && w.getD b false) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
      x 6 && x 8 || x 8 && x 5))
    (withNot : ∀ (gs : List Gate) (a b : ℕ),
      gs.length = 13 → FanInTwo ⟨gs, 0⟩ →
      gs.countP (fun g => g.op.eval [false]) = 1 →
      10 ≤ a → a ≤ b → b < 23 →
      ∃ x : Fin 9 → Bool,
        let w := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 3])
        (w.getD a false && w.getD b false) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
      x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             ∃ (x9 : Fin (9 : ℕ) → Bool),               have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ))]);               (x10.getD x2 Bool.false && x10.getD x3 Bool.false) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro gs a b hlen hfan hnot _ _
  let target (x : Fin 9 → Bool) := (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
      x 6 && x 8 || x 8 && x 5)
  let raw (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 3]
  let wires (x : Fin 9 → Bool) := (Circuit.mk gs 0).wires (raw x)
  change ∃ x : Fin 9 → Bool, ((wires x).getD a false && (wires x).getD b false) ≠ target x
  by_contra h
  have computes (x : Fin 9 → Bool) :
      ((wires x).getD a false && (wires x).getD b false) = target x := by
    by_contra different
    exact h ⟨x, different⟩
  let step (bits : List Bool) (g : Gate) :=
    bits ++ [g.op.eval (g.inputs.map fun i => bits.getD i false)]
  have foldLength (ls : List Gate) (bits : List Bool) :
      (ls.foldl step bits).length = bits.length + ls.length := by
    induction ls generalizing bits with
    | nil => simp
    | cons g ls ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have rawLength (x : Fin 9 → Bool) : (raw x).length = 10 := by simp [raw]
  have wireLength (x : Fin 9 → Bool) : (wires x).length = 23 := by
    change (gs.foldl step (raw x)).length = 23
    rw [foldLength, rawLength, hlen]
  have prefixRead (ls : List Gate) (bits : List Bool) (i : ℕ) (hi : i < bits.length) :
      (ls.foldl step bits).getD i false = bits.getD i false := by
    induction ls generalizing bits with
    | nil => rfl
    | cons g ls ih =>
      have hstep : i < (step bits g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ih _ hstep]
      exact List.getD_append _ _ _ _ hi
  let leftEdge (i : Fin 9) : Bool := decide (i = 1 ∨ i = 2)
  let rightEdge (i : Fin 9) : Bool := decide (i = 5 ∨ i = 7)
  have leftTrue : target leftEdge = true := by decide +kernel
  have rightTrue : target rightEdge = true := by decide +kernel
  have rawFalse : ∀ i : Fin 10,
      (raw leftEdge).getD i.val false = false ∨ (raw rightEdge).getD i.val false = false := by
    decide +kernel
  have tapTrue (t : ℕ) (ht : t = a ∨ t = b) (x : Fin 9 → Bool) (hx : target x = true) :
      (wires x).getD t false = true := by
    have both := Bool.and_eq_true_iff.mp ((computes x).trans hx)
    rcases ht with rfl | rfl
    · exact both.1
    · exact both.2
  have tapLt (t : ℕ) (ht : t = a ∨ t = b) : t < 23 := by
    by_contra! hOut
    have hTrue := tapTrue t ht leftEdge leftTrue
    have past : (wires leftEdge).length ≤ t := by rwa [wireLength]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none past] at hTrue
    contradiction
  have tapGe (t : ℕ) (ht : t = a ∨ t = b) : 10 ≤ t := by
    by_contra! hIn
    have never (x : Fin 9 → Bool) (hx : target x = true)
        (no : (raw x).getD t false = false) : False := by
      have hTrue := tapTrue t ht x hx
      change (gs.foldl step (raw x)).getD t false = true at hTrue
      rw [prefixRead _ _ _ (by rwa [rawLength]), no] at hTrue
      contradiction
    rcases rawFalse ⟨t, hIn⟩ with no | no
    · exact never leftEdge leftTrue no
    · exact never rightEdge rightTrue no
  have impossible (t u : ℕ) (lo : 10 ≤ t) (order : t ≤ u) (hi : u < 23)
      (ok : ∀ x, ((wires x).getD t false && (wires x).getD u false) = target x) : False := by
    by_cases zero : gs.countP (fun g => g.op.eval [false]) = 0
    · obtain ⟨x, hx⟩ := withoutNot gs t u hlen hfan zero lo order hi
      exact hx (ok x)
    · have one : gs.countP (fun g => g.op.eval [false]) = 1 := by omega
      obtain ⟨x, hx⟩ := withNot gs t u hlen hfan one lo order hi
      exact hx (ok x)
  by_cases order : a ≤ b
  · exact impossible a b (tapGe a (Or.inl rfl)) order (tapLt b (Or.inr rfl)) computes
  · exact impossible b a (tapGe b (Or.inr rfl)) (by omega) (tapLt a (Or.inl rfl))
      (fun x => by simpa only [Bool.and_comm] using computes x)
