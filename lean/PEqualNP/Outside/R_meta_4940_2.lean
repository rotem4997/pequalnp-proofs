import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4940_2
    (hElim : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : Finset ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ x6 ∈ x4, ∃ (x8 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x8 ∧ ↑x3 ∈ x8.inputs ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.not → x8.inputs.head? = Option.some ↑x3)) → (∃ (x7 : Bool), ∀ (x8 : Fin x1 → Bool), x8 x3 = Bool.false → x2.eval (List.ofFn x8) = x7) ∨ ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size + x4.card ≤ x2.size ∧ ∀ (x8 : Fin x1 → Bool), x8 x3 = Bool.false → x7.eval (List.ofFn x8) = x2.eval (List.ofFn x8))
    (hSmall : ∀ (x1 : Fin (10 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Bool), PEqualNP.MetaComplexity.FanInTwo x2 → (x2.size + if x3 = Bool.true then (1 : ℕ) else (0 : ℕ)) ≤ (15 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x6 x1 = Bool.false ∧ (if x3 = Bool.true then !x2.eval (List.ofFn x6) else x2.eval (List.ofFn x6)) ≠ (x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))))
    (hLowDeg : ∀ (D : Circuit) (a b : ℕ), FanInTwo D → D.size = 18 →
      (∀ (v : Fin 10) (S : Finset ℕ),
        (∀ j ∈ S, ∃ g : Gate, (D.gates ++ [⟨GateOp.or, [a, b]⟩])[j]? = some g ∧
          (v : ℕ) ∈ g.inputs ∧ (g.op = GateOp.not → g.inputs.head? = some (v : ℕ))) →
        S.card ≤ 3) →
      ∃ x : Fin 10 → Bool,
        ((D.wires (List.ofFn x)).getD a false || (D.wires (List.ofFn x)).getD b false) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size = (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  intro g tail a b fanG fanT sizeT
  let F := fun x : Fin 10 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let D : Circuit := ⟨g :: tail.gates, 0⟩
  let W := fun (x : Fin 10 → Bool) (i : ℕ) => (D.wires (List.ofFn x)).getD i false
  change (∃ x, W x a = true ∧ W x b = false) →
    (∃ x, W x a = false ∧ W x b = true) →
    (∀ x, F x = false → W x a = false ∧ W x b = false) →
    ∃ x, F x = true ∧ W x a = false ∧ W x b = false
  intro _ _ off
  have fanD : FanInTwo D := by
    intro h mem
    rcases List.mem_cons.mp mem with rfl | ht
    · exact fanG _ List.mem_cons_self
    · exact fanT _ ht
  have sizeD : D.size = 18 := by
    change (g :: tail.gates).length = 18
    change tail.gates.length = 17 at sizeT
    simp only [List.length_cons, sizeT]
  by_contra missed
  have covered (x : Fin 10 → Bool) : (W x a || W x b) = F x := by
    cases hf : F x with
    | false =>
      obtain ⟨ha, hb⟩ := off x hf
      rw [ha, hb]
      rfl
    | true =>
      cases ha : W x a <;> cases hb : W x b
      · exact False.elim (missed ⟨x, hf, ha, hb⟩)
      all_goals rfl
  let last : Gate := ⟨GateOp.or, [a, b]⟩
  let E : Circuit := ⟨D.gates ++ [last], 10 + D.size⟩
  have fanE : FanInTwo E := by
    intro h mem
    rcases List.mem_append.mp mem with hd | hl
    · exact fanD _ hd
    · have eq : h = last := List.mem_singleton.mp hl
      subst h
      exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
  have sizeE : E.size = 19 := by
    change (D.gates ++ [last]).length = 19
    change D.gates.length = 18 at sizeD
    simp only [List.length_append, List.length_singleton, sizeD]
  have lenW (gs : List Gate) (w : List Bool) :
      (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons h gs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have orEval (u v : Bool) : GateOp.or.eval [u, v] = (u || v) := by
    cases u <;> cases v <;> rfl
  have computes (x : Fin 10 → Bool) : E.eval (List.ofFn x) = F x := by
    have dl : (D.wires (List.ofFn x)).length = 10 + D.size := by
      change (D.gates.foldl _ (List.ofFn x)).length = _
      rw [lenW]
      simp only [List.length_ofFn]
      rfl
    change ((D.gates ++ [last]).foldl _ (List.ofFn x)).getD (10 + D.size) false = _
    rw [List.foldl_append]
    change ((D.wires (List.ofFn x)) ++ [GateOp.or.eval [W x a, W x b]]).getD (10 + D.size) false = _
    rw [orEval, ← dl]
    simpa using covered x
  have key : ∀ v : Fin 10, F (fun i => decide (i ≠ v)) = true := by decide
  by_cases hbig : ∃ (v : Fin 10) (S : Finset ℕ),
      (∀ j ∈ S, ∃ g : Gate, E.gates[j]? = some g ∧ (v : ℕ) ∈ g.inputs ∧
        (g.op = GateOp.not → g.inputs.head? = some (v : ℕ))) ∧
      3 < S.card
  · obtain ⟨v, S, hS, hcard⟩ := hbig
    rcases hElim 10 E v S fanE hS with ⟨c, hc⟩ | ⟨E', fanE', hsz, hagree⟩
    · cases c with
      | false =>
        have h1 := computes (fun i => decide (i ≠ v))
        rw [hc _ (by simp), key v] at h1
        exact Bool.false_ne_true h1
      | true =>
        have h0 := computes (fun _ => false)
        rw [hc _ rfl] at h0
        exact Bool.false_ne_true h0.symm
    · have hsz' : (E'.size + if false = true then (1 : ℕ) else (0 : ℕ)) ≤ (15 : ℕ) := by
        simp only [Bool.false_eq_true, ite_false]
        omega
      obtain ⟨x, hxv, hne⟩ := hSmall v E' false fanE' hsz'
      apply hne
      simpa only [Bool.false_eq_true, ite_false, hagree x hxv] using computes x
  · have hdeg : ∀ (v : Fin 10) (S : Finset ℕ),
        (∀ j ∈ S, ∃ g : Gate, (D.gates ++ [⟨GateOp.or, [a, b]⟩])[j]? = some g ∧
          (v : ℕ) ∈ g.inputs ∧ (g.op = GateOp.not → g.inputs.head? = some (v : ℕ))) →
        S.card ≤ 3 := by
      intro v S hS
      by_contra hlt
      exact hbig ⟨v, S, hS, by omega⟩
    obtain ⟨x, hx⟩ := hLowDeg D a b fanD sizeD hdeg
    exact hx (covered x)
