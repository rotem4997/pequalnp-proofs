import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2373_71
    (hzero : ∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo E →
      E.size ≤ 15 → ∃ x : Fin 9 → Bool, E.eval (List.ofFn x) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (hone : ∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo E →
      E.size ≤ 10 → ∃ x : Fin 9 → Bool, E.eval (List.ofFn x) ≠ (x 4 || x 6 || x 7 || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 5) || (x 3 && x 8) || (x 8 && x 5)))
    (hrestrict :
      let G := (fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))))
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 18 →
        let W := fun (x : Fin 10 → Bool) (i : ℕ) => (D.wires (List.ofFn x)).getD i false
        let U := fun x => W x a || W x b
        (∃ x, W x a = true ∧ W x b = false) →
        (∃ x, W x a = false ∧ W x b = true) →
        (∀ x, G x = false ∨ (List.ofFn x).count true ≤ 2 → U x = G x) →
        ∃ (s : Equiv.Perm (Fin 10)) (v : Bool) (E : PEqualNP.CircuitLowerBounds.Circuit),
          (∀ x : Fin 10 → Bool, G (x ∘ s) = G x) ∧
          PEqualNP.MetaComplexity.FanInTwo E ∧ E.size ≤ (if v then 10 else 15) ∧
          ∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = U ((Fin.lastCases v y : Fin 10 → Bool) ∘ s)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  intro g C a b hg hC size
  let F := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let G := (fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))))
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨g :: C.gates, 0⟩
  let W := fun (x : Fin 10 → Bool) (i : ℕ) => (D.wires (List.ofFn x)).getD i false
  let U := fun x => W x a || W x b
  change (∃ x, W x a = true ∧ W x b = false) → (∃ x, W x a = false ∧ W x b = true) →
    (∀ x, F x = false → W x a = false ∧ W x b = false) →
    ∃ x, F x = true ∧ W x a = false ∧ W x b = false
  intro ha hb off
  have same (x : Fin 10 → Bool) : G x = F x := by
    change (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || (false)))))) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
    simp only [Bool.or_false]
    ac_rfl
  have legal : PEqualNP.MetaComplexity.FanInTwo D := by
    intro gate mem
    rcases List.mem_cons.mp mem with rfl | tail
    · exact hg _ List.mem_cons_self
    · exact hC _ tail
  have budget : D.size ≤ 18 := by
    change (g :: C.gates).length ≤ 18
    change C.gates.length ≤ 17 at size
    simp only [List.length_cons]
    omega
  by_contra missed
  have allRows (x : Fin 10 → Bool) : U x = G x := by
    rw [same]
    change (W x a || W x b) = F x
    cases h : F x with
    | false =>
      obtain ⟨h1,h2⟩ := off x h
      rw [h1,h2]
      rfl
    | true =>
      cases h1 : W x a <;> cases h2 : W x b
      · exact False.elim (missed ⟨x,h,h1,h2⟩)
      all_goals rfl
  obtain ⟨s, v, E, auto, leE, cost, sim⟩ :=
    hrestrict D a b legal budget ha hb (fun x _ => allRows x)
  have restricted (y : Fin 9 → Bool) : E.eval (List.ofFn y) = F (Fin.lastCases v y) := by
    exact (sim y).trans ((allRows _).trans ((auto _).trans (same _)))
  cases v with
  | false =>
    obtain ⟨x,hx⟩ := hzero E leE cost
    apply hx
    rw [restricted]
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && false) || (x 5 && x 7) || (x 7 && false) || (false && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    simp only [Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or]
  | true =>
    obtain ⟨x,hx⟩ := hone E leE cost
    apply hx
    rw [restricted]
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && true) || (x 5 && x 7) || (x 7 && true) || (true && x 6) || (x 6 && x 8) || (x 8 && x 5)) = (x 4 || x 6 || x 7 || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 5) || (x 3 && x 8) || (x 8 && x 5))
    cases h4 : x 4 <;> cases h6 : x 6 <;> cases h7 : x 7 <;> simp <;> ac_rfl
