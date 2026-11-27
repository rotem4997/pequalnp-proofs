import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_1666_3
    (small : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (normalize :
      ∀ (C : Circuit) (lo hi : (Fin 8 → Bool) → Bool), FanInTwo C → C.size ≤ 15 →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) →
      (∀ (x : Fin 8 → Bool) (b : Bool),
        C.eval ((List.ofFn x).insertIdx 4 b) = if b then hi x else lo x) →
      lo ≠ hi → HasCircuitSize 8 lo 12 ∨
        ∃ (p t : Circuit) (i : ℕ) (d : Bool),
          FanInTwo p ∧ FanInTwo t ∧ p.size + t.size ≤ 13 ∧ i < 8 + p.size ∧
          ∀ (x : Fin 8 → Bool) (b : Bool),
            let w := p.wires (List.ofFn x)
            t.eval (w ++ [if b then d else w.getD i false]) = if b then hi x else lo x)
    (exclude :
      let lo := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
      let hi := fun x : Fin 8 → Bool => lo x || x 0 || x 3
      ∀ (p t : Circuit) (i : ℕ) (d : Bool), FanInTwo p → FanInTwo t →
        p.size + t.size ≤ 13 → i < 8 + p.size →
        let w := fun x : Fin 8 → Bool => p.wires (List.ofFn x)
        let u := fun x : Fin 8 → Bool => (w x).getD i false
        (∀ j : Fin 8, u ≠ (fun x => x j) ∧ u ≠ (fun x => !(x j))) →
        (∀ x : Fin 8 → Bool, lo x ≠ hi x → u x = !d) →
        (∀ x : Fin 8 → Bool, t.eval (w x ++ [u x]) = lo x) →
        ∃ x : Fin 8 → Bool, t.eval (w x ++ [d]) ≠ hi x) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C fan first output
  by_contra! short
  let lo := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let hi := fun x : Fin 8 → Bool => lo x || x 0 || x 3
  have split (x : Fin 8 → Bool) (b : Bool) :
      C.eval ((List.ofFn x).insertIdx 4 b) = (if b then hi x else lo x) := by
    change circuitFun 9 C ![x 0,x 1,x 2,x 3,b,x 4,x 5,x 6,x 7] = _
    rw [output]
    change ((((((((((((x 0 && x 1) || (x 1 && x 2)) || (x 2 && x 3)) || (x 3 && b)) ||
      (b && x 0)) || (x 0 && x 4)) || (x 1 && x 5)) || (x 2 && x 6)) ||
      (x 3 && x 7)) || (x 4 && x 6)) || (x 5 && x 7)) || (x 7 && x 4)) = _
    cases b <;> simp [hi, lo, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  have witnesses (j : Fin 8) (d : Bool) :
      ∃ x : Fin 8 → Bool, lo x ≠ hi x ∧ x j = d := by
    dsimp [lo, hi]
    fin_cases j <;> cases d <;> decide +kernel
  have diff : lo ≠ hi := by
    obtain ⟨x, hx, _⟩ := witnesses 0 false
    exact fun e => hx (congrFun e x)
  rcases normalize C lo hi fan (by omega) first split diff with core | shape
  · exact small core
  obtain ⟨p, t, i, d, fp, ft, size, index, simulate⟩ := shape
  let u := fun x : Fin 8 → Bool => (p.wires (List.ofFn x)).getD i false
  have low (x : Fin 8 → Bool) :
      t.eval (p.wires (List.ofFn x) ++ [u x]) = lo x := simulate x false
  have high (x : Fin 8 → Bool) :
      t.eval (p.wires (List.ofFn x) ++ [d]) = hi x := simulate x true
  have sensitive (x : Fin 8 → Bool) (hx : lo x ≠ hi x) : u x = !d := by
    have clash : u x ≠ d := by
      intro e
      have eq := low x
      rw [e, high] at eq
      exact hx eq.symm
    cases h : u x <;> cases d <;> simp_all
  have nonlinear (j : Fin 8) : u ≠ (fun x => x j) ∧ u ≠ (fun x => !(x j)) := by
    constructor
    · obtain ⟨x, hx, bit⟩ := witnesses j d
      intro e
      have h := sensitive x hx
      rw [e] at h
      change x j = !d at h
      rw [bit] at h
      cases d <;> contradiction
    · obtain ⟨x, hx, bit⟩ := witnesses j (!d)
      intro e
      have h := sensitive x hx
      rw [e] at h
      change (!(x j)) = !d at h
      rw [bit] at h
      cases d <;> contradiction
  obtain ⟨x, hx⟩ := exclude p t i d fp ft size index nonlinear sensitive low
  exact hx (high x)
