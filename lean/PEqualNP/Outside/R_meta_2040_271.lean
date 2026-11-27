import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2040_271
    (cofactor : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (normalize :
      let reads := fun g : Gate =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any
          (fun i => i == 4 || i == 9)
      let input := fun (b : Bool) (x : Fin 8 → Bool) =>
        [x 0, x 1, x 2, x 3, b, x 4, x 5, x 6, x 7, !b]
      ∀ D : Circuit, FanInTwo D → D.gates.countP reads ≤ 1 →
        D.eval (input false (fun _ => false)) = false →
        D.eval (input false (fun _ => true)) = true →
        (∃ x, D.eval (input false x) ≠ D.eval (input true x)) →
        (∃ R : Circuit, FanInTwo R ∧ R.size + 2 ≤ D.size ∧
          ∀ x : Fin 8 → Bool, R.eval (List.ofFn x) = D.eval (input false x)) ∨
        ∃ (p t : Circuit) (i : ℕ) (d : Bool),
          FanInTwo p ∧ FanInTwo t ∧ p.size + t.size + 1 ≤ D.size ∧
            i < 8 + p.size ∧
            ∀ (x : Fin 8 → Bool) (b : Bool),
              let w := p.wires (List.ofFn x)
              t.eval (w ++ [if b then d else w.getD i false]) = D.eval (input b x))
    (exclude :
      let lo := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
      ∀ (p t : Circuit) (i : ℕ) (d : Bool), FanInTwo p → FanInTwo t →
        p.size + t.size ≤ 13 → 8 ≤ i → i < 8 + p.size →
        let w := fun x : Fin 8 → Bool => p.wires (List.ofFn x)
        let u := fun x : Fin 8 → Bool => (w x).getD i false
        (∀ x, lo x = false → (x 0 || x 3) = true → u x = !d) →
        (∀ x, t.eval (w x ++ [u x]) = lo x) →
        ∃ x, t.eval (w x ++ [d]) ≠ (lo x || x 0 || x 3)) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => x2 == (4 : ℕ) || x2 == (9 : ℕ); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (0 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x2, x3 (4 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (6 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), !x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∀ (x8 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x8) = x3 x8) → ∃ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x9) ≠ (x3 x9 || x9 (0 : Fin (8 : ℕ)) || x9 (3 : Fin (8 : ℕ))) := by
  let lo := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let input := fun (b : Bool) (x : Fin 8 → Bool) =>
    [x 0, x 1, x 2, x 3, b, x 4, x 5, x 6, x 7, !b]
  dsimp only
  intro D fan size readers low
  by_contra! high
  change ∀ x, D.eval (input false x) = lo x at low
  change ∀ x, D.eval (input true x) = (lo x || x 0 || x 3) at high
  have witnesses (j : Fin 8) (d : Bool) :
      ∃ x : Fin 8 → Bool, lo x = false ∧ (x 0 || x 3) = true ∧ x j = d := by
    dsimp [lo]
    fin_cases j <;> cases d <;> decide +kernel
  have diff : ∃ x, D.eval (input false x) ≠ D.eval (input true x) := by
    obtain ⟨x, a, b, _⟩ := witnesses 0 true
    refine ⟨x, ?_⟩
    rw [low, high, a, Bool.false_or, b]
    decide
  have zero : D.eval (input false (fun _ => false)) = false := by
    simpa [lo] using low (fun _ => false)
  have one : D.eval (input false (fun _ => true)) = true := by
    simpa [lo] using low (fun _ => true)
  rcases normalize D fan readers zero one diff with restricted | split
  · obtain ⟨R, fr, sz, same⟩ := restricted
    exact cofactor ⟨R, fr, by omega, fun x => (same x).trans (low x)⟩
  obtain ⟨p, t, i, d, fp, ft, bound, valid, sim⟩ := split
  let w := fun x : Fin 8 → Bool => p.wires (List.ofFn x)
  let u := fun x : Fin 8 → Bool => (w x).getD i false
  have a (x : Fin 8 → Bool) : t.eval (w x ++ [u x]) = lo x :=
    (sim x false).trans (low x)
  have b (x : Fin 8 → Bool) : t.eval (w x ++ [d]) = (lo x || x 0 || x 3) :=
    (sim x true).trans (high x)
  have sensitive (x : Fin 8 → Bool) (hx : lo x = false) (hz : (x 0 || x 3) = true) :
      u x = !d := by
    have clash : u x ≠ d := by
      intro e
      have eq := a x
      rw [e, b, hx, Bool.false_or, hz] at eq
      contradiction
    cases d <;> cases e : u x <;> first | rfl | exact (clash e).elim
  have generated : 8 ≤ i := by
    by_contra! short
    let j : Fin 8 := ⟨i, short⟩
    obtain ⟨x, hx, hz, bit⟩ := witnesses j d
    have keep (gs : List Gate) (ys : List Bool) (h : i < ys.length) :
        (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)])
          ys).getD i false = ys.getD i false := by
      induction gs generalizing ys with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp; omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    have value : u x = x j := by
      change (p.gates.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)])
        (List.ofFn x)).getD i false = x j
      have lt : i < (List.ofFn x).length := by simpa only [List.length_ofFn] using short
      rw [keep _ _ lt, List.getD_eq_getElem _ _ lt, List.getElem_ofFn]
    have h := sensitive x hx hz
    rw [value, bit] at h
    cases d <;> contradiction
  obtain ⟨x, bad⟩ := exclude p t i d fp ft (by omega) generated valid sensitive a
  exact bad (b x)
