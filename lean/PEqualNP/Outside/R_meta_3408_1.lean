import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3408_1
    (short : ∀ (pins : List (Fin 11)) (P D : Circuit), pins.length ≤ 1 →
      Monotone2 P → FanInTwo D → P.size + D.size ≤ 12 → P.output ≤ 24 → D.output ≤ 24 →
      (∀ g ∈ P.gates ++ D.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 || x 4]
        let v := P.wires (w ++ [GateOp.and.eval (pins.map fun i => w.getD i.val false)])
        D.eval (v ++ [!(v.getD P.output false)]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (pair : ∀ (a b : Fin 10) (P D : Circuit), a < b →
      Monotone2 P → FanInTwo D → P.size + D.size ≤ 12 → P.output ≤ 24 → D.output ≤ 24 →
      (∀ g ∈ P.gates ++ D.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 || x 4]
        let v := P.wires (w ++ [w.getD a.val false && w.getD b.val false])
        D.eval (v ++ [!(v.getD P.output false)]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    : ∀ (x1 : List (Fin (11 : ℕ))) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x2 →       PEqualNP.MetaComplexity.FanInTwo x3 →         x2.size + x3.size ≤ (12 : ℕ) →           x2.output ≤ (24 : ℕ) →             x3.output ≤ (24 : ℕ) →               (∀ x10 ∈ x2.gates ++ x3.gates, ∀ x12 ∈ x10.inputs, x12 ≤ (24 : ℕ)) →                 ∃ (x11 : Fin (9 : ℕ) → Bool),                   have x12 : List Bool := List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))];                   have x13 : List Bool := x2.wires (x12 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x13 : Fin (11 : ℕ)) => x12.getD (↑x13) Bool.false) x1)]);                   x3.eval (x13 ++ [!x13.getD x2.output Bool.false]) ≠ (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ))) := by
  intro x1 x2 x3 hlen hm hf hs ho2 ho3 hb
  have hd : ∀ x : Fin 9 → Bool, (List.ofFn x ++ [x 0 || x 4]).getD 10 false = false :=
    fun x => List.getD_eq_default _ _ (by simp)
  have eAnd : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  rcases x1 with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exact short [] x2 x3 (by simp) hm hf hs ho2 ho3 hb
  · exact short [a] x2 x3 (by simp) hm hf hs ho2 ho3 hb
  ·
    by_cases h10 : a.val = 10 ∨ b.val = 10
    · obtain ⟨x, hx⟩ := short [10] x2 x3 (by simp) hm hf hs ho2 ho3 hb
      refine ⟨x, ?_⟩
      dsimp only at hx ⊢
      have e : GateOp.and.eval (List.map (fun i : Fin 11 => (List.ofFn x ++ [x 0 || x 4]).getD i.val false) [a, b]) =
          GateOp.and.eval (List.map (fun i : Fin 11 => (List.ofFn x ++ [x 0 || x 4]).getD i.val false) [10]) := by
        have h := hd x
        rcases h10 with h1 | h1
        · simp only [List.map_cons, List.map_nil, eAnd, List.all_cons, List.all_nil, h1, h]
          simp
        · simp only [List.map_cons, List.map_nil, eAnd, List.all_cons, List.all_nil, h1, h]
          simp
      rw [e]
      exact hx
    · by_cases hab : a = b
      · obtain ⟨x, hx⟩ := short [a] x2 x3 (by simp) hm hf hs ho2 ho3 hb
        refine ⟨x, ?_⟩
        dsimp only at hx ⊢
        have e : GateOp.and.eval (List.map (fun i : Fin 11 => (List.ofFn x ++ [x 0 || x 4]).getD i.val false) [a, b]) =
            GateOp.and.eval (List.map (fun i : Fin 11 => (List.ofFn x ++ [x 0 || x 4]).getD i.val false) [a]) := by
          subst hab
          simp [eAnd]
        rw [e]
        exact hx
      · have ha : a.val < 10 := by omega
        have hb' : b.val < 10 := by omega
        have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
        have e : ∀ x : Fin 9 → Bool, GateOp.and.eval (List.map (fun i : Fin 11 => (List.ofFn x ++ [x 0 || x 4]).getD i.val false) [a, b]) =
            ((List.ofFn x ++ [x 0 || x 4]).getD a.val false && (List.ofFn x ++ [x 0 || x 4]).getD b.val false) := by
          intro x
          simp [eAnd]
        by_cases hlt : a.val < b.val
        · obtain ⟨x, hx⟩ := pair ⟨a.val, ha⟩ ⟨b.val, hb'⟩ x2 x3 hlt hm hf hs ho2 ho3 hb
          refine ⟨x, ?_⟩
          dsimp only at hx ⊢
          rw [e]
          exact hx
        · obtain ⟨x, hx⟩ := pair ⟨b.val, hb'⟩ ⟨a.val, ha⟩ x2 x3 (show b.val < a.val by omega) hm hf hs ho2 ho3 hb
          refine ⟨x, ?_⟩
          dsimp only at hx ⊢
          rw [e, Bool.and_comm]
          exact hx
  · exact absurd hlen (by simp)
