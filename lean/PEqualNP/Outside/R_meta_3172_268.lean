import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A cut of step L-meta-3172 by the second gate, up to symmetry.
-- The graph has one symmetry that fixes vertex 0: it swaps 1 with 5, 2 with 8 and 6 with 7.
-- Renaming the input wires of a circuit by it, and using that OR does not depend on the
-- order of its two inputs, every second gate of the step is one of the 4 below.
theorem PEqualNP.Outside.R_meta_3172_268
    (h22 : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
      C.eval ((List.ofFn x ++ [!x 0]) ++ [GateOp.or.eval (List.map (fun i : ℕ => (List.ofFn x ++ [!x 0]).getD i false) [2, 2])]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (h33 : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
      C.eval ((List.ofFn x ++ [!x 0]) ++ [GateOp.or.eval (List.map (fun i : ℕ => (List.ofFn x ++ [!x 0]).getD i false) [3, 3])]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (h23 : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
      C.eval ((List.ofFn x ++ [!x 0]) ++ [GateOp.or.eval (List.map (fun i : ℕ => (List.ofFn x ++ [!x 0]).getD i false) [2, 3])]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (h28 : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
      C.eval ((List.ofFn x ++ [!x 0]) ++ [GateOp.or.eval (List.map (fun i : ℕ => (List.ofFn x ++ [!x 0]).getD i false) [2, 8])]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    :
  ∀ (x1 : List ℕ), x1.length = (2 : ℕ) → (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) → (∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → x5.size ≤ (13 : ℕ) → ∃ (x8 : Fin (9 : ℕ) → Bool), have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))]; x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  classical
  let rho : ℕ → ℕ := fun i => ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ).getD i i
  let adv : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let ren : Gate → Gate := fun g => ⟨g.op, g.inputs.map rho⟩
  let W : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [!x 0]
  let F : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  let S : List ℕ → Prop := fun l =>
    ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
      C.eval (W x ++ [GateOp.or.eval (List.map (fun i : ℕ => (W x).getD i false) l)]) ≠ F x
  -- facts on the renaming of wire indices
  have rho_lt : ∀ i, i < 9 → rho i < 9 := by
    intro i hi
    interval_cases i <;> decide
  have rho_ge : ∀ i, 9 ≤ i → rho i = i := by
    intro i hi
    show ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ).getD i i = i
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hi)]
    rfl
  have rho_rho : ∀ i, rho (rho i) = i := by
    intro i
    rcases Nat.lt_or_ge i 9 with hi | hi
    · interval_cases i <;> rfl
    · rw [rho_ge i hi, rho_ge i hi]
  have getD_snoc : ∀ (w : List Bool) (v : Bool) (i : ℕ),
      (w ++ [v]).getD i false = if i < w.length then w.getD i false else if i = w.length then v else false := by
    intro w v i
    simp only [List.getD_eq_getElem?_getD]
    split_ifs with h1 h2
    · rw [List.getElem?_append_left h1]
    · subst h2
      simp
    · rw [List.getElem?_eq_none (by simp; omega)]
      rfl
  -- renaming the wires of a whole gate list
  have key : ∀ (gs : List Gate) (w w' : List Bool), w'.length = w.length → 9 ≤ w.length →
      (∀ i, w'.getD i false = w.getD (rho i) false) →
      ∀ i, ((gs.map ren).foldl adv w').getD i false = (gs.foldl adv w).getD (rho i) false := by
    intro gs
    induction gs with
    | nil =>
      intro w w' _ _ h
      exact h
    | cons g gs ih =>
      intro w w' hl h9 h
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hv : (ren g).op.eval ((ren g).inputs.map fun j => w'.getD j false) =
          g.op.eval (g.inputs.map fun j => w.getD j false) := by
        show g.op.eval ((g.inputs.map rho).map fun j => w'.getD j false) = _
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        show w'.getD (rho j) false = w.getD j false
        rw [h, rho_rho]
      apply ih
      · show (w' ++ [_]).length = (w ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil, hl]
      · show 9 ≤ (w ++ [_]).length
        rw [List.length_append]
        omega
      · intro i
        show (w' ++ [(ren g).op.eval ((ren g).inputs.map fun j => w'.getD j false)]).getD i false =
          (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).getD (rho i) false
        rw [hv, getD_snoc, getD_snoc, hl]
        rcases Nat.lt_or_ge i 9 with hi | hi
        · have h1 : i < w.length := by omega
          have h2 : rho i < w.length := by
            have := rho_lt i hi
            omega
          rw [ite_eq_left h1, ite_eq_left h2]
          exact h i
        · rw [rho_ge i hi]
          split_ifs
          · rw [h i, rho_ge i hi]
          · rfl
          · rfl
  -- the function of the graph does not see the symmetry
  have Fsym : ∀ x : Fin 9 → Bool, F (fun i => (List.ofFn x).getD (rho i) false) = F x := by
    intro x
    show ((x 0 && x 5 || x 5 && x 8 || x 8 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 1 ||
      x 5 && x 7 || x 8 && x 6 || x 3 && x 2 || x 1 && x 6 || x 7 && x 2 || x 2 && x 1) : Bool) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
    generalize x 0 = b0
    generalize x 1 = b1
    generalize x 2 = b2
    generalize x 3 = b3
    generalize x 4 = b4
    generalize x 5 = b5
    generalize x 6 = b6
    generalize x 7 = b7
    generalize x 8 = b8
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8
    decide
  -- the first ten wires, before and after the symmetry
  have Wsym : ∀ (x : Fin 9 → Bool) (i : ℕ),
      (W x).getD i false = (W (fun i => (List.ofFn x).getD (rho i) false)).getD (rho i) false := by
    intro x i
    rcases Nat.lt_or_ge i 10 with hi | hi
    · interval_cases i <;> rfl
    · rw [rho_ge i (by omega)]
      show (List.ofFn x ++ [!x 0]).getD i false = (List.ofFn _ ++ [_]).getD i false
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  -- the order of the two inputs of the second gate does not matter
  have comm : ∀ a b : ℕ, S [a, b] → S [b, a] := by
    intro a b h C hF hs
    obtain ⟨x, hx⟩ := h C hF hs
    refine ⟨x, ?_⟩
    have e : GateOp.or.eval (List.map (fun i : ℕ => (W x).getD i false) [b, a]) =
        GateOp.or.eval (List.map (fun i : ℕ => (W x).getD i false) [a, b]) := by
      show (((W x).getD b false || ((W x).getD a false || false)) : Bool) =
        ((W x).getD a false || ((W x).getD b false || false))
      rw [Bool.or_false, Bool.or_false, Bool.or_comm]
    rw [e]
    exact hx
  -- the symmetry carries a second gate to its image
  have sym : ∀ a b : ℕ, S [a, b] → S [rho a, rho b] := by
    intro a b h C hF hs
    have hF' : FanInTwo ⟨C.gates.map ren, rho C.output⟩ := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      refine ⟨(hF g0 hg0).1, ?_⟩
      show (g0.inputs.map rho).length ≤ 2
      rw [List.length_map]
      exact (hF g0 hg0).2
    have hs' : (⟨C.gates.map ren, rho C.output⟩ : Circuit).size ≤ 13 := by
      show (C.gates.map ren).length ≤ 13
      rw [List.length_map]
      exact hs
    obtain ⟨x, hx⟩ := h ⟨C.gates.map ren, rho C.output⟩ hF' hs'
    refine ⟨fun i => (List.ofFn x).getD (rho i) false, ?_⟩
    rw [Fsym x]
    have hw : ∀ i, (W x ++ [GateOp.or.eval (List.map (fun i : ℕ => (W x).getD i false) [a, b])]).getD i false =
        (W (fun i => (List.ofFn x).getD (rho i) false) ++
          [GateOp.or.eval (List.map (fun i : ℕ => (W (fun i => (List.ofFn x).getD (rho i) false)).getD i false)
            [rho a, rho b])]).getD (rho i) false := by
      intro i
      have e : GateOp.or.eval (List.map (fun i : ℕ => (W (fun i => (List.ofFn x).getD (rho i) false)).getD i false)
            [rho a, rho b]) = GateOp.or.eval (List.map (fun i : ℕ => (W x).getD i false) [a, b]) := by
        show GateOp.or.eval [(W _).getD (rho a) false, (W _).getD (rho b) false] =
          GateOp.or.eval [(W x).getD a false, (W x).getD b false]
        rw [← Wsym x a, ← Wsym x b]
      rw [e]
      generalize GateOp.or.eval (List.map (fun i : ℕ => (W x).getD i false) [a, b]) = v
      have l1 : (W x).length = 10 := by simp [W]
      have l2 : (W (fun i => (List.ofFn x).getD (rho i) false)).length = 10 := by simp [W]
      have A := getD_snoc (W x) v i
      have B := getD_snoc (W (fun i => (List.ofFn x).getD (rho i) false)) v (rho i)
      rw [l1] at A
      rw [l2] at B
      rw [A, B]
      rcases Nat.lt_or_ge i 9 with hi | hi
      · have h2 := rho_lt i hi
        rw [ite_eq_left (by omega : i < 10), ite_eq_left (by omega : rho i < 10)]
        exact Wsym x i
      · rw [rho_ge i hi]
        have h3 := Wsym x i
        rw [rho_ge i hi] at h3
        rw [h3]
    have hk := key C.gates _ _ (by simp [W]) (by simp [W]) hw (rho C.output)
    rw [rho_rho] at hk
    intro hc
    apply hx
    show ((C.gates.map ren).foldl adv _).getD (rho C.output) false = F x
    rw [hk]
    exact hc
  -- every second gate of the step
  intro x1 hlen _ hmem C hF hs
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have ha := hmem a (by simp)
  have hb := hmem b (by simp)
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact h22 C hF hs
  · exact h23 C hF hs
  · exact h28 C hF hs
  · exact comm 2 3 h23 C hF hs
  · exact h33 C hF hs
  · exact sym 3 2 (comm 2 3 h23) C hF hs
  · exact comm 2 8 h28 C hF hs
  · exact sym 2 3 h23 C hF hs
  · exact sym 2 2 h22 C hF hs
