import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- Normalize the second NOT input and identify its three graph orbits.
-- The lower bounds for those fixed representatives remain hypotheses.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2917_741
    (h1 : ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!(x 0),!(x 1)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (h2 : ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!(x 0),!(x 2)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (h6 : ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!(x 0),!(x 6)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
  ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     (5 : ℕ) ≤ x1.headD (10 : ℕ) ∧ x1.headD (10 : ℕ) ≤ (8 : ℕ) →       ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 →           x4.size ≤ (13 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  let edgeF (x : Fin 9 → Bool) : Bool :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
    (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
    (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

  have ofFn_read (x : Fin 9 → Bool) (i : Fin 9) :
      (List.ofFn x).getD i.val false = x i := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt,
      ↓reduceDIte, Option.getD_some]

  have normalize_second_not (pins : List Nat)
      (hb : 5 ≤ pins.headD 10 ∧ pins.headD 10 ≤ 8) :
      ∃ i : Fin 9, 5 ≤ i.val ∧ i.val ≤ 8 ∧
        ∀ x : Fin 9 → Bool,
          GateOp.not.eval (pins.map fun j => (List.ofFn x ++ [!(x 0)]).getD j false) = !(x i) := by
    cases pins with
    | nil => simp at hb
    | cons j js =>
      have hj : j < 9 := by simpa using Nat.lt_succ_of_le hb.2
      refine ⟨⟨j,hj⟩,hb.1,hb.2,fun x => ?_⟩
      change Bool.not ((List.ofFn x ++ [!(x 0)]).getD j false) = Bool.not (x ⟨j,hj⟩)
      rw [List.getD_append _ _ _ _ (by simpa)]
      exact congrArg Bool.not (ofFn_read x ⟨j,hj⟩)

  let perm (i : Nat) : Nat :=
    if i < 9 then [0,5,8,3,4,1,7,6,2].getD i 0 else i

  have perm_small (i : Nat) (hi : i < 9) : perm i < 9 := by
    interval_cases i <;> decide

  have perm_large (i : Nat) (hi : 9 ≤ i) : perm i = i := by
    simp [perm,show ¬i<9 by omega]

  have perm_lt (i n : Nat) (hn : 9 ≤ n) : perm i < n ↔ i < n := by
    by_cases hi : i < 9
    · have hp := perm_small i hi
      omega
    · rw [perm_large i (by omega)]

  let rho : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]

  have rho_val (i : Fin 9) : (rho i).val = perm i.val := by
    fin_cases i <;> rfl

  have graph_invariant : ∀ x : Fin 9 → Bool, edgeF (fun i => x (rho i)) = edgeF x := by
    dsimp only [edgeF,rho]
    decide +kernel

  let run (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  let renameGate (g : Gate) : Gate := ⟨g.op,g.inputs.map perm⟩

  let renameCircuit (C : Circuit) : Circuit := ⟨C.gates.map renameGate,perm C.output⟩

  have append_related (x y : List Bool) (a : Bool) (hlen : x.length = y.length)
      (hn : 9 ≤ x.length) (hxy : ∀ i, x.getD i false = y.getD (perm i) false) :
      ∀ i, (x ++ [a]).getD i false = (y ++ [a]).getD (perm i) false := by
    intro i
    by_cases hi : i < x.length
    · rw [List.getD_append _ _ _ _ hi,
        List.getD_append _ _ _ _ (by rw [← hlen];exact (perm_lt i _ hn).2 hi)]
      exact hxy i
    · rw [perm_large i (by omega),List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega),hlen]

  have run_related (gs : List Gate) (x y : List Bool) (hlen : x.length = y.length)
      (hn : 9 ≤ x.length) (hxy : ∀ i, x.getD i false = y.getD (perm i) false) :
      ∀ i, (run gs x).getD i false = (run (gs.map renameGate) y).getD (perm i) false := by
    induction gs generalizing x y with
    | nil => exact hxy
    | cons g gs ih =>
      have hv : g.op.eval (g.inputs.map fun i => x.getD i false) =
          (renameGate g).op.eval ((renameGate g).inputs.map fun i => y.getD i false) := by
        simp only [renameGate,List.map_map]
        congr 1
        exact List.map_congr_left (fun i _ => hxy i)
      change ∀ i, (run gs (x ++ [_])).getD i false =
        (run (gs.map renameGate) (y ++ [_])).getD (perm i) false
      rw [← hv]
      exact ih _ _ (by simp [hlen]) (by simp;omega) (append_related x y _ hlen hn hxy)

  have prefix_related (x : Fin 9 → Bool) (a b : Bool) :
      ∀ i, (List.ofFn (fun j => x (rho j)) ++ [a,b]).getD i false =
        (List.ofFn x ++ [a,b]).getD (perm i) false := by
    intro i
    by_cases hi : i < 9
    · rw [List.getD_append _ _ _ _ (by simpa),
        List.getD_append _ _ _ _ (by simpa using perm_small i hi)]
      have h := (ofFn_read (fun j => x (rho j)) ⟨i,hi⟩).trans (ofFn_read x (rho ⟨i,hi⟩)).symm
      simpa only [rho_val] using h
    · rw [perm_large i (by omega),
        List.getD_append_right _ _ _ _ (by simp;omega),
        List.getD_append_right _ _ _ _ (by simp;omega)]
      simp

  have rename_correct (C : Circuit) (j : Fin 9) (hf : PEqualNP.MetaComplexity.FanInTwo C)
      (hc : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!(x 0),!(x j)]) = edgeF x) :
      PEqualNP.MetaComplexity.FanInTwo (renameCircuit C) ∧
        (renameCircuit C).size = C.size ∧
        ∀ x : Fin 9 → Bool,
          (renameCircuit C).eval (List.ofFn x ++ [!(x 0),!(x (rho j))]) = edgeF x := by
    refine ⟨?_,by change (C.gates.map renameGate).length = C.gates.length; simp only [List.length_map],?_⟩
    · intro g hg
      obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
      simpa [renameGate] using hf g' hg'
    · intro x
      have he := run_related C.gates
        (List.ofFn (fun j => x (rho j)) ++ [!(x 0),!(x (rho j))])
        (List.ofFn x ++ [!(x 0),!(x (rho j))]) (by simp) (by simp)
        (prefix_related x _ _) C.output
      change (run _ _).getD _ false = _
      dsimp only [renameCircuit]
      rw [← he]
      have h := hc (fun j => x (rho j))
      exact h.trans (graph_invariant x)
  intro pins _ hb C hf hs
  obtain ⟨⟨i,hi⟩,hmin,hmax,hnot⟩ := normalize_second_not pins hb
  by_contra! hcorrect
  have hc : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!(x 0),!(x ⟨i,hi⟩)]) = edgeF x := by
    intro x
    have h := hcorrect x
    dsimp only at h
    simp only [not_not] at h
    rw [hnot x] at h
    simpa only [List.append_assoc,List.singleton_append] using h
  change 5 ≤ i at hmin
  change i ≤ 8 at hmax
  interval_cases i
  · obtain ⟨hf',hs',hc'⟩ := rename_correct C 5 hf hc
    obtain ⟨x,hx⟩ := h1 (renameCircuit C) hf' (by omega)
    exact hx (hc' x)
  · obtain ⟨x,hx⟩ := h6 C hf hs
    exact hx (hc x)
  · obtain ⟨hf',hs',hc'⟩ := rename_correct C 7 hf hc
    obtain ⟨x,hx⟩ := h6 (renameCircuit C) hf' (by omega)
    exact hx (hc' x)
  · obtain ⟨hf',hs',hc'⟩ := rename_correct C 8 hf hc
    obtain ⟨x,hx⟩ := h2 (renameCircuit C) hf' (by omega)
    exact hx (hc' x)

