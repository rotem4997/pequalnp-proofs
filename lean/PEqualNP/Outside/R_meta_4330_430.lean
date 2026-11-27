import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4330_430
    (h1 : have fP : (Fin (10 : ℕ) → Bool) → Bool := fun x => (List.finRange (5 : ℕ)).any fun i : Fin (5 : ℕ) =>
            x (Fin.castAdd (5 : ℕ) i) && x (Fin.castAdd (5 : ℕ) (i + (1 : Fin (5 : ℕ)))) ||
            x (Fin.castAdd (5 : ℕ) i) && x (Fin.natAdd (5 : ℕ) i) ||
            x (Fin.natAdd (5 : ℕ) i) && x (Fin.natAdd (5 : ℕ) (i + (2 : Fin (5 : ℕ))));
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (b : Bool),
        PEqualNP.MetaComplexity.FanInTwo D → D.size = (17 : ℕ) →
        D.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).contains (0 : ℕ)) = (0 : ℕ) →
        D.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).contains (10 : ℕ)) = (1 : ℕ) →
        (∀ v : Fin (10 : ℕ), D.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).contains v.val) ≤ (2 : ℕ)) →
        (∀ x : Fin (10 : ℕ) → Bool, (if b = Bool.true then !((D.wires (List.ofFn x ++ [!x (0 : Fin (10 : ℕ))])).getD u Bool.false) else (D.wires (List.ofFn x ++ [!x (0 : Fin (10 : ℕ))])).getD u Bool.false) = fP x) →
        ∃ (E : PEqualNP.CircuitLowerBounds.Circuit) (u' : ℕ) (b' : Bool),
          PEqualNP.MetaComplexity.FanInTwo E ∧ E.size ≤ (15 : ℕ) ∧
          ∀ x : Fin (10 : ℕ) → Bool, x (9 : Fin (10 : ℕ)) = Bool.false →
            (if b' = Bool.true then !((E.wires (List.ofFn x)).getD u' Bool.false) else (E.wires (List.ofFn x)).getD u' Bool.false) = fP x)
    (h2 : have fP : (Fin (10 : ℕ) → Bool) → Bool := fun x => (List.finRange (5 : ℕ)).any fun i : Fin (5 : ℕ) =>
            x (Fin.castAdd (5 : ℕ) i) && x (Fin.castAdd (5 : ℕ) (i + (1 : Fin (5 : ℕ)))) ||
            x (Fin.castAdd (5 : ℕ) i) && x (Fin.natAdd (5 : ℕ) i) ||
            x (Fin.natAdd (5 : ℕ) i) && x (Fin.natAdd (5 : ℕ) (i + (2 : Fin (5 : ℕ))));
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (b : Bool),
        PEqualNP.MetaComplexity.FanInTwo D → D.size = (17 : ℕ) →
        D.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).contains (0 : ℕ)) = (1 : ℕ) →
        D.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).contains (1 : ℕ)) = (1 : ℕ) →
        (∀ v : Fin (10 : ℕ), D.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).contains v.val) ≤ (2 : ℕ)) →
        (∀ x : Fin (10 : ℕ) → Bool, (if b = Bool.true then !((D.wires (List.ofFn x ++ [x (0 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ))])).getD u Bool.false) else (D.wires (List.ofFn x ++ [x (0 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ))])).getD u Bool.false) = fP x) →
        ∃ (E : PEqualNP.CircuitLowerBounds.Circuit) (u' : ℕ) (b' : Bool),
          PEqualNP.MetaComplexity.FanInTwo E ∧ E.size ≤ (15 : ℕ) ∧
          ∀ x : Fin (10 : ℕ) → Bool, x (9 : Fin (10 : ℕ)) = Bool.false →
            (if b' = Bool.true then !((E.wires (List.ofFn x)).getD u' Bool.false) else (E.wires (List.ofFn x)).getD u' Bool.false) = fP x)
    (h3 : have fP : (Fin (10 : ℕ) → Bool) → Bool := fun x => (List.finRange (5 : ℕ)).any fun i : Fin (5 : ℕ) =>
            x (Fin.castAdd (5 : ℕ) i) && x (Fin.castAdd (5 : ℕ) (i + (1 : Fin (5 : ℕ)))) ||
            x (Fin.castAdd (5 : ℕ) i) && x (Fin.natAdd (5 : ℕ) i) ||
            x (Fin.natAdd (5 : ℕ) i) && x (Fin.natAdd (5 : ℕ) (i + (2 : Fin (5 : ℕ))));
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (b : Bool),
        PEqualNP.MetaComplexity.FanInTwo D → D.size = (17 : ℕ) →
        D.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).contains (0 : ℕ)) = (1 : ℕ) →
        D.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).contains (2 : ℕ)) = (1 : ℕ) →
        (∀ v : Fin (10 : ℕ), D.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).contains v.val) ≤ (2 : ℕ)) →
        (∀ x : Fin (10 : ℕ) → Bool, (if b = Bool.true then !((D.wires (List.ofFn x ++ [x (0 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ))])).getD u Bool.false) else (D.wires (List.ofFn x ++ [x (0 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ))])).getD u Bool.false) = fP x) →
        ∃ (E : PEqualNP.CircuitLowerBounds.Circuit) (u' : ℕ) (b' : Bool),
          PEqualNP.MetaComplexity.FanInTwo E ∧ E.size ≤ (15 : ℕ) ∧
          ∀ x : Fin (10 : ℕ) → Bool, x (9 : Fin (10 : ℕ)) = Bool.false →
            (if b' = Bool.true then !((E.wires (List.ofFn x)).getD u' Bool.false) else (E.wires (List.ofFn x)).getD u' Bool.false) = fP x) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Gate) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x2], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size = (17 : ℕ) →         have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => (x3.wires ({ gates := [x2], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x4 Bool.false;         (∀ (x10 : Fin (10 : ℕ) → Bool), (if x5 = Bool.true then !x9 x10 else x9 x10) = x1 x10) →           ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit) (x12 : ℕ) (x13 : Bool),             PEqualNP.MetaComplexity.FanInTwo x11 ∧               x11.size ≤ (15 : ℕ) ∧                 have x14 : (Fin (10 : ℕ) → Bool) → Bool := fun (x14 : Fin (10 : ℕ) → Bool) => (x11.wires (List.ofFn x14)).getD x12 Bool.false;                 ∀ (x15 : Fin (10 : ℕ) → Bool), x15 (9 : Fin (10 : ℕ)) = Bool.false → (if x13 = Bool.true then !x14 x15 else x14 x15) = x1 x15 := by
  dsimp only at h1 h2 h3 ⊢
  intro g0 D u b hg0 hfanD hszD hcomp0
  let f10 : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let G5 : (Fin 10 → Bool) → Bool := fun x => (List.finRange 5).any fun i : Fin 5 =>
    x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1)) ||
    x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
    x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))
  have hG5_eq : ∀ x : Fin 10 → Bool, f10 x = G5 x := by
    intro x
    dsimp only [f10, G5]
    have hfr5 : List.finRange 5 = [0, 1, 2, 3, 4] := by decide
    rw [hfr5]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    change _ = ((x 0 && x 1 || x 0 && x 5 || x 5 && x 7) ||
      ((x 1 && x 2 || x 1 && x 6 || x 6 && x 8) ||
      ((x 2 && x 3 || x 2 && x 7 || x 7 && x 9) ||
      ((x 3 && x 4 || x 3 && x 8 || x 8 && x 5) ||
      (x 4 && x 0 || x 4 && x 9 || x 9 && x 6)))))
    ac_rfl
  let edgeList : List (Fin 10 × Fin 10) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
     (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
     (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
  have hG5_edges : ∀ x : Fin 10 → Bool, G5 x = edgeList.any (fun e => x e.1 && x e.2) := by
    intro x
    rw [← hG5_eq]
    dsimp [f10, edgeList]
    simp only [Bool.or_false, Bool.or_assoc]
  have hedge_pres : ∀ (f g : Fin 10 → Fin 10),
      (edgeList.all (fun e => edgeList.any (fun e' => (f e.1 == e'.1 && f e.2 == e'.2) || (f e.1 == e'.2 && f e.2 == e'.1)))) = true →
      (edgeList.all (fun e => edgeList.any (fun e' => (g e.1 == e'.1 && g e.2 == e'.2) || (g e.1 == e'.2 && g e.2 == e'.1)))) = true →
      (∀ k : Fin 10, f (g k) = k) →
      ∀ x : Fin 10 → Bool, G5 (x ∘ f) = G5 x := by
    intro f g hf hg hfg x
    rw [hG5_edges, hG5_edges]
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      rw [List.any_eq_true] at h ⊢
      rcases h with ⟨e, he, hev⟩
      rw [List.all_eq_true] at hf
      have he1 := hf e he
      rw [List.any_eq_true] at he1
      rcases he1 with ⟨e', he', heq⟩
      refine ⟨e', he', ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at heq hev ⊢
      rcases heq with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact ⟨h1' ▸ hev.1, h2' ▸ hev.2⟩
      · exact ⟨h2' ▸ hev.2, h1' ▸ hev.1⟩
    · intro h
      rw [List.any_eq_true] at h ⊢
      rcases h with ⟨e', he', hev⟩
      rw [List.all_eq_true] at hg
      have he1 := hg e' he'
      rw [List.any_eq_true] at he1
      rcases he1 with ⟨e, he, heq⟩
      refine ⟨e, he, ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at heq hev ⊢
      rcases heq with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact ⟨by change x (f e.1) = true; rw [← h1', hfg e'.1]; exact hev.1,
               by change x (f e.2) = true; rw [← h2', hfg e'.2]; exact hev.2⟩
      · exact ⟨by change x (f e.1) = true; rw [← h2', hfg e'.2]; exact hev.2,
               by change x (f e.2) = true; rw [← h1', hfg e'.1]; exact hev.1⟩
  let sigma0Tbl : List (List (Fin 10)) :=
    [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
     [2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
     [2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
     [1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
     [1, 2, 3, 8, 6, 0, 7, 4, 5, 9],
     [2, 1, 6, 8, 3, 7, 0, 9, 5, 4],
     [2, 3, 4, 9, 7, 1, 8, 0, 6, 5],
     [2, 3, 8, 5, 7, 1, 4, 6, 0, 9],
     [2, 3, 8, 6, 1, 7, 4, 5, 9, 0]]
  let sigma0InvTbl : List (List (Fin 10)) :=
    [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
     [2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
     [3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
     [4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
     [5, 0, 1, 2, 7, 8, 4, 6, 3, 9],
     [6, 1, 0, 4, 9, 8, 2, 5, 3, 7],
     [7, 5, 0, 1, 2, 9, 8, 4, 6, 3],
     [8, 5, 0, 1, 6, 3, 7, 4, 2, 9],
     [9, 4, 0, 1, 6, 7, 3, 5, 2, 8]]
  let sigma9Tbl : List (List (Fin 10)) :=
    [[9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
     [4, 9, 6, 1, 0, 3, 7, 8, 2, 5],
     [0, 4, 9, 6, 1, 5, 3, 7, 8, 2],
     [0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
     [4, 0, 1, 6, 9, 3, 5, 2, 8, 7],
     [4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
     [0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
     [0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
     [0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
     [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
  let sigma9InvTbl : List (List (Fin 10)) :=
    [[2, 3, 8, 6, 1, 7, 4, 5, 9, 0],
     [4, 3, 8, 5, 0, 9, 2, 6, 7, 1],
     [0, 4, 9, 6, 1, 5, 3, 7, 8, 2],
     [0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
     [1, 2, 7, 5, 0, 6, 3, 9, 8, 4],
     [1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
     [0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
     [0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
     [0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
     [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
  let stab0Tbl : List (List (Fin 10)) :=
    [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
     [0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
     [0, 4, 3, 8, 5, 1, 9, 2, 6, 7],
     [0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
     [0, 4, 3, 8, 5, 1, 9, 2, 6, 7],
     [0, 4, 9, 7, 5, 1, 3, 6, 2, 8],
     [0, 4, 9, 6, 1, 5, 3, 7, 8, 2]]
  let stab0InvTbl : List (List (Fin 10)) :=
    [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
     [0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
     [0, 5, 7, 2, 1, 4, 8, 9, 3, 6],
     [0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
     [0, 5, 7, 2, 1, 4, 8, 9, 3, 6],
     [0, 5, 8, 6, 1, 4, 7, 3, 9, 2],
     [0, 4, 9, 6, 1, 5, 3, 7, 8, 2]]
  let tblAt : List (List (Fin 10)) → Fin 10 → Fin 10 → Fin 10 := fun tbl r k =>
    (tbl.getD r.val []).getD k.val 0
  let sigma0 := tblAt sigma0Tbl
  let sigma0Inv := tblAt sigma0InvTbl
  let sigma9 := tblAt sigma9Tbl
  let sigma9Inv := tblAt sigma9InvTbl
  let stab0 := tblAt stab0Tbl
  let stab0Inv := tblAt stab0InvTbl
  have hs0_pres : ∀ r : Fin 10, (edgeList.all (fun e => edgeList.any (fun e' => (sigma0 r e.1 == e'.1 && sigma0 r e.2 == e'.2) || (sigma0 r e.1 == e'.2 && sigma0 r e.2 == e'.1)))) = true := by
    dsimp only [sigma0, tblAt, sigma0Tbl, edgeList]; decide
  have hs0i_pres : ∀ r : Fin 10, (edgeList.all (fun e => edgeList.any (fun e' => (sigma0Inv r e.1 == e'.1 && sigma0Inv r e.2 == e'.2) || (sigma0Inv r e.1 == e'.2 && sigma0Inv r e.2 == e'.1)))) = true := by
    dsimp only [sigma0Inv, tblAt, sigma0InvTbl, edgeList]; decide
  have hs0_inv1 : ∀ r k : Fin 10, sigma0 r (sigma0Inv r k) = k := by
    dsimp only [sigma0, sigma0Inv, tblAt, sigma0Tbl, sigma0InvTbl]; decide
  have hs0_inv2 : ∀ r k : Fin 10, sigma0Inv r (sigma0 r k) = k := by
    dsimp only [sigma0, sigma0Inv, tblAt, sigma0Tbl, sigma0InvTbl]; decide
  have hG5_sigma0 : ∀ r : Fin 10, ∀ x : Fin 10 → Bool, G5 (x ∘ sigma0 r) = G5 x :=
    fun r x => hedge_pres (sigma0 r) (sigma0Inv r) (hs0_pres r) (hs0i_pres r) (hs0_inv1 r) x
  have hs0_self : ∀ r : Fin 10, sigma0 r r = 0 := by
    dsimp only [sigma0, tblAt, sigma0Tbl]; decide
  have hs9_pres : ∀ r : Fin 10, (edgeList.all (fun e => edgeList.any (fun e' => (sigma9 r e.1 == e'.1 && sigma9 r e.2 == e'.2) || (sigma9 r e.1 == e'.2 && sigma9 r e.2 == e'.1)))) = true := by
    dsimp only [sigma9, tblAt, sigma9Tbl, edgeList]; decide
  have hs9i_pres : ∀ r : Fin 10, (edgeList.all (fun e => edgeList.any (fun e' => (sigma9Inv r e.1 == e'.1 && sigma9Inv r e.2 == e'.2) || (sigma9Inv r e.1 == e'.2 && sigma9Inv r e.2 == e'.1)))) = true := by
    dsimp only [sigma9Inv, tblAt, sigma9InvTbl, edgeList]; decide
  have hs9_inv1 : ∀ r k : Fin 10, sigma9 r (sigma9Inv r k) = k := by
    dsimp only [sigma9, sigma9Inv, tblAt, sigma9Tbl, sigma9InvTbl]; decide
  have hs9_inv2 : ∀ r k : Fin 10, sigma9Inv r (sigma9 r k) = k := by
    dsimp only [sigma9, sigma9Inv, tblAt, sigma9Tbl, sigma9InvTbl]; decide
  have hG5_sigma9 : ∀ r : Fin 10, ∀ x : Fin 10 → Bool, G5 (x ∘ sigma9 r) = G5 x :=
    fun r x => hedge_pres (sigma9 r) (sigma9Inv r) (hs9_pres r) (hs9i_pres r) (hs9_inv1 r) x
  have hG5_sigma9Inv : ∀ r : Fin 10, ∀ x : Fin 10 → Bool, G5 (x ∘ sigma9Inv r) = G5 x :=
    fun r x => hedge_pres (sigma9Inv r) (sigma9 r) (hs9i_pres r) (hs9_pres r) (hs9_inv2 r) x
  have hs9_self : ∀ r : Fin 10, sigma9 r r = 9 := by
    dsimp only [sigma9, tblAt, sigma9Tbl]; decide
  have hst0_pres : ∀ r : Fin 10, (edgeList.all (fun e => edgeList.any (fun e' => (stab0 r e.1 == e'.1 && stab0 r e.2 == e'.2) || (stab0 r e.1 == e'.2 && stab0 r e.2 == e'.1)))) = true := by
    dsimp only [stab0, tblAt, stab0Tbl, edgeList]; decide
  have hst0i_pres : ∀ r : Fin 10, (edgeList.all (fun e => edgeList.any (fun e' => (stab0Inv r e.1 == e'.1 && stab0Inv r e.2 == e'.2) || (stab0Inv r e.1 == e'.2 && stab0Inv r e.2 == e'.1)))) = true := by
    dsimp only [stab0Inv, tblAt, stab0InvTbl, edgeList]; decide
  have hst0_inv1 : ∀ r k : Fin 10, stab0 r (stab0Inv r k) = k := by
    dsimp only [stab0, stab0Inv, tblAt, stab0Tbl, stab0InvTbl]; decide
  have hst0_inv2 : ∀ r k : Fin 10, stab0Inv r (stab0 r k) = k := by
    dsimp only [stab0, stab0Inv, tblAt, stab0Tbl, stab0InvTbl]; decide
  have hG5_stab0 : ∀ r : Fin 10, ∀ x : Fin 10 → Bool, G5 (x ∘ stab0 r) = G5 x :=
    fun r x => hedge_pres (stab0 r) (stab0Inv r) (hst0_pres r) (hst0i_pres r) (hst0_inv1 r) x
  have hst0_0 : ∀ r : Fin 10, stab0 r 0 = 0 := by
    dsimp only [stab0, tblAt, stab0Tbl]; decide
  have hst0_12 : ∀ r : Fin 10, r ≠ 0 → stab0 r r = 1 ∨ stab0 r r = 2 := by
    dsimp only [stab0, tblAt, stab0Tbl]; decide
  have hP_dep : ∀ v : Fin 10, ∃ a : Fin 10, a ≠ v ∧
      G5 (fun k => decide (k = a)) ≠ G5 (fun k => decide (k = v ∨ k = a)) := by
    dsimp only [G5]; decide
  have hP_nonconst : ∀ v : Fin 10,
      G5 (fun _ => false) ≠ G5 (fun k => decide (k ≠ v)) := by
    dsimp only [G5]; decide
  have hP_not_lit : ∀ (v : Fin 10) (neg : Bool), ∃ x : Fin 10 → Bool, (if neg = true then !(x v) else x v) ≠ G5 x := by
    intro v neg
    cases neg with
    | false =>
      refine ⟨fun k => decide (k = v), ?_⟩
      revert v
      dsimp only [G5]
      decide
    | true =>
      refine ⟨fun _ => false, ?_⟩
      revert v
      dsimp only [G5]
      decide
  have hP_and_wit : ∀ v w : Fin 10, v ≠ w → ∃ a : Fin 10, a ≠ v ∧ a ≠ w ∧
      G5 (fun k => decide (k = a)) ≠ G5 (fun k => decide (k = v ∨ k = a)) := by
    dsimp only [G5]; decide
  have hP_or_wit : ∀ v w : Fin 10, v ≠ w →
      G5 (fun k => decide (k = w)) ≠ G5 (fun k => decide (k = v ∨ k = w)) ∨
      ∃ a : Fin 10, a ≠ v ∧ a ≠ w ∧ G5 (fun k => decide (k = w ∨ k = a)) ≠ G5 (fun k => decide (k = v ∨ k = w ∨ k = a)) := by
    dsimp only [G5]; decide
  have hP_or_sym : ∀ v w : Fin 10, v ≠ w → ∃ a : Fin 10, a ≠ v ∧ a ≠ w ∧
      G5 (fun k => decide (k = v ∨ k = a)) ≠ G5 (fun k => decide (k = w ∨ k = a)) := by
    dsimp only [G5]; decide
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs w => gs.foldl step w
  have hrun_cons : ∀ (g : Gate) (gs : List Gate) (w : List Bool), run (g :: gs) w = run gs (step w g) :=
    fun _ _ _ => rfl
  have hrun_append : ∀ (gs hs : List Gate) (w : List Bool), run (gs ++ hs) w = run hs (run gs w) := by
    intro gs hs w
    simp [run, List.foldl_append]
  have hrun_len : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      rw [hrun_cons, ih]
      simp [step]
      omega
  have hstep_len : ∀ (w : List Bool) (g : Gate), (step w g).length = w.length + 1 := by
    intro w g
    simp [step]
  have hstep_pres : ∀ (w : List Bool) (g : Gate) (m : ℕ), m < w.length → (step w g).getD m false = w.getD m false := by
    intro w g m hm
    exact List.getD_append _ _ _ _ hm
  have hrun_preserves : ∀ (gs : List Gate) (w : List Bool) (m : ℕ), m < w.length →
      (run gs w).getD m false = w.getD m false := by
    intro gs
    induction gs with
    | nil => intro w m _; rfl
    | cons g gs ih =>
      intro w m hm
      rw [hrun_cons, ih (step w g) m (by rw [hstep_len]; omega)]
      exact hstep_pres w g m hm
  have hgetD_append_len : ∀ {α : Type} (xs ys : List α) (d : α), (xs ++ ys).getD xs.length d = ys.getD 0 d := by
    intro α xs ys d
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  have hgetFn10 : ∀ (x : Fin 10 → Bool) (ext : List Bool) (i : Fin 10), (List.ofFn x ++ ext).getD i.val false = x i := by
    intro x ext i
    have hi : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  have hstep_last : ∀ (w : List Bool) (g : Gate),
      (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) :=
    fun w g => hgetD_append_len w _ false
  have hgetFn10' : ∀ (x : Fin 10 → Bool) (i : Fin 10), (List.ofFn x).getD i.val false = x i := by
    intro x i
    simpa using hgetFn10 x [] i
  have hgetFn10Nat : ∀ (x : Fin 10 → Bool) (m : ℕ) (hm : m < 10), (List.ofFn x).getD m false = x ⟨m, hm⟩ :=
    fun x m hm => hgetFn10' x ⟨m, hm⟩
  have hstep_10 : ∀ (y : Fin 10 → Bool) (g : Gate),
      (step (List.ofFn y) g).getD 10 false = g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false) :=
    fun y g => by have h := hstep_last (List.ofFn y) g; rwa [List.length_ofFn] at h
  have happend_10 : ∀ (y : Fin 10 → Bool) (ext : List Bool),
      (List.ofFn y ++ ext).getD 10 false = ext.getD 0 false :=
    fun y ext => by have h := hgetD_append_len (List.ofFn y) ext false; rwa [List.length_ofFn] at h
  have hfinRange10 : ∀ (m : ℕ) (hm : m < (List.finRange 10).length),
      (List.finRange 10)[m] = (⟨m, by rw [List.length_finRange] at hm; exact hm⟩ : Fin 10) :=
    fun m hm => Fin.ext (by simp)
  let effInputs : Gate → List ℕ := fun g => cond (g.op.eval [false]) (g.inputs.take 1) g.inputs
  let fanOK : Gate → Prop := fun g =>
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2
  have hcontains_eq_all : ∀ (qs : List Gate) (w : ℕ),
      qs.countP (fun g => (effInputs g).any (fun x => x == w)) =
      qs.countP (fun g => (effInputs g).contains w) := by
    intro qs w
    apply List.countP_congr
    intro g _
    simp only [List.any_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq]
    exact ⟨fun h => Exists.elim h fun a ha => ha.2 ▸ ha.1, fun h => ⟨w, h, rfl⟩⟩
  have hcomp_init_Agree : ∀ (w1 w2 : List Bool) (gs : List Gate) (B : ℕ → Prop) (uOut : ℕ),
      w1.length = w2.length →
      ¬ B uOut →
      (∀ i, ¬ B i → w1.getD i false = w2.getD i false) →
      (∀ g ∈ gs, ∀ i ∈ effInputs g, ¬ B i) →
      (∀ g ∈ gs, fanOK g) →
      (run gs w1).getD uOut false = (run gs w2).getD uOut false := by
    intro w1 w2 gs
    induction gs generalizing w1 w2 with
    | nil =>
      intro B uOut _ hBu hinit _ _
      exact hinit uOut hBu
    | cons g gs ih =>
      intro B uOut hlen hBu hinit hnoB hfan_gs
      rw [hrun_cons, hrun_cons]
      apply ih (step w1 g) (step w2 g) B uOut (by simp [step, hlen]) hBu
      · intro i hi
        by_cases hil : i < w1.length
        · rw [List.getD_append _ _ _ _ hil, List.getD_append _ _ _ _ (by omega)]
          exact hinit i hi
        · by_cases hieq : i = w1.length
          · subst hieq
            rw [hgetD_append_len w1 _, hlen, hgetD_append_len w2 _]
            cases g
            rename_i op ins
            rcases (hfan_gs ⟨op, ins⟩ List.mem_cons_self).1 with rfl | rfl | rfl
            · have hmap : ins.map (fun j => w1.getD j false) = ins.map (fun j => w2.getD j false) := by
                apply List.map_congr_left
                intro j hj
                exact hinit j (hnoB ⟨GateOp.and, ins⟩ List.mem_cons_self j (by exact hj))
              rw [hmap]
            · have hmap : ins.map (fun j => w1.getD j false) = ins.map (fun j => w2.getD j false) := by
                apply List.map_congr_left
                intro j hj
                exact hinit j (hnoB ⟨GateOp.or, ins⟩ List.mem_cons_self j (by exact hj))
              rw [hmap]
            · cases ins with
              | nil => rfl
              | cons a t =>
                have ha : ¬ B a := hnoB ⟨GateOp.not, a :: t⟩ List.mem_cons_self a (by change a ∈ [a]; simp)
                change Bool.not ((w1.getD a false :: t.map _).headD false) = Bool.not ((w2.getD a false :: t.map _).headD false)
                rw [List.headD_cons, List.headD_cons, hinit a ha]
          · rw [List.getD_eq_default (step w1 g) false (by rw [hstep_len]; omega),
              List.getD_eq_default (step w2 g) false (by rw [hstep_len]; omega)]
      · intro g' hg'
        exact hnoB g' (List.mem_cons_of_mem _ hg')
      · intro g' hg'
        exact hfan_gs g' (List.mem_cons_of_mem _ hg')
  let evalVal : List Bool → Sum Bool ℕ → Bool := fun W v =>
    Sum.casesOn (motive := fun _ => Bool) v (fun b => b) (fun w => W.getD w false)
  let evalOne (nOut : ℕ) (g : Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate) : Sum Bool ℕ × Option Gate :=
    GateOp.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) g.op
      (List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) g.inputs (Sum.inl true, none) fun a t =>
        List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) t (env.getD a (Sum.inl false), none) fun b _ =>
          Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD a (Sum.inl false))
            (fun ba => cond ba (env.getD b (Sum.inl false), none) (Sum.inl false, none))
            (fun wa => Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD b (Sum.inl false))
              (fun bb => cond bb (Sum.inr wa, none) (Sum.inl false, none))
              (fun wb => (Sum.inr (nOut + gs'.length), some ⟨GateOp.and, [wa, wb]⟩))))
      (List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) g.inputs (Sum.inl false, none) fun a t =>
        List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) t (env.getD a (Sum.inl false), none) fun b _ =>
          Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD a (Sum.inl false))
            (fun ba => cond ba (Sum.inl true, none) (env.getD b (Sum.inl false), none))
            (fun wa => Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD b (Sum.inl false))
              (fun bb => cond bb (Sum.inl true, none) (Sum.inr wa, none))
              (fun wb => (Sum.inr (nOut + gs'.length), some ⟨GateOp.or, [wa, wb]⟩))))
      (List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) g.inputs (Sum.inl true, none) fun a _ =>
        Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD a (Sum.inl false))
          (fun b => (Sum.inl (!b), none))
          (fun wa => (Sum.inr (nOut + gs'.length), some ⟨GateOp.not, [wa]⟩)))
      (fun _ => (Sum.inl false, none))
      (Sum.inl false, none)
  let compileStep (nOut : ℕ) (st : List (Sum Bool ℕ) × List Gate) (g : Gate) : List (Sum Bool ℕ) × List Gate :=
    let r := evalOne nOut g st.1 st.2
    Option.casesOn (motive := fun _ => List (Sum Bool ℕ) × List Gate) r.2
      (st.1 ++ [r.1], st.2)
      (fun g' => (st.1 ++ [r.1], st.2 ++ [g']))
  let compileLoop (nOut : ℕ) : List Gate → List (Sum Bool ℕ) × List Gate → List (Sum Bool ℕ) × List Gate :=
    fun gs st => gs.foldl (compileStep nOut) st
  have hcomp_step_props : ∀ (nOut boundW : ℕ) (isZ : ℕ → Bool) (hisZ : ∀ w, isZ w = true → w < boundW)
      (g : Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate),
      fanOK g →
      boundW ≤ env.length →
      (∀ w, isZ w = true → ∃ b, env.getD w (Sum.inl false) = Sum.inl b) →
      (∀ v ∈ env, ∀ j, v = Sum.inr j → j < nOut + gs'.length) →
      (∀ g' ∈ gs', fanOK g') →
      let st1 := compileStep nOut (env, gs') g
      (∃ ext1, st1.2 = gs' ++ ext1 ∧ ext1.length ≤ 1) ∧
        ((effInputs g).any isZ = true → st1.2 = gs') ∧
        (∀ g' ∈ st1.2, fanOK g') ∧
        (∀ v ∈ st1.1, ∀ j, v = Sum.inr j → j < nOut + st1.2.length) ∧
        st1.1.length = env.length + 1 ∧
        (∀ w, isZ w = true → ∃ b, st1.1.getD w (Sum.inl false) = Sum.inl b) := by
    intro nOut boundW isZ hisZ g env gs' hg hlen hZ hbound hfg
    cases g
    rename_i op ins
    have hgfan : fanOK ⟨op, ins⟩ := hg
    let st1 := compileStep nOut (env, gs') ⟨op, ins⟩
    have hlen1 : st1.1.length = env.length + 1 := by
      dsimp [st1, compileStep]
      cases (evalOne nOut ⟨op, ins⟩ env gs').2 <;> simp
    have hZ' : ∀ w, isZ w = true → ∃ b, st1.1.getD w (Sum.inl false) = Sum.inl b := by
      intro w hw
      have hwb : w < env.length := by have := hisZ w hw; omega
      have hsame : st1.1.getD w (Sum.inl false) = env.getD w (Sum.inl false) := by
        dsimp [st1, compileStep]
        cases (evalOne nOut ⟨op, ins⟩ env gs').2 <;> exact List.getD_append _ _ _ _ hwb
      rw [hsame]
      exact hZ w hw
    have hnone_case : ∀ val : Sum Bool ℕ, (∀ j, val = Sum.inr j → j < nOut + gs'.length) →
        (evalOne nOut ⟨op, ins⟩ env gs').2 = none →
        (evalOne nOut ⟨op, ins⟩ env gs').1 = val →
        (∃ ext1, st1.2 = gs' ++ ext1 ∧ ext1.length ≤ 1) ∧
        ((effInputs ⟨op, ins⟩).any isZ = true → st1.2 = gs') ∧
        (∀ g' ∈ st1.2, fanOK g') ∧
        (∀ v ∈ st1.1, ∀ j, v = Sum.inr j → j < nOut + st1.2.length) := by
      intro val hvb h2 h1
      have hst2 : st1.2 = gs' := by dsimp [st1, compileStep]; rw [h2]
      refine ⟨⟨[], by simp [hst2]⟩, fun _ => hst2, fun g' hg' => hfg g' (hst2 ▸ hg'), ?_⟩
      intro v hv j hj
      dsimp [st1, compileStep] at hv
      rw [h2, h1] at hv
      rw [hst2]
      rw [List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact hbound v hv j hj
      · exact hvb j hj
    have hget_bound : ∀ a, ∀ j, env.getD a (Sum.inl false) = Sum.inr j → j < nOut + gs'.length := by
      intro a j ha
      by_cases hlt : a < env.length
      · rw [List.getD_eq_getElem _ _ hlt] at ha
        exact hbound _ (List.getElem_mem hlt) j ha
      · rw [List.getD_eq_default _ _ (by omega)] at ha
        cases ha
    have hcore :
        (∃ ext1, st1.2 = gs' ++ ext1 ∧ ext1.length ≤ 1) ∧
        ((effInputs ⟨op, ins⟩).any isZ = true → st1.2 = gs') ∧
        (∀ g' ∈ st1.2, fanOK g') ∧
        (∀ v ∈ st1.1, ∀ j, v = Sum.inr j → j < nOut + st1.2.length) := by
      rcases hgfan with ⟨hop, hilen⟩
      rcases hop with rfl | rfl | rfl
      · cases ins with
        | nil => exact hnone_case (Sum.inl true) (fun _ h => by cases h) rfl rfl
        | cons a t =>
          cases t with
          | nil => exact hnone_case (env.getD a (Sum.inl false)) (hget_bound a) rfl rfl
          | cons b r =>
            have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilen
            subst hr_nil
            have hrz_none : (effInputs ⟨GateOp.and, [a, b]⟩).any isZ = true →
                (evalOne nOut ⟨GateOp.and, [a, b]⟩ env gs').2 = none := by
              intro hrz
              change ([a, b].any isZ) = true at hrz
              simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hrz
              dsimp [evalOne]
              rcases hrz with ha | hb
              · obtain ⟨ba, hba⟩ := hZ a ha
                rw [hba]
                cases ba <;> cases env.getD b (Sum.inl false) with
                | inl bb => cases bb <;> rfl
                | inr _ => rfl
              · obtain ⟨bb, hbb⟩ := hZ b hb
                rw [hbb]
                cases env.getD a (Sum.inl false) with
                | inl ba => cases ba <;> cases bb <;> rfl
                | inr _ => cases bb <;> rfl
            cases hga : env.getD a (Sum.inl false) with
            | inl ba =>
              cases ba
              · have hev : evalOne nOut ⟨GateOp.and, [a, b]⟩ env gs' = (Sum.inl false, none) := by dsimp [evalOne]; rw [hga]; rfl
                exact hnone_case (Sum.inl false) (fun _ h => by cases h) (congrArg Prod.snd hev) (congrArg Prod.fst hev)
              · cases hgb : env.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb
                  · have hev : evalOne nOut ⟨GateOp.and, [a, b]⟩ env gs' = (Sum.inl false, none) := by dsimp [evalOne]; rw [hga, hgb]; rfl
                    exact hnone_case (Sum.inl false) (fun _ h => by cases h) (congrArg Prod.snd hev) (congrArg Prod.fst hev)
                  · have hev : evalOne nOut ⟨GateOp.and, [a, b]⟩ env gs' = (Sum.inl true, none) := by dsimp [evalOne]; rw [hga, hgb]; rfl
                    exact hnone_case (Sum.inl true) (fun _ h => by cases h) (congrArg Prod.snd hev) (congrArg Prod.fst hev)
                | inr wb =>
                  have hev : evalOne nOut ⟨GateOp.and, [a, b]⟩ env gs' = (Sum.inr wb, none) := by dsimp [evalOne]; rw [hga, hgb]; rfl
                  exact hnone_case (Sum.inr wb) (fun j hj => by cases hj; exact hget_bound b wb hgb) (congrArg Prod.snd hev) (congrArg Prod.fst hev)
            | inr wa =>
              cases hgb : env.getD b (Sum.inl false) with
              | inl bb =>
                cases bb
                · have hev : evalOne nOut ⟨GateOp.and, [a, b]⟩ env gs' = (Sum.inl false, none) := by dsimp [evalOne]; rw [hga, hgb]; rfl
                  exact hnone_case (Sum.inl false) (fun _ h => by cases h) (congrArg Prod.snd hev) (congrArg Prod.fst hev)
                · have hev : evalOne nOut ⟨GateOp.and, [a, b]⟩ env gs' = (Sum.inr wa, none) := by dsimp [evalOne]; rw [hga, hgb]; rfl
                  exact hnone_case (Sum.inr wa) (fun j hj => by cases hj; exact hget_bound a wa hga) (congrArg Prod.snd hev) (congrArg Prod.fst hev)
              | inr wb =>
                have hev : evalOne nOut ⟨GateOp.and, [a, b]⟩ env gs' = (Sum.inr (nOut + gs'.length), some ⟨GateOp.and, [wa, wb]⟩) := by
                  dsimp [evalOne]; rw [hga, hgb]
                have hst1_1 : st1.1 = env ++ [Sum.inr (nOut + gs'.length)] := by dsimp [st1, compileStep]; rw [hev]
                have hst1_2 : st1.2 = gs' ++ [⟨GateOp.and, [wa, wb]⟩] := by dsimp [st1, compileStep]; rw [hev]
                refine ⟨⟨[⟨GateOp.and, [wa, wb]⟩], hst1_2, by simp⟩, ?_, ?_, ?_⟩
                · intro hrz; have h' := hrz_none hrz; rw [hev] at h'; cases h'
                · intro g' hg'; rw [hst1_2, List.mem_append, List.mem_singleton] at hg'
                  rcases hg' with hg' | rfl
                  · exact hfg g' hg'
                  · exact ⟨Or.inl rfl, by simp⟩
                · intro v hv j hj; rw [hst1_1, List.mem_append, List.mem_singleton] at hv
                  rw [hst1_2, List.length_append, List.length_singleton]
                  rcases hv with hv | rfl
                  · have := hbound v hv j hj; omega
                  · cases hj; omega
      · cases ins with
        | nil => exact hnone_case (Sum.inl false) (fun _ h => by cases h) rfl rfl
        | cons a t =>
          cases t with
          | nil => exact hnone_case (env.getD a (Sum.inl false)) (hget_bound a) rfl rfl
          | cons b r =>
            have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilen
            subst hr_nil
            have hrz_none : (effInputs ⟨GateOp.or, [a, b]⟩).any isZ = true →
                (evalOne nOut ⟨GateOp.or, [a, b]⟩ env gs').2 = none := by
              intro hrz
              change ([a, b].any isZ) = true at hrz
              simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hrz
              dsimp [evalOne]
              rcases hrz with ha | hb
              · obtain ⟨ba, hba⟩ := hZ a ha
                rw [hba]
                cases ba <;> cases env.getD b (Sum.inl false) with
                | inl bb => cases bb <;> rfl
                | inr _ => rfl
              · obtain ⟨bb, hbb⟩ := hZ b hb
                rw [hbb]
                cases env.getD a (Sum.inl false) with
                | inl ba => cases ba <;> cases bb <;> rfl
                | inr _ => cases bb <;> rfl
            cases hga : env.getD a (Sum.inl false) with
            | inl ba =>
              cases ba
              · cases hgb : env.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb
                  · have hev : evalOne nOut ⟨GateOp.or, [a, b]⟩ env gs' = (Sum.inl false, none) := by dsimp [evalOne]; rw [hga, hgb]; rfl
                    exact hnone_case (Sum.inl false) (fun _ h => by cases h) (congrArg Prod.snd hev) (congrArg Prod.fst hev)
                  · have hev : evalOne nOut ⟨GateOp.or, [a, b]⟩ env gs' = (Sum.inl true, none) := by dsimp [evalOne]; rw [hga, hgb]; rfl
                    exact hnone_case (Sum.inl true) (fun _ h => by cases h) (congrArg Prod.snd hev) (congrArg Prod.fst hev)
                | inr wb =>
                  have hev : evalOne nOut ⟨GateOp.or, [a, b]⟩ env gs' = (Sum.inr wb, none) := by dsimp [evalOne]; rw [hga, hgb]; rfl
                  exact hnone_case (Sum.inr wb) (fun j hj => by cases hj; exact hget_bound b wb hgb) (congrArg Prod.snd hev) (congrArg Prod.fst hev)
              · have hev : evalOne nOut ⟨GateOp.or, [a, b]⟩ env gs' = (Sum.inl true, none) := by dsimp [evalOne]; rw [hga]; rfl
                exact hnone_case (Sum.inl true) (fun _ h => by cases h) (congrArg Prod.snd hev) (congrArg Prod.fst hev)
            | inr wa =>
              cases hgb : env.getD b (Sum.inl false) with
              | inl bb =>
                cases bb
                · have hev : evalOne nOut ⟨GateOp.or, [a, b]⟩ env gs' = (Sum.inr wa, none) := by dsimp [evalOne]; rw [hga, hgb]; rfl
                  exact hnone_case (Sum.inr wa) (fun j hj => by cases hj; exact hget_bound a wa hga) (congrArg Prod.snd hev) (congrArg Prod.fst hev)
                · have hev : evalOne nOut ⟨GateOp.or, [a, b]⟩ env gs' = (Sum.inl true, none) := by dsimp [evalOne]; rw [hga, hgb]; rfl
                  exact hnone_case (Sum.inl true) (fun _ h => by cases h) (congrArg Prod.snd hev) (congrArg Prod.fst hev)
              | inr wb =>
                have hev : evalOne nOut ⟨GateOp.or, [a, b]⟩ env gs' = (Sum.inr (nOut + gs'.length), some ⟨GateOp.or, [wa, wb]⟩) := by
                  dsimp [evalOne]; rw [hga, hgb]
                have hst1_1 : st1.1 = env ++ [Sum.inr (nOut + gs'.length)] := by dsimp [st1, compileStep]; rw [hev]
                have hst1_2 : st1.2 = gs' ++ [⟨GateOp.or, [wa, wb]⟩] := by dsimp [st1, compileStep]; rw [hev]
                refine ⟨⟨[⟨GateOp.or, [wa, wb]⟩], hst1_2, by simp⟩, ?_, ?_, ?_⟩
                · intro hrz; have h' := hrz_none hrz; rw [hev] at h'; cases h'
                · intro g' hg'; rw [hst1_2, List.mem_append, List.mem_singleton] at hg'
                  rcases hg' with hg' | rfl
                  · exact hfg g' hg'
                  · exact ⟨Or.inr (Or.inl rfl), by simp⟩
                · intro v hv j hj; rw [hst1_1, List.mem_append, List.mem_singleton] at hv
                  rw [hst1_2, List.length_append, List.length_singleton]
                  rcases hv with hv | rfl
                  · have := hbound v hv j hj; omega
                  · cases hj; omega
      · cases ins with
        | nil => exact hnone_case (Sum.inl true) (fun _ h => by cases h) rfl rfl
        | cons a t =>
          have hrz_none : (effInputs ⟨GateOp.not, a :: t⟩).any isZ = true →
              (evalOne nOut ⟨GateOp.not, a :: t⟩ env gs').2 = none := by
            intro hrz
            change (([a]).any isZ) = true at hrz
            simp only [List.any_cons, List.any_nil, Bool.or_false] at hrz
            obtain ⟨ba, hba⟩ := hZ a hrz
            dsimp [evalOne]
            rw [hba]
          cases hga : env.getD a (Sum.inl false) with
          | inl ba =>
            have hev : evalOne nOut ⟨GateOp.not, a :: t⟩ env gs' = (Sum.inl (!ba), none) := by dsimp [evalOne]; rw [hga]
            exact hnone_case (Sum.inl (!ba)) (fun _ h => by cases h) (congrArg Prod.snd hev) (congrArg Prod.fst hev)
          | inr wa =>
            have hev : evalOne nOut ⟨GateOp.not, a :: t⟩ env gs' = (Sum.inr (nOut + gs'.length), some ⟨GateOp.not, [wa]⟩) := by
              dsimp [evalOne]; rw [hga]
            have hst1_1 : st1.1 = env ++ [Sum.inr (nOut + gs'.length)] := by dsimp [st1, compileStep]; rw [hev]
            have hst1_2 : st1.2 = gs' ++ [⟨GateOp.not, [wa]⟩] := by dsimp [st1, compileStep]; rw [hev]
            refine ⟨⟨[⟨GateOp.not, [wa]⟩], hst1_2, by simp⟩, ?_, ?_, ?_⟩
            · intro hrz; have h' := hrz_none hrz; rw [hev] at h'; cases h'
            · intro g' hg'; rw [hst1_2, List.mem_append, List.mem_singleton] at hg'
              rcases hg' with hg' | rfl
              · exact hfg g' hg'
              · exact ⟨Or.inr (Or.inr rfl), by simp⟩
            · intro v hv j hj; rw [hst1_1, List.mem_append, List.mem_singleton] at hv
              rw [hst1_2, List.length_append, List.length_singleton]
              rcases hv with hv | rfl
              · have := hbound v hv j hj; omega
              · cases hj; omega
    exact ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2, hlen1, hZ'⟩
  have hcomp_struct : ∀ (nOut boundW : ℕ) (isZ : ℕ → Bool) (hisZ : ∀ w, isZ w = true → w < boundW)
      (gs : List Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate),
      boundW ≤ env.length →
      (∀ w, isZ w = true → ∃ b, env.getD w (Sum.inl false) = Sum.inl b) →
      (∀ v ∈ env, ∀ j, v = Sum.inr j → j < nOut + gs'.length) →
      (∀ g' ∈ gs', fanOK g') →
      (∀ g ∈ gs, fanOK g) →
      let res := compileLoop nOut gs (env, gs')
      (∃ ext, res.2 = gs' ++ ext) ∧
        (∀ g' ∈ res.2, fanOK g') ∧
        (∀ v ∈ res.1, ∀ j, v = Sum.inr j → j < nOut + res.2.length) ∧
        res.1.length = env.length + gs.length ∧
        res.2.length + gs.countP (fun g => (effInputs g).any isZ) ≤ gs'.length + gs.length := by
    intro nOut boundW isZ hisZ gs
    induction gs with
    | nil =>
      intro env gs' _ _ hbound hfg _
      refine ⟨⟨[], by dsimp [compileLoop]; simp⟩, hfg, hbound, by rfl, ?_⟩
      change gs'.length + 0 ≤ gs'.length + 0
      exact le_refl _
    | cons g gs ih =>
      intro env gs' hlen hZ hbound hfg hgs
      have hgfan : fanOK g := hgs g List.mem_cons_self
      have hgs_tail : ∀ h ∈ gs, fanOK h := fun h hh => hgs h (List.mem_cons_of_mem _ hh)
      obtain ⟨⟨ext1, hext1, hext1_len⟩, hrz1, hfg1, hbound1, hlen1, hZ'⟩ :=
        hcomp_step_props nOut boundW isZ hisZ g env gs' hgfan hlen hZ hbound hfg
      obtain ⟨⟨ext2, hext2⟩, hfg2, hbound2, hlen2, hcnt2⟩ :=
        ih (compileStep nOut (env, gs') g).1 (compileStep nOut (env, gs') g).2 (by omega) hZ' hbound1 hfg1 hgs_tail
      have hfold : compileLoop nOut (g :: gs) (env, gs') =
          compileLoop nOut gs ((compileStep nOut (env, gs') g).1, (compileStep nOut (env, gs') g).2) := rfl
      rw [hfold]
      refine ⟨⟨ext1 ++ ext2, by rw [hext2, hext1, List.append_assoc]⟩, hfg2, hbound2, by rw [hlen2, hlen1, List.length_cons]; omega, ?_⟩
      rw [List.countP_cons, List.length_cons]
      by_cases hrzg : (effInputs g).any isZ = true
      · simp only [hrzg, ↓reduceIte]
        rw [hrz1 hrzg] at hcnt2 ⊢
        omega
      · simp only [hrzg, Bool.false_eq_true, ↓reduceIte]
        rw [hext1] at hcnt2 ⊢
        rw [List.length_append] at hcnt2
        omega
  have hcomp_step_sem : ∀ (nOut : ℕ) (y : Fin nOut → Bool) (g : Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate)
      (w WF : List Bool),
      fanOK g →
      env.length = w.length →
      (∀ v ∈ env, ∀ j, v = Sum.inr j → j < nOut + gs'.length) →
      (∀ k, k < nOut + (compileStep nOut (env, gs') g).2.length →
        WF.getD k false = (run (compileStep nOut (env, gs') g).2 (List.ofFn y)).getD k false) →
      (∀ m, evalVal WF (env.getD m (Sum.inl false)) = w.getD m false) →
      ∀ m, evalVal WF ((compileStep nOut (env, gs') g).1.getD m (Sum.inl false)) = (step w g).getD m false := by
    intro nOut y g env gs' w WF hgfan hlen hbound hWF hsem m
    cases g
    rename_i op ins
    let st1 := compileStep nOut (env, gs') ⟨op, ins⟩
    by_cases hm : m < w.length
    · have hm' : m < env.length := by omega
      have h1m : st1.1.getD m (Sum.inl false) = env.getD m (Sum.inl false) := by
        dsimp [st1, compileStep]
        cases (evalOne nOut ⟨op, ins⟩ env gs').2 <;> exact List.getD_append _ _ _ _ hm'
      rw [h1m, List.getD_append _ _ _ _ hm]
      exact hsem m
    · by_cases heq : m = w.length
      · subst heq
        have hw1 : (step w ⟨op, ins⟩).getD w.length false = op.eval (ins.map fun i => w.getD i false) :=
          hgetD_append_len w [op.eval (ins.map fun i => w.getD i false)] false
        have hs1 : st1.1.getD env.length (Sum.inl false) = (evalOne nOut ⟨op, ins⟩ env gs').1 := by
          dsimp [st1, compileStep]
          cases (evalOne nOut ⟨op, ins⟩ env gs').2 <;> exact hgetD_append_len env _ _
        change evalVal WF (st1.1.getD w.length (Sum.inl false)) = (step w ⟨op, ins⟩).getD w.length false
        rw [hw1, ← hlen, hs1]
        have hget_bound : ∀ a, ∀ j, env.getD a (Sum.inl false) = Sum.inr j → j < nOut + gs'.length := by
          intro a j ha
          by_cases hlt : a < env.length
          · rw [List.getD_eq_getElem _ _ hlt] at ha
            exact hbound _ (List.getElem_mem hlt) j ha
          · rw [List.getD_eq_default _ _ (by omega)] at ha
            cases ha
        rcases hgfan with ⟨hop, hilen⟩
        rcases hop with rfl | rfl | rfl
        · cases ins with
          | nil => rfl
          | cons a t =>
            cases t with
            | nil =>
              dsimp [evalOne]
              rw [hsem a]
              change _ = GateOp.and.eval [w.getD a false]
              cases (w.getD a false) <;> rfl
            | cons b r =>
              have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilen
              subst hr_nil
              have hsa := hsem a
              have hsb := hsem b
              dsimp [evalOne]
              change _ = (w.getD a false && (w.getD b false && true))
              cases hga : env.getD a (Sum.inl false) <;> cases hgb : env.getD b (Sum.inl false) <;>
                rw [hga] at hsa <;> rw [hgb] at hsb
              · rename_i ba bb
                cases ba <;> cases bb <;> dsimp [evalVal] at hsa hsb ⊢ <;> rw [← hsa, ← hsb] <;> rfl
              · rename_i ba wb
                cases ba <;> dsimp [evalVal, cond] at hsa hsb ⊢
                · rw [← hsa]; rfl
                · rw [← hsa, hsb]; cases (w.getD b false) <;> rfl
              · rename_i wa bb
                cases bb <;> dsimp [evalVal, cond] at hsa hsb ⊢
                · rw [← hsb]; cases (w.getD a false) <;> rfl
                · rw [hsa, ← hsb]; cases (w.getD a false) <;> rfl
              · rename_i wa wb
                have hst1eq : (compileStep nOut (env, gs') ⟨GateOp.and, [a, b]⟩).2 = gs' ++ [⟨GateOp.and, [wa, wb]⟩] := by
                  dsimp [compileStep, evalOne]
                  rw [hga, hgb]
                have hlt1 : nOut + gs'.length < nOut + (compileStep nOut (env, gs') ⟨GateOp.and, [a, b]⟩).2.length := by
                  rw [hst1eq, List.length_append, List.length_singleton]; omega
                have hw0 := hWF (nOut + gs'.length) hlt1
                rw [hst1eq, hrun_append] at hw0
                have hlenrun : (run gs' (List.ofFn y)).length = nOut + gs'.length := by
                  rw [hrun_len, List.length_ofFn]
                have hw_eval : (run [⟨GateOp.and, [wa, wb]⟩] (run gs' (List.ofFn y))).getD (nOut + gs'.length) false =
                    ((run gs' (List.ofFn y)).getD wa false && ((run gs' (List.ofFn y)).getD wb false && true)) := by
                  rw [← hlenrun]
                  exact hgetD_append_len (run gs' (List.ofFn y)) _ false
                have hwa_bd := hget_bound a wa hga
                have hwb_bd := hget_bound b wb hgb
                have hwa_eq : (run gs' (List.ofFn y)).getD wa false = WF.getD wa false := by
                  have hwa1 : WF.getD wa false = (run (compileStep nOut (env, gs') ⟨GateOp.and, [a, b]⟩).2 (List.ofFn y)).getD wa false :=
                    hWF wa (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                  rw [hst1eq, hrun_append] at hwa1
                  have hp := hrun_preserves [⟨GateOp.and, [wa, wb]⟩] (run gs' (List.ofFn y)) wa (by rw [hlenrun]; exact hwa_bd)
                  rw [hp] at hwa1
                  exact hwa1.symm
                have hwb_eq : (run gs' (List.ofFn y)).getD wb false = WF.getD wb false := by
                  have hwb1 : WF.getD wb false = (run (compileStep nOut (env, gs') ⟨GateOp.and, [a, b]⟩).2 (List.ofFn y)).getD wb false :=
                    hWF wb (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                  rw [hst1eq, hrun_append] at hwb1
                  have hp := hrun_preserves [⟨GateOp.and, [wa, wb]⟩] (run gs' (List.ofFn y)) wb (by rw [hlenrun]; exact hwb_bd)
                  rw [hp] at hwb1
                  exact hwb1.symm
                dsimp [evalVal] at hsa hsb ⊢
                rw [hw0, hw_eval, hwa_eq, hwb_eq, hsa, hsb]
        · cases ins with
          | nil => rfl
          | cons a t =>
            cases t with
            | nil =>
              dsimp [evalOne]
              rw [hsem a]
              change _ = GateOp.or.eval [w.getD a false]
              cases (w.getD a false) <;> rfl
            | cons b r =>
              have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilen
              subst hr_nil
              have hsa := hsem a
              have hsb := hsem b
              dsimp [evalOne]
              change _ = (w.getD a false || (w.getD b false || false))
              cases hga : env.getD a (Sum.inl false) <;> cases hgb : env.getD b (Sum.inl false) <;>
                rw [hga] at hsa <;> rw [hgb] at hsb
              · rename_i ba bb
                cases ba <;> cases bb <;> dsimp [evalVal] at hsa hsb ⊢ <;> rw [← hsa, ← hsb] <;> rfl
              · rename_i ba wb
                cases ba <;> dsimp [evalVal, cond] at hsa hsb ⊢
                · rw [← hsa, hsb]; cases (w.getD b false) <;> rfl
                · rw [← hsa]; rfl
              · rename_i wa bb
                cases bb <;> dsimp [evalVal, cond] at hsa hsb ⊢
                · rw [hsa, ← hsb]; cases (w.getD a false) <;> rfl
                · rw [← hsb]; cases (w.getD a false) <;> rfl
              · rename_i wa wb
                have hst1eq : (compileStep nOut (env, gs') ⟨GateOp.or, [a, b]⟩).2 = gs' ++ [⟨GateOp.or, [wa, wb]⟩] := by
                  dsimp [compileStep, evalOne]
                  rw [hga, hgb]
                have hlt1 : nOut + gs'.length < nOut + (compileStep nOut (env, gs') ⟨GateOp.or, [a, b]⟩).2.length := by
                  rw [hst1eq, List.length_append, List.length_singleton]; omega
                have hw0 := hWF (nOut + gs'.length) hlt1
                rw [hst1eq, hrun_append] at hw0
                have hlenrun : (run gs' (List.ofFn y)).length = nOut + gs'.length := by
                  rw [hrun_len, List.length_ofFn]
                have hw_eval : (run [⟨GateOp.or, [wa, wb]⟩] (run gs' (List.ofFn y))).getD (nOut + gs'.length) false =
                    ((run gs' (List.ofFn y)).getD wa false || ((run gs' (List.ofFn y)).getD wb false || false)) := by
                  rw [← hlenrun]
                  exact hgetD_append_len (run gs' (List.ofFn y)) _ false
                have hwa_bd := hget_bound a wa hga
                have hwb_bd := hget_bound b wb hgb
                have hwa_eq : (run gs' (List.ofFn y)).getD wa false = WF.getD wa false := by
                  have hwa1 : WF.getD wa false = (run (compileStep nOut (env, gs') ⟨GateOp.or, [a, b]⟩).2 (List.ofFn y)).getD wa false :=
                    hWF wa (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                  rw [hst1eq, hrun_append] at hwa1
                  have hp := hrun_preserves [⟨GateOp.or, [wa, wb]⟩] (run gs' (List.ofFn y)) wa (by rw [hlenrun]; exact hwa_bd)
                  rw [hp] at hwa1
                  exact hwa1.symm
                have hwb_eq : (run gs' (List.ofFn y)).getD wb false = WF.getD wb false := by
                  have hwb1 : WF.getD wb false = (run (compileStep nOut (env, gs') ⟨GateOp.or, [a, b]⟩).2 (List.ofFn y)).getD wb false :=
                    hWF wb (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                  rw [hst1eq, hrun_append] at hwb1
                  have hp := hrun_preserves [⟨GateOp.or, [wa, wb]⟩] (run gs' (List.ofFn y)) wb (by rw [hlenrun]; exact hwb_bd)
                  rw [hp] at hwb1
                  exact hwb1.symm
                dsimp [evalVal] at hsa hsb ⊢
                rw [hw0, hw_eval, hwa_eq, hwb_eq, hsa, hsb]
        · cases ins with
          | nil => rfl
          | cons a t =>
            have hsa := hsem a
            dsimp [evalOne]
            change _ = !(w.getD a false)
            cases hga : env.getD a (Sum.inl false) with
            | inl ba =>
              rw [hga] at hsa
              dsimp [evalVal] at hsa ⊢
              rw [hsa]
            | inr wa =>
              rw [hga] at hsa
              have hst1eq : (compileStep nOut (env, gs') ⟨GateOp.not, a :: t⟩).2 = gs' ++ [⟨GateOp.not, [wa]⟩] := by
                dsimp [compileStep, evalOne]
                rw [hga]
              have hlt1 : nOut + gs'.length < nOut + (compileStep nOut (env, gs') ⟨GateOp.not, a :: t⟩).2.length := by
                rw [hst1eq, List.length_append, List.length_singleton]; omega
              have hw0 := hWF (nOut + gs'.length) hlt1
              rw [hst1eq, hrun_append] at hw0
              have hlenrun : (run gs' (List.ofFn y)).length = nOut + gs'.length := by
                rw [hrun_len, List.length_ofFn]
              have hw_eval : (run [⟨GateOp.not, [wa]⟩] (run gs' (List.ofFn y))).getD (nOut + gs'.length) false =
                  !((run gs' (List.ofFn y)).getD wa false) := by
                rw [← hlenrun]
                exact hgetD_append_len (run gs' (List.ofFn y)) _ false
              have hwa_bd := hget_bound a wa hga
              have hwa_eq : (run gs' (List.ofFn y)).getD wa false = WF.getD wa false := by
                have hwa1 : WF.getD wa false = (run (compileStep nOut (env, gs') ⟨GateOp.not, a :: t⟩).2 (List.ofFn y)).getD wa false :=
                  hWF wa (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                rw [hst1eq, hrun_append] at hwa1
                have hp := hrun_preserves [⟨GateOp.not, [wa]⟩] (run gs' (List.ofFn y)) wa (by rw [hlenrun]; exact hwa_bd)
                rw [hp] at hwa1
                exact hwa1.symm
              dsimp [evalVal] at hsa ⊢
              rw [hw0, hw_eval, hwa_eq, hsa]
      · have hgt1 : st1.1.length ≤ m := by
          dsimp [st1, compileStep]
          cases (evalOne nOut ⟨op, ins⟩ env gs').2 <;> simp <;> omega
        have hgt2 : (step w ⟨op, ins⟩).length ≤ m := by
          rw [hstep_len]
          omega
        change evalVal WF (st1.1.getD m (Sum.inl false)) = (step w ⟨op, ins⟩).getD m false
        rw [List.getD_eq_default _ _ hgt1, List.getD_eq_default _ _ hgt2]
  have hcomp_sem : ∀ (nOut boundW : ℕ) (isZ : ℕ → Bool) (hisZ : ∀ w, isZ w = true → w < boundW)
      (y : Fin nOut → Bool) (gs : List Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate) (w : List Bool),
      boundW ≤ env.length →
      env.length = w.length →
      (∀ w', isZ w' = true → ∃ b, env.getD w' (Sum.inl false) = Sum.inl b) →
      (∀ v ∈ env, ∀ j, v = Sum.inr j → j < nOut + gs'.length) →
      (∀ g' ∈ gs', fanOK g') →
      (∀ g ∈ gs, fanOK g) →
      (∀ m, evalVal (run (compileLoop nOut gs (env, gs')).2 (List.ofFn y)) (env.getD m (Sum.inl false)) = w.getD m false) →
      ∀ m, evalVal (run (compileLoop nOut gs (env, gs')).2 (List.ofFn y)) ((compileLoop nOut gs (env, gs')).1.getD m (Sum.inl false)) =
        (run gs w).getD m false := by
    intro nOut boundW isZ hisZ y gs
    induction gs with
    | nil =>
      intro env gs' w _ _ _ _ _ _ hsem m
      exact hsem m
    | cons g gs ih =>
      intro env gs' w hlen hwl hZ hbound hfg hgs hsem m
      have hgfan : fanOK g := hgs g List.mem_cons_self
      have hgs_tail : ∀ h ∈ gs, fanOK h := fun h hh => hgs h (List.mem_cons_of_mem _ hh)
      obtain ⟨_, _, hfg1, hbound1, hlen1, hZ'⟩ :=
        hcomp_step_props nOut boundW isZ hisZ g env gs' hgfan hlen hZ hbound hfg
      let st1 := compileStep nOut (env, gs') g
      have hstr_tail := hcomp_struct nOut boundW isZ hisZ gs st1.1 st1.2 (by dsimp [st1]; omega) hZ' hbound1 hfg1 hgs_tail
      obtain ⟨ext2, hext2⟩ := hstr_tail.1
      have hfold : compileLoop nOut (g :: gs) (env, gs') = compileLoop nOut gs st1 := rfl
      rw [hfold]
      let WF := run (compileLoop nOut gs st1).2 (List.ofFn y)
      have hWF_pres : ∀ k, k < nOut + st1.2.length → WF.getD k false = (run st1.2 (List.ofFn y)).getD k false := by
        intro k hk
        change (run (compileLoop nOut gs st1).2 (List.ofFn y)).getD k false = _
        rw [hext2, hrun_append]
        exact hrun_preserves ext2 (run st1.2 (List.ofFn y)) k (by rw [hrun_len, List.length_ofFn]; exact hk)
      have hsem1 : ∀ k, evalVal WF (st1.1.getD k (Sum.inl false)) = (step w g).getD k false :=
        hcomp_step_sem nOut y g env gs' w WF hgfan hwl hbound hWF_pres hsem
      exact ih st1.1 st1.2 (step w g) (by change st1.1.length = env.length + 1 at hlen1; omega)
        (by rw [hstep_len, ← hwl]; exact hlen1)
        hZ' hbound1 hfg1 hgs_tail hsem1 m
  let remapPi : (Fin 10 → Fin 10) → ℕ → ℕ := fun π i => if h : i < 10 then (π ⟨i, h⟩).val else i
  let mapPi : (Fin 10 → Fin 10) → Gate → Gate := fun π g => ⟨g.op, g.inputs.map (remapPi π)⟩
  have hremap_run : ∀ (π : Fin 10 → Fin 10) (gs : List Gate) (u v : List Bool),
      u.length = v.length → 10 ≤ u.length →
      (∀ j, v.getD j false = u.getD (remapPi π j) false) →
      ∀ m, (run gs v).getD m false = (run (gs.map (mapPi π)) u).getD (remapPi π m) false := by
    intro π gs
    induction gs with
    | nil =>
      intro u v _ _ hmap m
      exact hmap m
    | cons g gs ih =>
      intro u v hlen hu hmap m
      let g' : Gate := mapPi π g
      have hstep_map : ∀ j, (step v g).getD j false = (step u g').getD (remapPi π j) false := by
        intro j
        by_cases hj : j < v.length
        · have hrm_lt : remapPi π j < u.length := by
            dsimp [remapPi]
            split_ifs with hlt10
            · have := (π ⟨j, hlt10⟩).isLt; omega
            · omega
          rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hrm_lt]
          exact hmap j
        · by_cases hjv : j = v.length
          · subst hjv
            have hrm : remapPi π v.length = u.length := by
              dsimp [remapPi]
              split_ifs <;> omega
            have hs1 : (step v g).getD v.length false = g.op.eval (g.inputs.map fun i => v.getD i false) :=
              hgetD_append_len v _ false
            have hs2 : (step u g').getD u.length false = g'.op.eval (g'.inputs.map fun i => u.getD i false) :=
              hgetD_append_len u _ false
            rw [hrm, hs1, hs2]
            change g.op.eval (g.inputs.map fun i => v.getD i false) =
              g.op.eval ((g.inputs.map (remapPi π)).map fun i => u.getD i false)
            rw [List.map_map]
            have harg : (g.inputs.map fun i => v.getD i false) =
                (g.inputs.map fun i => u.getD (remapPi π i) false) := by
              apply List.map_congr_left
              intro i _
              exact hmap i
            rw [harg]; rfl
          · have hrm_ge : (step u g').length ≤ remapPi π j := by
              rw [hstep_len]
              dsimp [remapPi]
              split_ifs <;> omega
            rw [List.getD_eq_default (step v g) false (by rw [hstep_len]; omega),
              List.getD_eq_default (step u g') false hrm_ge]
      exact ih (step u g') (step v g) (by rw [hstep_len, hstep_len, hlen]) (by rw [hstep_len]; omega) hstep_map m
  have hremap_eff_contains : ∀ (π πInv : Fin 10 → Fin 10),
      (∀ k, π (πInv k) = k) → (∀ k, πInv (π k) = k) →
      ∀ (gs : List Gate) (w : ℕ),
      (gs.map (mapPi π)).countP (fun g => (effInputs g).contains w) =
        gs.countP (fun g => (effInputs g).contains (remapPi πInv w)) := by
    intro π πInv h12 h21 gs w
    rw [List.countP_map]
    apply List.countP_congr
    intro g _
    have heff : effInputs (mapPi π g) = (effInputs g).map (remapPi π) := by
      dsimp only [effInputs, mapPi]
      cases g.op.eval [false] <;> simp [List.map_take]
    dsimp only [Function.comp_apply]
    rw [heff]
    simp only [List.contains_eq_mem, List.mem_map, decide_eq_true_eq]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hinv : remapPi πInv (remapPi π a) = a := by
        dsimp [remapPi]
        by_cases ha10 : a < 10
        · rw [dif_pos ha10, dif_pos (π ⟨a, ha10⟩).isLt]
          exact congrArg Fin.val (h21 ⟨a, ha10⟩)
        · rw [dif_neg ha10, dif_neg ha10]
      rw [hinv]
      exact ha
    · intro hw
      refine ⟨remapPi πInv w, hw, ?_⟩
      dsimp [remapPi]
      by_cases hw10 : w < 10
      · rw [dif_pos hw10, dif_pos (πInv ⟨w, hw10⟩).isLt]
        exact congrArg Fin.val (h12 ⟨w, hw10⟩)
      · rw [dif_neg hw10, dif_neg hw10]
  have hmove_to_9 : ∀ (v : Fin 10) (E : Circuit) (u' : ℕ) (b' : Bool),
      FanInTwo E → E.size ≤ 15 →
      (∀ x : Fin 10 → Bool, x v = false →
        (if b' = true then !((E.wires (List.ofFn x)).getD u' false) else (E.wires (List.ofFn x)).getD u' false) = G5 x) →
      ∃ (E' : Circuit) (u'' : ℕ) (b'' : Bool),
        FanInTwo E' ∧ E'.size ≤ 15 ∧
        ∀ x : Fin 10 → Bool, x 9 = false →
          (if b'' = true then !((E'.wires (List.ofFn x)).getD u'' false) else (E'.wires (List.ofFn x)).getD u'' false) = f10 x := by
    intro v E u' b' hfanE hszE hEeq
    let π := sigma9 v
    let πInv := sigma9Inv v
    let E' : Circuit := ⟨E.gates.map (mapPi π), remapPi π u'⟩
    have hfanE' : FanInTwo E' := by
      intro g hg
      rw [List.mem_map] at hg
      rcases hg with ⟨g0, hg0, rfl⟩
      exact ⟨(hfanE g0 hg0).1, by simpa [mapPi] using (hfanE g0 hg0).2⟩
    have hszE' : E'.size ≤ 15 := by
      change (E.gates.map (mapPi π)).length ≤ 15
      rw [List.length_map]; exact hszE
    refine ⟨E', remapPi π u', b', hfanE', hszE', ?_⟩
    intro x hx9
    have hx_v : (x ∘ π) v = false := by
      change x (π v) = false
      have hpv : π v = 9 := hs9_self v
      rw [hpv, hx9]
    have hE'eval : (E'.wires (List.ofFn x)).getD (remapPi π u') false =
        (E.wires (List.ofFn (x ∘ π))).getD u' false := by
      change (run (E.gates.map (mapPi π)) (List.ofFn x)).getD (remapPi π u') false =
        (run E.gates (List.ofFn (x ∘ π))).getD u' false
      refine (hremap_run π E.gates (List.ofFn x) (List.ofFn (x ∘ π)) (by simp) (by simp) (fun j => ?_) u').symm
      by_cases hj10 : j < 10
      · have hrm : remapPi π j = (π ⟨j, hj10⟩).val := by dsimp [remapPi]; rw [dif_pos hj10]
        rw [hrm, hgetFn10' x (π ⟨j, hj10⟩), hgetFn10Nat (x ∘ π) j hj10]
        rfl
      · have hrm : remapPi π j = j := by dsimp [remapPi]; rw [dif_neg hj10]
        rw [hrm, List.getD_eq_default (List.ofFn (x ∘ π)) false (by rw [List.length_ofFn]; omega),
          List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega)]
    rw [hE'eval, hEeq (x ∘ π) hx_v, hG5_sigma9 v x, hG5_eq]
  -- Dead gate erasure
  let shiftIdx (k : ℕ) (i : ℕ) : ℕ := if k < i then i - 1 else i
  let shiftG (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftIdx k)⟩
  have herase_mid : ∀ (A : List Bool) (val : Bool) (T : List Bool), (A ++ val :: T).eraseIdx A.length = A ++ T := by
    intro A val T
    induction A with
    | nil => rfl
    | cons a As ih => simp [ih]
  have hshift_erase : ∀ (k : ℕ) (A : List Bool) (hA : A.length = k) (val : Bool) (post : List Gate) (T : List Bool),
      (∀ g ∈ post, ¬((effInputs g).contains k)) →
      (∀ g ∈ post, fanOK g) →
      run (post.map (shiftG k)) (A ++ T) = (run post (A ++ val :: T)).eraseIdx k := by
    intro k A hA val post
    induction post with
    | nil =>
      intro T _ _
      dsimp [run]
      rw [← hA, herase_mid]
      rfl
    | cons g post ih =>
      intro T hpost hfan_post
      have hgk : ¬((effInputs g).contains k) := hpost g List.mem_cons_self
      have heval_eq : (shiftG k g).op.eval ((shiftG k g).inputs.map fun i => (A ++ T).getD i false) =
          g.op.eval (g.inputs.map fun i => (A ++ val :: T).getD i false) := by
        dsimp [shiftG]
        have hpt : ∀ j ∈ effInputs g, (A ++ T).getD (shiftIdx k j) false = (A ++ val :: T).getD j false := by
          intro j hj
          have hne : j ≠ k := by
            intro heq
            apply hgk
            subst heq
            exact List.contains_iff_mem.mpr hj
          dsimp [shiftIdx]
          by_cases hlt : k < j
          · rw [if_pos hlt]
            rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
            obtain ⟨t, rfl⟩ : ∃ t, j = k + 1 + t := ⟨j - k - 1, by omega⟩
            have h1' : k + 1 + t - 1 - A.length = t := by omega
            have h2' : k + 1 + t - A.length = t + 1 := by omega
            rw [h1', h2']
            simp
          · rw [if_neg hlt]
            have hjk : j < k := by omega
            rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        cases g
        rename_i op ins
        rcases (hfan_post ⟨op, ins⟩ List.mem_cons_self).1 with rfl | rfl | rfl
        · have hm : (ins.map (shiftIdx k)).map (fun i => (A ++ T).getD i false) = ins.map (fun i => (A ++ val :: T).getD i false) := by
            rw [List.map_map]; apply List.map_congr_left; intro j hj; exact hpt j hj
          rw [hm]
        · have hm : (ins.map (shiftIdx k)).map (fun i => (A ++ T).getD i false) = ins.map (fun i => (A ++ val :: T).getD i false) := by
            rw [List.map_map]; apply List.map_congr_left; intro j hj; exact hpt j hj
          rw [hm]
        · cases ins with
          | nil => rfl
          | cons a t =>
            have ha := hpt a (by change a ∈ [a]; simp)
            change Bool.not (((A ++ T).getD (shiftIdx k a) false :: _).headD false) = Bool.not (((A ++ val :: T).getD a false :: _).headD false)
            rw [List.headD_cons, List.headD_cons, ha]
      rw [List.map_cons, hrun_cons, hrun_cons]
      dsimp [step]
      rw [heval_eq]
      have hrest := ih (T ++ [g.op.eval (g.inputs.map fun i => (A ++ val :: T).getD i false)])
        (fun g' hg' => hpost g' (List.mem_cons_of_mem _ hg'))
        (fun g' hg' => hfan_post g' (List.mem_cons_of_mem _ hg'))
      simpa [List.append_assoc] using hrest
  have herase_dead_run : ∀ (pre : List Gate) (gm : Gate) (post : List Gate) (w0 : List Bool) (uOut : ℕ),
      uOut ≠ w0.length + pre.length →
      (∀ g ∈ post, ¬((effInputs g).contains (w0.length + pre.length))) →
      (∀ g ∈ post, fanOK g) →
      let k := w0.length + pre.length
      let gsNew := pre ++ post.map (shiftG k)
      (run gsNew w0).getD (shiftIdx k uOut) false = (run (pre ++ gm :: post) w0).getD uOut false := by
    intro pre gm post w0 uOut hu hpost hfan_post
    let k := w0.length + pre.length
    have hA : (run pre w0).length = k := hrun_len pre w0
    have hlhs : run (pre ++ post.map (shiftG k)) w0 = (run (post) (run pre w0 ++ [gm.op.eval (gm.inputs.map fun i => (run pre w0).getD i false)])).eraseIdx k := by
      rw [hrun_append]
      simpa using hshift_erase k (run pre w0) hA (gm.op.eval (gm.inputs.map fun i => (run pre w0).getD i false)) post [] hpost hfan_post
    have hrhs : run (pre ++ gm :: post) w0 = run post (run pre w0 ++ [gm.op.eval (gm.inputs.map fun i => (run pre w0).getD i false)]) := by
      rw [hrun_append, hrun_cons]
    dsimp only
    rw [hlhs, hrhs]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
    dsimp [shiftIdx]
    split_ifs with h1 h2 h3
    · exfalso; omega
    · have hsub : uOut - 1 + 1 = uOut := by omega
      rw [hsub]
    · rfl
    · exfalso; omega
  have hsplit_first : ∀ (p : Gate → Bool) (gs : List Gate), (∃ g ∈ gs, p g = true) →
      ∃ pre gm post, gs = pre ++ gm :: post ∧ p gm = true ∧ (∀ g ∈ pre, p g = false) := by
    intro p gs
    induction gs with
    | nil => intro hex; rcases hex with ⟨g, hg, _⟩; cases hg
    | cons g tl ih =>
      intro hex
      cases hpg : p g with
      | true => exact ⟨[], g, tl, rfl, hpg, fun _ h => by cases h⟩
      | false =>
        have htl : ∃ a ∈ tl, p a = true := by
          rcases hex with ⟨a, ha, hpa⟩
          rcases List.mem_cons.mp ha with rfl | hat
          · rw [hpg] at hpa; cases hpa
          · exact ⟨a, hat, hpa⟩
        obtain ⟨pre, gm, post, htl_eq, hgm, hpre⟩ := ih htl
        refine ⟨g :: pre, gm, post, by rw [htl_eq]; rfl, hgm, ?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | hap
        · exact hpg
        · exact hpre a hap
  -- Case 1: gs.length <= 16 computing G5 on all inputs
  have h1_le16 : ∀ (gs : List Gate) (u : ℕ) (b : Bool),
      (∀ g ∈ gs, fanOK g) → gs.length ≤ 16 →
      (∀ x : Fin 10 → Bool, (if b = true then !((run gs (List.ofFn x)).getD u false) else (run gs (List.ofFn x)).getD u false) = G5 x) →
      ∃ (E : Circuit) (u' : ℕ) (b' : Bool),
        FanInTwo E ∧ E.size ≤ 15 ∧
        ∀ x : Fin 10 → Bool, x 9 = false →
          (if b' = true then !((E.wires (List.ofFn x)).getD u' false) else (E.wires (List.ofFn x)).getD u' false) = f10 x := by
    intro gs u b hfan hlen hcomp
    have hne : gs.countP (fun g => (effInputs g).contains 9) ≠ 0 := by
      intro hzero
      have hnone : ∀ g ∈ gs, ∀ i ∈ effInputs g, i ≠ 9 := by
        intro g hg i hi heq
        have hz := List.countP_eq_zero.mp hzero g hg
        apply hz
        rw [← heq]
        exact List.contains_iff_mem.mpr hi
      have hu9 : u ≠ 9 := by
        intro heq
        obtain ⟨x, hx⟩ := hP_not_lit 9 b
        have hc := hcomp x
        have hlen10 : (List.ofFn x).length = 10 := List.length_ofFn
        have h9 : (run gs (List.ofFn x)).getD 9 false = x 9 := by
          rw [hrun_preserves gs (List.ofFn x) 9 (by rw [hlen10]; decide), hgetFn10Nat x 9 (by decide)]; rfl
        rw [heq, h9] at hc
        exact hx hc
      obtain ⟨a, hav, haG⟩ := hP_dep 9
      apply haG
      let xA : Fin 10 → Bool := fun k => decide (k = a)
      let xB : Fin 10 → Bool := fun k => decide (k = 9 ∨ k = a)
      have hcA := hcomp xA
      have hcB := hcomp xB
      have hagree : (run gs (List.ofFn xA)).getD u false = (run gs (List.ofFn xB)).getD u false := by
        apply hcomp_init_Agree (List.ofFn xA) (List.ofFn xB) gs (fun i => i = 9) u (by simp) hu9
        · intro i hi
          by_cases hi10 : i < 10
          · rw [hgetFn10Nat xA i hi10, hgetFn10Nat xB i hi10]
            have h9ne : (⟨i, hi10⟩ : Fin 10) ≠ 9 := fun h => hi (congrArg Fin.val h)
            dsimp [xA, xB]
            simp [h9ne]
          · rw [List.getD_eq_default (List.ofFn xA) false (by rw [List.length_ofFn]; omega),
              List.getD_eq_default (List.ofFn xB) false (by rw [List.length_ofFn]; omega)]
        · exact hnone
        · exact hfan
      rw [← hcA, ← hcB, hagree]
    have hge1 : 1 ≤ gs.countP (fun g => (effInputs g).contains 9) := by omega
    let env0 : List (Sum Bool ℕ) := (List.finRange 10).map fun k : Fin 10 =>
      if k.val = 9 then Sum.inl false else Sum.inr k.val
    have henv0_len : env0.length = 10 := by simp [env0]
    have hZ0 : ∀ w, (w == 9) = true → ∃ bv, env0.getD w (Sum.inl false) = Sum.inl bv := by
      intro w hw
      rw [beq_iff_eq] at hw; subst hw
      have h9 : 9 < env0.length := by rw [henv0_len]; decide
      refine ⟨false, ?_⟩
      rw [List.getD_eq_getElem _ _ h9]
      dsimp only [env0]
      rw [List.getElem_map, hfinRange10]
      rfl
    have hbound0 : ∀ v ∈ env0, ∀ j, v = Sum.inr j → j < 10 + ([] : List Gate).length := by
      intro v hv j hj
      dsimp [env0] at hv
      rw [List.mem_map] at hv
      rcases hv with ⟨k, _, rfl⟩
      split_ifs at hj
      cases hj
      exact k.isLt
    let res := compileLoop 10 gs (env0, [])
    have hstr := hcomp_struct 10 10 (fun w => w == 9) (fun w hw => by rw [beq_iff_eq] at hw; omega)
      gs env0 [] (by omega) hZ0 hbound0 (fun _ h => by cases h) hfan
    have hres_len : res.2.length ≤ 15 := by
      have hc := hstr.2.2.2.2
      rw [hcontains_eq_all gs 9] at hc
      change res.2.length + _ ≤ 0 + gs.length at hc
      omega
    have hsem0 : ∀ x : Fin 10 → Bool, x 9 = false →
        (if b = true then !(evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false)))
         else evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false))) = f10 x := by
      intro x hx9
      have hsem_in : ∀ m, evalVal (run res.2 (List.ofFn x)) (env0.getD m (Sum.inl false)) = (List.ofFn x).getD m false := by
        intro m
        by_cases hm : m < 10
        · have hme : m < env0.length := by rw [henv0_len]; exact hm
          rw [List.getD_eq_getElem _ _ hme]
          dsimp [env0]
          rw [List.getElem_map, hfinRange10]
          split_ifs with h9m
          · rw [hgetFn10Nat x m hm]
            have hmf : ⟨m, hm⟩ = (9 : Fin 10) := Fin.ext h9m
            rw [hmf, hx9]
          · change (run res.2 (List.ofFn x)).getD m false = (List.ofFn x).getD m false
            rw [hrun_preserves res.2 (List.ofFn x) m (by rw [List.length_ofFn]; exact hm)]
        · rw [List.getD_eq_default env0 (Sum.inl false) (by rw [henv0_len]; omega),
            List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega)]
      have hcs := hcomp_sem 10 10 (fun w => w == 9) (fun w hw => by rw [beq_iff_eq] at hw; omega)
        x gs env0 [] (List.ofFn x) (by omega) (by rw [henv0_len, List.length_ofFn])
        hZ0 hbound0 (fun _ h => by cases h) hfan hsem_in u
      rw [hcs, hcomp x, hG5_eq]
    cases huval : res.1.getD u (Sum.inl false) with
    | inl cv =>
      exfalso
      have h9f : (fun _ : Fin 10 => false) (9 : Fin 10) = false := rfl
      have hkf : (fun k : Fin 10 => decide (k ≠ 9)) (9 : Fin 10) = false := by decide
      have hc0 := hsem0 (fun _ => false) h9f
      have hc1 := hsem0 (fun k => decide (k ≠ 9)) hkf
      rw [huval] at hc0 hc1
      have hc0' := hc0.trans (hG5_eq (fun _ => false))
      have hc1' := hc1.trans (hG5_eq (fun k => decide (k ≠ 9)))
      have hne01 := hP_nonconst 9
      rw [← hc0', ← hc1'] at hne01
      exact hne01 rfl
    | inr outW =>
      refine ⟨⟨res.2, outW⟩, outW, b, hstr.2.1, hres_len, ?_⟩
      intro x hx9
      have hc := hsem0 x hx9
      rw [huval] at hc
      exact hc
  -- Case 2: gs.length <= 17 computing G5 on all inputs
  have h1_core : ∀ (gs : List Gate) (u : ℕ) (b : Bool),
      (∀ g ∈ gs, fanOK g) → gs.length ≤ 17 →
      (∀ x : Fin 10 → Bool, (if b = true then !((run gs (List.ofFn x)).getD u false) else (run gs (List.ofFn x)).getD u false) = G5 x) →
      ∃ (E : Circuit) (u' : ℕ) (b' : Bool),
        FanInTwo E ∧ E.size ≤ 15 ∧
        ∀ x : Fin 10 → Bool, x 9 = false →
          (if b' = true then !((E.wires (List.ofFn x)).getD u' false) else (E.wires (List.ofFn x)).getD u' false) = f10 x := by
    intro gs u b hfan hlen hcomp
    by_cases h16 : gs.length ≤ 16
    · exact h1_le16 gs u b hfan h16 hcomp
    · have h17 : gs.length = 17 := by omega
      -- using hcontains_eq_all
      by_cases hge2 : ∃ v : Fin 10, 2 ≤ gs.countP (fun g => (effInputs g).contains v.val)
      · obtain ⟨v, hv2⟩ := hge2
        let env0 : List (Sum Bool ℕ) := (List.finRange 10).map fun k : Fin 10 =>
          if k = v then Sum.inl false else Sum.inr k.val
        have henv0_len : env0.length = 10 := by simp [env0]
        have hZ0 : ∀ w, (w == v.val) = true → ∃ bv, env0.getD w (Sum.inl false) = Sum.inl bv := by
          intro w hw
          rw [beq_iff_eq] at hw; subst hw
          have hlt : v.val < env0.length := by rw [henv0_len]; exact v.isLt
          refine ⟨false, ?_⟩
          rw [List.getD_eq_getElem _ _ hlt]
          dsimp [env0]
          rw [List.getElem_map, hfinRange10]
          have hveq : (⟨v.val, v.isLt⟩ : Fin 10) = v := Fin.ext rfl
          rw [hveq, if_pos rfl]
        have hbound0 : ∀ x ∈ env0, ∀ j, x = Sum.inr j → j < 10 + ([] : List Gate).length := by
          intro x hx j hj
          dsimp [env0] at hx
          rw [List.mem_map] at hx
          rcases hx with ⟨k, _, rfl⟩
          split_ifs at hj
          cases hj
          exact k.isLt
        let res := compileLoop 10 gs (env0, [])
        have hstr := hcomp_struct 10 10 (fun w => w == v.val) (fun w hw => by rw [beq_iff_eq] at hw; have := v.isLt; omega)
          gs env0 [] (by omega) hZ0 hbound0 (fun _ h => by cases h) hfan
        have hres_len : res.2.length ≤ 15 := by
          have hc := hstr.2.2.2.2
          rw [hcontains_eq_all gs v.val] at hc
          change res.2.length + _ ≤ 0 + gs.length at hc
          omega
        have hsem0 : ∀ x : Fin 10 → Bool, x v = false →
            (if b = true then !(evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false)))
             else evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false))) = G5 x := by
          intro x hxv
          have hsem_in : ∀ m, evalVal (run res.2 (List.ofFn x)) (env0.getD m (Sum.inl false)) = (List.ofFn x).getD m false := by
            intro m
            by_cases hm : m < 10
            · have hme : m < env0.length := by rw [henv0_len]; exact hm
              rw [List.getD_eq_getElem _ _ hme]
              dsimp [env0]
              rw [List.getElem_map, hfinRange10]
              split_ifs with hkv
              · rw [hgetFn10Nat x m hm, hkv, hxv]
              · change (run res.2 (List.ofFn x)).getD m false = (List.ofFn x).getD m false
                rw [hrun_preserves res.2 (List.ofFn x) m (by rw [List.length_ofFn]; exact hm)]
            · rw [List.getD_eq_default env0 (Sum.inl false) (by rw [henv0_len]; omega),
                List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega)]
          have hcs := hcomp_sem 10 10 (fun w => w == v.val) (fun w hw => by rw [beq_iff_eq] at hw; have := v.isLt; omega)
            x gs env0 [] (List.ofFn x) (by omega) (by rw [henv0_len, List.length_ofFn])
            hZ0 hbound0 (fun _ h => by cases h) hfan hsem_in u
          rw [hcs, hcomp x]
        cases huval : res.1.getD u (Sum.inl false) with
        | inl cv =>
          exfalso
          have hc0 := hsem0 (fun _ => false) rfl
          have hc1 := hsem0 (fun k => decide (k ≠ v)) (by simp)
          rw [huval] at hc0 hc1
          have hne01 := hP_nonconst v
          rw [← hc0, ← hc1] at hne01
          exact hne01 rfl
        | inr outW =>
          exact hmove_to_9 v ⟨res.2, outW⟩ outW b hstr.2.1 hres_len (fun x hxv => by have hc := hsem0 x hxv; rw [huval] at hc; exact hc)
      · have hle1 : ∀ v : Fin 10, gs.countP (fun g => (effInputs g).contains v.val) ≤ 1 := by
          intro v
          exact Nat.le_of_not_gt (fun hgt => hge2 ⟨v, hgt⟩)
        have hnz : ∀ v : Fin 10, gs.countP (fun g => (effInputs g).contains v.val) ≠ 0 := by
          intro v hzero
          have hnone : ∀ g ∈ gs, ∀ i ∈ effInputs g, i ≠ v.val := by
            intro g hg i hi heq
            have hz := List.countP_eq_zero.mp hzero g hg
            apply hz; rw [← heq]; exact List.contains_iff_mem.mpr hi
          have huv : u ≠ v.val := by
            intro heq
            obtain ⟨x, hx⟩ := hP_not_lit v b
            have hc := hcomp x
            have hv : (run gs (List.ofFn x)).getD v.val false = x v := by
              rw [hrun_preserves gs (List.ofFn x) v.val (by rw [List.length_ofFn]; exact v.isLt), hgetFn10' x v]
            rw [heq, hv] at hc
            exact hx hc
          obtain ⟨a, hav, haG⟩ := hP_dep v
          apply haG
          let xA : Fin 10 → Bool := fun k => decide (k = a)
          let xB : Fin 10 → Bool := fun k => decide (k = v ∨ k = a)
          have hagree : (run gs (List.ofFn xA)).getD u false = (run gs (List.ofFn xB)).getD u false := by
            apply hcomp_init_Agree (List.ofFn xA) (List.ofFn xB) gs (fun i => i = v.val) u (by simp) huv
            · intro i hi
              by_cases hi10 : i < 10
              · rw [hgetFn10Nat xA i hi10, hgetFn10Nat xB i hi10]
                have hvne : (⟨i, hi10⟩ : Fin 10) ≠ v := fun h => hi (congrArg Fin.val h)
                dsimp [xA, xB]; simp [hvne]
              · rw [List.getD_eq_default (List.ofFn xA) false (by rw [List.length_ofFn]; omega),
                  List.getD_eq_default (List.ofFn xB) false (by rw [List.length_ofFn]; omega)]
            · exact hnone
            · exact hfan
          rw [← hcomp xA, ← hcomp xB, hagree]
        have heq1 : ∀ v : Fin 10, gs.countP (fun g => (effInputs g).contains v.val) = 1 := by
          intro v; have := hle1 v; have := hnz v; omega
        let constAt (v : Fin 10) : Prop :=
          ∃ (pre : List Gate) (gm : Gate) (post : List Gate) (cv : Bool), gs = pre ++ gm :: post ∧ (effInputs gm).contains v.val = true ∧
            (∀ g ∈ pre, ¬((effInputs g).contains v.val)) ∧
            (∀ g ∈ post, ¬((effInputs g).contains v.val)) ∧
            let env0 : List (Sum Bool ℕ) := (List.finRange 10).map fun k : Fin 10 =>
              if k = v then Sum.inl false else Sum.inr k.val
            let stPre := compileLoop 10 pre (env0, [])
            evalOne 10 gm stPre.1 stPre.2 = (Sum.inl cv, none)
        by_cases hcol : ∃ v : Fin 10, constAt v
        · obtain ⟨v, pre, gm, post, cv, hgs_eq, hgm_v, hpre_nv, hpost_nv, hconstGm⟩ := hcol
          let env0 : List (Sum Bool ℕ) := (List.finRange 10).map fun k : Fin 10 =>
            if k = v then Sum.inl false else Sum.inr k.val
          have henv0_len : env0.length = 10 := by simp [env0]
          have hZ0 : ∀ w, (w == v.val) = true → ∃ bv, env0.getD w (Sum.inl false) = Sum.inl bv := by
            intro w hw
            rw [beq_iff_eq] at hw; subst hw
            have hlt : v.val < env0.length := by rw [henv0_len]; exact v.isLt
            refine ⟨false, ?_⟩
            rw [List.getD_eq_getElem _ _ hlt]
            dsimp [env0]
            rw [List.getElem_map, hfinRange10]
            have hveq : (⟨v.val, v.isLt⟩ : Fin 10) = v := Fin.ext rfl
            rw [hveq, if_pos rfl]
          have hbound0 : ∀ x ∈ env0, ∀ j, x = Sum.inr j → j < 10 + ([] : List Gate).length := by
            intro x hx j hj
            dsimp [env0] at hx
            rw [List.mem_map] at hx
            rcases hx with ⟨k, _, rfl⟩
            split_ifs at hj
            cases hj
            exact k.isLt
          have hfan_pre : ∀ g ∈ pre, fanOK g := fun g hg => hfan g (by rw [hgs_eq]; exact List.mem_append_left _ hg)
          have hfan_gm : fanOK gm := hfan gm (by rw [hgs_eq]; exact List.mem_append_right _ List.mem_cons_self)
          have hfan_post : ∀ g ∈ post, fanOK g := fun g hg => hfan g (by rw [hgs_eq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
          let stPre := compileLoop 10 pre (env0, [])
          have hstrPre := hcomp_struct 10 10 (fun w => w == v.val) (fun w hw => by rw [beq_iff_eq] at hw; have := v.isLt; omega)
            pre env0 [] (by omega) hZ0 hbound0 (fun _ h => by cases h) hfan_pre
          have hstPre_len1 : stPre.1.length = 10 + pre.length := by
            have := hstrPre.2.2.2.1; rw [henv0_len] at this; exact this
          have hstPre_len2 : stPre.2.length ≤ pre.length := by
            have := hstrPre.2.2.2.2; change stPre.2.length + _ ≤ 0 + pre.length at this; omega
          let kWire := 10 + pre.length
          let st1 := compileStep 10 stPre gm
          have hst1_eq : st1 = (stPre.1 ++ [Sum.inl cv], stPre.2) := by
            dsimp [st1, compileStep]
            rw [hconstGm]
          have hst1_2 : st1.2 = stPre.2 := by rw [hst1_eq]
          have hst1_1 : st1.1 = stPre.1 ++ [Sum.inl cv] := by rw [hst1_eq]
          have hst1_len1 : st1.1.length = kWire + 1 := by
            rw [hst1_1, List.length_append, List.length_singleton, hstPre_len1]
          have hst1_bound : ∀ a ∈ st1.1, ∀ j, a = Sum.inr j → j < 10 + st1.2.length := by
            intro a ha j hj
            rw [hst1_1, List.mem_append, List.mem_singleton] at ha
            rw [hst1_2]
            rcases ha with ha | rfl
            · exact hstrPre.2.2.1 a ha j hj
            · cases hj
          have hZk : ∀ w, (w == kWire) = true → ∃ bv, st1.1.getD w (Sum.inl false) = Sum.inl bv := by
            intro w hw
            rw [beq_iff_eq] at hw; subst hw
            refine ⟨cv, ?_⟩
            rw [hst1_1]; dsimp [kWire]; rw [← hstPre_len1, hgetD_append_len]; rfl
          by_cases hpost_k : 1 ≤ post.countP (fun g => (effInputs g).contains kWire)
          · let res := compileLoop 10 post st1
            have hstrPost := hcomp_struct 10 (kWire + 1) (fun w => w == kWire) (fun w hw => by rw [beq_iff_eq] at hw; omega)
              post st1.1 st1.2 (by omega) hZk hst1_bound (by rw [hst1_2]; exact hstrPre.2.1) hfan_post
            have hcnt_post : post.countP (fun g => (effInputs g).any (fun w => w == kWire)) =
                post.countP (fun g => (effInputs g).contains kWire) := hcontains_eq_all post kWire
            have hres_len : res.2.length ≤ 15 := by
              have hlsum : gs.length = pre.length + 1 + post.length := by
                rw [hgs_eq, List.length_append, List.length_cons]; omega
              have hc := hstrPost.2.2.2.2
              rw [hcnt_post] at hc
              change res.2.length + _ ≤ st1.2.length + post.length at hc
              rw [hst1_2] at hc
              omega
            obtain ⟨ext1, hext1⟩ := hstrPre.1
            obtain ⟨ext2, hext2⟩ := hstrPost.1
            have hsem_res : ∀ x : Fin 10 → Bool, x v = false →
                (if b = true then !(evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false)))
                 else evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false))) = G5 x := by
              intro x hxv
              have hsem_in0 : ∀ m, evalVal (run res.2 (List.ofFn x)) (env0.getD m (Sum.inl false)) = (List.ofFn x).getD m false := by
                intro m
                by_cases hm : m < 10
                · have hme : m < env0.length := by rw [henv0_len]; exact hm
                  rw [List.getD_eq_getElem _ _ hme]
                  dsimp [env0]
                  rw [List.getElem_map, hfinRange10]
                  split_ifs with hkv
                  · rw [hgetFn10Nat x m hm, hkv, hxv]
                  · change (run res.2 (List.ofFn x)).getD m false = (List.ofFn x).getD m false
                    rw [hrun_preserves res.2 (List.ofFn x) m (by rw [List.length_ofFn]; exact hm)]
                · rw [List.getD_eq_default env0 (Sum.inl false) (by rw [henv0_len]; omega),
                    List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega)]
              have hWF_pre : ∀ k, k < 10 + stPre.2.length →
                  (run res.2 (List.ofFn x)).getD k false = (run stPre.2 (List.ofFn x)).getD k false := by
                intro k hk
                change (run res.2 (List.ofFn x)).getD k false = _
                have hres_eq : res.2 = stPre.2 ++ ext2 := by
                  change (compileLoop 10 post st1).2 = stPre.2 ++ ext2
                  rw [hext2, hst1_2]
                rw [hres_eq, hrun_append]
                exact hrun_preserves ext2 (run stPre.2 (List.ofFn x)) k (by rw [hrun_len, List.length_ofFn]; exact hk)
              have hsem_pre_WF : ∀ m, evalVal (run res.2 (List.ofFn x)) (stPre.1.getD m (Sum.inl false)) =
                  (run pre (List.ofFn x)).getD m false := by
                have hc_pre := hcomp_sem 10 10 (fun w => w == v.val) (fun w hw => by rw [beq_iff_eq] at hw; have := v.isLt; omega)
                  x pre env0 [] (List.ofFn x) (by omega) (by rw [henv0_len, List.length_ofFn])
                  hZ0 hbound0 (fun _ h => by cases h) hfan_pre
                have hsem_in_pre : ∀ m, evalVal (run stPre.2 (List.ofFn x)) (env0.getD m (Sum.inl false)) = (List.ofFn x).getD m false := by
                  intro m
                  by_cases hm : m < 10
                  · have hme : m < env0.length := by rw [henv0_len]; exact hm
                    rw [List.getD_eq_getElem _ _ hme]
                    dsimp [env0]
                    rw [List.getElem_map, hfinRange10]
                    split_ifs with hkv
                    · rw [hgetFn10Nat x m hm, hkv, hxv]
                    · change (run stPre.2 (List.ofFn x)).getD m false = (List.ofFn x).getD m false
                      rw [hrun_preserves stPre.2 (List.ofFn x) m (by rw [List.length_ofFn]; exact hm)]
                  · rw [List.getD_eq_default env0 (Sum.inl false) (by rw [henv0_len]; omega),
                      List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega)]
                intro m
                have hc1 := hc_pre hsem_in_pre m
                have heval_agree : evalVal (run res.2 (List.ofFn x)) (stPre.1.getD m (Sum.inl false)) =
                    evalVal (run stPre.2 (List.ofFn x)) (stPre.1.getD m (Sum.inl false)) := by
                  cases hmval : stPre.1.getD m (Sum.inl false) with
                  | inl bv => rfl
                  | inr j =>
                    have hjlt : j < 10 + stPre.2.length := by
                      have hmlt : m < stPre.1.length := by
                        refine Classical.byContradiction fun hge => ?_
                        rw [List.getD_eq_default stPre.1 (Sum.inl false) (by omega)] at hmval
                        cases hmval
                      rw [List.getD_eq_getElem _ _ hmlt] at hmval
                      exact hstrPre.2.2.1 _ (List.getElem_mem hmlt) j hmval
                    exact hWF_pre j hjlt
                exact heval_agree.trans hc1
              have hWF_st1 : ∀ k, k < 10 + st1.2.length →
                  (run res.2 (List.ofFn x)).getD k false = (run st1.2 (List.ofFn x)).getD k false := by
                rw [hst1_2]; exact hWF_pre
              have hsem_st1 : ∀ m, evalVal (run res.2 (List.ofFn x)) (st1.1.getD m (Sum.inl false)) =
                  (step (run pre (List.ofFn x)) gm).getD m false :=
                hcomp_step_sem 10 x gm stPre.1 stPre.2 (run pre (List.ofFn x)) (run res.2 (List.ofFn x))
                  hfan_gm (by rw [hstPre_len1, hrun_len, List.length_ofFn]) hstrPre.2.2.1
                  (by intro k hk; change (run res.2 (List.ofFn x)).getD k false = (run st1.2 (List.ofFn x)).getD k false; rw [hst1_2]; exact hWF_pre k (by rw [← hst1_2]; exact hk))
                  hsem_pre_WF
              have hcs_post := hcomp_sem 10 (kWire + 1) (fun w => w == kWire) (fun w hw => by rw [beq_iff_eq] at hw; omega)
                x post st1.1 st1.2 (step (run pre (List.ofFn x)) gm)
                (by omega) (by rw [hst1_len1, hstep_len, hrun_len, List.length_ofFn])
                hZk hst1_bound (by rw [hst1_2]; exact hstrPre.2.1) hfan_post hsem_st1 u
              have hgs_run : run post (step (run pre (List.ofFn x)) gm) = run gs (List.ofFn x) := by
                rw [hgs_eq, hrun_append, hrun_cons]
              rw [hcs_post, hgs_run, hcomp x]
            cases huval : res.1.getD u (Sum.inl false) with
            | inl cOut =>
              exfalso
              have hc0 := hsem_res (fun _ => false) rfl
              have hc1 := hsem_res (fun k => decide (k ≠ v)) (by simp)
              rw [huval] at hc0 hc1
              have hne01 := hP_nonconst v
              rw [← hc0, ← hc1] at hne01
              exact hne01 rfl
            | inr outW =>
              exact hmove_to_9 v ⟨res.2, outW⟩ outW b hstrPost.2.1 hres_len (fun x hxv => by have hc := hsem_res x hxv; rw [huval] at hc; exact hc)
          · have hpost_nk : ∀ g ∈ post, ¬((effInputs g).contains kWire) :=
              List.countP_eq_zero.mp (by omega)
            by_cases huk : u = kWire
            · exfalso
              have hconst_kWire : ∀ x : Fin 10 → Bool, x v = false →
                  (run gs (List.ofFn x)).getD kWire false = cv := by
                intro x hxv
                have hrun_eq : run gs (List.ofFn x) = run post (step (run pre (List.ofFn x)) gm) := by
                  rw [hgs_eq, hrun_append, hrun_cons]
                rw [hrun_eq, hrun_preserves post (step (run pre (List.ofFn x)) gm) kWire
                  (by rw [hstep_len, hrun_len, List.length_ofFn]; omega)]
                have hsem_in0 : ∀ m, evalVal (run stPre.2 (List.ofFn x)) (env0.getD m (Sum.inl false)) = (List.ofFn x).getD m false := by
                  intro m
                  by_cases hm : m < 10
                  · have hme : m < env0.length := by rw [henv0_len]; exact hm
                    rw [List.getD_eq_getElem _ _ hme]
                    dsimp [env0]
                    rw [List.getElem_map, hfinRange10]
                    split_ifs with hkv
                    · rw [hgetFn10Nat x m hm, hkv, hxv]
                    · change (run stPre.2 (List.ofFn x)).getD m false = (List.ofFn x).getD m false
                      rw [hrun_preserves stPre.2 (List.ofFn x) m (by rw [List.length_ofFn]; exact hm)]
                  · rw [List.getD_eq_default env0 (Sum.inl false) (by rw [henv0_len]; omega),
                      List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega)]
                have hsem_pre := hcomp_sem 10 10 (fun w => w == v.val) (fun w hw => by rw [beq_iff_eq] at hw; have := v.isLt; omega)
                  x pre env0 [] (List.ofFn x) (by omega) (by rw [henv0_len, List.length_ofFn])
                  hZ0 hbound0 (fun _ h => by cases h) hfan_pre hsem_in0
                have hWF_st1 : ∀ k, k < 10 + st1.2.length →
                    (run stPre.2 (List.ofFn x)).getD k false = (run st1.2 (List.ofFn x)).getD k false := by
                  rw [hst1_2]; intro k _; rfl
                have hsem_st1 := hcomp_step_sem 10 x gm stPre.1 stPre.2 (run pre (List.ofFn x)) (run stPre.2 (List.ofFn x))
                  hfan_gm (by rw [hstPre_len1, hrun_len, List.length_ofFn]) hstrPre.2.2.1
                  (by intro k _; change (run stPre.2 (List.ofFn x)).getD k false = (run st1.2 (List.ofFn x)).getD k false; rw [hst1_2])
                  hsem_pre kWire
                rw [← hsem_st1, hst1_1]; dsimp [kWire]; rw [← hstPre_len1, hgetD_append_len]; rfl
              have hc0 := hcomp (fun _ => false)
              have hc1 := hcomp (fun k => decide (k ≠ v))
              rw [huk, hconst_kWire _ rfl] at hc0
              rw [huk, hconst_kWire _ (by simp)] at hc1
              have hne01 := hP_nonconst v
              rw [← hc0, ← hc1] at hne01
              exact hne01 rfl
            · exfalso
              have huv : u ≠ v.val := by
                intro heq
                obtain ⟨x, hx⟩ := hP_not_lit v b
                have hc := hcomp x
                have hv : (run gs (List.ofFn x)).getD v.val false = x v := by
                  rw [hrun_preserves gs (List.ofFn x) v.val (by rw [List.length_ofFn]; exact v.isLt), hgetFn10' x v]
                rw [heq, hv] at hc
                exact hx hc
              obtain ⟨a, hav, haG⟩ := hP_dep v
              apply haG
              let xA : Fin 10 → Bool := fun k => decide (k = a)
              let xB : Fin 10 → Bool := fun k => decide (k = v ∨ k = a)
              have hpre_agree : ∀ i, i ≠ v.val → (run pre (List.ofFn xA)).getD i false = (run pre (List.ofFn xB)).getD i false := by
                intro i hi
                apply hcomp_init_Agree (List.ofFn xA) (List.ofFn xB) pre (fun w => w = v.val) i (by simp) hi
                · intro m hm
                  by_cases hm10 : m < 10
                  · rw [hgetFn10Nat xA m hm10, hgetFn10Nat xB m hm10]
                    have hvne : (⟨m, hm10⟩ : Fin 10) ≠ v := fun h => hm (congrArg Fin.val h)
                    dsimp [xA, xB]; simp [hvne]
                  · rw [List.getD_eq_default (List.ofFn xA) false (by rw [List.length_ofFn]; omega),
                      List.getD_eq_default (List.ofFn xB) false (by rw [List.length_ofFn]; omega)]
                · intro g hg w hw heq
                  exact hpre_nv g hg (heq ▸ List.contains_iff_mem.mpr hw)
                · exact hfan_pre
              have hpost_agree : (run post (step (run pre (List.ofFn xA)) gm)).getD u false =
                  (run post (step (run pre (List.ofFn xB)) gm)).getD u false := by
                apply hcomp_init_Agree (step (run pre (List.ofFn xA)) gm) (step (run pre (List.ofFn xB)) gm) post
                  (fun w => w = v.val ∨ w = kWire) u
                  (by rw [hstep_len, hstep_len, hrun_len, hrun_len, List.length_ofFn, List.length_ofFn])
                  (fun h => by rcases h with h1' | h2' <;> [exact huv h1'; exact huk h2'])
                · intro m hm
                  have hmv : m ≠ v.val := fun h => hm (Or.inl h)
                  have hmk : m ≠ kWire := fun h => hm (Or.inr h)
                  by_cases hmlt : m < kWire
                  · rw [hstep_pres _ _ _ (by rw [hrun_len, List.length_ofFn]; exact hmlt),
                      hstep_pres _ _ _ (by rw [hrun_len, List.length_ofFn]; exact hmlt)]
                    exact hpre_agree m hmv
                  · rw [List.getD_eq_default (step (run pre (List.ofFn xA)) gm) false (by rw [hstep_len, hrun_len, List.length_ofFn]; omega),
                      List.getD_eq_default (step (run pre (List.ofFn xB)) gm) false (by rw [hstep_len, hrun_len, List.length_ofFn]; omega)]
                · intro g hg w hw hmem
                  rcases hmem with rfl | rfl
                  · exact hpost_nv g hg (List.contains_iff_mem.mpr hw)
                  · exact hpost_nk g hg (List.contains_iff_mem.mpr hw)
                · exact hfan_post
              have hrunA : (run gs (List.ofFn xA)).getD u false = (run post (step (run pre (List.ofFn xA)) gm)).getD u false := by
                rw [hgs_eq, hrun_append, hrun_cons]
              have hrunB : (run gs (List.ofFn xB)).getD u false = (run post (step (run pre (List.ofFn xB)) gm)).getD u false := by
                rw [hgs_eq, hrun_append, hrun_cons]
              rw [← hcomp xA, ← hcomp xB, hrunA, hrunB, hpost_agree]
        · have hbad_or : ∀ v : Fin 10, ∀ pre gm post,
              gs = pre ++ gm :: post → (effInputs gm).contains v.val = true →
              (∀ g ∈ pre, ¬((effInputs g).contains v.val)) →
              (∀ g ∈ post, ¬((effInputs g).contains v.val)) →
              gm.op = GateOp.or ∧ ∃ y, y < 10 + pre.length ∧ y ≠ v.val ∧ (gm.inputs = [v.val, y] ∨ gm.inputs = [y, v.val]) := by
            intro v pre gm post hgs_eq hgm_v hpre_nv hpost_nv
            have hnotc : ¬ constAt v := fun h => hcol ⟨v, h⟩
            let env0 : List (Sum Bool ℕ) := (List.finRange 10).map fun k : Fin 10 =>
              if k = v then Sum.inl false else Sum.inr k.val
            let stPre := compileLoop 10 pre (env0, [])
            have henv0_len : env0.length = 10 := by simp [env0]
            have hZ0 : ∀ w, (w == v.val) = true → ∃ bv, env0.getD w (Sum.inl false) = Sum.inl bv := by
              intro w hw
              rw [beq_iff_eq] at hw; subst hw
              have hlt : v.val < env0.length := by rw [henv0_len]; exact v.isLt
              refine ⟨false, ?_⟩
              rw [List.getD_eq_getElem _ _ hlt]
              dsimp [env0]
              rw [List.getElem_map, hfinRange10]
              have hveq : (⟨v.val, v.isLt⟩ : Fin 10) = v := Fin.ext rfl
              rw [hveq, if_pos rfl]
            have hbound0 : ∀ x ∈ env0, ∀ j, x = Sum.inr j → j < 10 + ([] : List Gate).length := by
              intro x hx j hj
              dsimp [env0] at hx
              rw [List.mem_map] at hx
              rcases hx with ⟨k, _, rfl⟩
              split_ifs at hj
              cases hj
              exact k.isLt
            have hfan_pre : ∀ g ∈ pre, fanOK g := fun g hg => hfan g (by rw [hgs_eq]; exact List.mem_append_left _ hg)
            have hfan_gm : fanOK gm := hfan gm (by rw [hgs_eq]; exact List.mem_append_right _ List.mem_cons_self)
            have hstrPre := hcomp_struct 10 10 (fun w => w == v.val) (fun w hw => by rw [beq_iff_eq] at hw; have := v.isLt; omega)
              pre env0 [] (by omega) hZ0 hbound0 (fun _ h => by cases h) hfan_pre
            have hstPre_len1 : stPre.1.length = 10 + pre.length := by
              have := hstrPre.2.2.2.1; rw [henv0_len] at this; exact this
            have hv_in_pre : stPre.1.getD v.val (Sum.inl false) = Sum.inl false := by
              have hv0 : env0.getD v.val (Sum.inl false) = Sum.inl false := by
                have hlt : v.val < env0.length := by rw [henv0_len]; exact v.isLt
                rw [List.getD_eq_getElem _ _ hlt]
                dsimp [env0]
                rw [List.getElem_map, hfinRange10]
                have hveq : (⟨v.val, v.isLt⟩ : Fin 10) = v := Fin.ext rfl
                rw [hveq, if_pos rfl]
              have hsame := hstrPre.2.2.1
              have : stPre.1.getD v.val (Sum.inl false) = env0.getD v.val (Sum.inl false) := by
                clear hnotc hbound0 hfan_pre hfan_gm hgm_v hpre_nv hpost_nv hgs_eq
                clear hstrPre hstPre_len1
                have hfold : ∀ (qs : List Gate) (e : List (Sum Bool ℕ)) (g0s : List Gate),
                    10 ≤ e.length → (compileLoop 10 qs (e, g0s)).1.getD v.val (Sum.inl false) = e.getD v.val (Sum.inl false) := by
                  intro qs
                  induction qs with
                  | nil => intro e g0s _; rfl
                  | cons q qs ihq =>
                    intro e g0s he
                    have he1 : (compileStep 10 (e, g0s) q).1.length = e.length + 1 := by
                      dsimp [compileStep]; cases (evalOne 10 q e g0s).2 <;> simp
                    have heq1 : (compileStep 10 (e, g0s) q).1.getD v.val (Sum.inl false) = e.getD v.val (Sum.inl false) := by
                      dsimp [compileStep]; cases (evalOne 10 q e g0s).2 <;> exact List.getD_append _ _ _ _ (by have := v.isLt; omega)
                    have hge : 10 ≤ (compileStep 10 (e, g0s) q).1.length := by omega
                    change (compileLoop 10 qs (compileStep 10 (e, g0s) q)).1.getD v.val (Sum.inl false) = _
                    rw [ihq _ _ hge, heq1]
                exact hfold pre env0 [] (by omega)
              rw [this, hv0]
            have hnoc : ∀ cv : Bool, evalOne 10 gm stPre.1 stPre.2 ≠ (Sum.inl cv, none) := fun cv heq =>
              hnotc ⟨pre, gm, post, cv, hgs_eq, hgm_v, hpre_nv, hpost_nv, heq⟩
            cases gm
            rename_i opm insm
            rcases hfan_gm with ⟨hopm, hilm⟩
            rcases hopm with rfl | rfl | rfl
            · exfalso
              cases insm with
              | nil => exact hnoc true rfl
              | cons a t =>
                cases t with
                | nil =>
                  have hm : v.val ∈ ([a] : List ℕ) := List.contains_iff_mem.mp hgm_v
                  have hav : a = v.val := (List.mem_singleton.mp hm).symm
                  subst hav
                  exact hnoc false (by dsimp [evalOne]; rw [hv_in_pre])
                | cons b r =>
                  have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilm
                  subst hr_nil
                  have hmem : v.val ∈ [a, b] := List.contains_iff_mem.mp hgm_v
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                  rcases hmem with rfl | rfl
                  · exact hnoc false (by dsimp [evalOne]; rw [hv_in_pre]; rfl)
                  · dsimp [evalOne] at hnoc
                    cases ha : stPre.1.getD a (Sum.inl false) with
                    | inl ba =>
                      cases ba
                      · exact hnoc false (by rw [ha]; rfl)
                      · exact hnoc false (by rw [ha, hv_in_pre]; rfl)
                    | inr wa =>
                      exact hnoc false (by rw [ha, hv_in_pre]; rfl)
            · cases insm with
              | nil => exact False.elim (hnoc false rfl)
              | cons a t =>
                cases t with
                | nil =>
                  have hm : v.val ∈ ([a] : List ℕ) := List.contains_iff_mem.mp hgm_v
                  have hav : a = v.val := (List.mem_singleton.mp hm).symm
                  subst hav
                  exact False.elim (hnoc false (by dsimp [evalOne]; rw [hv_in_pre]))
                | cons b r =>
                  have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilm
                  subst hr_nil
                  have hmem : v.val ∈ [a, b] := List.contains_iff_mem.mp hgm_v
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                  have hboth : (a = v.val ∧ b ≠ v.val) ∨ (b = v.val ∧ a ≠ v.val) := by
                    rcases hmem with rfl | rfl
                    · by_cases hbv : b = v.val
                      · subst hbv; exact False.elim (hnoc false (by dsimp [evalOne]; rw [hv_in_pre]; rfl))
                      · exact Or.inl ⟨rfl, hbv⟩
                    · by_cases hav : a = v.val
                      · subst hav; exact False.elim (hnoc false (by dsimp [evalOne]; rw [hv_in_pre]; rfl))
                      · exact Or.inr ⟨rfl, hav⟩
                  rcases hboth with ⟨rfl, hne⟩ | ⟨rfl, hne⟩
                  · have hbinr : ∃ wy, stPre.1.getD b (Sum.inl false) = Sum.inr wy := by
                      cases hb : stPre.1.getD b (Sum.inl false) with
                      | inl bb =>
                        exfalso
                        exact hnoc bb (by dsimp [evalOne]; rw [hv_in_pre, hb]; rfl)
                      | inr wy => exact ⟨wy, rfl⟩
                    have hblt : b < 10 + pre.length := by
                      rcases hbinr with ⟨wy, hbw⟩
                      refine Classical.byContradiction fun hge => ?_
                      rw [List.getD_eq_default stPre.1 (Sum.inl false) (by omega)] at hbw
                      cases hbw
                    exact ⟨rfl, b, hblt, hne, Or.inl rfl⟩
                  · have hainr : ∃ wy, stPre.1.getD a (Sum.inl false) = Sum.inr wy := by
                      cases ha : stPre.1.getD a (Sum.inl false) with
                      | inl ba =>
                        exfalso
                        exact hnoc ba (by dsimp [evalOne]; rw [ha, hv_in_pre]; cases ba <;> rfl)
                      | inr wy => exact ⟨wy, rfl⟩
                    have halt : a < 10 + pre.length := by
                      rcases hainr with ⟨wy, haw⟩
                      refine Classical.byContradiction fun hge => ?_
                      rw [List.getD_eq_default stPre.1 (Sum.inl false) (by omega)] at haw
                      cases haw
                    exact ⟨rfl, a, halt, hne, Or.inr rfl⟩
            · exfalso
              cases insm with
              | nil => exact hnoc true rfl
              | cons a t =>
                have hm : v.val ∈ ([a] : List ℕ) := List.contains_iff_mem.mp hgm_v
                have hav : a = v.val := (List.mem_singleton.mp hm).symm
                subst hav
                exact hnoc true (by dsimp [evalOne]; rw [hv_in_pre]; rfl)
          -- Now inspect gs[0] (gs = g1 :: rest)
          cases hgs0 : gs with
          | nil => rw [hgs0] at h17; simp at h17
          | cons g1 rest =>
            have hrest_len : rest.length = 16 := by rw [hgs0, List.length_cons] at h17; omega
            have hfan_g1 : fanOK g1 := hfan g1 (by rw [hgs0]; exact List.mem_cons_self)
            have hfan_rest : ∀ g ∈ rest, fanOK g := fun g hg => hfan g (by rw [hgs0]; exact List.mem_cons_of_mem _ hg)
            by_cases hg1v : ∃ v : Fin 10, (effInputs g1).contains v.val = true
            · exfalso
              obtain ⟨v, hv1⟩ := hg1v
              have hrest_nv : ∀ g ∈ rest, ¬((effInputs g).contains v.val) := by
                have hc := heq1 v
                rw [hgs0, List.countP_cons, hv1] at hc
                simp only [↓reduceIte] at hc
                exact List.countP_eq_zero.mp (by omega)
              have hbad1 := hbad_or v [] g1 rest hgs0 hv1 (fun _ h => by cases h) hrest_nv
              rcases hbad1 with ⟨hor1, y, hy10, hyne, hins1⟩
              simp only [List.length_nil, Nat.add_zero] at hy10
              let yF : Fin 10 := ⟨y, hy10⟩
              have hy1 : (effInputs g1).contains yF.val = true := by
                apply List.contains_iff_mem.mpr
                change y ∈ cond (g1.op.eval [false]) (g1.inputs.take 1) g1.inputs
                rw [hor1]
                rcases hins1 with h | h
                · rw [h]; change y ∈ [v.val, y]; simp
                · rw [h]; change y ∈ [y, v.val]; simp
              have hrest_ny : ∀ g ∈ rest, ¬((effInputs g).contains yF.val) := by
                have hc := heq1 yF
                rw [hgs0, List.countP_cons, hy1] at hc
                simp only [↓reduceIte] at hc
                exact List.countP_eq_zero.mp (by omega)
              have huv : u ≠ v.val := by
                intro heq
                obtain ⟨x, hx⟩ := hP_not_lit v b
                have hc := hcomp x
                have hv : (run gs (List.ofFn x)).getD v.val false = x v := by
                  rw [hrun_preserves gs (List.ofFn x) v.val (by rw [List.length_ofFn]; exact v.isLt), hgetFn10' x v]
                rw [heq, hv] at hc
                exact hx hc
              have huy : u ≠ yF.val := by
                intro heq
                obtain ⟨x, hx⟩ := hP_not_lit yF b
                have hc := hcomp x
                have hy : (run gs (List.ofFn x)).getD yF.val false = x yF := by
                  rw [hrun_preserves gs (List.ofFn x) yF.val (by rw [List.length_ofFn]; exact yF.isLt), hgetFn10' x yF]
                rw [heq, hy] at hc
                exact hx hc
              obtain ⟨a, hav, hay, haG⟩ := hP_or_sym v yF (fun h => hyne (congrArg Fin.val h).symm)
              apply haG
              let xA : Fin 10 → Bool := fun k => decide (k = v ∨ k = a)
              let xB : Fin 10 → Bool := fun k => decide (k = yF ∨ k = a)
              have hstep10 : (step (List.ofFn xA) g1).getD 10 false = true ∧
                  (step (List.ofFn xB) g1).getD 10 false = true := by
                have heA : (step (List.ofFn xA) g1).getD 10 false = g1.op.eval (g1.inputs.map fun i => (List.ofFn xA).getD i false) :=
                  hstep_10 xA g1
                have heB : (step (List.ofFn xB) g1).getD 10 false = g1.op.eval (g1.inputs.map fun i => (List.ofFn xB).getD i false) :=
                  hstep_10 xB g1
                rw [heA, heB, hor1]
                have hAv : (List.ofFn xA).getD v.val false = true := by rw [hgetFn10' xA v]; simp [xA]
                have hBy : (List.ofFn xB).getD y false = true := by
                  change (List.ofFn xB).getD yF.val false = true
                  rw [hgetFn10' xB yF]; simp [xB]
                rcases hins1 with h | h <;> rw [h]
                · change ((List.ofFn xA).getD v.val false || ((List.ofFn xA).getD y false || false)) = true ∧
                      ((List.ofFn xB).getD v.val false || ((List.ofFn xB).getD y false || false)) = true
                  rw [hAv, hBy]; simp
                · change ((List.ofFn xA).getD y false || ((List.ofFn xA).getD v.val false || false)) = true ∧
                      ((List.ofFn xB).getD y false || ((List.ofFn xB).getD v.val false || false)) = true
                  rw [hAv, hBy]; simp
              have hagree_rest : (run rest (step (List.ofFn xA) g1)).getD u false =
                  (run rest (step (List.ofFn xB) g1)).getD u false := by
                apply hcomp_init_Agree (step (List.ofFn xA) g1) (step (List.ofFn xB) g1) rest
                  (fun w => w = v.val ∨ w = yF.val) u
                  (by rw [hstep_len, hstep_len, List.length_ofFn, List.length_ofFn])
                  (fun h => by rcases h with h1' | h2' <;> [exact huv h1'; exact huy h2'])
                · intro m hm
                  have hmv : m ≠ v.val := fun h => hm (Or.inl h)
                  have hmy : m ≠ yF.val := fun h => hm (Or.inr h)
                  by_cases hm10 : m < 10
                  · rw [hstep_pres _ _ _ (by rw [List.length_ofFn]; exact hm10),
                      hstep_pres _ _ _ (by rw [List.length_ofFn]; exact hm10),
                      hgetFn10Nat xA m hm10, hgetFn10Nat xB m hm10]
                    have hmv' : (⟨m, hm10⟩ : Fin 10) ≠ v := fun h => hmv (congrArg Fin.val h)
                    have hmy' : (⟨m, hm10⟩ : Fin 10) ≠ yF := fun h => hmy (congrArg Fin.val h)
                    dsimp [xA, xB]; simp [hmv', hmy']
                  · by_cases hm10' : m = 10
                    · subst hm10'; rw [hstep10.1, hstep10.2]
                    · rw [List.getD_eq_default (step (List.ofFn xA) g1) false (by rw [hstep_len, List.length_ofFn]; omega),
                        List.getD_eq_default (step (List.ofFn xB) g1) false (by rw [hstep_len, List.length_ofFn]; omega)]
                · intro g hg w hw hmem
                  rcases hmem with rfl | rfl
                  · exact hrest_nv g hg (List.contains_iff_mem.mpr hw)
                  · exact hrest_ny g hg (List.contains_iff_mem.mpr hw)
                · exact hfan_rest
              have hrunA : (run gs (List.ofFn xA)).getD u false = (run rest (step (List.ofFn xA) g1)).getD u false := by
                rw [hgs0, hrun_cons]
              have hrunB : (run gs (List.ofFn xB)).getD u false = (run rest (step (List.ofFn xB) g1)).getD u false := by
                rw [hgs0, hrun_cons]
              rw [← hcomp xA, ← hcomp xB, hrunA, hrunB, hagree_rest]
            · have hg1_no : ∀ v : Fin 10, ¬((effInputs g1).contains v.val) := by
                intro v hv; exact hg1v ⟨v, hv⟩
              let xZ : Fin 10 → Bool := fun _ => false
              let c0 : Bool := g1.op.eval (g1.inputs.map fun i => (List.ofFn xZ).getD i false)
              have hge10 : ∀ i ∈ effInputs g1, 10 ≤ i := by
                intro i hi
                refine Classical.byContradiction fun hlt => ?_
                exact hg1_no ⟨i, by omega⟩ (List.contains_iff_mem.mpr hi)
              have hg1_const : ∀ x : Fin 10 → Bool,
                  g1.op.eval (g1.inputs.map fun i => (List.ofFn x).getD i false) = c0 := by
                intro x
                dsimp [c0]
                cases g1
                rename_i op1 ins1
                rcases hfan_g1 with ⟨hop1, _⟩
                rcases hop1 with rfl | rfl | rfl
                · have hm : ins1.map (fun i => (List.ofFn x).getD i false) =
                      ins1.map (fun i => (List.ofFn xZ).getD i false) := by
                    apply List.map_congr_left
                    intro i hi
                    have hi10 := hge10 i hi
                    rw [List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega),
                      List.getD_eq_default (List.ofFn xZ) false (by rw [List.length_ofFn]; omega)]
                  rw [hm]
                · have hm : ins1.map (fun i => (List.ofFn x).getD i false) =
                      ins1.map (fun i => (List.ofFn xZ).getD i false) := by
                    apply List.map_congr_left
                    intro i hi
                    have hi10 := hge10 i hi
                    rw [List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega),
                      List.getD_eq_default (List.ofFn xZ) false (by rw [List.length_ofFn]; omega)]
                  rw [hm]
                · cases ins1 with
                  | nil => rfl
                  | cons a t =>
                    have ha10 : 10 ≤ a := hge10 a (by change a ∈ [a]; simp)
                    have hfa : (List.ofFn x).getD a false = (List.ofFn xZ).getD a false := by
                      rw [List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega),
                        List.getD_eq_default (List.ofFn xZ) false (by rw [List.length_ofFn]; omega)]
                    change Bool.not (( (List.ofFn x).getD a false :: _).headD false) = Bool.not (( (List.ofFn xZ).getD a false :: _).headD false)
                    rw [List.headD_cons, List.headD_cons, hfa]
              let env1 : List (Sum Bool ℕ) := (List.finRange 10).map (fun k : Fin 10 => Sum.inr k.val) ++ [Sum.inl c0]
              have henv1_len : env1.length = 11 := by simp [env1]
              have hZ1 : ∀ w, (fun _ => false) w = true → ∃ bv, env1.getD w (Sum.inl false) = Sum.inl bv :=
                fun _ h => by cases h
              have hbound1 : ∀ x ∈ env1, ∀ j, x = Sum.inr j → j < 10 + ([] : List Gate).length := by
                intro x hx j hj
                dsimp [env1] at hx
                rw [List.mem_append, List.mem_map, List.mem_singleton] at hx
                rcases hx with ⟨k, _, rfl⟩ | rfl
                · cases hj; exact k.isLt
                · cases hj
              let res := compileLoop 10 rest (env1, [])
              have hstr := hcomp_struct 10 10 (fun _ => false) (fun _ h => by cases h)
                rest env1 [] (by omega) hZ1 hbound1 (fun _ h => by cases h) hfan_rest
              have hres_len : res.2.length ≤ 16 := by
                have hc := hstr.2.2.2.2
                change res.2.length + _ ≤ 0 + rest.length at hc
                omega
              have hsem_res : ∀ x : Fin 10 → Bool,
                  (if b = true then !(evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false)))
                   else evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false))) = G5 x := by
                intro x
                have hsem_in : ∀ m, evalVal (run res.2 (List.ofFn x)) (env1.getD m (Sum.inl false)) =
                    (step (List.ofFn x) g1).getD m false := by
                  intro m
                  by_cases hm : m < 10
                  · have hmlt : m < ((List.finRange 10).map (fun k : Fin 10 => (Sum.inr k.val : Sum Bool ℕ))).length := by simp [hm]
                    dsimp [env1]
                    rw [List.getD_append _ _ _ _ hmlt, List.getD_eq_getElem _ _ hmlt, List.getElem_map, hfinRange10]
                    change (run res.2 (List.ofFn x)).getD m false = (step (List.ofFn x) g1).getD m false
                    rw [hrun_preserves res.2 (List.ofFn x) m (by rw [List.length_ofFn]; exact hm),
                      hstep_pres _ _ _ (by rw [List.length_ofFn]; exact hm)]
                  · by_cases hm10 : m = 10
                    · subst hm10
                      have hl10 : ((List.finRange 10).map (fun k : Fin 10 => (Sum.inr k.val : Sum Bool ℕ))).length = 10 := by simp
                      dsimp [env1]
                      rw [List.getD_append_right _ _ _ _ (by omega), hl10, Nat.sub_self]
                      have hst10 : (step (List.ofFn x) g1).getD 10 false = c0 := by
                        rw [hstep_10]; exact hg1_const x
                      rw [hst10]; rfl
                    · rw [List.getD_eq_default env1 (Sum.inl false) (by rw [henv1_len]; omega),
                        List.getD_eq_default (step (List.ofFn x) g1) false (by rw [hstep_len, List.length_ofFn]; omega)]
                have hcs := hcomp_sem 10 10 (fun _ => false) (fun _ h => by cases h)
                  x rest env1 [] (step (List.ofFn x) g1)
                  (by omega) (by rw [henv1_len, hstep_len, List.length_ofFn])
                  hZ1 hbound1 (fun _ h => by cases h) hfan_rest hsem_in u
                have hgs_eq' : run rest (step (List.ofFn x) g1) = run gs (List.ofFn x) := by
                  rw [hgs0, hrun_cons]
                rw [hcs, hgs_eq', hcomp x]
              cases huval : res.1.getD u (Sum.inl false) with
              | inl cv =>
                exfalso
                have hc0 := hsem_res (fun _ => false)
                have hc1 := hsem_res (fun k => decide (k ≠ 0))
                rw [huval] at hc0 hc1
                have hne01 := hP_nonconst 0
                rw [← hc0, ← hc1] at hne01
                exact hne01 rfl
              | inr outW =>
                exact h1_le16 res.2 outW b hstr.2.1 hres_len (fun x => by have hc := hsem_res x; rw [huval] at hc; exact hc)
  -- Main proof on (g0 :: D.gates), length = 18
  have hcomp_full : ∀ x : Fin 10 → Bool,
      (if b = true then !((run (g0 :: D.gates) (List.ofFn x)).getD u false) else (run (g0 :: D.gates) (List.ofFn x)).getD u false) = G5 x := by
    intro x
    rw [← hG5_eq]
    exact hcomp0 x
  have hfan0 : fanOK g0 := hg0 g0 List.mem_cons_self
  have hfanD' : ∀ g ∈ D.gates, fanOK g := hfanD
  have hfan_all : ∀ g ∈ g0 :: D.gates, fanOK g := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hgD
    · exact hfan0
    · exact hfanD' g hgD
  -- using hcontains_eq_all
  by_cases hge3 : ∃ v : Fin 10, 3 ≤ (g0 :: D.gates).countP (fun g => (effInputs g).contains v.val)
  · obtain ⟨v, hv3⟩ := hge3
    let env0 : List (Sum Bool ℕ) := (List.finRange 10).map fun k : Fin 10 =>
      if k = v then Sum.inl false else Sum.inr k.val
    have henv0_len : env0.length = 10 := by simp [env0]
    have hZ0 : ∀ w, (w == v.val) = true → ∃ bv, env0.getD w (Sum.inl false) = Sum.inl bv := by
      intro w hw
      rw [beq_iff_eq] at hw; subst hw
      have hlt : v.val < env0.length := by rw [henv0_len]; exact v.isLt
      refine ⟨false, ?_⟩
      rw [List.getD_eq_getElem _ _ hlt]
      dsimp [env0]
      rw [List.getElem_map, hfinRange10]
      have hveq : (⟨v.val, v.isLt⟩ : Fin 10) = v := Fin.ext rfl
      rw [hveq, if_pos rfl]
    have hbound0 : ∀ x ∈ env0, ∀ j, x = Sum.inr j → j < 10 + ([] : List Gate).length := by
      intro x hx j hj
      dsimp [env0] at hx
      rw [List.mem_map] at hx
      rcases hx with ⟨k, _, rfl⟩
      split_ifs at hj
      cases hj
      exact k.isLt
    let res := compileLoop 10 (g0 :: D.gates) (env0, [])
    have hstr := hcomp_struct 10 10 (fun w => w == v.val) (fun w hw => by rw [beq_iff_eq] at hw; have := v.isLt; omega)
      (g0 :: D.gates) env0 [] (by omega) hZ0 hbound0 (fun _ h => by cases h) hfan_all
    have hres_len : res.2.length ≤ 15 := by
      have hc := hstr.2.2.2.2
      rw [hcontains_eq_all (g0 :: D.gates) v.val] at hc
      have h18 : (g0 :: D.gates).length = 18 := by rw [List.length_cons]; exact congrArg Nat.succ hszD
      change res.2.length + _ ≤ 0 + (g0 :: D.gates).length at hc
      omega
    have hsem0 : ∀ x : Fin 10 → Bool, x v = false →
        (if b = true then !(evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false)))
         else evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false))) = G5 x := by
      intro x hxv
      have hsem_in : ∀ m, evalVal (run res.2 (List.ofFn x)) (env0.getD m (Sum.inl false)) = (List.ofFn x).getD m false := by
        intro m
        by_cases hm : m < 10
        · have hme : m < env0.length := by rw [henv0_len]; exact hm
          rw [List.getD_eq_getElem _ _ hme]
          dsimp [env0]
          rw [List.getElem_map, hfinRange10]
          split_ifs with hkv
          · rw [hgetFn10Nat x m hm, hkv, hxv]
          · change (run res.2 (List.ofFn x)).getD m false = (List.ofFn x).getD m false
            rw [hrun_preserves res.2 (List.ofFn x) m (by rw [List.length_ofFn]; exact hm)]
        · rw [List.getD_eq_default env0 (Sum.inl false) (by rw [henv0_len]; omega),
            List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega)]
      have hcs := hcomp_sem 10 10 (fun w => w == v.val) (fun w hw => by rw [beq_iff_eq] at hw; have := v.isLt; omega)
        x (g0 :: D.gates) env0 [] (List.ofFn x) (by omega) (by rw [henv0_len, List.length_ofFn])
        hZ0 hbound0 (fun _ h => by cases h) hfan_all hsem_in u
      rw [hcs, hcomp_full x]
    cases huval : res.1.getD u (Sum.inl false) with
    | inl cv =>
      exfalso
      have hc0 := hsem0 (fun _ => false) rfl
      have hc1 := hsem0 (fun k => decide (k ≠ v)) (by simp)
      rw [huval] at hc0 hc1
      have hne01 := hP_nonconst v
      rw [← hc0, ← hc1] at hne01
      exact hne01 rfl
    | inr outW =>
      exact hmove_to_9 v ⟨res.2, outW⟩ outW b hstr.2.1 hres_len (fun x hxv => by have hc := hsem0 x hxv; rw [huval] at hc; exact hc)
  · have hle2_all : ∀ v : Fin 10, (g0 :: D.gates).countP (fun g => (effInputs g).contains v.val) ≤ 2 := fun v =>
      Nat.le_of_not_gt (fun hgt => hge3 ⟨v, hgt⟩)
    have hle2_D : ∀ v : Fin 10, D.gates.countP (fun g => (effInputs g).contains v.val) ≤ 2 := by
      intro v
      have h := hle2_all v
      rw [List.countP_cons] at h
      split_ifs at h <;> omega
    have hconst_g0 : ∀ c : Bool,
        (∀ x : Fin 10 → Bool, g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = c) →
        ∃ (E : Circuit) (u' : ℕ) (b' : Bool), FanInTwo E ∧ E.size ≤ 15 ∧
          ∀ x : Fin 10 → Bool, x 9 = false →
            (if b' = true then !((E.wires (List.ofFn x)).getD u' false) else (E.wires (List.ofFn x)).getD u' false) = f10 x := by
      intro c hc0
      let env1 : List (Sum Bool ℕ) := (List.finRange 10).map (fun k : Fin 10 => Sum.inr k.val) ++ [Sum.inl c]
      have henv1_len : env1.length = 11 := by simp [env1]
      have hZ1 : ∀ w, (fun _ => false) w = true → ∃ bv, env1.getD w (Sum.inl false) = Sum.inl bv :=
        fun _ h => by cases h
      have hbound1 : ∀ x ∈ env1, ∀ j, x = Sum.inr j → j < 10 + ([] : List Gate).length := by
        intro x hx j hj
        dsimp [env1] at hx
        rw [List.mem_append, List.mem_map, List.mem_singleton] at hx
        rcases hx with ⟨k, _, rfl⟩ | rfl
        · cases hj; exact k.isLt
        · cases hj
      let res := compileLoop 10 D.gates (env1, [])
      have hstr := hcomp_struct 10 10 (fun _ => false) (fun _ h => by cases h)
        D.gates env1 [] (by omega) hZ1 hbound1 (fun _ h => by cases h) hfanD'
      have hres_len : res.2.length ≤ 17 := by
        have hc := hstr.2.2.2.2
        change res.2.length + _ ≤ 0 + D.size at hc
        omega
      have hsem_res : ∀ x : Fin 10 → Bool,
          (if b = true then !(evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false)))
           else evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false))) = G5 x := by
        intro x
        have hsem_in : ∀ m, evalVal (run res.2 (List.ofFn x)) (env1.getD m (Sum.inl false)) =
            (step (List.ofFn x) g0).getD m false := by
          intro m
          by_cases hm : m < 10
          · have hmlt : m < ((List.finRange 10).map (fun k : Fin 10 => (Sum.inr k.val : Sum Bool ℕ))).length := by simp [hm]
            dsimp [env1]
            rw [List.getD_append _ _ _ _ hmlt, List.getD_eq_getElem _ _ hmlt, List.getElem_map, hfinRange10]
            change (run res.2 (List.ofFn x)).getD m false = (step (List.ofFn x) g0).getD m false
            rw [hrun_preserves res.2 (List.ofFn x) m (by rw [List.length_ofFn]; exact hm),
              hstep_pres _ _ _ (by rw [List.length_ofFn]; exact hm)]
          · by_cases hm10 : m = 10
            · subst hm10
              have hl10 : ((List.finRange 10).map (fun k : Fin 10 => (Sum.inr k.val : Sum Bool ℕ))).length = 10 := by simp
              dsimp [env1]
              rw [List.getD_append_right _ _ _ _ (by omega), hl10, Nat.sub_self]
              have hst10 : (step (List.ofFn x) g0).getD 10 false = c := by
                rw [hstep_10]; exact hc0 x
              rw [hst10]; rfl
            · rw [List.getD_eq_default env1 (Sum.inl false) (by rw [henv1_len]; omega),
                List.getD_eq_default (step (List.ofFn x) g0) false (by rw [hstep_len, List.length_ofFn]; omega)]
        have hcs := hcomp_sem 10 10 (fun _ => false) (fun _ h => by cases h)
          x D.gates env1 [] (step (List.ofFn x) g0)
          (by omega) (by rw [henv1_len, hstep_len, List.length_ofFn])
          hZ1 hbound1 (fun _ h => by cases h) hfanD' hsem_in u
        rw [hcs, ← hrun_cons, hcomp_full x]
      cases huval : res.1.getD u (Sum.inl false) with
      | inl cv =>
        exfalso
        have hcA := hsem_res (fun _ => false)
        have hcB := hsem_res (fun k => decide (k ≠ 0))
        rw [huval] at hcA hcB
        have hne01 := hP_nonconst 0
        rw [← hcA, ← hcB] at hne01
        exact hne01 rfl
      | inr outW =>
        exact h1_core res.2 outW b hstr.2.1 hres_len (fun x => by have hc := hsem_res x; rw [huval] at hc; exact hc)
    have hwire_g0 : ∀ a : Fin 10,
        (∀ x : Fin 10 → Bool, g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = x a) →
        ∃ (E : Circuit) (u' : ℕ) (b' : Bool), FanInTwo E ∧ E.size ≤ 15 ∧
          ∀ x : Fin 10 → Bool, x 9 = false →
            (if b' = true then !((E.wires (List.ofFn x)).getD u' false) else (E.wires (List.ofFn x)).getD u' false) = f10 x := by
      intro a ha0
      let env1 : List (Sum Bool ℕ) := (List.finRange 10).map (fun k : Fin 10 => Sum.inr k.val) ++ [Sum.inr a.val]
      have henv1_len : env1.length = 11 := by simp [env1]
      have hZ1 : ∀ w, (fun _ => false) w = true → ∃ bv, env1.getD w (Sum.inl false) = Sum.inl bv :=
        fun _ h => by cases h
      have hbound1 : ∀ x ∈ env1, ∀ j, x = Sum.inr j → j < 10 + ([] : List Gate).length := by
        intro x hx j hj
        dsimp [env1] at hx
        rw [List.mem_append, List.mem_map, List.mem_singleton] at hx
        rcases hx with ⟨k, _, rfl⟩ | rfl
        · cases hj; exact k.isLt
        · cases hj; exact a.isLt
      let res := compileLoop 10 D.gates (env1, [])
      have hstr := hcomp_struct 10 10 (fun _ => false) (fun _ h => by cases h)
        D.gates env1 [] (by omega) hZ1 hbound1 (fun _ h => by cases h) hfanD'
      have hres_len : res.2.length ≤ 17 := by
        have hc := hstr.2.2.2.2
        change res.2.length + _ ≤ 0 + D.size at hc
        omega
      have hsem_res : ∀ x : Fin 10 → Bool,
          (if b = true then !(evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false)))
           else evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false))) = G5 x := by
        intro x
        have hsem_in : ∀ m, evalVal (run res.2 (List.ofFn x)) (env1.getD m (Sum.inl false)) =
            (step (List.ofFn x) g0).getD m false := by
          intro m
          by_cases hm : m < 10
          · have hmlt : m < ((List.finRange 10).map (fun k : Fin 10 => (Sum.inr k.val : Sum Bool ℕ))).length := by simp [hm]
            dsimp [env1]
            rw [List.getD_append _ _ _ _ hmlt, List.getD_eq_getElem _ _ hmlt, List.getElem_map, hfinRange10]
            change (run res.2 (List.ofFn x)).getD m false = (step (List.ofFn x) g0).getD m false
            rw [hrun_preserves res.2 (List.ofFn x) m (by rw [List.length_ofFn]; exact hm),
              hstep_pres _ _ _ (by rw [List.length_ofFn]; exact hm)]
          · by_cases hm10 : m = 10
            · subst hm10
              have hl10 : ((List.finRange 10).map (fun k : Fin 10 => (Sum.inr k.val : Sum Bool ℕ))).length = 10 := by simp
              dsimp [env1]
              rw [List.getD_append_right _ _ _ _ (by omega), hl10, Nat.sub_self]
              have hst10 : (step (List.ofFn x) g0).getD 10 false = x a := by
                rw [hstep_10]; exact ha0 x
              rw [hst10]
              change (run res.2 (List.ofFn x)).getD a.val false = x a
              rw [hrun_preserves res.2 (List.ofFn x) a.val (by rw [List.length_ofFn]; exact a.isLt),
                hgetFn10' x a]
            · rw [List.getD_eq_default env1 (Sum.inl false) (by rw [henv1_len]; omega),
                List.getD_eq_default (step (List.ofFn x) g0) false (by rw [hstep_len, List.length_ofFn]; omega)]
        have hcs := hcomp_sem 10 10 (fun _ => false) (fun _ h => by cases h)
          x D.gates env1 [] (step (List.ofFn x) g0)
          (by omega) (by rw [henv1_len, hstep_len, List.length_ofFn])
          hZ1 hbound1 (fun _ h => by cases h) hfanD' hsem_in u
        rw [hcs, ← hrun_cons, hcomp_full x]
      cases huval : res.1.getD u (Sum.inl false) with
      | inl cv =>
        exfalso
        have hcA := hsem_res (fun _ => false)
        have hcB := hsem_res (fun k => decide (k ≠ 0))
        rw [huval] at hcA hcB
        have hne01 := hP_nonconst 0
        rw [← hcA, ← hcB] at hne01
        exact hne01 rfl
      | inr outW =>
        exact h1_core res.2 outW b hstr.2.1 hres_len (fun x => by have hc := hsem_res x; rw [huval] at hc; exact hc)
    have hconst10_kill : ∀ (v : Fin 10) (c : Bool),
        (∀ x : Fin 10 → Bool, x v = false → g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = c) →
        1 ≤ D.gates.countP (fun g => (effInputs g).contains v.val) ∨ D.gates.countP (fun g => (effInputs g).contains 10) ≠ 1 →
        ∃ (E : Circuit) (u' : ℕ) (b' : Bool), FanInTwo E ∧ E.size ≤ 15 ∧
          ∀ x : Fin 10 → Bool, x 9 = false →
            (if b' = true then !((E.wires (List.ofFn x)).getD u' false) else (E.wires (List.ofFn x)).getD u' false) = f10 x := by
      intro v c hvc hcond
      by_cases h10_0 : D.gates.countP (fun g => (effInputs g).contains 10) = 0
      · have hD_n10 : ∀ g ∈ D.gates, ¬((effInputs g).contains 10) := List.countP_eq_zero.mp h10_0
        by_cases hu10 : u = 10
        · exfalso
          have hc10 : ∀ x : Fin 10 → Bool, x v = false →
              (run (g0 :: D.gates) (List.ofFn x)).getD 10 false = c := by
            intro x hxv
            rw [hrun_cons, hrun_preserves D.gates (step (List.ofFn x) g0) 10 (by rw [hstep_len, List.length_ofFn]; omega)]
            rw [hstep_10]
            exact hvc x hxv
          have hc0 := hcomp_full (fun _ => false)
          have hc1 := hcomp_full (fun k => decide (k ≠ v))
          rw [hu10, hc10 _ rfl] at hc0
          rw [hu10, hc10 _ (by simp)] at hc1
          have hne01 := hP_nonconst v
          rw [← hc0, ← hc1] at hne01
          exact hne01 rfl
        · let gsNew := D.gates.map (shiftG 10)
          have hfanNew : ∀ g ∈ gsNew, fanOK g := by
            intro g hg
            rw [List.mem_map] at hg
            rcases hg with ⟨g', hg', rfl⟩
            exact ⟨(hfanD' g' hg').1, by simpa [shiftG] using (hfanD' g' hg').2⟩
          have hlenNew : gsNew.length ≤ 17 := by dsimp [gsNew]; rw [List.length_map]; exact hszD.le
          have hevalNew : ∀ x : Fin 10 → Bool,
              (run gsNew (List.ofFn x)).getD (shiftIdx 10 u) false = (run (g0 :: D.gates) (List.ofFn x)).getD u false := by
            intro x
            have herr := herase_dead_run [] g0 D.gates (List.ofFn x) u (by rw [List.length_ofFn, List.length_nil, Nat.add_zero]; exact hu10) hD_n10 hfanD'
            simpa [gsNew] using herr
          apply h1_core gsNew (shiftIdx 10 u) b hfanNew hlenNew
          intro x
          rw [hevalNew x, hcomp_full x]
      · have h10_ge1 : 1 ≤ D.gates.countP (fun g => (effInputs g).contains 10) := by omega
        let env1 : List (Sum Bool ℕ) := ((List.finRange 10).map fun k : Fin 10 =>
          if k = v then Sum.inl false else Sum.inr k.val) ++ [Sum.inl c]
        have henv1_len : env1.length = 11 := by simp [env1]
        have hZ1 : ∀ w, (w == v.val || w == 10) = true → ∃ bv, env1.getD w (Sum.inl false) = Sum.inl bv := by
          intro w hw
          simp only [Bool.or_eq_true, beq_iff_eq] at hw
          rcases hw with rfl | rfl
          · have hlt : v.val < ((List.finRange 10).map fun k : Fin 10 => if k = v then Sum.inl false else (Sum.inr k.val : Sum Bool ℕ)).length := by
              simp [v.isLt]
            refine ⟨false, ?_⟩
            dsimp [env1]
            rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_map, hfinRange10]
            have hveq : (⟨v.val, v.isLt⟩ : Fin 10) = v := Fin.ext rfl
            rw [hveq, if_pos rfl]
          · refine ⟨c, ?_⟩
            have hl10 : ((List.finRange 10).map fun k : Fin 10 => if k = v then Sum.inl false else (Sum.inr k.val : Sum Bool ℕ)).length = 10 := by simp
            dsimp [env1]
            rw [List.getD_append_right _ _ _ _ (by omega), hl10, Nat.sub_self]; rfl
        have hbound1 : ∀ x ∈ env1, ∀ j, x = Sum.inr j → j < 10 + ([] : List Gate).length := by
          intro x hx j hj
          dsimp [env1] at hx
          rw [List.mem_append, List.mem_map, List.mem_singleton] at hx
          rcases hx with ⟨k, _, rfl⟩ | rfl
          · split_ifs at hj; cases hj; exact k.isLt
          · cases hj
        have hsem_in1 : ∀ (gsComp : List Gate) (x : Fin 10 → Bool), x v = false →
            ∀ m, evalVal (run gsComp (List.ofFn x)) (env1.getD m (Sum.inl false)) = (step (List.ofFn x) g0).getD m false := by
          intro gsComp x hxv m
          by_cases hm : m < 10
          · have hlt : m < ((List.finRange 10).map fun k : Fin 10 => if k = v then Sum.inl false else (Sum.inr k.val : Sum Bool ℕ)).length := by simp [hm]
            dsimp [env1]
            rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_map, hfinRange10]
            rw [hstep_pres _ _ _ (by rw [List.length_ofFn]; exact hm)]
            split_ifs with hkv
            · rw [hgetFn10Nat x m hm, hkv, hxv]
            · change (run gsComp (List.ofFn x)).getD m false = (List.ofFn x).getD m false
              rw [hrun_preserves gsComp (List.ofFn x) m (by rw [List.length_ofFn]; exact hm)]
          · by_cases hm10 : m = 10
            · subst hm10
              have hl10 : ((List.finRange 10).map fun k : Fin 10 => if k = v then Sum.inl false else (Sum.inr k.val : Sum Bool ℕ)).length = 10 := by simp
              dsimp [env1]
              rw [List.getD_append_right _ _ _ _ (by omega), hl10, Nat.sub_self]
              have hst10 : (step (List.ofFn x) g0).getD 10 false = c := by rw [hstep_10]; exact hvc x hxv
              rw [hst10]; rfl
            · rw [List.getD_eq_default env1 (Sum.inl false) (by rw [henv1_len]; omega),
                List.getD_eq_default (step (List.ofFn x) g0) false (by rw [hstep_len, List.length_ofFn]; omega)]
        by_cases hboth2 : 2 ≤ D.gates.countP (fun g => (effInputs g).contains v.val || (effInputs g).contains 10)
        · let res := compileLoop 10 D.gates (env1, [])
          have hstr := hcomp_struct 10 11 (fun w => w == v.val || w == 10)
            (fun w hw => by simp only [Bool.or_eq_true, beq_iff_eq] at hw; rcases hw with rfl | rfl; exact Nat.lt_succ_of_lt v.isLt; omega)
            D.gates env1 [] (by omega) hZ1 hbound1 (fun _ h => by cases h) hfanD'
          have hcnt_both : D.gates.countP (fun g => (effInputs g).any (fun w => w == v.val || w == 10)) =
              D.gates.countP (fun g => (effInputs g).contains v.val || (effInputs g).contains 10) := by
            apply List.countP_congr
            intro g _
            simp only [List.any_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq]
            exact ⟨fun h => Exists.elim h fun w hw => by rcases hw.2 with rfl | rfl <;> [exact Or.inl hw.1; exact Or.inr hw.1],
              fun h => by rcases h with h1' | h2' <;> [exact ⟨v.val, h1', Or.inl rfl⟩; exact ⟨10, h2', Or.inr rfl⟩]⟩
          have hres_len : res.2.length ≤ 15 := by
            have hc := hstr.2.2.2.2
            rw [hcnt_both] at hc
            change res.2.length + _ ≤ 0 + D.size at hc
            omega
          have hsem_res : ∀ x : Fin 10 → Bool, x v = false →
              (if b = true then !(evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false)))
               else evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false))) = G5 x := by
            intro x hxv
            have hcs := hcomp_sem 10 11 (fun w => w == v.val || w == 10)
              (fun w hw => by simp only [Bool.or_eq_true, beq_iff_eq] at hw; rcases hw with rfl | rfl; exact Nat.lt_succ_of_lt v.isLt; omega)
              x D.gates env1 [] (step (List.ofFn x) g0) (by omega) (by rw [henv1_len, hstep_len, List.length_ofFn])
              hZ1 hbound1 (fun _ h => by cases h) hfanD' (hsem_in1 res.2 x hxv) u
            rw [hcs, ← hrun_cons, hcomp_full x]
          cases huval : res.1.getD u (Sum.inl false) with
          | inl cv =>
            exfalso
            have hc0 := hsem_res (fun _ => false) rfl
            have hc1 := hsem_res (fun k => decide (k ≠ v)) (by simp)
            rw [huval] at hc0 hc1
            have hne01 := hP_nonconst v
            rw [← hc0, ← hc1] at hne01
            exact hne01 rfl
          | inr outW =>
            exact hmove_to_9 v ⟨res.2, outW⟩ outW b hstr.2.1 hres_len (fun x hxv => by have hc := hsem_res x hxv; rw [huval] at hc; exact hc)
        · have hle_or1 : ∀ (q1 q2 : Gate → Bool), (∀ g ∈ D.gates, q1 g = true → (q1 g || q2 g) = true) :=
            fun q1 q2 g _ h => by rw [h]; rfl
          have hcount_le1 : D.gates.countP (fun g => (effInputs g).contains 10) ≤
              D.gates.countP (fun g => (effInputs g).contains v.val || (effInputs g).contains 10) := by
            apply List.countP_mono_left
            intro g _ h; rw [h]; exact Bool.or_true _
          have hcount_le2 : D.gates.countP (fun g => (effInputs g).contains v.val) ≤
              D.gates.countP (fun g => (effInputs g).contains v.val || (effInputs g).contains 10) := by
            apply List.countP_mono_left
            intro g _ h; rw [h]; exact Bool.true_or _
          have hboth_eq1 : D.gates.countP (fun g => (effInputs g).contains v.val || (effInputs g).contains 10) = 1 := by omega
          have h10_eq1 : D.gates.countP (fun g => (effInputs g).contains 10) = 1 := by omega
          have hv_ge1 : 1 ≤ D.gates.countP (fun g => (effInputs g).contains v.val) := by
            rcases hcond with hv1 | hne1
            · exact hv1
            · exact absurd h10_eq1 hne1
          have hv_eq1 : D.gates.countP (fun g => (effInputs g).contains v.val) = 1 := by omega
          have hex_gm : ∃ g ∈ D.gates, ((effInputs g).contains v.val || (effInputs g).contains 10) = true := by
            refine Classical.byContradiction fun hne => ?_
            have h0 : D.gates.countP (fun g => (effInputs g).contains v.val || (effInputs g).contains 10) = 0 :=
              List.countP_eq_zero.mpr (fun g hg h => hne ⟨g, hg, h⟩)
            omega
          obtain ⟨pre, gm, post, hD_eq, hgm_or, hpre_no⟩ :=
            hsplit_first (fun g => (effInputs g).contains v.val || (effInputs g).contains 10) D.gates hex_gm
          have hpre_cnt0 : pre.countP (fun g => (effInputs g).contains v.val || (effInputs g).contains 10) = 0 :=
            List.countP_eq_zero.mpr (fun g hg => by rw [hpre_no g hg]; exact Bool.false_ne_true)
          have hpost_cnt0 : post.countP (fun g => (effInputs g).contains v.val || (effInputs g).contains 10) = 0 := by
            have hc := hboth_eq1
            rw [hD_eq, List.countP_append, List.countP_cons, hgm_or, hpre_cnt0] at hc
            simp only [↓reduceIte] at hc
            omega
          have hpre_nv : ∀ g ∈ pre, ¬((effInputs g).contains v.val) := fun g hg h =>
            Bool.false_ne_true ((hpre_no g hg).symm.trans (by rw [h]; exact Bool.true_or _))
          have hpre_n10 : ∀ g ∈ pre, ¬((effInputs g).contains 10) := fun g hg h =>
            Bool.false_ne_true ((hpre_no g hg).symm.trans (by rw [h]; exact Bool.or_true _))
          have hpost_nv : ∀ g ∈ post, ¬((effInputs g).contains v.val) := fun g hg h =>
            List.countP_eq_zero.mp hpost_cnt0 g hg (by rw [h]; exact Bool.true_or _)
          have hpost_n10 : ∀ g ∈ post, ¬((effInputs g).contains 10) := fun g hg h =>
            List.countP_eq_zero.mp hpost_cnt0 g hg (by rw [h]; exact Bool.or_true _)
          have hgm_v : (effInputs gm).contains v.val = true := by
            have hc := hv_eq1
            rw [hD_eq, List.countP_append, List.countP_cons] at hc
            have hpc : pre.countP (fun g => (effInputs g).contains v.val) = 0 := List.countP_eq_zero.mpr hpre_nv
            have hqc : post.countP (fun g => (effInputs g).contains v.val) = 0 := List.countP_eq_zero.mpr hpost_nv
            rw [hpc, hqc] at hc
            cases hvgm : (effInputs gm).contains v.val with
            | true => rfl
            | false => rw [hvgm] at hc; simp at hc
          have hgm_10 : (effInputs gm).contains 10 = true := by
            have hc := h10_eq1
            rw [hD_eq, List.countP_append, List.countP_cons] at hc
            have hpc : pre.countP (fun g => (effInputs g).contains 10) = 0 := List.countP_eq_zero.mpr hpre_n10
            have hqc : post.countP (fun g => (effInputs g).contains 10) = 0 := List.countP_eq_zero.mpr hpost_n10
            rw [hpc, hqc] at hc
            cases hvgm : (effInputs gm).contains 10 with
            | true => rfl
            | false => rw [hvgm] at hc; simp at hc
          have hfan_pre : ∀ g ∈ pre, fanOK g := fun g hg => hfanD' g (by rw [hD_eq]; exact List.mem_append_left _ hg)
          have hfan_gm : fanOK gm := hfanD' gm (by rw [hD_eq]; exact List.mem_append_right _ List.mem_cons_self)
          have hfan_post : ∀ g ∈ post, fanOK g := fun g hg => hfanD' g (by rw [hD_eq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
          let stPre := compileLoop 10 pre (env1, [])
          have hstrPre := hcomp_struct 10 11 (fun w => w == v.val || w == 10)
            (fun w hw => by simp only [Bool.or_eq_true, beq_iff_eq] at hw; rcases hw with rfl | rfl; exact Nat.lt_succ_of_lt v.isLt; omega)
            pre env1 [] (by omega) hZ1 hbound1 (fun _ h => by cases h) hfan_pre
          have hstPre_len1 : stPre.1.length = 11 + pre.length := by
            have := hstrPre.2.2.2.1; rw [henv1_len] at this; exact this
          have hstPre_len2 : stPre.2.length ≤ pre.length := by
            have := hstrPre.2.2.2.2; change stPre.2.length + _ ≤ 0 + pre.length at this; omega
          have hstPre_v10 : stPre.1.getD v.val (Sum.inl false) = Sum.inl false ∧
              stPre.1.getD 10 (Sum.inl false) = Sum.inl c := by
            have hfold : ∀ (wIdx : ℕ) (hw : wIdx < 11) (qs : List Gate) (e : List (Sum Bool ℕ)) (g0s : List Gate),
                11 ≤ e.length → (compileLoop 10 qs (e, g0s)).1.getD wIdx (Sum.inl false) = e.getD wIdx (Sum.inl false) := by
              intro wIdx hw qs
              induction qs with
              | nil => intro e g0s _; rfl
              | cons q qs ihq =>
                intro e g0s he
                have he1 : (compileStep 10 (e, g0s) q).1.length = e.length + 1 := by
                  dsimp [compileStep]; cases (evalOne 10 q e g0s).2 <;> simp
                have heq1 : (compileStep 10 (e, g0s) q).1.getD wIdx (Sum.inl false) = e.getD wIdx (Sum.inl false) := by
                  dsimp [compileStep]; cases (evalOne 10 q e g0s).2 <;> exact List.getD_append _ _ _ _ (by omega)
                have hge : 11 ≤ (compileStep 10 (e, g0s) q).1.length := by omega
                change (compileLoop 10 qs (compileStep 10 (e, g0s) q)).1.getD wIdx (Sum.inl false) = _
                rw [ihq _ _ hge, heq1]
            have hv0 : env1.getD v.val (Sum.inl false) = Sum.inl false := by
              have hlt : v.val < ((List.finRange 10).map fun k : Fin 10 => if k = v then Sum.inl false else (Sum.inr k.val : Sum Bool ℕ)).length := by simp [v.isLt]
              dsimp [env1]; rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_map, hfinRange10]
              have hveq : (⟨v.val, v.isLt⟩ : Fin 10) = v := Fin.ext rfl; rw [hveq, if_pos rfl]
            have h100 : env1.getD 10 (Sum.inl false) = Sum.inl c := by
              have hl10 : ((List.finRange 10).map fun k : Fin 10 => if k = v then Sum.inl false else (Sum.inr k.val : Sum Bool ℕ)).length = 10 := by simp
              dsimp [env1]; rw [List.getD_append_right _ _ _ _ (by omega), hl10, Nat.sub_self]; rfl
            exact ⟨(hfold v.val (by have := v.isLt; omega) pre env1 [] (by omega)).trans hv0,
              (hfold 10 (by omega) pre env1 [] (by omega)).trans h100⟩
          have hgm_evalC : ∃ c2 : Bool, evalOne 10 gm stPre.1 stPre.2 = (Sum.inl c2, none) := by
            cases gm
            rename_i opm insm
            rcases hfan_gm with ⟨hopm, hilm⟩
            have hne_v10 : v.val ≠ 10 := by have := v.isLt; omega
            rcases hopm with rfl | rfl | rfl
            · cases insm with
              | nil => exact ⟨true, rfl⟩
              | cons a t =>
                cases t with
                | nil =>
                  have ha1 : v.val ∈ ([a] : List ℕ) := List.contains_iff_mem.mp hgm_v
                  have ha2 : 10 ∈ ([a] : List ℕ) := List.contains_iff_mem.mp hgm_10
                  have e1 : a = v.val := (List.mem_singleton.mp ha1).symm
                  have e2 : a = 10 := (List.mem_singleton.mp ha2).symm
                  exact absurd (e1.symm.trans e2) hne_v10
                | cons b r =>
                  have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilm
                  subst hr_nil
                  have hmv : v.val ∈ [a, b] := List.contains_iff_mem.mp hgm_v
                  have hm10 : 10 ∈ [a, b] := List.contains_iff_mem.mp hgm_10
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv hm10
                  rcases hmv with rfl | rfl <;> rcases hm10 with h10 | h10
                  · exact absurd h10.symm hne_v10
                  · subst h10; exact ⟨false, by dsimp [evalOne]; rw [hstPre_v10.1]; rfl⟩
                  · subst h10; exact ⟨false, by dsimp [evalOne]; rw [hstPre_v10.2, hstPre_v10.1]; cases c <;> rfl⟩
                  · exact absurd h10.symm hne_v10
            · cases insm with
              | nil => exact ⟨false, rfl⟩
              | cons a t =>
                cases t with
                | nil =>
                  have ha1 : v.val ∈ ([a] : List ℕ) := List.contains_iff_mem.mp hgm_v
                  have ha2 : 10 ∈ ([a] : List ℕ) := List.contains_iff_mem.mp hgm_10
                  have e1 : a = v.val := (List.mem_singleton.mp ha1).symm
                  have e2 : a = 10 := (List.mem_singleton.mp ha2).symm
                  exact absurd (e1.symm.trans e2) hne_v10
                | cons b r =>
                  have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilm
                  subst hr_nil
                  have hmv : v.val ∈ [a, b] := List.contains_iff_mem.mp hgm_v
                  have hm10 : 10 ∈ [a, b] := List.contains_iff_mem.mp hgm_10
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv hm10
                  rcases hmv with rfl | rfl <;> rcases hm10 with h10 | h10
                  · exact absurd h10.symm hne_v10
                  · subst h10; exact ⟨c, by dsimp [evalOne]; rw [hstPre_v10.1, hstPre_v10.2]; rfl⟩
                  · subst h10; exact ⟨c, by dsimp [evalOne]; rw [hstPre_v10.2, hstPre_v10.1]; cases c <;> rfl⟩
                  · exact absurd h10.symm hne_v10
            · cases insm with
              | nil => exact ⟨true, rfl⟩
              | cons a t =>
                have ha1 : v.val ∈ ([a] : List ℕ) := List.contains_iff_mem.mp hgm_v
                have ha2 : 10 ∈ ([a] : List ℕ) := List.contains_iff_mem.mp hgm_10
                have e1 : a = v.val := (List.mem_singleton.mp ha1).symm
                have e2 : a = 10 := (List.mem_singleton.mp ha2).symm
                exact absurd (e1.symm.trans e2) hne_v10
          obtain ⟨c2, hc2⟩ := hgm_evalC
          let kWire := 11 + pre.length
          let st1 := compileStep 10 stPre gm
          have hst1_eq : st1 = (stPre.1 ++ [Sum.inl c2], stPre.2) := by dsimp [st1, compileStep]; rw [hc2]
          have hst1_2 : st1.2 = stPre.2 := by rw [hst1_eq]
          have hst1_1 : st1.1 = stPre.1 ++ [Sum.inl c2] := by rw [hst1_eq]
          have hst1_len1 : st1.1.length = kWire + 1 := by rw [hst1_1, List.length_append, List.length_singleton, hstPre_len1]
          have hst1_bound : ∀ x ∈ st1.1, ∀ j, x = Sum.inr j → j < 10 + st1.2.length := by
            intro x hx j hj
            rw [hst1_1, List.mem_append, List.mem_singleton] at hx
            rw [hst1_2]
            rcases hx with hx | rfl
            · exact hstrPre.2.2.1 x hx j hj
            · cases hj
          have hZk : ∀ w, (w == kWire) = true → ∃ bv, st1.1.getD w (Sum.inl false) = Sum.inl bv := by
            intro w hw
            rw [beq_iff_eq] at hw; subst hw
            refine ⟨c2, ?_⟩
            rw [hst1_1]; dsimp [kWire]; rw [← hstPre_len1, hgetD_append_len]; rfl
          by_cases hpost_k : 1 ≤ post.countP (fun g => (effInputs g).contains kWire)
          · let res := compileLoop 10 post st1
            have hstrPost := hcomp_struct 10 (kWire + 1) (fun w => w == kWire) (fun w hw => by rw [beq_iff_eq] at hw; omega)
              post st1.1 st1.2 (by omega) hZk hst1_bound (by rw [hst1_2]; exact hstrPre.2.1) hfan_post
            have hres_len : res.2.length ≤ 15 := by
              have hlsum : 17 = pre.length + 1 + post.length := by
                rw [← hszD]; change D.gates.length = _; rw [hD_eq, List.length_append, List.length_cons]; omega
              have hc := hstrPost.2.2.2.2
              rw [hcontains_eq_all post kWire] at hc
              change res.2.length + _ ≤ st1.2.length + post.length at hc
              rw [hst1_2] at hc
              omega
            obtain ⟨ext1, hext1⟩ := hstrPre.1
            obtain ⟨ext2, hext2⟩ := hstrPost.1
            have hsem_res : ∀ x : Fin 10 → Bool, x v = false →
                (if b = true then !(evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false)))
                 else evalVal (run res.2 (List.ofFn x)) (res.1.getD u (Sum.inl false))) = G5 x := by
              intro x hxv
              have hWF_pre : ∀ k, k < 10 + stPre.2.length →
                  (run res.2 (List.ofFn x)).getD k false = (run stPre.2 (List.ofFn x)).getD k false := by
                intro k hk
                change (run res.2 (List.ofFn x)).getD k false = _
                have hres_eq : res.2 = stPre.2 ++ ext2 := by
                  change (compileLoop 10 post st1).2 = stPre.2 ++ ext2
                  rw [hext2, hst1_2]
                rw [hres_eq, hrun_append]
                exact hrun_preserves ext2 (run stPre.2 (List.ofFn x)) k (by rw [hrun_len, List.length_ofFn]; exact hk)
              have hsem_pre_WF : ∀ m, evalVal (run res.2 (List.ofFn x)) (stPre.1.getD m (Sum.inl false)) =
                  (run pre (step (List.ofFn x) g0)).getD m false := by
                have hc_pre := hcomp_sem 10 11 (fun w => w == v.val || w == 10)
                  (fun w hw => by simp only [Bool.or_eq_true, beq_iff_eq] at hw; rcases hw with rfl | rfl; exact Nat.lt_succ_of_lt v.isLt; omega)
                  x pre env1 [] (step (List.ofFn x) g0) (by omega) (by rw [henv1_len, hstep_len, List.length_ofFn])
                  hZ1 hbound1 (fun _ h => by cases h) hfan_pre (hsem_in1 stPre.2 x hxv)
                intro m
                have hc1 := hc_pre m
                have heval_agree : evalVal (run res.2 (List.ofFn x)) (stPre.1.getD m (Sum.inl false)) =
                    evalVal (run stPre.2 (List.ofFn x)) (stPre.1.getD m (Sum.inl false)) := by
                  cases hmval : stPre.1.getD m (Sum.inl false) with
                  | inl bv => rfl
                  | inr j =>
                    have hjlt : j < 10 + stPre.2.length := by
                      have hmlt : m < stPre.1.length := by
                        refine Classical.byContradiction fun hge => ?_
                        rw [List.getD_eq_default stPre.1 (Sum.inl false) (by omega)] at hmval; cases hmval
                      rw [List.getD_eq_getElem _ _ hmlt] at hmval
                      exact hstrPre.2.2.1 _ (List.getElem_mem hmlt) j hmval
                    exact hWF_pre j hjlt
                exact heval_agree.trans hc1
              have hsem_st1 := hcomp_step_sem 10 x gm stPre.1 stPre.2 (run pre (step (List.ofFn x) g0)) (run res.2 (List.ofFn x))
                hfan_gm (by rw [hstPre_len1, hrun_len, hstep_len, List.length_ofFn]) hstrPre.2.2.1
                (by intro k hk; change (run res.2 (List.ofFn x)).getD k false = (run st1.2 (List.ofFn x)).getD k false; rw [hst1_2]; exact hWF_pre k (by rw [← hst1_2]; exact hk))
                hsem_pre_WF
              have hcs_post := hcomp_sem 10 (kWire + 1) (fun w => w == kWire) (fun w hw => by rw [beq_iff_eq] at hw; omega)
                x post st1.1 st1.2 (step (run pre (step (List.ofFn x) g0)) gm)
                (by omega) (by rw [hst1_len1, hstep_len, hrun_len, hstep_len, List.length_ofFn]; try (dsimp [kWire]; omega))
                hZk hst1_bound (by rw [hst1_2]; exact hstrPre.2.1) hfan_post hsem_st1 u
              have hrun_full : run post (step (run pre (step (List.ofFn x) g0)) gm) = run (g0 :: D.gates) (List.ofFn x) := by
                rw [hrun_cons, hD_eq, hrun_append, hrun_cons]
              rw [hcs_post, hrun_full, hcomp_full x]
            cases huval : res.1.getD u (Sum.inl false) with
            | inl cOut =>
              exfalso
              have hc0 := hsem_res (fun _ => false) rfl
              have hc1 := hsem_res (fun k => decide (k ≠ v)) (by simp)
              rw [huval] at hc0 hc1
              have hne01 := hP_nonconst v
              rw [← hc0, ← hc1] at hne01
              exact hne01 rfl
            | inr outW =>
              exact hmove_to_9 v ⟨res.2, outW⟩ outW b hstrPost.2.1 hres_len (fun x hxv => by have hc := hsem_res x hxv; rw [huval] at hc; exact hc)
          · have hpost_nk : ∀ g ∈ post, ¬((effInputs g).contains kWire) := List.countP_eq_zero.mp (by omega)
            by_cases huk : u = kWire
            · exfalso
              have hconst_kWire : ∀ x : Fin 10 → Bool, x v = false →
                  (run (g0 :: D.gates) (List.ofFn x)).getD kWire false = c2 := by
                intro x hxv
                have hrun_eq : run (g0 :: D.gates) (List.ofFn x) = run post (step (run pre (step (List.ofFn x) g0)) gm) := by
                  rw [hrun_cons, hD_eq, hrun_append, hrun_cons]
                rw [hrun_eq, hrun_preserves post (step (run pre (step (List.ofFn x) g0)) gm) kWire
                  (by rw [hstep_len, hrun_len, hstep_len, List.length_ofFn]; omega)]
                have hsem_pre := hcomp_sem 10 11 (fun w => w == v.val || w == 10)
                  (fun w hw => by simp only [Bool.or_eq_true, beq_iff_eq] at hw; rcases hw with rfl | rfl; exact Nat.lt_succ_of_lt v.isLt; omega)
                  x pre env1 [] (step (List.ofFn x) g0) (by omega) (by rw [henv1_len, hstep_len, List.length_ofFn])
                  hZ1 hbound1 (fun _ h => by cases h) hfan_pre (hsem_in1 stPre.2 x hxv)
                have hWF_st1 : ∀ k, k < 10 + st1.2.length → (run stPre.2 (List.ofFn x)).getD k false = (run st1.2 (List.ofFn x)).getD k false := by
                  rw [hst1_2]; intro k _; rfl
                have hsem_st1 := hcomp_step_sem 10 x gm stPre.1 stPre.2 (run pre (step (List.ofFn x) g0)) (run stPre.2 (List.ofFn x))
                  hfan_gm (by rw [hstPre_len1, hrun_len, hstep_len, List.length_ofFn]) hstrPre.2.2.1
                  (by intro k _; change (run stPre.2 (List.ofFn x)).getD k false = (run st1.2 (List.ofFn x)).getD k false; rw [hst1_2])
                  hsem_pre kWire
                rw [← hsem_st1, hst1_1]; dsimp [kWire]; rw [← hstPre_len1, hgetD_append_len]; rfl
              have hc0 := hcomp_full (fun _ => false)
              have hc1 := hcomp_full (fun k => decide (k ≠ v))
              rw [huk, hconst_kWire _ rfl] at hc0
              rw [huk, hconst_kWire _ (by simp)] at hc1
              have hne01 := hP_nonconst v
              rw [← hc0, ← hc1] at hne01
              exact hne01 rfl
            · let gsNew : List Gate := g0 :: (pre ++ post.map (shiftG kWire))
              have hfanNew : ∀ g ∈ gsNew, fanOK g := by
                intro g hg
                rw [List.mem_cons, List.mem_append, List.mem_map] at hg
                rcases hg with rfl | hgpre | ⟨gp, hgp, rfl⟩
                · exact hfan0
                · exact hfan_pre g hgpre
                · exact ⟨(hfan_post gp hgp).1, by simpa [shiftG] using (hfan_post gp hgp).2⟩
              have hlenNew : gsNew.length ≤ 17 := by
                have hlsum : 17 = pre.length + 1 + post.length := by
                  rw [← hszD]; change D.gates.length = _; rw [hD_eq, List.length_append, List.length_cons]; omega
                dsimp [gsNew]
                simp only [List.length_append, List.length_map]
                omega
              have hevalNew : ∀ x : Fin 10 → Bool,
                  (run gsNew (List.ofFn x)).getD (shiftIdx kWire u) false =
                    (run (g0 :: D.gates) (List.ofFn x)).getD u false := by
                intro x
                have herr := herase_dead_run pre gm post (step (List.ofFn x) g0) u
                  (by rw [hstep_len, List.length_ofFn]; exact huk)
                  (by simpa only [hstep_len, List.length_ofFn] using hpost_nk) hfan_post
                have hk_eq : (step (List.ofFn x) g0).length + pre.length = kWire := by
                  rw [hstep_len, List.length_ofFn]
                rw [hk_eq] at herr
                change (run gsNew (List.ofFn x)).getD (shiftIdx kWire u) false = (run (g0 :: D.gates) (List.ofFn x)).getD u false
                dsimp [gsNew]
                rw [hrun_cons, herr, hrun_cons, hD_eq]
              apply h1_core gsNew (shiftIdx kWire u) b hfanNew hlenNew
              intro x
              rw [hevalNew x, hcomp_full x]
    -- Bridge helper to invoke h1/h2/h3 after automorphism π
    have hremap_11 : ∀ (π : Fin 10 → Fin 10) (extra' : (Fin 10 → Bool) → Bool)
        (extra : (Fin 10 → Bool) → Bool),
        (∀ x, extra (x ∘ π) = extra' x) →
        (∀ x, g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = extra x) →
        ∀ x : Fin 10 → Bool,
        ((Circuit.mk (D.gates.map (mapPi π)) (remapPi π u)).wires (List.ofFn x ++ [extra' x])).getD (remapPi π u) false =
          (run (g0 :: D.gates) (List.ofFn (x ∘ π))).getD u false := by
      intro π extra' extra hextra hg0x x
      change (run (D.gates.map (mapPi π)) (List.ofFn x ++ [extra' x])).getD (remapPi π u) false =
        (run D.gates (step (List.ofFn (x ∘ π)) g0)).getD u false
      refine (hremap_run π D.gates (List.ofFn x ++ [extra' x]) (step (List.ofFn (x ∘ π)) g0)
        (by rw [List.length_append, List.length_ofFn, List.length_singleton, hstep_len, List.length_ofFn])
        (by rw [List.length_append, List.length_ofFn, List.length_singleton]; omega)
        (fun j => ?_) u).symm
      by_cases hj10 : j < 10
      · have hrm : remapPi π j = (π ⟨j, hj10⟩).val := by dsimp [remapPi]; rw [dif_pos hj10]
        rw [hrm, hstep_pres _ _ _ (by rw [List.length_ofFn]; exact hj10),
          hgetFn10Nat (x ∘ π) j hj10, hgetFn10 x [extra' x] (π ⟨j, hj10⟩)]
        rfl
      · by_cases hj_eq10 : j = 10
        · subst hj_eq10
          have hrm : remapPi π 10 = 10 := rfl
          rw [hrm, hstep_10, happend_10, hg0x (x ∘ π), hextra x]
          rfl
        · have hj11 : 11 ≤ j := by omega
          have hrm : remapPi π j = j := by dsimp [remapPi]; rw [dif_neg (by omega)]
          rw [hrm, List.getD_eq_default (step (List.ofFn (x ∘ π)) g0) false (by rw [hstep_len, List.length_ofFn]; omega),
            List.getD_eq_default (List.ofFn x ++ [extra' x]) false (by rw [List.length_append, List.length_ofFn, List.length_singleton]; omega)]
    cases g0
    rename_i op0 ins0
    rcases hfan0 with ⟨hop0, hil0⟩
    rcases hop0 with rfl | rfl | rfl
    · -- g0 is AND
      cases ins0 with
      | nil => exact hconst_g0 true (fun _ => rfl)
      | cons a t =>
        cases t with
        | nil =>
          by_cases ha10 : a < 10
          · exact hwire_g0 ⟨a, ha10⟩ (fun x => by
              change ((List.ofFn x).getD a false && true) = x ⟨a, ha10⟩
              rw [hgetFn10Nat x a ha10, Bool.and_true])
          · exact hconst_g0 false (fun x => by
              change ((List.ofFn x).getD a false && true) = false
              rw [List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega)]; rfl)
        | cons c r =>
          have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hil0
          subst hr_nil
          by_cases ha10 : a < 10
          · by_cases hc10 : c < 10
            · by_cases hac : a = c
              · subst hac
                exact hwire_g0 ⟨a, ha10⟩ (fun x => by
                  change ((List.ofFn x).getD a false && ((List.ofFn x).getD a false && true)) = x ⟨a, ha10⟩
                  rw [hgetFn10Nat x a ha10, Bool.and_true, Bool.and_self])
              · let v : Fin 10 := ⟨a, ha10⟩
                let w : Fin 10 := ⟨c, hc10⟩
                have hvw : v ≠ w := fun h => hac (congrArg Fin.val h)
                have hv_false : ∀ x : Fin 10 → Bool, x v = false →
                    GateOp.and.eval ([a, c].map fun i => (List.ofFn x).getD i false) = false := by
                  intro x hxv
                  change ((List.ofFn x).getD v.val false && ((List.ofFn x).getD w.val false && true)) = false
                  rw [hgetFn10' x v, hxv]; rfl
                have hw_false : ∀ x : Fin 10 → Bool, x w = false →
                    GateOp.and.eval ([a, c].map fun i => (List.ofFn x).getD i false) = false := by
                  intro x hxw
                  change ((List.ofFn x).getD v.val false && ((List.ofFn x).getD w.val false && true)) = false
                  rw [hgetFn10' x w, hxw]; cases ((List.ofFn x).getD v.val false) <;> rfl
                by_cases hdv : D.gates.countP (fun g => (effInputs g).contains v.val) = 0
                · exfalso
                  have huv : u ≠ v.val := by
                    intro heq
                    obtain ⟨x, hx⟩ := hP_not_lit v b
                    have hc := hcomp_full x
                    have hv : (run (⟨GateOp.and, [a, c]⟩ :: D.gates) (List.ofFn x)).getD v.val false = x v := by
                      rw [hrun_preserves (⟨GateOp.and, [a, c]⟩ :: D.gates) (List.ofFn x) v.val (by rw [List.length_ofFn]; exact v.isLt), hgetFn10' x v]
                    rw [heq, hv] at hc; exact hx hc
                  obtain ⟨q, hqv, hqw, hqG⟩ := hP_and_wit v w hvw
                  apply hqG
                  let xA : Fin 10 → Bool := fun k => decide (k = q)
                  let xB : Fin 10 → Bool := fun k => decide (k = v ∨ k = q)
                  have hstep10 : (step (List.ofFn xA) ⟨GateOp.and, [a, c]⟩).getD 10 false = false ∧
                      (step (List.ofFn xB) ⟨GateOp.and, [a, c]⟩).getD 10 false = false := by
                    constructor
                    · rw [hstep_10]; exact hv_false xA (by simp [xA, hqv.symm])
                    · rw [hstep_10]; exact hw_false xB (by simp [xB, hvw.symm, hqw.symm])
                  have hagree_D : (run D.gates (step (List.ofFn xA) ⟨GateOp.and, [a, c]⟩)).getD u false =
                      (run D.gates (step (List.ofFn xB) ⟨GateOp.and, [a, c]⟩)).getD u false := by
                    apply hcomp_init_Agree (step (List.ofFn xA) ⟨GateOp.and, [a, c]⟩) (step (List.ofFn xB) ⟨GateOp.and, [a, c]⟩)
                      D.gates (fun i => i = v.val) u
                      (by rw [hstep_len, hstep_len, List.length_ofFn, List.length_ofFn]) huv
                    · intro m hm
                      by_cases hm10 : m < 10
                      · rw [hstep_pres _ _ _ (by rw [List.length_ofFn]; exact hm10),
                          hstep_pres _ _ _ (by rw [List.length_ofFn]; exact hm10),
                          hgetFn10Nat xA m hm10, hgetFn10Nat xB m hm10]
                        have hmv : (⟨m, hm10⟩ : Fin 10) ≠ v := fun h => hm (congrArg Fin.val h)
                        dsimp [xA, xB]; simp [hmv]
                      · by_cases hm10' : m = 10
                        · subst hm10'; rw [hstep10.1, hstep10.2]
                        · rw [List.getD_eq_default (step (List.ofFn xA) ⟨GateOp.and, [a, c]⟩) false (by rw [hstep_len, List.length_ofFn]; omega),
                            List.getD_eq_default (step (List.ofFn xB) ⟨GateOp.and, [a, c]⟩) false (by rw [hstep_len, List.length_ofFn]; omega)]
                    · intro g hg w' hw' heq
                      exact List.countP_eq_zero.mp hdv g hg (heq ▸ List.contains_iff_mem.mpr hw')
                    · exact hfanD'
                  rw [← hcomp_full xA, ← hcomp_full xB, hrun_cons, hrun_cons, hagree_D]
                · exact hconst10_kill v false hv_false (Or.inl (by omega))
            · exact hconst_g0 false (fun x => by
                change ((List.ofFn x).getD a false && ((List.ofFn x).getD c false && true)) = false
                have hc_def : (List.ofFn x).getD c false = false := List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega); rw [hc_def, Bool.false_and, Bool.and_false])
          · exact hconst_g0 false (fun x => by
              change ((List.ofFn x).getD a false && ((List.ofFn x).getD c false && true)) = false
              rw [List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega), Bool.false_and])
    · -- g0 is OR
      cases ins0 with
      | nil => exact hconst_g0 false (fun _ => rfl)
      | cons a t =>
        cases t with
        | nil =>
          by_cases ha10 : a < 10
          · exact hwire_g0 ⟨a, ha10⟩ (fun x => by
              change ((List.ofFn x).getD a false || false) = x ⟨a, ha10⟩
              rw [hgetFn10Nat x a ha10, Bool.or_false])
          · exact hconst_g0 false (fun x => by
              change ((List.ofFn x).getD a false || false) = false
              rw [List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega)]; rfl)
        | cons c r =>
          have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hil0
          subst hr_nil
          by_cases ha10 : a < 10
          · by_cases hc10 : c < 10
            · by_cases hac : a = c
              · subst hac
                exact hwire_g0 ⟨a, ha10⟩ (fun x => by
                  change ((List.ofFn x).getD a false || ((List.ofFn x).getD a false || false)) = x ⟨a, ha10⟩
                  rw [hgetFn10Nat x a ha10, Bool.or_false, Bool.or_self])
              · let v : Fin 10 := ⟨a, ha10⟩
                let w : Fin 10 := ⟨c, hc10⟩
                have hvw : v ≠ w := fun h => hac (congrArg Fin.val h)
                have hdv_le1 : D.gates.countP (fun g => (effInputs g).contains v.val) ≤ 1 := by
                  have h := hle2_all v
                  rw [List.countP_cons] at h
                  have hv_in : (effInputs ⟨GateOp.or, [a, c]⟩).contains v.val = true := by
                    change ([a, c].contains a) = true; simp
                  rw [hv_in] at h
                  simp only [↓reduceIte] at h
                  omega
                have hdw_le1 : D.gates.countP (fun g => (effInputs g).contains w.val) ≤ 1 := by
                  have h := hle2_all w
                  rw [List.countP_cons] at h
                  have hw_in : (effInputs ⟨GateOp.or, [a, c]⟩).contains w.val = true := by
                    change ([a, c].contains c) = true; simp
                  rw [hw_in] at h
                  simp only [↓reduceIte] at h
                  omega
                have hdv_ne0 : D.gates.countP (fun g => (effInputs g).contains v.val) ≠ 0 := by
                  intro hzero
                  have huv : u ≠ v.val := by
                    intro heq
                    obtain ⟨x, hx⟩ := hP_not_lit v b
                    have hc := hcomp_full x
                    have hv : (run (⟨GateOp.or, [a, c]⟩ :: D.gates) (List.ofFn x)).getD v.val false = x v := by
                      rw [hrun_preserves (⟨GateOp.or, [a, c]⟩ :: D.gates) (List.ofFn x) v.val (by rw [List.length_ofFn]; exact v.isLt), hgetFn10' x v]
                    rw [heq, hv] at hc; exact hx hc
                  have hkill_vw : ∀ xA xB : Fin 10 → Bool,
                      (∀ k : Fin 10, k ≠ v → xA k = xB k) → xA w = true → xB w = true → G5 xA ≠ G5 xB → False := by
                    intro xA xB hsame hAw hBw hneG
                    apply hneG
                    have hstep10 : (step (List.ofFn xA) ⟨GateOp.or, [a, c]⟩).getD 10 false = true ∧
                        (step (List.ofFn xB) ⟨GateOp.or, [a, c]⟩).getD 10 false = true := by
                      constructor
                      · rw [hstep_10]
                        change ((List.ofFn xA).getD v.val false || ((List.ofFn xA).getD w.val false || false)) = true
                        rw [hgetFn10' xA w, hAw]; simp
                      · rw [hstep_10]
                        change ((List.ofFn xB).getD v.val false || ((List.ofFn xB).getD w.val false || false)) = true
                        rw [hgetFn10' xB w, hBw]; simp
                    have hagree_D : (run D.gates (step (List.ofFn xA) ⟨GateOp.or, [a, c]⟩)).getD u false =
                        (run D.gates (step (List.ofFn xB) ⟨GateOp.or, [a, c]⟩)).getD u false := by
                      apply hcomp_init_Agree (step (List.ofFn xA) ⟨GateOp.or, [a, c]⟩) (step (List.ofFn xB) ⟨GateOp.or, [a, c]⟩)
                        D.gates (fun i => i = v.val) u
                        (by rw [hstep_len, hstep_len, List.length_ofFn, List.length_ofFn]) huv
                      · intro m hm
                        by_cases hm10 : m < 10
                        · rw [hstep_pres _ _ _ (by rw [List.length_ofFn]; exact hm10),
                            hstep_pres _ _ _ (by rw [List.length_ofFn]; exact hm10),
                            hgetFn10Nat xA m hm10, hgetFn10Nat xB m hm10]
                          exact hsame ⟨m, hm10⟩ (fun h => hm (congrArg Fin.val h))
                        · by_cases hm10' : m = 10
                          · subst hm10'; rw [hstep10.1, hstep10.2]
                          · rw [List.getD_eq_default (step (List.ofFn xA) ⟨GateOp.or, [a, c]⟩) false (by rw [hstep_len, List.length_ofFn]; omega),
                              List.getD_eq_default (step (List.ofFn xB) ⟨GateOp.or, [a, c]⟩) false (by rw [hstep_len, List.length_ofFn]; omega)]
                      · intro g hg w' hw' heq
                        exact List.countP_eq_zero.mp hzero g hg (heq ▸ List.contains_iff_mem.mpr hw')
                      · exact hfanD'
                    rw [← hcomp_full xA, ← hcomp_full xB, hrun_cons, hrun_cons, hagree_D]
                  rcases hP_or_wit v w hvw with h1' | ⟨q, hqv, hqw, h2'⟩
                  · exact hkill_vw (fun k => decide (k = w)) (fun k => decide (k = v ∨ k = w))
                      (fun k hk => by simp [hk]) (by simp) (by simp) h1'
                  · exact hkill_vw (fun k => decide (k = w ∨ k = q)) (fun k => decide (k = v ∨ k = w ∨ k = q))
                      (fun k hk => by simp [hk]) (by simp) (by simp) h2'
                have hdw_ne0 : D.gates.countP (fun g => (effInputs g).contains w.val) ≠ 0 := by
                  intro hzero
                  have huw : u ≠ w.val := by
                    intro heq
                    obtain ⟨x, hx⟩ := hP_not_lit w b
                    have hc := hcomp_full x
                    have hw : (run (⟨GateOp.or, [a, c]⟩ :: D.gates) (List.ofFn x)).getD w.val false = x w := by
                      rw [hrun_preserves (⟨GateOp.or, [a, c]⟩ :: D.gates) (List.ofFn x) w.val (by rw [List.length_ofFn]; exact w.isLt), hgetFn10' x w]
                    rw [heq, hw] at hc; exact hx hc
                  have hkill_wv : ∀ xA xB : Fin 10 → Bool,
                      (∀ k : Fin 10, k ≠ w → xA k = xB k) → xA v = true → xB v = true → G5 xA ≠ G5 xB → False := by
                    intro xA xB hsame hAv hBv hneG
                    apply hneG
                    have hstep10 : (step (List.ofFn xA) ⟨GateOp.or, [a, c]⟩).getD 10 false = true ∧
                        (step (List.ofFn xB) ⟨GateOp.or, [a, c]⟩).getD 10 false = true := by
                      constructor
                      · rw [hstep_10]
                        change ((List.ofFn xA).getD v.val false || ((List.ofFn xA).getD w.val false || false)) = true
                        rw [hgetFn10' xA v, hAv]; simp
                      · rw [hstep_10]
                        change ((List.ofFn xB).getD v.val false || ((List.ofFn xB).getD w.val false || false)) = true
                        rw [hgetFn10' xB v, hBv]; simp
                    have hagree_D : (run D.gates (step (List.ofFn xA) ⟨GateOp.or, [a, c]⟩)).getD u false =
                        (run D.gates (step (List.ofFn xB) ⟨GateOp.or, [a, c]⟩)).getD u false := by
                      apply hcomp_init_Agree (step (List.ofFn xA) ⟨GateOp.or, [a, c]⟩) (step (List.ofFn xB) ⟨GateOp.or, [a, c]⟩)
                        D.gates (fun i => i = w.val) u
                        (by rw [hstep_len, hstep_len, List.length_ofFn, List.length_ofFn]) huw
                      · intro m hm
                        by_cases hm10 : m < 10
                        · rw [hstep_pres _ _ _ (by rw [List.length_ofFn]; exact hm10),
                            hstep_pres _ _ _ (by rw [List.length_ofFn]; exact hm10),
                            hgetFn10Nat xA m hm10, hgetFn10Nat xB m hm10]
                          exact hsame ⟨m, hm10⟩ (fun h => hm (congrArg Fin.val h))
                        · by_cases hm10' : m = 10
                          · subst hm10'; rw [hstep10.1, hstep10.2]
                          · rw [List.getD_eq_default (step (List.ofFn xA) ⟨GateOp.or, [a, c]⟩) false (by rw [hstep_len, List.length_ofFn]; omega),
                              List.getD_eq_default (step (List.ofFn xB) ⟨GateOp.or, [a, c]⟩) false (by rw [hstep_len, List.length_ofFn]; omega)]
                      · intro g hg w' hw' heq
                        exact List.countP_eq_zero.mp hzero g hg (heq ▸ List.contains_iff_mem.mpr hw')
                      · exact hfanD'
                    rw [← hcomp_full xA, ← hcomp_full xB, hrun_cons, hrun_cons, hagree_D]
                  rcases hP_or_wit w v hvw.symm with h1' | ⟨q, hqw, hqv, h2'⟩
                  · exact hkill_wv (fun k => decide (k = v)) (fun k => decide (k = w ∨ k = v))
                      (fun k hk => by simp [hk]) (by simp) (by simp) h1'
                  · exact hkill_wv (fun k => decide (k = v ∨ k = q)) (fun k => decide (k = w ∨ k = v ∨ k = q))
                      (fun k hk => by simp [hk]) (by simp) (by simp) h2'
                have hdv_eq1 : D.gates.countP (fun g => (effInputs g).contains v.val) = 1 := by omega
                have hdw_eq1 : D.gates.countP (fun g => (effInputs g).contains w.val) = 1 := by omega
                let u1 := sigma0 v w
                have hu1_ne0 : u1 ≠ 0 := by
                  intro h0
                  apply hvw
                  have hs1 := congrArg (sigma0Inv v) h0
                  have hs2 := hs0_inv2 v w
                  have h0' : sigma0Inv v 0 = v := by
                    rw [← hs0_self v, hs0_inv2 v v]
                  rw [hs2, h0'] at hs1
                  exact hs1.symm
                let π : Fin 10 → Fin 10 := fun k => stab0 u1 (sigma0 v k)
                let πInv : Fin 10 → Fin 10 := fun k => sigma0Inv v (stab0Inv u1 k)
                have hpi_inv1 : ∀ k, π (πInv k) = k := by
                  intro k; dsimp [π, πInv]; rw [hs0_inv1, hst0_inv1]
                have hpi_inv2 : ∀ k, πInv (π k) = k := by
                  intro k; dsimp [π, πInv]; rw [hst0_inv2, hs0_inv2]
                have hpi_v : π v = 0 := by dsimp [π]; rw [hs0_self v, hst0_0 u1]
                let D' : Circuit := ⟨D.gates.map (mapPi π), remapPi π u⟩
                have hfanD'_pi : FanInTwo D' := by
                  intro g hg
                  rw [List.mem_map] at hg
                  rcases hg with ⟨g', hg', rfl⟩
                  exact ⟨(hfanD' g' hg').1, by simpa [mapPi] using (hfanD' g' hg').2⟩
                have hszD'_pi : D'.size = 17 := by
                  change (D.gates.map (mapPi π)).length = 17
                  rw [List.length_map]; exact hszD
                have hc_0 : D'.gates.countP (fun g => (effInputs g).contains 0) = 1 := by
                  change (D.gates.map (mapPi π)).countP (fun g => (effInputs g).contains 0) = 1
                  rw [hremap_eff_contains π πInv hpi_inv1 hpi_inv2]
                  have hr0 : remapPi πInv 0 = v.val := by
                    dsimp [remapPi]
                    change (πInv 0).val = v.val
                    rw [← hpi_v, hpi_inv2]
                  rw [hr0]; exact hdv_eq1
                have hc_all : ∀ q : Fin 10, D'.gates.countP (fun g => (effInputs g).contains q.val) ≤ 2 := by
                  intro q
                  change (D.gates.map (mapPi π)).countP (fun g => (effInputs g).contains q.val) ≤ 2
                  rw [hremap_eff_contains π πInv hpi_inv1 hpi_inv2]
                  have hrq : remapPi πInv q.val = (πInv q).val := by
                    dsimp [remapPi]; split_ifs with hq
                    · rfl
                    · exact absurd q.isLt hq
                  rw [hrq]; exact hle2_D (πInv q)
                have hG5_pi : ∀ x : Fin 10 → Bool, G5 (x ∘ π) = G5 x := by
                  intro x
                  change G5 ((x ∘ stab0 u1) ∘ sigma0 v) = G5 x
                  rw [hG5_sigma0, hG5_stab0]
                rcases hst0_12 u1 hu1_ne0 with hpi_w | hpi_w
                · have hpi_w' : π w = 1 := hpi_w
                  have hc_1 : D'.gates.countP (fun g => (effInputs g).contains 1) = 1 := by
                    change (D.gates.map (mapPi π)).countP (fun g => (effInputs g).contains 1) = 1
                    rw [hremap_eff_contains π πInv hpi_inv1 hpi_inv2]
                    have hr1 : remapPi πInv 1 = w.val := by
                      dsimp [remapPi]
                      change (πInv 1).val = w.val
                      have h1eq : (1 : Fin 10) = π w := hpi_w'.symm
                      rw [h1eq, hpi_inv2]
                    rw [hr1]; exact hdw_eq1
                  have hcompD' : ∀ x : Fin 10 → Bool,
                      (if b = true then !((D'.wires (List.ofFn x ++ [x 0 || x 1])).getD (remapPi π u) false)
                       else (D'.wires (List.ofFn x ++ [x 0 || x 1])).getD (remapPi π u) false) = G5 x := by
                    intro x
                    have h11 := hremap_11 π (fun y => y 0 || y 1) (fun y => y v || y w)
                      (fun y => by change (y (π v) || y (π w)) = (y 0 || y 1); rw [hpi_v, hpi_w'])
                      (fun y => by change ((List.ofFn y).getD a false || ((List.ofFn y).getD c false || false)) = (y v || y w); rw [hgetFn10Nat y a ha10, hgetFn10Nat y c hc10, Bool.or_false]) x
                    dsimp only [D']
                    rw [h11, hcomp_full (x ∘ π), hG5_pi x]
                  obtain ⟨E, u', b', hE, hszE, hEq⟩ := h2 D' (remapPi π u) b hfanD'_pi hszD'_pi hc_0 hc_1 hc_all hcompD'
                  refine ⟨E, u', b', hE, hszE, fun x hx9 => ?_⟩
                  exact (hEq x hx9).trans (hG5_eq x).symm
                · have hpi_w' : π w = 2 := hpi_w
                  have hc_2 : D'.gates.countP (fun g => (effInputs g).contains 2) = 1 := by
                    change (D.gates.map (mapPi π)).countP (fun g => (effInputs g).contains 2) = 1
                    rw [hremap_eff_contains π πInv hpi_inv1 hpi_inv2]
                    have hr2 : remapPi πInv 2 = w.val := by
                      dsimp [remapPi]
                      change (πInv 2).val = w.val
                      have h2eq : (2 : Fin 10) = π w := hpi_w'.symm
                      rw [h2eq, hpi_inv2]
                    rw [hr2]; exact hdw_eq1
                  have hcompD' : ∀ x : Fin 10 → Bool,
                      (if b = true then !((D'.wires (List.ofFn x ++ [x 0 || x 2])).getD (remapPi π u) false)
                       else (D'.wires (List.ofFn x ++ [x 0 || x 2])).getD (remapPi π u) false) = G5 x := by
                    intro x
                    have h11 := hremap_11 π (fun y => y 0 || y 2) (fun y => y v || y w)
                      (fun y => by change (y (π v) || y (π w)) = (y 0 || y 2); rw [hpi_v, hpi_w'])
                      (fun y => by change ((List.ofFn y).getD a false || ((List.ofFn y).getD c false || false)) = (y v || y w); rw [hgetFn10Nat y a ha10, hgetFn10Nat y c hc10, Bool.or_false]) x
                    dsimp only [D']
                    rw [h11, hcomp_full (x ∘ π), hG5_pi x]
                  obtain ⟨E, u', b', hE, hszE, hEq⟩ := h3 D' (remapPi π u) b hfanD'_pi hszD'_pi hc_0 hc_2 hc_all hcompD'
                  refine ⟨E, u', b', hE, hszE, fun x hx9 => ?_⟩
                  exact (hEq x hx9).trans (hG5_eq x).symm
            · exact hwire_g0 ⟨a, ha10⟩ (fun x => by
                change ((List.ofFn x).getD a false || ((List.ofFn x).getD c false || false)) = x ⟨a, ha10⟩
                rw [hgetFn10Nat x a ha10, List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega), Bool.or_false, Bool.or_false])
          · by_cases hc10 : c < 10
            · exact hwire_g0 ⟨c, hc10⟩ (fun x => by
                change ((List.ofFn x).getD a false || ((List.ofFn x).getD c false || false)) = x ⟨c, hc10⟩
                rw [List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega), hgetFn10Nat x c hc10, Bool.false_or, Bool.or_false])
            · exact hconst_g0 false (fun x => by
                change ((List.ofFn x).getD a false || ((List.ofFn x).getD c false || false)) = false
                rw [List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega),
                  List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega)]; rfl)
    · -- g0 is NOT
      cases ins0 with
      | nil => exact hconst_g0 true (fun _ => rfl)
      | cons a t =>
        by_cases ha10 : a < 10
        · let v : Fin 10 := ⟨a, ha10⟩
          have hv_false : ∀ x : Fin 10 → Bool, x v = false →
              GateOp.not.eval ((a :: t).map fun i => (List.ofFn x).getD i false) = true := by
            intro x hxv
            change Bool.not (( (List.ofFn x).getD v.val false :: _).headD false) = true
            rw [List.headD_cons, hgetFn10' x v, hxv]; rfl
          by_cases hkill : 1 ≤ D.gates.countP (fun g => (effInputs g).contains v.val) ∨
              D.gates.countP (fun g => (effInputs g).contains 10) ≠ 1
          · exact hconst10_kill v true hv_false hkill
          · push Not at hkill
            have hdv_0 : D.gates.countP (fun g => (effInputs g).contains v.val) = 0 := by omega
            have hd10_1 : D.gates.countP (fun g => (effInputs g).contains 10) = 1 := hkill.2
            let π := sigma0 v
            let πInv := sigma0Inv v
            let D' : Circuit := ⟨D.gates.map (mapPi π), remapPi π u⟩
            have hfanD'_pi : FanInTwo D' := by
              intro g hg
              rw [List.mem_map] at hg
              rcases hg with ⟨g', hg', rfl⟩
              exact ⟨(hfanD' g' hg').1, by simpa [mapPi] using (hfanD' g' hg').2⟩
            have hszD'_pi : D'.size = 17 := by
              change (D.gates.map (mapPi π)).length = 17
              rw [List.length_map]; exact hszD
            have hc_0 : D'.gates.countP (fun g => (effInputs g).contains 0) = 0 := by
              change (D.gates.map (mapPi π)).countP (fun g => (effInputs g).contains 0) = 0
              rw [hremap_eff_contains π πInv (hs0_inv1 v) (hs0_inv2 v)]
              have hr0 : remapPi πInv 0 = v.val := by
                dsimp [remapPi]
                change (sigma0Inv v 0).val = v.val; rw [← hs0_self v, hs0_inv2 v]
              rw [hr0]; exact hdv_0
            have hc_10 : D'.gates.countP (fun g => (effInputs g).contains 10) = 1 := by
              change (D.gates.map (mapPi π)).countP (fun g => (effInputs g).contains 10) = 1
              rw [hremap_eff_contains π πInv (hs0_inv1 v) (hs0_inv2 v)]
              have hr10 : remapPi πInv 10 = 10 := rfl
              rw [hr10]; exact hd10_1
            have hc_all : ∀ q : Fin 10, D'.gates.countP (fun g => (effInputs g).contains q.val) ≤ 2 := by
              intro q
              change (D.gates.map (mapPi π)).countP (fun g => (effInputs g).contains q.val) ≤ 2
              rw [hremap_eff_contains π πInv (hs0_inv1 v) (hs0_inv2 v)]
              have hrq : remapPi πInv q.val = (πInv q).val := by
                dsimp [remapPi]; split_ifs with hq
                · rfl
                · exact absurd q.isLt hq
              rw [hrq]; exact hle2_D (πInv q)
            have hcompD' : ∀ x : Fin 10 → Bool,
                (if b = true then !((D'.wires (List.ofFn x ++ [!x 0])).getD (remapPi π u) false)
                 else (D'.wires (List.ofFn x ++ [!x 0])).getD (remapPi π u) false) = G5 x := by
              intro x
              have h11 := hremap_11 π (fun y => !y 0) (fun y => !y v)
                (fun y => by change Bool.not (y (π v)) = Bool.not (y 0); dsimp only [π]; rw [hs0_self v])
                (fun y => by
                  change Bool.not (( (List.ofFn y).getD v.val false :: _).headD false) = Bool.not (y v)
                  rw [List.headD_cons, hgetFn10' y v]) x
              dsimp only [D']
              rw [h11, hcomp_full (x ∘ π), hG5_sigma0 v x]
            obtain ⟨E, u', b', hE, hszE, hEq⟩ := h1 D' (remapPi π u) b hfanD'_pi hszD'_pi hc_0 hc_10 hc_all hcompD'
            refine ⟨E, u', b', hE, hszE, fun x hx9 => ?_⟩
            exact (hEq x hx9).trans (hG5_eq x).symm
        · exact hconst_g0 true (fun x => by
            change Bool.not (( (List.ofFn x).getD a false :: _).headD false) = true
            rw [List.headD_cons, List.getD_eq_default (List.ofFn x) false (by rw [List.length_ofFn]; omega)]; rfl)
