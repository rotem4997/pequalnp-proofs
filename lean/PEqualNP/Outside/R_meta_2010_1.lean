import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The suffix has ten input wires. Setting wires 0, 4, and 9 to false
-- gives the seven-input theta graph. Its eleven-gate bound leaves room
-- for at most three gates that read any of these three wires.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_2010_1
    (countReaders : ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
      (∀ y : Fin 7 → Bool, D.eval [false, y 3, y 0, y 2, false, y 6, y 4, y 5, y 1, false] = (fun y : Fin 7 → Bool => (y 0 && y 2) || (y 2 && y 1) || (y 0 && y 3) || (y 3 && y 4) || (y 4 && y 1) || (y 0 && y 5) || (y 5 && y 6) || (y 6 && y 1)) y) →
      ∀ S : Finset (Fin D.gates.length), (∀ i ∈ S,
        ∃ w ∈ (D.gates.get i).inputs, (w = 0 ∨ w = 4 ∨ w = 9) ∧
        ((D.gates.get i).op = GateOp.not → (D.gates.get i).inputs.head? = some w)) → S.card ≤ 3)
    (splice : ∀ D : Circuit, let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      FanInTwo D → D.size ≤ 14 → (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4]) = f x) →
      (∀ S : Finset (Fin D.gates.length), (∀ i ∈ S,
        ∃ w ∈ (D.gates.get i).inputs, (w = 0 ∨ w = 4 ∨ w = 9) ∧
        ((D.gates.get i).op = GateOp.not → (D.gates.get i).inputs.head? = some w)) → S.card ≤ 3) →
      HasCircuitSize 9 f 14 ∨ ∃ B : Circuit, FanInTwo B ∧ B.size ≤ 11 ∧
        circuitFun 7 B = (fun y => f (Fin.insertNth 0 false (Fin.insertNth 3 false y))) ∧
        ∀ t : Bool, ∃ (u v : ℕ) (K : Circuit), K.output = B.output + 1 ∧
          List.Forall₂ (fun g h => g.op = h.op ∧ List.Forall₂ (fun a b =>
            b = a + 1 ∨ b = 0 ∧ (a = u ∨ a = v)) g.inputs h.inputs) B.gates K.gates ∧
          ∀ y : Fin 7 → Bool, K.eval (true :: List.ofFn y) =
            f (Fin.insertNth 0 t (Fin.insertNth 3 (!t) y))) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → x2.size ≤ (15 : ℕ) → PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ) ∨ ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size ≤ (11 : ℕ) ∧ (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x7 = fun (x8 : Fin (7 : ℕ) → Bool) => x1 (Fin.insertNth (0 : Fin (9 : ℕ)) Bool.false (Fin.insertNth (3 : Fin (8 : ℕ)) Bool.false x8))) ∧ ∀ (x8 : Bool), ∃ (x9 : ℕ) (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Circuit), x11.output = x7.output + (1 : ℕ) ∧ List.Forall₂ (fun (x12 x13 : PEqualNP.CircuitLowerBounds.Gate) => x12.op = x13.op ∧ List.Forall₂ (fun (x14 x15 : ℕ) => x15 = x14 + (1 : ℕ) ∨ x15 = (0 : ℕ) ∧ (x14 = x9 ∨ x14 = x10)) x12.inputs x13.inputs) x7.gates x11.gates ∧ ∀ (x12 : Fin (7 : ℕ) → Bool), x11.eval (Bool.true :: List.ofFn x12) = x1 (Fin.insertNth (0 : Fin (9 : ℕ)) x8 (Fin.insertNth (3 : Fin (8 : ℕ)) (!x8) x12)) := by
  let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  intro graphValue C fan first computes size
  cases gates : C.gates with
  | nil =>
    have h := first (fun _ => true)
    have wrong : (C.wires (List.ofFn (fun _ : Fin 9 => true))).getD 9 false = false := by
      change (C.gates.foldl (fun w (h : Gate) => w ++ [h.op.eval (h.inputs.map (fun j => w.getD j false))]) (List.ofFn (fun _ : Fin 9 => true))).getD 9 false = false
      rw [gates, List.foldl_nil]
      simp
    rw [wrong] at h
    contradiction
  | cons g gs =>
    let D : Circuit := ⟨gs, C.output⟩
    have fanD : FanInTwo D := fun h hh => fan h (by rw [gates]; exact List.mem_cons_of_mem g hh)
    have sizeD : D.size ≤ 14 := by
      change C.gates.length ≤ 15 at size
      change gs.length ≤ 14
      rw [gates, List.length_cons] at size
      omega
    have keep (l : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
        (l.foldl (fun w (h : Gate) => w ++ [h.op.eval (h.inputs.map (fun j => w.getD j false))]) xs).getD i false =
          xs.getD i false := by
      induction l generalizing xs with
      | nil => rfl
      | cons h l ih =>
        rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]
    have suffix (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 || x 4]) = f x := by
      let w := List.ofFn x
      let value := g.op.eval (g.inputs.map (fun i => w.getD i false))
      have val : value = (x 0 || x 4) := by
        have hp := first x
        change (C.gates.foldl (fun w (h : Gate) => w ++ [h.op.eval (h.inputs.map (fun j => w.getD j false))]) (List.ofFn x)).getD 9 false = _ at hp
        rw [gates, List.foldl_cons] at hp
        change (gs.foldl _ (w ++ [value])).getD 9 false = _ at hp
        rw [keep gs (w ++ [value]) 9 (by simp [w])] at hp
        have atNine : (w ++ [value]).getD w.length false = value := by simp
        have len : w.length = 9 := by simp [w]
        rw [len] at atNine
        exact atNine.symm.trans hp
      have eqv := congrFun computes x
      change (C.wires (List.ofFn x)).getD C.output false = f x at eqv
      change (C.gates.foldl (fun w (h : Gate) => w ++ [h.op.eval (h.inputs.map (fun j => w.getD j false))]) (List.ofFn x)).getD C.output false = _ at eqv
      rw [gates, List.foldl_cons] at eqv
      change (gs.foldl _ (w ++ [value])).getD C.output false = f x at eqv
      rw [val] at eqv
      exact eqv
    apply splice D fanD sizeD suffix
    apply countReaders D fanD sizeD
    intro y
    let x : Fin 9 → Bool := ![false, y 3, y 0, y 2, false, y 6, y 4, y 5, y 1]
    have hx : List.ofFn x ++ [x 0 || x 4] = [false, y 3, y 0, y 2, false, y 6, y 4, y 5, y 1, false] := rfl
    rw [← hx, suffix]
    have graph : ∀ z : Fin 7 → Bool, f (![false, z 3, z 0, z 2, false, z 6, z 4, z 5, z 1]) = (fun y : Fin 7 → Bool => (y 0 && y 2) || (y 2 && y 1) || (y 0 && y 3) || (y 3 && y 4) || (y 4 && y 1) || (y 0 && y 5) || (y 5 && y 6) || (y 6 && y 1)) z := by decide +kernel
    exact graph y
