import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4940_631
    (restrict : let P := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
      (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1))) ||
      (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2)))
      ∀ C : Circuit, FanInTwo C → (∀ x, C.eval (List.ofFn x) = P x) →
      ∃ D : Circuit, FanInTwo D ∧
        D.gates.countP (fun g : Gate => GateOp.rec true true false (fun _ => true) true g.op) + 1 ≤ C.gates.countP (fun g : Gate => GateOp.rec true true false (fun _ => true) true g.op) ∧
        ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = P (Fin.lastCases false y))
    (floor : let P := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
      (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1))) ||
      (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2)))
      ∀ D : Circuit, FanInTwo D →
      (∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = P (Fin.lastCases false y)) →
      14 ≤ D.gates.countP (fun g : Gate => GateOp.rec true true false (fun _ => true) true g.op))
    (few : let P := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
      (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1))) ||
      (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2)))
      ∀ D : Circuit, FanInTwo D → D.size = 18 →
      D.gates.countP (fun g : Gate => GateOp.rec false false true (fun _ => false) false g.op) ≤ 4 →
      ∀ a b : ℕ, ¬ ∀ x : Fin 10 → Bool,
        ((D.wires (List.ofFn x)).getD a false ||
        (D.wires (List.ofFn x)).getD b false) = P x) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size = (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  intro g tail a b fanG fanT sizeT
  let P := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
      (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1))) ||
      (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2)))
  let F := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let cost : Gate → Bool := fun g : Gate => GateOp.rec true true false (fun _ => true) true g.op
  let neg : Gate → Bool := fun g : Gate => GateOp.rec false false true (fun _ => false) false g.op
  let D : Circuit := ⟨g :: tail.gates, 0⟩
  let W := fun (x : Fin 10 → Bool) (i : ℕ) => (D.wires (List.ofFn x)).getD i false
  change (∃ x, W x a = true ∧ W x b = false) →
    (∃ x, W x a = false ∧ W x b = true) →
    (∀ x, F x = false → W x a = false ∧ W x b = false) →
    ∃ x, F x = true ∧ W x a = false ∧ W x b = false
  intro _ _ off
  have same (x : Fin 10 → Bool) : P x = F x := by
    change (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) ||
      (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) ||
      (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) ||
      (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) ||
      (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false))))) = _
    dsimp only [F]
    simp only [Bool.or_false]
    ac_rfl
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
  have covered (x : Fin 10 → Bool) : (W x a || W x b) = P x := by
    rw [same]
    cases hf : F x with
    | false =>
      obtain ⟨ha,hb⟩ := off x hf
      rw [ha,hb]
      rfl
    | true =>
      cases ha : W x a <;> cases hb : W x b
      · exact False.elim (missed ⟨x,hf,ha,hb⟩)
      all_goals rfl
  let last : Gate := ⟨.or, [a,b]⟩
  let E : Circuit := ⟨D.gates ++ [last], 10 + D.size⟩
  have fanE : FanInTwo E := by
    intro h mem
    rcases List.mem_append.mp mem with hd | hl
    · exact fanD _ hd
    · have eq : h = last := List.mem_singleton.mp hl
      subst h
      constructor
      · exact Or.inr (Or.inl rfl)
      · exact Nat.le_refl 2
  have lenW (gs : List Gate) (w : List Bool) :
      (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons h gs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append,List.length_cons,List.length_nil]
      omega
  have orEval (u v : Bool) : GateOp.or.eval [u,v] = (u || v) := by
    cases u <;> cases v <;> rfl
  have computes (x : Fin 10 → Bool) : E.eval (List.ofFn x) = P x := by
    have dl : (D.wires (List.ofFn x)).length = 10 + D.size := by
      change (D.gates.foldl _ (List.ofFn x)).length = _
      rw [lenW]
      simp only [List.length_ofFn]
      rfl
    change ((D.gates ++ [last]).foldl _ (List.ofFn x)).getD (10 + D.size) false = _
    rw [List.foldl_append]
    change ((D.wires (List.ofFn x)) ++ [GateOp.or.eval [W x a,W x b]]).getD (10 + D.size) false = _
    rw [orEval,← dl]
    simpa using covered x
  obtain ⟨T,fanT,cut,evalT⟩ := restrict E fanE computes
  have lower := floor T fanT evalT
  change T.gates.countP cost + 1 ≤ E.gates.countP cost at cut
  change 14 ≤ T.gates.countP cost at lower
  have bound : 15 ≤ E.gates.countP cost := by omega
  have partition (gs : List Gate) : gs.countP cost + gs.countP neg = gs.length := by
    induction gs with
    | nil => rfl
    | cons h gs ih =>
      obtain ⟨op,ins⟩ := h
      cases op <;> simpa [cost,neg,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using congrArg Nat.succ ih
  have total := partition E.gates
  have countE : E.gates.countP neg = D.gates.countP neg := by
    change (D.gates ++ [last]).countP neg = _
    simp [last,neg]
  have sizeE : E.gates.length = 19 := by
    change (D.gates ++ [last]).length = 19
    change D.gates.length = 18 at sizeD
    simp only [List.length_append,List.length_singleton,sizeD]
  have nots : D.gates.countP neg ≤ 4 := by omega
  exact few D fanD sizeD nots a b covered
