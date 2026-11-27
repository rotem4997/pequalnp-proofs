import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_18787_1
  (hor :
  let I := fun (i : Fin 12) (j : Fin 13) =>
    i.succ = j ∨ i.succ = j+1 ∨ i.succ = j+3 ∨ i.succ = j+9
  let pair := fun (i : Fin 12) (j : Fin 13) (v : Fin 25) =>
    decide (v = Fin.castAdd 13 i ∨ v = Fin.natAdd 12 j)
  let neg := fun (S : Finset (Fin 12)) (v : Fin 25) =>
    Fin.addCases (motive := fun _ => Bool) (fun i => decide (i ∈ S)) (fun j => decide (∀ i ∈ S, ¬I i j)) v
  ∀ (D : Circuit) (ws : List ℕ), Monotone2 D → D.size ≤ 56 → ws.length ≤ 2 →
    let reads := fun (x : Fin 25 → Bool) => (ws.map fun w => (D.wires (List.ofFn x)).getD w false).any id
    (∀ i j, I i j → reads (pair i j) = true) → ∃ S, (∀ i ∉ S, ∃ j, I i j ∧ ∀ k ∈ S, ¬I k j) ∧ reads (neg S) = true)
  (hand :
  let I := fun (i : Fin 12) (j : Fin 13) =>
    i.succ = j ∨ i.succ = j+1 ∨ i.succ = j+3 ∨ i.succ = j+9
  let pair := fun (i : Fin 12) (j : Fin 13) (v : Fin 25) =>
    decide (v = Fin.castAdd 13 i ∨ v = Fin.natAdd 12 j)
  let neg := fun (S : Finset (Fin 12)) (v : Fin 25) =>
    Fin.addCases (motive := fun _ => Bool) (fun i => decide (i ∈ S)) (fun j => decide (∀ i ∈ S, ¬I i j)) v
  ∀ (D : Circuit) (ws : List ℕ), Monotone2 D → D.size ≤ 56 → ws.length ≤ 2 →
    let reads := fun (x : Fin 25 → Bool) => (ws.map fun w => (D.wires (List.ofFn x)).getD w false).all id
    (∀ i j, I i j → reads (pair i j) = true) → ∃ S, (∀ i ∉ S, ∃ j, I i j ∧ ∀ k ∈ S, ¬I k j) ∧ reads (neg S) = true) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (13 : ℕ)), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (9 : Fin ((12 : ℕ) + (1 : ℕ)))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true) → (58 : ℕ) ≤ x1.size := by
  intro C mono computes
  by_contra! small
  let I := fun (i : Fin 12) (j : Fin 13) =>
    i.succ = j ∨ i.succ = j+1 ∨ i.succ = j+3 ∨ i.succ = j+9
  let pair := fun (i : Fin 12) (j : Fin 13) (v : Fin 25) =>
    decide (v = Fin.castAdd 13 i ∨ v = Fin.natAdd 12 j)
  let neg := fun (S : Finset (Fin 12)) (v : Fin 25) =>
    Fin.addCases (motive := fun _ => Bool) (fun i => decide (i ∈ S)) (fun j => decide (∀ i ∈ S, ¬I i j)) v
  let step := fun (xs : List Bool) (g : Gate) =>
    xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]
  have len (gs : List Gate) (xs : List Bool) : (gs.foldl step xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp
    | cons g gs ih => simpa [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (step xs g)
  have stable (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
      (gs.foldl step xs).getD i false = xs.getD i false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step xs g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have pos (i : Fin 12) (j : Fin 13) (e : I i j) : C.eval (List.ofFn (pair i j)) = true :=
    (computes _).mpr ⟨i,j,e,by simp [pair],by simp [pair]⟩
  have no (S : Finset (Fin 12)) : C.eval (List.ofFn (neg S)) ≠ true := by
    intro h
    obtain ⟨i,j,e,hi,hj⟩ := (computes _).mp h
    simp [neg] at hi hj
    exact hj i hi e
  have low : 25 ≤ C.output := by
    by_contra! prim
    let v : Fin 25 := ⟨_,prim⟩
    have miss : ∀ v : Fin 25, ∃ i j, I i j ∧ pair i j v = false := by decide +kernel
    obtain ⟨i,j,e,off⟩ := miss v
    have on := pos i j e
    change (C.gates.foldl step _).getD C.output false = true at on
    rw [stable _ _ _ (by simpa using prim),
      List.getD_eq_getElem _ _ (by simpa using prim), List.getElem_ofFn] at on
    exact Bool.noConfusion (off.symm.trans on)
  have high : C.output < 25+C.gates.length := by
    by_contra! bad
    have on := pos 0 0 (by decide +kernel)
    change (C.gates.foldl step _).getD C.output false = true at on
    rw [List.getD_eq_default _ _ (by rw [len,List.length_ofFn]; omega)] at on
    contradiction
  let k := C.output - 25
  have hk : k < C.gates.length := by dsimp [k]; omega
  let pre := C.gates.take k
  let g := C.gates[k]
  let D : Circuit := ⟨pre,0⟩
  have pl : pre.length = k := by simp [pre,Nat.min_eq_left (Nat.le_of_lt hk)]
  have split : C.gates = pre ++ g :: C.gates.drop (k+1) := by
    simp only [pre,g,List.getElem_cons_drop hk,List.take_append_drop]
  have md : Monotone2 D := by
    intro t ht
    exact mono t (List.mem_of_mem_take ht)
  have size : D.size ≤ 56 := by
    change pre.length ≤ 56
    change C.gates.length < 58 at small
    omega
  have gm := mono g (List.getElem_mem hk)
  have val (x : Fin 25 → Bool) : C.eval (List.ofFn x) =
      g.op.eval (g.inputs.map fun i => (D.wires (List.ofFn x)).getD i false) := by
    change (C.gates.foldl step _).getD C.output false = _
    rw [split,List.foldl_append,List.foldl_cons]
    let xs := pre.foldl step (List.ofFn x)
    have xl : xs.length = C.output := by simp only [xs,len,List.length_ofFn,pl,k]; omega
    change ((C.gates.drop (k+1)).foldl step (step xs g)).getD C.output false = _
    rw [stable _ _ _ (by simp [step,xl])]
    change (xs ++ [_]).getD C.output false = _
    rw [List.getD_append_right _ _ _ _ (by omega)]
    rw [show C.output - xs.length = 0 by omega]
    rfl
  rcases gm.1 with h | h
  · have eq : g.op = .and := h
    have unpack (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
    obtain ⟨S,_,hs⟩ := hand D g.inputs md size gm.2 (fun i j e => by simpa only [eq,unpack] using (val (pair i j)).symm.trans (pos i j e))
    exact no S ((val _).trans (by simpa only [eq,unpack] using hs))
  · have eq := Set.mem_singleton_iff.mp h
    have unpack (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
    obtain ⟨S,_,hs⟩ := hor D g.inputs md size gm.2 (fun i j e => by simpa only [eq,unpack] using (val (pair i j)).symm.trans (pos i j e))
    exact no S ((val _).trans (by simpa only [eq,unpack] using hs))
