import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2519_608
    (suffix : ∀ (D : Circuit), FanInTwo D → D.size ≤ 7 →
      ∀ i j : Fin D.gates.length, i < j →
      (D.gates.get i).op = .not → (D.gates.get j).op = .not →
      ∃ U : Finset ℕ, U ⊆ Finset.range 17 ∧ U.card ≤ 6 ∧
        ∀ w v : List Bool, w.length = 17 → v.length = 17 →
          (∀ k ∈ U, w.getD k false = v.getD k false) → D.eval w = D.eval v)
    (prefixLower :
      let f := fun (x : Fin 9 → Bool) =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (P : Circuit), FanInTwo P → P.size = 8 → (∀ g ∈ P.gates, g.op ≠ .not) →
        (∀ y : Fin 9 → Bool, (P.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) →
        ∀ U ⊆ Finset.range 17, U.card ≤ 6 → ∃ x y : Fin 9 → Bool, f x ≠ f y ∧
          ∀ k ∈ U, (P.wires (List.ofFn x)).getD k false =
            (P.wires (List.ofFn y)).getD k false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ (8 : ℕ) ≤ ↑x3 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan negs first computes
  by_contra! small
  obtain ⟨i,j,ord,late,ni,nj,allNot⟩ := negs
  have hi := i.isLt
  have hj := j.isLt
  have ilt : i.val < j.val := ord
  change C.gates.length < 16 at small
  let P : Circuit := ⟨C.gates.take 8, 0⟩
  let D : Circuit := ⟨C.gates.drop 8, C.output⟩
  have plen : P.gates.length = 8 := by simp [P]; omega
  have dlen : D.gates.length = C.gates.length - 8 := by simp [D]
  have preFan : FanInTwo P := fun g hg => fan g (List.mem_of_mem_take hg)
  have tailFan : FanInTwo D := fun g hg => fan g (List.mem_of_mem_drop hg)
  have positive : ∀ g ∈ P.gates, g.op ≠ .not := by
    intro g hg ng
    obtain ⟨k, hk, eq⟩ := List.mem_iff_getElem.mp hg
    have ko : k < C.gates.length := by omega
    have found : (C.gates.get ⟨k,ko⟩).op = .not := by
      change (C.gates.take 8)[k] = g at eq
      have eg : C.gates[k] = g := by simpa only [List.getElem_take] using eq
      exact (congrArg Gate.op eg).trans ng
    have same := allNot ⟨k,ko⟩ found
    rcases same with eqi | eqj
    · have et := congrArg Fin.val eqi
      change k = i.val at et
      omega
    · have et := congrArg Fin.val eqj
      change k = j.val at et
      omega
  let iv : Fin D.gates.length := ⟨i.val - 8, by omega⟩
  let jv : Fin D.gates.length := ⟨j.val - 8, by omega⟩
  have getD' (k : Fin C.gates.length) (h : 8 ≤ k.val) :
      D.gates.get ⟨k.val-8, by have := k.isLt; omega⟩ = C.gates.get k := by
    simp [D, List.get_eq_getElem, Nat.add_sub_of_le h]
  obtain ⟨U, urange, budget, factors⟩ := suffix D tailFan (by change D.gates.length ≤ 7; omega)
    iv jv (by change i.val-8 < j.val-8; omega)
    ((congrArg Gate.op (getD' i late)).trans ni)
    ((congrArg Gate.op (getD' j (by omega))).trans nj)
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  have combine (x : List Bool) : C.wires x = D.wires (P.wires x) := by
    change C.gates.foldl step x =
      (C.gates.drop 8).foldl step ((C.gates.take 8).foldl step x)
    rw [←List.foldl_append, List.take_append_drop]
  have length' (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have wlen (x : Fin 9 → Bool) : (P.wires (List.ofFn x)).length = 17 := by
    change (P.gates.foldl step (List.ofFn x)).length = 17
    simp [length',plen]
  have keep (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
      (gs.foldl step w).getD k false = w.getD k false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hk
  have preFirst (x : Fin 9 → Bool) :
      (P.wires (List.ofFn x)).getD 9 false = (x 0 || x 2) := by
    have h := first x
    rw [combine] at h
    change (D.gates.foldl step (P.wires (List.ofFn x))).getD 9 false = _ at h
    rwa [keep _ _ _ (by rw [wlen]; decide)] at h
  obtain ⟨x,y,ne,agree⟩ := prefixLower P preFan plen positive preFirst U urange budget
  have out := factors (P.wires (List.ofFn x)) (P.wires (List.ofFn y)) (wlen x) (wlen y) agree
  change (D.wires (P.wires (List.ofFn x))).getD C.output false =
    (D.wires (P.wires (List.ofFn y))).getD C.output false at out
  rw [←combine, ←combine] at out
  change circuitFun 9 C x = circuitFun 9 C y at out
  rw [computes] at out
  have formula : ∀ z : Fin 9 → Bool, ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => z (Fin.ofNat 9 (e / 10)) && z (Fin.ofNat 9 (e % 10))) =
      (z 0 && z 1 || z 1 && z 2 || z 2 && z 3 || z 3 && z 4 || z 4 && z 0 ||
       z 0 && z 5 || z 1 && z 6 || z 2 && z 7 || z 3 && z 8 || z 5 && z 7 ||
       z 6 && z 8 || z 8 && z 5) := by decide +kernel
  exact ne ((formula x).trans (out.trans (formula y).symm))
