import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2012_271
    (cofactor : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) ||
      (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) ||
      (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (pin :
      let read := fun (v : Fin 9) (g : Gate) =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains v.val
      ∀ (C : Circuit) (v : Fin 9), IsMinimalCircuit 9 C →
        let evalAt := fun (b : Bool) (x : Fin 8 → Bool) =>
          C.eval ((List.ofFn x).insertIdx v.val b)
        (∃ x y, evalAt false x ≠ evalAt false y) →
        (∀ j : Fin 9, j ≠ v → ∃ x : Fin 8 → Bool, evalAt false x ≠ evalAt true x ∧
          ((List.ofFn x).insertIdx v.val false).getD j.val false = true) →
        (∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧ circuitFun 8 D = evalAt false) ∨
        ∃ (g : Fin C.size) (w : ℕ), 9 ≤ w ∧ w < 9 + g.val ∧
          (C.gates.get g).op = GateOp.or ∧
          ((C.gates.get g).inputs = [v.val,w] ∨ (C.gates.get g).inputs = [w,v.val]) ∧
          ∀ h : Fin C.size, read v (C.gates.get h) = true → h = g)
    (exclude :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let read := fun (v : Fin 9) (g : Gate) =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains v.val
      ∀ C : Circuit, FanInTwo C → C.size ≤ 14 →
        (∀ v : Fin 9, v = 4 ∨ v = 6 ∨ v = 7 →
          ∃ (g : Fin C.size) (w : ℕ), 9 ≤ w ∧ w < 9 + g.val ∧
            (C.gates.get g).op = GateOp.or ∧
            ((C.gates.get g).inputs = [v.val,w] ∨ (C.gates.get g).inputs = [w,v.val]) ∧
            ∀ h : Fin C.size, read v (C.gates.get h) = true → h = g) →
        ∃ x : Fin 9 → Bool, circuitFun 9 C x ≠ f x) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ) := by
  classical
  let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let read := fun (v : Fin 9) (g : Gate) =>
    (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains v.val
  let insert := fun (v : Fin 9) (b : Bool) (x : Fin 8 → Bool) =>
    v.insertNth (α := fun _ => Bool) b x
  let base := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)
  have relabel (f : (Fin 8 → Bool) → Bool) (p : Equiv.Perm (Fin 8)) (s : ℕ)
      (small : HasCircuitSize 8 f s) : HasCircuitSize 8 (fun x => f (fun i => x (p i))) s := by
    obtain ⟨C, basis, limit, computes⟩ := small
    let wire (i : ℕ) : ℕ := if h : i < 8 then (p ⟨i,h⟩).val else i
    let rename (g : Gate) : Gate := ⟨g.op, g.inputs.map wire⟩
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let relates (a b : List Bool) : Prop :=
      a.length = b.length ∧ 8 ≤ a.length ∧ ∀ i, a.getD i false = b.getD (wire i) false
    have extend (a : List Bool) (bit : Bool) (i : ℕ) :
        (a ++ [bit]).getD i false = if i < a.length then a.getD i false
          else if i = a.length then bit else false := by
      by_cases before : i < a.length
      · simp only [ite_eq_left before, List.getD_eq_getElem?_getD, List.getElem?_append_left before]
      · rw [ite_eq_right before, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        by_cases atEnd : i = a.length
        · simp [atEnd]
        · rw [ite_eq_right atEnd, List.getElem?_eq_none (by simp; omega)]
          rfl
    have forward (a b : List Bool) (g : Gate) (same : relates a b) :
        relates (step a g) (step b (rename g)) := by
      obtain ⟨len, enough, lookup⟩ := same
      refine ⟨by simp [step,len], by simp [step]; omega, ?_⟩
      intro i
      have bits : g.op.eval (g.inputs.map fun j => a.getD j false) =
          g.op.eval ((g.inputs.map wire).map fun j => b.getD j false) := by
        rw [List.map_map]
        congr 1
        exact List.map_congr_left (fun j _ => lookup j)
      change (a ++ [g.op.eval _]).getD i false = (b ++ [g.op.eval _]).getD (wire i) false
      rw [extend, extend, bits, ← len, lookup i]
      by_cases first : i < 8
      · have hw : wire i < 8 := by simp [wire,first]
        rw [ite_eq_left (by omega : i < a.length), ite_eq_left (by omega : wire i < a.length)]
      · have hw : wire i = i := dite_eq_right first
        rw [hw]
    have iterate (gs : List Gate) (a b : List Bool) (same : relates a b) :
        relates (gs.foldl step a) ((gs.map rename).foldl step b) := by
      induction gs generalizing a b with
      | nil => exact same
      | cons g gs ih => exact ih _ _ (forward a b g same)
    let D : Circuit := ⟨C.gates.map rename, wire C.output⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ C.gates.map rename at hg
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
      simpa [rename] using basis q hq
    · change (C.gates.map rename).length ≤ s
      exact (List.length_map ..).le.trans limit
    · intro x
      let a := List.ofFn (fun i => x (p i))
      let b := List.ofFn x
      have init : relates a b := by
        refine ⟨by simp [a,b], by simp [a], ?_⟩
        intro i
        by_cases first : i < 8
        · have hw : wire i < 8 := by simp [wire,first]
          have ha : i < a.length := by simpa only [a,List.length_ofFn] using first
          have hb : wire i < b.length := by simpa only [b,List.length_ofFn] using hw
          rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]
          simp only [a,b,List.getElem_ofFn]
          congr 1
          apply Fin.ext
          change (p ⟨i,first⟩).val = wire i
          simp [wire,first]
        · have ha : a.length ≤ i := by simpa only [a,List.length_ofFn] using Nat.le_of_not_gt first
          have hb : b.length ≤ i := by simpa only [b,List.length_ofFn] using Nat.le_of_not_gt first
          rw [show wire i = i from dite_eq_right first, List.getD_eq_getElem?_getD,
            List.getD_eq_getElem?_getD, List.getElem?_eq_none ha, List.getElem?_eq_none hb]
      have same := (iterate C.gates a b init).2.2 C.output
      change C.eval a = D.eval b at same
      exact same.symm.trans (computes (fun i => x (p i)))
  have cofactors (v : Fin 9) (special : v = 4 ∨ v = 6 ∨ v = 7) :
      ¬ HasCircuitSize 8 (fun x => f (insert v false x)) 12 := by
    let p6 : Equiv.Perm (Fin 8) := Equiv.ofBijective ![1,0,4,7,5,2,6,3] (by decide +kernel)
    let p7 : Equiv.Perm (Fin 8) := Equiv.ofBijective ![1,2,3,7,5,0,6,4] (by decide +kernel)
    have iso : ∃ p : Equiv.Perm (Fin 8), ∀ x : Fin 8 → Bool,
        f (insert v false (fun i => x (p i))) = base x := by
      rcases special with rfl | rfl | rfl
      · exact ⟨Equiv.refl _, by decide +kernel⟩
      · exact ⟨p6, by decide +kernel⟩
      · exact ⟨p7, by decide +kernel⟩
    intro small
    obtain ⟨p, equal⟩ := iso
    have h := relabel (fun x => f (insert v false x)) p 12 small
    rw [funext equal] at h
    exact cofactor h
  have guards (v : Fin 9) (special : v = 4 ∨ v = 6 ∨ v = 7) (j : Fin 9)
      (unequal : j ≠ v) : ∃ x : Fin 8 → Bool,
      f (insert v false x) ≠ f (insert v true x) ∧ insert v false x j = true := by
    rcases special with rfl | rfl | rfl
    · fin_cases j
      · exact ⟨fun i => (1 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (10 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (5 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (8 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact (unequal rfl).elim
      · exact ⟨fun i => (24 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (33 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (65 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (129 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
    · fin_cases j
      · exact ⟨fun i => (129 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (2 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (132 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (10 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (18 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (34 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact (unequal rfl).elim
      · exact ⟨fun i => (66 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (128 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
    · fin_cases j
      · exact ⟨fun i => (5 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (34 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (4 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (40 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (20 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (32 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact ⟨fun i => (68 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
      · exact (unequal rfl).elim
      · exact ⟨fun i => (132 : ℕ).testBit i.val, by decide +kernel, by decide +kernel⟩
  have lowVaries (v : Fin 9) (special : v = 4 ∨ v = 6 ∨ v = 7) :
      ∃ x y : Fin 8 → Bool, f (insert v false x) ≠ f (insert v false y) := by
    rcases special with rfl | rfl | rfl <;>
      exact ⟨fun _ => false, fun j => decide (j = 1 ∨ j = 2), by decide +kernel⟩
  have listInsert (v : Fin 9) (special : v = 4 ∨ v = 6 ∨ v = 7) (b : Bool) (x : Fin 8 → Bool) :
      (List.ofFn x).insertIdx v.val b = List.ofFn (insert v b x) := by
    rcases special with rfl | rfl | rfl <;>
      simp only [List.ofFn_succ, List.ofFn_zero] <;> rfl
  change ¬ HasCircuitSize 9 f 14
  intro small
  have feasible : ∃ s, HasCircuitSize 9 f s := ⟨14,small⟩
  obtain ⟨C,basis,bound,computes⟩ := Nat.find_spec feasible
  have value (x : Fin 9 → Bool) : circuitFun 9 C x = f x := computes x
  have minimum : IsMinimalCircuit 9 C := by
    refine ⟨basis, fun D hD same => bound.trans (Nat.find_min' feasible ?_)⟩
    exact ⟨D,hD,le_rfl,fun x => (congrFun same x).trans (computes x)⟩
  have size : C.size ≤ 14 := bound.trans (Nat.find_min' feasible small)
  have profile (v : Fin 9) (special : v = 4 ∨ v = 6 ∨ v = 7) :
      ∃ (g : Fin C.size) (w : ℕ), 9 ≤ w ∧ w < 9 + g.val ∧
        (C.gates.get g).op = GateOp.or ∧
        ((C.gates.get g).inputs = [v.val,w] ∨ (C.gates.get g).inputs = [w,v.val]) ∧
        ∀ h : Fin C.size, read v (C.gates.get h) = true → h = g := by
    have evalAt (b : Bool) (x : Fin 8 → Bool) :
        C.eval ((List.ofFn x).insertIdx v.val b) = f (insert v b x) := by
      rw [listInsert v special b x]
      exact value _
    obtain ⟨x,y,unequal⟩ := lowVaries v special
    have varies : ∃ x y : Fin 8 → Bool, C.eval ((List.ofFn x).insertIdx v.val false) ≠
        C.eval ((List.ofFn y).insertIdx v.val false) := by
      refine ⟨x,y,?_⟩
      simpa only [evalAt] using unequal
    have guarded (j : Fin 9) (hj : j ≠ v) : ∃ x : Fin 8 → Bool,
        C.eval ((List.ofFn x).insertIdx v.val false) ≠ C.eval ((List.ofFn x).insertIdx v.val true) ∧
        ((List.ofFn x).insertIdx v.val false).getD j.val false = true := by
      obtain ⟨x,h,z⟩ := guards v special j hj
      refine ⟨x,by simpa only [evalAt] using h, ?_⟩
      rw [listInsert v special false x, List.getD_eq_getElem _ _ (by simpa using j.isLt),
        List.getElem_ofFn]
      exact z
    rcases pin C v minimum varies guarded with reduced | readers
    · obtain ⟨D,fd,sd,ed⟩ := reduced
      exact (cofactors v special ⟨D,fd,by omega,fun x =>
        (congrFun ed x).trans (evalAt false x)⟩).elim
    · exact readers
  obtain ⟨x,hx⟩ := exclude C basis size profile
  exact hx (computes x)
