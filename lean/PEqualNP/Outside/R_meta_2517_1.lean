import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- In a minimum candidate the fourteen gates after the first OR read all nine
-- raw variables and every earlier gate output. Two negations leave twenty-six
-- operand occurrences to cover twenty-three wires, so at most three wires
-- can occur twice. Every direct merge of two raw variables needs one of them.
set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2517_1
    (live : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → C.size ≤ 15 →
      C.size = 15 ∧ C.output = 23 ∧ ∀ j < 14, ∃ q : Fin C.gates.length,
        j < q.val ∧ 9 + j ∈ (C.gates.get q).inputs)
    (pairs : ∀ T : Circuit, 10 ≤ T.output →
      (∀ x : Fin 9 → Bool, T.eval (List.ofFn x ++ [x 0 || x 2]) = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x) →
      let R := T.gates.flatMap Gate.inputs
      (∀ a : Fin 9, a.val ∈ R) ∧ ∀ g ∈ T.gates, ∀ a b : Fin 9, a ≠ b →
        (g.op = GateOp.and ∨ g.op = GateOp.or) → g.inputs = [a.val,b.val] →
        2 ≤ R.count a.val ∨ 2 ≤ R.count b.val)
    (terminal : ∀ (C : Circuit) (i j : Fin C.gates.length), FanInTwo C → i < j → j.val + 1 = C.size →
      C.output = 9 + j.val → (C.gates.get i).op = GateOp.not → (C.gates.get j).op = GateOp.not →
      (∀ k : Fin C.gates.length, (C.gates.get k).op = GateOp.not → k = i ∨ k = j) →
      circuitFun 9 C (fun _ => false) = false → circuitFun 9 C (fun _ => true) = true →
      ∃ D : Circuit, FanInTwo D ∧ D.size ≤ i.val ∧ circuitFun 9 D = circuitFun 9 C)
    (residual : ∀ T : Circuit, FanInTwo T → T.size = 14 → T.output = 23 →
      (∀ g ∈ T.gates, g.op = GateOp.not → g.inputs.length ≤ 1) →
      (∃ i j : Fin T.gates.length, i < j ∧ 3 ≤ i.val ∧ i.val ≤ 6 ∧ j.val < 13 ∧
        (T.gates.get i).op = GateOp.not ∧ (T.gates.get j).op = GateOp.not ∧
        ∀ k : Fin T.gates.length, (T.gates.get k).op = GateOp.not → k = i ∨ k = j) →
      let R := T.gates.flatMap Gate.inputs
      let B := (Finset.range 23).filter (fun k => 2 ≤ R.count k)
      (∀ k < 23, k ∈ R) → B.card ≤ 3 →
      (∀ g ∈ T.gates, ∀ a b : Fin 9, a ≠ b → (g.op = GateOp.and ∨ g.op = GateOp.or) →
        g.inputs = [a.val,b.val] → a.val ∈ B ∨ b.val ∈ B) →
      ∃ r : ℕ, r < 512 ∧ T.eval (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++
        [r.testBit 0 || r.testBit 2]) ≠ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ).any (fun e => (r &&& e) == e)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ (4 : ℕ) ≤ ↑x3 ∧ ↑x3 ≤ (7 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let E : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
  classical
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  have prefixOK (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl step w = w ++ t := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp⟩
    | cons g gs ih =>
      obtain ⟨t, ht⟩ := ih (step w g)
      exact ⟨g.op.eval (g.inputs.map fun k => w.getD k false) :: t, by rw [List.foldl_cons, ht]; simp [step]⟩
  let norm := fun (g : Gate) => (⟨g.op, if g.op = GateOp.not then g.inputs.take 1 else g.inputs⟩ : Gate)
  have sameGate (g : Gate) (w : List Bool) : step w (norm g) = step w g := by
    by_cases hn : g.op = GateOp.not
    · have en (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl
      cases l : g.inputs <;> simp [step, norm, hn, l, en]
    · simp [step, norm, hn]
  have sameRun (gs : List Gate) (w : List Bool) : (gs.map norm).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih => simp only [List.map_cons, List.foldl_cons, sameGate, ih]
  have cardinality (R : List ℕ) (covers : ∀ k < 23, k ∈ R) (small : R.length ≤ 26) :
      ((Finset.range 23).filter (fun k => 2 ≤ R.count k)).card ≤ 3 := by
    let B := (Finset.range 23).filter (fun k => 2 ≤ R.count k)
    have weight : ∀ k ∈ Finset.range 23, 1 + (if k ∈ B then 1 else 0) ≤ R.count k := by
      intro k hk
      by_cases h : k ∈ B
      · simpa [h] using (Finset.mem_filter.mp h).2
      · have pos : 0 < R.count k := List.count_pos_iff.mpr (covers k (Finset.mem_range.mp hk))
        rw [if_neg h]
        exact pos
    have lower := Finset.sum_le_sum weight
    have ind : ∑ k ∈ Finset.range 23, (if k ∈ B then 1 else 0 : ℕ) = B.card := by
      rw [← Finset.card_filter]
      congr 1
      ext k
      simp [B]
    rw [Finset.sum_add_distrib, ind] at lower
    have sub : Finset.range 23 ⊆ R.toFinset := fun k hk => List.mem_toFinset.mpr (covers k (Finset.mem_range.mp hk))
    have upper : ∑ k ∈ Finset.range 23, R.count k ≤ ∑ k ∈ R.toFinset, R.count k :=
      Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
    have total : ∑ k ∈ R.toFinset, R.count k = R.length := by
      simpa using Multiset.toFinset_sum_count_eq (R : Multiset ℕ)
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at lower
    change B.card ≤ 3
    omega
  have lengthBudget (gs : List Gate) (ok : ∀ g ∈ gs, g.inputs.length ≤ 2)
      (unary : ∀ g ∈ gs, g.op = GateOp.not → g.inputs.length ≤ 1) :
      (gs.flatMap Gate.inputs).length + gs.countP (fun g => decide (g.op = GateOp.not)) ≤ 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      have tail := ih (fun k h => ok k (List.mem_cons_of_mem _ h))
        (fun k h => unary k (List.mem_cons_of_mem _ h))
      have ordinary := ok g List.mem_cons_self
      have one := unary g List.mem_cons_self
      simp only [List.flatMap_cons, List.length_append, List.countP_cons, List.length_cons]
      by_cases hn : g.op = GateOp.not
      · have := one hn
        simp only [hn, decide_true, if_true]
        omega
      · simp only [hn, decide_false, Bool.false_eq_true, if_false]
        omega
  have countIndex (gs : List Gate) :
      gs.countP (fun g => decide (g.op = GateOp.not)) =
        ∑ j : Fin gs.length, if (gs.get j).op = GateOp.not then 1 else 0 := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      change (g :: gs).countP _ = ∑ j : Fin (gs.length + 1),
        if ((g :: gs).get j).op = GateOp.not then 1 else 0
      rw [List.countP_cons, Fin.sum_univ_succ]
      have head : ((g :: gs).get (0 : Fin (gs.length + 1))).op = g.op := rfl
      have tail (j : Fin gs.length) : ((g :: gs).get j.succ).op = (gs.get j).op := rfl
      simp only [head, tail, ih, decide_eq_true_eq]
      omega
  intro C legal flags first correct
  by_contra! sm
  obtain ⟨gs, o⟩ := C
  rcases gs with _ | ⟨g0, gs⟩
  · obtain ⟨i, _, _⟩ := flags
    exact i.elim0
  · let T : Circuit := ⟨gs.map norm, o⟩
    let C' : Circuit := ⟨g0 :: T.gates, o⟩
    have sameSize : T.gates.length = gs.length := by simp [T]
    have ct : C'.size = (Circuit.mk (g0 :: gs) o).size := by change T.gates.length + 1 = _; rw [sameSize]; rfl
    have rawSize : C'.size = T.size + 1 := rfl
    have okT : FanInTwo T := by
      intro g hg
      obtain ⟨a, h, rfl⟩ := List.mem_map.mp hg
      have ha := legal a (List.mem_cons_of_mem g0 h)
      refine ⟨ha.1, ?_⟩
      by_cases hn : a.op = GateOp.not <;> simp [norm, hn, ha.2]
    have one : ∀ g ∈ T.gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
      intro g hg hn
      obtain ⟨a, h, rfl⟩ := List.mem_map.mp hg
      change a.op = GateOp.not at hn
      simp [norm, hn]
    have okC : FanInTwo C' := fun g hg => by
      rcases List.mem_cons.mp hg with h | h
      · exact h ▸ legal g0 List.mem_cons_self
      · exact okT g h
    have eqC : circuitFun 9 C' = F := by
      funext x
      change ((gs.map norm).foldl step (step (List.ofFn x) g0)).getD o false = _
      rw [sameRun]
      exact congrFun correct x
    obtain ⟨sz, out, allUsed⟩ := live C' okC eqC (by omega)
    have len : T.size = 14 := by omega
    have lenG : T.gates.length = 14 := len
    have outT : T.output = 23 := out
    have run (x : Fin 9 → Bool) : T.eval (List.ofFn x ++ [x 0 || x 2]) = F x := by
      let b := g0.op.eval (g0.inputs.map fun k => (List.ofFn x).getD k false)
      have hv := first x
      change (gs.foldl step (List.ofFn x ++ [b])).getD 9 false = _ at hv
      obtain ⟨t, ht⟩ := prefixOK gs (List.ofFn x ++ [b])
      rw [ht, List.getD_append _ _ _ _ (by simp)] at hv
      have firstBit : b = (x 0 || x 2) := by
        simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp :
          (List.ofFn x).length ≤ 9), List.length_ofFn, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] using hv
      have r := congrFun eqC x
      change T.eval (List.ofFn x ++ [b]) = F x at r
      rwa [firstBit] at r
    obtain ⟨rawUsed, rawPairs⟩ := pairs T (by omega) run
    let R := T.gates.flatMap Gate.inputs
    let B := (Finset.range 23).filter (fun k => 2 ≤ R.count k)
    have all (k : ℕ) (hk : k < 23) : k ∈ R := by
      by_cases rawK : k < 9
      · exact rawUsed ⟨k,rawK⟩
      · obtain ⟨q, lt, hq⟩ := allUsed (k - 9) (by omega)
        have qpos : 0 < q.val := by omega
        have gq : C'.gates.get q ∈ T.gates := by
          have range := q.isLt
          change q.val < T.gates.length + 1 at range
          obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q.val ≠ 0)
          let j : Fin T.gates.length := ⟨v, by omega⟩
          have eqQ : q = j.succ := Fin.ext hv
          rw [eqQ]
          exact List.get_mem T.gates j
        apply List.mem_flatMap.mpr
        exact ⟨_, gq, (show 9 + (k - 9) = k by omega) ▸ hq⟩
    obtain ⟨i,j,ij,lo,hi,ni,nj,only⟩ := flags
    let up (k : Fin T.gates.length) : Fin (g0 :: gs).length := ⟨k.val + 1, by
      have := k.isLt; simp only [List.length_cons]; omega⟩
    have lookup (k : Fin T.gates.length) :
        (T.gates.get k).op = ((g0 :: gs).get (up k)).op := by
      simp [T, up, List.get_eq_getElem, norm]
    let a : Fin T.gates.length := ⟨i.val-1, by have := i.isLt; simp only [List.length_cons] at this; omega⟩
    let b : Fin T.gates.length := ⟨j.val-1, by have := j.isLt; simp only [List.length_cons] at this; omega⟩
    have ua : up a = i := Fin.ext (by change i.val - 1 + 1 = i.val; omega)
    have ub : up b = j := Fin.ext (by change j.val - 1 + 1 = j.val; omega)
    have ab : a < b := by change i.val - 1 < j.val - 1; omega
    have ha : (T.gates.get a).op = GateOp.not := by rw [lookup, ua]; exact ni
    have hb : (T.gates.get b).op = GateOp.not := by rw [lookup, ub]; exact nj
    have allN (k : Fin T.gates.length) (h : (T.gates.get k).op = GateOp.not) : k = a ∨ k = b := by
      rw [lookup] at h
      rcases only (up k) h with lhs | rhs
      · left; apply Fin.ext; have eq := congrArg Fin.val lhs; change k.val + 1 = i.val at eq; dsimp [a]; omega
      · right; apply Fin.ext; have eq := congrArg Fin.val rhs; change k.val + 1 = j.val at eq; dsimp [b]; omega
    have beforeEnd : b.val < 13 := by
      by_contra! late
      have jb : j.val = 14 := by
        change 13 ≤ j.val - 1 at late
        have range := j.isLt
        change j.val < gs.length + 1 at range
        omega
      have he : circuitFun 9 (Circuit.mk (g0 :: gs) o) (fun _ => false) = false := by rw [correct]; decide
      have hf : circuitFun 9 (Circuit.mk (g0 :: gs) o) (fun _ => true) = true := by rw [correct]; decide
      have endSize : j.val + 1 = (Circuit.mk (g0 :: gs) o).size := by omega
      have endOut : (Circuit.mk (g0 :: gs) o).output = 9 + j.val := by change o = _; change o = 23 at out; omega
      obtain ⟨D, good, ds, eq⟩ := terminal (Circuit.mk (g0 :: gs) o) i j legal ij endSize endOut ni nj only he hf
      have impossible := (live D good (eq.trans correct) (by omega)).1
      omega
    have two : 2 ≤ T.gates.countP (fun g => decide (g.op = GateOp.not)) := by
      rw [countIndex]
      let w := fun j : Fin T.gates.length => if (T.gates.get j).op = GateOp.not then 1 else 0
      have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({a,b} : Finset _))
        (f := w) (fun _ _ _ => Nat.zero_le _)
      have e : ∑ j ∈ ({a,b} : Finset _), w j = 2 := by
        rw [Finset.sum_insert (by simp [ne_of_lt ab]), Finset.sum_singleton]
        simp only [w, ha, hb, if_true]
      rw [e] at h
      exact h
    have budget := lengthBudget T.gates (fun g h => (okT g h).2) one
    have small : B.card ≤ 3 := cardinality R all (by change (T.gates.flatMap Gate.inputs).length ≤ 26; omega)
    obtain ⟨r, hr, bad⟩ := residual T okT len outT one ⟨a,b,ab,(by dsimp [a]; omega),(by dsimp [a]; omega),beforeEnd,ha,hb,allN⟩ all small (by
      intro g hg l m ne op eq
      rcases rawPairs g hg l m ne op eq with h | h
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := l.isLt; omega), h⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := m.isLt; omega), h⟩))
    have table : ∀ r : Fin 512, F (fun i => r.val.testBit i.val) = E.any (fun e => (r.val &&& e) == e) := by decide +kernel
    exact bad ((run (fun i => r.testBit i.val)).trans (table ⟨r,hr⟩))
