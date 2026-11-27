import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotPremium

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_2046_1
  (zero : ∀ C : Circuit, FanInTwo C →
    (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 2)) →
    C.size = 15 →
    C.gates.countP (fun g => GateOp.rec false false true (fun _ => false) false g.op) = 0 →
    circuitFun 9 C ≠ fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
      (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  (essential : ∀ C : Circuit, FanInTwo C →
    (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 2)) →
    C.size = 15 → AtMostOneNot C.gates →
    ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not →
    (∃ m ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288] : List ℕ),
      circuitFun 9 ⟨replaceByConst C.gates q.val false, C.output⟩
        (fun j => m.testBit j.val) = false) →
    (∃ m ∈ ([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ),
      circuitFun 9 ⟨replaceByConst C.gates q.val true, C.output⟩
        (fun j => m.testBit j.val) = true) →
    circuitFun 9 C ≠ fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
      (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (1 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) := by
  intro C fan first size one correct
  let p (g : Gate) : Bool := GateOp.rec false false true (fun _ => false) false g.op
  change C.gates.countP p = 1 at one
  have p_not (g : Gate) : p g = true ↔ g.op = GateOp.not := by
    obtain ⟨op, inputs⟩ := g
    cases op <;> simp [p]
  obtain ⟨g, hg, hpg⟩ := List.countP_pos_iff.mp (show 0 < C.gates.countP p by omega)
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  let q : Fin C.gates.length := ⟨i, hi⟩
  have qnot : (C.gates.get q).op = GateOp.not := (p_not _).mp hpg
  have hq : i ≠ 0 := by
    intro iz
    obtain ⟨gs, out⟩ := C
    cases gs with
    | nil => simp at hi
    | cons hd tl =>
      subst i
      have e : hd.op = GateOp.not := qnot
      let step (w : List Bool) (g : Gate) :=
        w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
      have keep (ls : List Gate) (w : List Bool) (j : Nat) (hj : j < w.length) :
          (ls.foldl step w).getD j false = w.getD j false := by
        induction ls generalizing w with
        | nil => rfl
        | cons a as ih =>
          rw [List.foldl_cons, ih (step w a) (by simp [step]; omega)]
          exact List.getD_append _ _ _ _ hj
      have ha := first (fun _ => false)
      let w := List.ofFn (fun _ : Fin 9 => false)
      change (tl.foldl step (step w hd)).getD 9 false = false at ha
      have ew : w = List.replicate 9 false := by decide
      have get (j : Nat) : w.getD j false = false := by
        rw [ew]
        by_cases jlt : j < 9
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
                (show j < (List.replicate 9 false).length by simpa using jlt),
              List.getElem_replicate]
          rfl
        · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt jlt)]
      have actual : hd.op.eval (hd.inputs.map fun j => w.getD j false) = true := by
        rw [e]
        change (!(hd.inputs.map (fun j => w.getD j false)).headD false) = true
        simp only [get]
        cases hd.inputs <;> rfl
      have result := ha
      change (tl.foldl step (step w hd)).getD 9 false = false at result
      rw [keep tl (step w hd) 9 (by simp [step, w])] at result
      change (w ++ [hd.op.eval (hd.inputs.map fun j => w.getD j false)]).getD 9 false = false at result
      rw [actual, List.getD_append_right _ _ _ _ (by simp [w])] at result
      simp [w] at result
  have changed (b : Bool) :
      (replaceByConst C.gates q.val b).countP p = 0 := by
    change (C.gates.set i (constGate b)).countP p = 0
    rw [List.countP_set hi, one, hpg]
    cases b <;> rfl
  have cover (j : Fin C.gates.length) (hj : (C.gates.get j).op = GateOp.not) : j = q := by
    by_contra ne
    have hidx : i ≠ j.val := fun he => ne (Fin.ext he.symm)
    have bound : j.val < (replaceByConst C.gates q.val false).length := by
      change j.val < (C.gates.set i (constGate false)).length
      simpa only [List.length_set] using j.isLt
    have hmem := List.getElem_mem (l := replaceByConst C.gates q.val false) bound
    have hval : (replaceByConst C.gates q.val false)[j.val] = C.gates.get j := by
      change (C.gates.set i (constGate false))[j.val] = C.gates.get j
      exact List.getElem_set_ne hidx (show j.val < (C.gates.set i (constGate false)).length from bound)
    rw [hval] at hmem
    exact (List.countP_eq_zero.mp (changed false) _ hmem) ((p_not _).mpr hj)
  have changeout (b : Bool) :
      ChangesSomeOutput 9 C.gates (replaceByConst C.gates q.val b)
        (fun _ : Fin 1 => C.output) := by
    let D : Circuit := ⟨replaceByConst C.gates q.val b, C.output⟩
    have dfan : FanInTwo D := by
      intro a ha
      rcases List.mem_or_eq_of_mem_set ha with ha | rfl
      · exact fan a ha
      · cases b with
        | false =>
          change GateOp.or ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ ([] : List ℕ).length ≤ 2
          simp
        | true =>
          change GateOp.and ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ ([] : List ℕ).length ≤ 2
          simp
    have dfirst (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x 0 && x 2) := by
      obtain ⟨gs, out⟩ := C
      cases gs with
      | nil => simp at hi
      | cons hd tl =>
        let step (w : List Bool) (g : Gate) :=
          w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
        have keep (ls : List Gate) (w : List Bool) (j : Nat) (hj : j < w.length) :
            (ls.foldl step w).getD j false = w.getD j false := by
          induction ls generalizing w with
          | nil => rfl
          | cons a as ih =>
            rw [List.foldl_cons, ih (step w a) (by simp [step]; omega)]
            exact List.getD_append _ _ _ _ hj
        have e := first x
        change (tl.foldl step (step (List.ofFn x) hd)).getD 9 false = _ at e
        rw [keep tl (step (List.ofFn x) hd) 9 (by simp [step])] at e
        cases i with
        | zero => contradiction
        | succ j =>
          change ((tl.set j (constGate b)).foldl step (step (List.ofFn x) hd)).getD 9 false = _
          rw [keep _ _ 9 (by simp [step])]
          exact e
    have dz : D.size = 15 := by
      change (C.gates.set i (constGate b)).length = 15
      simpa only [List.length_set] using (show C.gates.length = 15 from size)
    have dnot := zero D dfan dfirst dz (changed b)
    have neq : circuitFun 9 D ≠ circuitFun 9 C := by rw [correct]; exact dnot
    obtain ⟨x, hx⟩ := Function.ne_iff.mp neq
    exact ⟨0, x, hx⟩
  let wiresStep (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
      w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
      (w ++ [b]).getD m false = b := by
    subst hm
    simp [List.getD_eq_getElem?_getD]

  have getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
      (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    simp [List.getD_eq_getElem?_getD, hi]

  have monotone_foldl_wiresStep (gs : List Gate)
      (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
      (w1 w2 : List Bool) (hlen : w1.length = w2.length)
      (hle : ∀ k : ℕ, w1.getD k false = true → w2.getD k false = true) :
      ∀ k : ℕ, (gs.foldl wiresStep w1).getD k false = true →
        (gs.foldl wiresStep w2).getD k false = true := by
    induction gs generalizing w1 w2 with
    | nil => exact hle
    | cons g gs ih =>
      have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
        simpa using hM g List.mem_cons_self
      have hM' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
        fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
      apply ih hM' (wiresStep w1 g) (wiresStep w2 g)
      · simp only [wiresStep, List.length_append, List.length_cons, List.length_nil, hlen]
      · intro k hk
        by_cases hlt : k < w1.length
        · have hlt2 : k < w2.length := hlen ▸ hlt
          simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
          simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
          exact hle k hk
        · by_cases heq : k = w1.length
          · subst heq
            have hk1 : g.op.eval (g.inputs.map fun i => w1.getD i false) = true := by
              simpa [wiresStep, getD_append_last_eq w1 _ w1.length rfl] using hk
            simp only [wiresStep]
            rw [getD_append_last_eq w2 _ w1.length hlen.symm]
            rcases hg with hand | hor
            · rw [hand] at hk1 ⊢
              change (g.inputs.map (fun i => w1.getD i false)).all id = true at hk1
              change (g.inputs.map (fun i => w2.getD i false)).all id = true
              simp only [List.all_eq_true, List.mem_map, id_eq,
                forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hk1 ⊢
              intro i hi
              exact hle i (hk1 i hi)
            · rw [hor] at hk1 ⊢
              change (g.inputs.map (fun i => w1.getD i false)).any id = true at hk1
              change (g.inputs.map (fun i => w2.getD i false)).any id = true
              simp only [List.any_eq_true, List.mem_map, id_eq] at hk1 ⊢
              obtain ⟨b, ⟨i, hi, rfl⟩, hbi⟩ := hk1
              exact ⟨true, ⟨i, hi, hle i hbi⟩, rfl⟩
          · have hge : (wiresStep w1 g).length ≤ k := by
              simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
              omega
            rw [getD_ge_length _ k hge] at hk
            cases hk

  have append_bit_mono (x y : List Bool) (hxy : x.length = y.length)
      (hval : ∀ k : ℕ, x.getD k false = true → y.getD k false = true)
      (u v : Bool) (huv : u = true → v = true) :
      ∀ k : ℕ, (x ++ [u]).getD k false = true → (y ++ [v]).getD k false = true := by
    intro k hk
    by_cases hlt : k < x.length
    · rw [List.getD_append _ _ _ _ hlt] at hk
      rw [List.getD_append _ _ _ _ (hxy ▸ hlt)]
      exact hval k hk
    · by_cases heq : k = x.length
      · rw [getD_append_last_eq x u k heq.symm] at hk
        rw [getD_append_last_eq y v k (hxy.symm.trans heq.symm)]
        exact huv hk
      · have hge : (x ++ [u]).length ≤ k := by simp; omega
        rw [getD_ge_length _ _ hge] at hk
        cases hk

  let F := fun x : Fin 9 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  -- The mask bit at index i encodes input i.
  let edgeMask : Fin 12 → ℕ := ![3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288]
  let independentMask : Fin 12 → ℕ := ![42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]
  let row (m : ℕ) (j : Fin 9) : Bool := m.testBit j.val
  have edgeCover : ∀ x : Fin 9 → Bool, F x = true →
      ∃ j : Fin 12, ∀ k : Fin 9, row (edgeMask j) k = true → x k = true := by decide
  have independentCover : ∀ x : Fin 9 → Bool, F x = false →
      ∃ j : Fin 12, ∀ k : Fin 9, x k = true → row (independentMask j) k = true := by decide
  have edgeMember : ∀ j, edgeMask j ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288] : List ℕ) := by decide
  have independentMember : ∀ j, independentMask j ∈ ([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ) := by decide
  let D (b : Bool) : Circuit := ⟨replaceByConst C.gates q.val b, C.output⟩
  have nonNot (b : Bool) (g : Gate) (hg : g ∈ (D b).gates) :
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
    have h := List.countP_eq_zero.mp (changed b) _ hg
    have hne : g.op ≠ GateOp.not := fun hn => h ((p_not _).mpr hn)
    rcases List.mem_or_eq_of_mem_set hg with hmem | rfl
    · have ha := (fan g hmem).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      tauto
    · cases b with
      | false =>
        change GateOp.or ∈ ({GateOp.and, GateOp.or} : Set GateOp)
        simp
      | true =>
        change GateOp.and ∈ ({GateOp.and, GateOp.or} : Set GateOp)
        simp
  have Dmono (b : Bool) (x y : Fin 9 → Bool)
      (h : ∀ j, x j = true → y j = true) :
      circuitFun 9 (D b) x = true → circuitFun 9 (D b) y = true := by
    apply monotone_foldl_wiresStep (D b).gates (nonNot b) (List.ofFn x) (List.ofFn y) (by simp) _ C.output
    intro j hj
    by_cases lt : j < 9
    · rw [getD_ofFn x j lt] at hj
      rw [getD_ofFn y j lt]
      exact h _ hj
    · rw [getD_ge_length (List.ofFn x) j (by simpa using Nat.le_of_not_gt lt)] at hj
      cases hj
  let pre := C.gates.take i
  let post := C.gates.drop (i + 1)
  have postMono (g : Gate) (hg : g ∈ post) :
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
    apply nonNot false g
    change g ∈ C.gates.set i (constGate false)
    rw [List.set_eq_take_append_cons_drop, ite_eq_left hi]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hg)
  have decomp (x : Fin 9 → Bool) (b : Bool) :
      circuitFun 9 (D b) x =
        (post.foldl wiresStep (pre.foldl wiresStep (List.ofFn x) ++ [b])).getD C.output false := by
    change (((C.gates.set i (constGate b)).foldl wiresStep (List.ofFn x))).getD C.output false = _
    rw [List.set_eq_take_append_cons_drop, ite_eq_left hi, List.foldl_append, List.foldl_cons]
    cases b <;> rfl
  have pairOrder (x : Fin 9 → Bool) :
      circuitFun 9 (D false) x = true → circuitFun 9 (D true) x = true := by
    rw [decomp, decomp]
    let w := pre.foldl wiresStep (List.ofFn x)
    exact monotone_foldl_wiresStep post postMono (w ++ [false]) (w ++ [true])
      (by simp) (append_bit_mono w w rfl (fun _ h => h) false true (by decide)) _
  have equalsSome (x : Fin 9 → Bool) : ∃ b, circuitFun 9 (D b) x = F x := by
    let w := pre.foldl wiresStep (List.ofFn x)
    let b := C.gates[i].op.eval (C.gates[i].inputs.map fun j => w.getD j false)
    refine ⟨b, ?_⟩
    have hx := congrFun correct x
    change (C.gates.foldl wiresStep (List.ofFn x)).getD C.output false = F x at hx
    have split : pre ++ C.gates[i] :: post = C.gates := by
      calc
        _ = C.gates.take i ++ ([C.gates[i]] ++ C.gates.drop (i + 1)) := rfl
        _ = (C.gates.take i ++ [C.gates[i]]) ++ C.gates.drop (i + 1) :=
          (List.append_assoc _ _ _).symm
        _ = C.gates := by rw [List.take_append_getElem hi, List.take_append_drop]
    rw [← split, List.foldl_append, List.foldl_cons] at hx
    rw [decomp]
    exact hx
  have below (x : Fin 9 → Bool) : circuitFun 9 (D false) x = true → F x = true := by
    intro h
    obtain ⟨b, hb⟩ := equalsSome x
    rw [← hb]
    cases b
    · exact h
    · exact pairOrder x h
  have above (x : Fin 9 → Bool) : F x = true → circuitFun 9 (D true) x = true := by
    intro h
    obtain ⟨b, hb⟩ := equalsSome x
    rw [← hb] at h
    cases b
    · exact pairOrder x h
    · exact h
  obtain ⟨_, x, hx⟩ := changeout false
  change circuitFun 9 (D false) x ≠ circuitFun 9 C x at hx
  rw [correct] at hx
  change circuitFun 9 (D false) x ≠ F x at hx
  have start : F x = true := by
    cases hb : F x
    · apply False.elim
      rw [hb] at hx
      exact Bool.noConfusion (hb.symm.trans (below x (Bool.eq_true_of_ne_false hx)))
    · rfl
  have reject : circuitFun 9 (D false) x = false := by
    rw [start] at hx
    cases hd : circuitFun 9 (D false) x
    · rfl
    · exact False.elim (hx hd)
  obtain ⟨j, includes⟩ := edgeCover x start
  have missed : circuitFun 9 (D false) (row (edgeMask j)) = false := by
    cases hd : circuitFun 9 (D false) (row (edgeMask j))
    · rfl
    · exact False.elim (Bool.noConfusion (reject.symm.trans (Dmono false _ _ includes hd)))
  obtain ⟨_, y, hy⟩ := changeout true
  change circuitFun 9 (D true) y ≠ circuitFun 9 C y at hy
  rw [correct] at hy
  change circuitFun 9 (D true) y ≠ F y at hy
  have endPoint : F y = false := by
    cases hb : F y
    · rfl
    · exact False.elim (hy ((above y hb).trans hb.symm))
  have accept : circuitFun 9 (D true) y = true := by
    rw [endPoint] at hy
    exact Bool.eq_true_of_ne_false hy
  obtain ⟨k, contained⟩ := independentCover y endPoint
  have spurious := Dmono true y (row (independentMask k)) contained accept
  exact essential C fan first size
    ⟨fun _ => q, fun j hj => ⟨0, (cover j hj).symm⟩⟩ q qnot
    ⟨edgeMask j, edgeMember j, missed⟩ ⟨independentMask k, independentMember k, spurious⟩ correct
