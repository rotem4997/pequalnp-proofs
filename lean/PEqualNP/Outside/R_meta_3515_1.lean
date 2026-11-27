import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

-- Input zero has two neighbors. The two blocks share a tapped wire across its two cofactors.
-- A single AND or OR at the tap restores the missing input.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 14000 in
theorem PEqualNP.Outside.R_meta_3515_1
    (blocks : ∃ (P S : Circuit) (useOr : Bool),
      IsAO2 9 P ∧ IsAO2 (10 + P.size) S ∧
      (∀ g ∈ P.gates ++ S.gates, g.inputs.Nodup) ∧
      P.output < 9 + P.size ∧ P.size + S.size ≤ 13 ∧
      ∀ (b : Bool) (m : ℕ), m ∈ (if b then [65, 66, 72, 129, 132, 160, 258, 272, 288, 516, 520, 528] else [63, 116, 154, 208, 269, 324, 392, 547, 608, 642, 769, 960] : List ℕ) →
        let w := List.ofFn (fun j : Fin 9 => m.testBit (j.val + 1))
        let z := P.eval w
        S.eval (P.wires w ++ [if useOr then m.testBit 0 || z else m.testBit 0 && z]) = b)
    (cover : ∀ x : Fin 10 → Bool,
      (∃ m ∈ ([65, 66, 72, 129, 132, 160, 258, 272, 288, 516, 520, 528] : List ℕ), ∀ i : Fin 10, m.testBit i.val = true → x i = true) ∨
      (∃ m ∈ ([63, 116, 154, 208, 269, 324, 392, 547, 608, 642, 769, 960] : List ℕ), ∀ i : Fin 10, x i = true → m.testBit i.val = true)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ x1.size ≤ (14 : ℕ) ∧ ∀ (x2 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (10 : ℕ)) (x4 : Fin (10 : ℕ)), (↑x3, ↑x4) ∈ [((0 : ℕ), (6 : ℕ)), ((0 : ℕ), (7 : ℕ)), ((1 : ℕ), (6 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (7 : ℕ)), ((2 : ℕ), (9 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (9 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (9 : ℕ)), ((5 : ℕ), (7 : ℕ)), ((5 : ℕ), (8 : ℕ))] ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true := by
  obtain ⟨P,S,useOr,hP,hS,distinct,tap,cost,computed⟩ := blocks
  have readGate (C : Circuit) (j : ℕ) : gateAt C j = C.gates.getD j ⟨.or,[]⟩ := rfl
  have sizeEq (C : Circuit) : C.size = C.gates.length := rfl
  let positives : List ℕ := [65, 66, 72, 129, 132, 160, 258, 272, 288, 516, 520, 528]
  let negatives : List ℕ := [63, 116, 154, 208, 269, 324, 392, 547, 608, 642, 769, 960]
  let row (m : ℕ) (i : Fin 10) := m.testBit i.val
  let target (x : Fin 10 → Bool) :=
    ([(0, 6), (0, 7), (1, 6), (1, 8), (2, 7), (2, 9), (3, 6), (3, 9), (4, 8), (4, 9), (5, 7), (5, 8)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)
  let liftGate (g : Gate) : Gate := ⟨g.op,g.inputs.map Nat.succ⟩
  let marked : Gate := ⟨if useOr then .or else .and,[0,P.output + 1]⟩
  let D : Circuit := ⟨(P.gates.map liftGate ++ [marked]) ++ S.gates.map liftGate,S.output + 1⟩
  let wf (n : ℕ) (gs : List Gate) :=
    ∀ (j : ℕ) (h : j < gs.length) (i : ℕ), i ∈ gs[j].inputs → i < n + j
  have wfOf (n : ℕ) (C : Circuit) (h : ReadsBack n C) : wf n C.gates := by
    intro j hj i hi
    apply h j hj i
    simpa only [readGate,List.getD_eq_getElem _ _ hj] using hi
  have liftWF (n : ℕ) (gs : List Gate) (h : wf n gs) : wf (n + 1) (gs.map liftGate) := by
    intro j hj i hi
    have old : j < gs.length := by simpa using hj
    simp only [List.getElem_map,liftGate,List.mem_map] at hi
    obtain ⟨k,hk,rfl⟩ := hi
    have := h j old k hk
    omega
  have appendWF (n : ℕ) (a b : List Gate) (ha : wf n a) (hb : wf (n + a.length) b) :
      wf n (a ++ b) := by
    intro j hj i hi
    by_cases early : j < a.length
    · rw [List.getElem_append_left early] at hi
      exact ha j early i hi
    · have later : a.length ≤ j := by omega
      rw [List.getElem_append_right later] at hi
      have bound : j - a.length < b.length := by simp only [List.length_append] at hj; omega
      have := hb _ bound i hi
      omega
  have markerWF : wf (10 + P.size) [marked] := by
    intro j hj i hi
    have e : j = 0 := by simpa using hj
    subst j
    simp only [List.getElem_cons_zero,marked,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl <;> omega
  have allWF : wf 10 D.gates := by
    apply appendWF
    · apply appendWF
      · exact liftWF 9 P.gates (wfOf 9 P hP.2.1)
      · simpa [sizeEq] using markerWF
    · simpa [sizeEq,Nat.add_assoc] using liftWF (10 + P.size) S.gates (wfOf _ S hS.2.1)
  have shape (g : Gate) (hg : g ∈ D.gates) :
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup := by
    change g ∈ (_ ++ [marked]) ++ _ at hg
    rcases List.mem_append.mp hg with earlyGates | lateGates
    · rcases List.mem_append.mp earlyGates with before | atMark
      · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp before
        refine ⟨hP.1 q hq,?_,?_⟩
        · simpa [liftGate] using hP.2.2 q hq
        · exact (distinct _ (List.mem_append_left _ hq)).map Nat.succ_injective
      · obtain rfl := List.mem_singleton.mp atMark
        exact ⟨by cases e : useOr <;> simp [marked,e],rfl,by simp [marked]⟩
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp lateGates
      refine ⟨hS.1 q hq,?_,?_⟩
      · simpa [liftGate] using hS.2.2 q hq
      · exact (distinct _ (List.mem_append_right _ hq)).map Nat.succ_injective
  have hD : IsAO2 10 D := by
    refine ⟨fun _ hg => (shape _ hg).1,?_,fun _ hg => (shape _ hg).2.1⟩
    intro j hj i hi
    apply allWF j hj i
    simpa only [readGate,List.getD_eq_getElem _ _ hj] using hi
  have sizeD : D.size ≤ 14 := by
    simp only [D,sizeEq,List.length_append,List.length_map,List.length_singleton]
    change P.gates.length + S.gates.length ≤ 13 at cost
    omega
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have shift (gs : List Gate) (b : Bool) (w : List Bool) :
      (gs.map liftGate).foldl step (b :: w) = b :: gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      have one : step (b :: w) (liftGate g) = b :: step w g := by
        simp only [step,liftGate,List.map_map,List.cons_append]
        rfl
      rw [List.map_cons,List.foldl_cons,List.foldl_cons,one,ih]
  have sample (b : Bool) (m : ℕ) (hm : m ∈ (if b then positives else negatives)) :
      D.eval (List.ofFn (row m)) = b := by
    let w := List.ofFn (fun j : Fin 9 => m.testBit (j.val + 1))
    have input : List.ofFn (row m) = m.testBit 0 :: w := by rw [List.ofFn_succ]; rfl
    let z := P.eval w
    let val := if useOr then m.testBit 0 || z else m.testBit 0 && z
    have op : step (m.testBit 0 :: P.wires w) marked = m.testBit 0 :: (P.wires w ++ [val]) := by
      have andTwo (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
      have orTwo (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
      change (m.testBit 0 :: P.wires w) ++ [marked.op.eval [m.testBit 0,z]] = _
      cases e : useOr <;> simp only [marked,val,e,Bool.false_eq_true,ite_false,ite_true,
        andTwo,orTwo,List.cons_append]
    change (D.gates.foldl step (List.ofFn (row m))).getD (S.output+1) false = b
    rw [input]
    change (((_ ++ [marked]) ++ _).foldl step _).getD (S.output+1) false = b
    rw [List.foldl_append,List.foldl_append,shift,List.foldl_cons,List.foldl_nil]
    change ((S.gates.map liftGate).foldl step (step (_ :: P.wires w) marked)).getD (S.output+1) false = b
    rw [op,shift]
    exact computed b m hm
  let below (w u : List Bool) := w.length = u.length ∧ ∀ i, w.getD i false = true → u.getD i false = true
  have extend {w u : List Bool} {a b : Bool} (h : below w u) (v : a = true → b = true) :
      below (w ++ [a]) (u ++ [b]) := by
    obtain ⟨len,old⟩ := h
    refine ⟨by simp [len],?_⟩
    intro i
    by_cases hi : i < w.length
    · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (len ▸ hi)]
      exact old i
    · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len]
      cases i - u.length with
      | zero => exact v
      | succ k => simp [List.getD]
  have runMono (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (w u : List Bool) (h : below w u) : below (gs.foldl step w) (gs.foldl step u) := by
    induction gs generalizing w u with
    | nil => exact h
    | cons g gs ih =>
      apply ih (fun q hq => ops q (List.mem_cons_of_mem _ hq)) (step w g) (step u g)
      apply extend h
      intro val
      rcases ops g List.mem_cons_self with op | op
      · rw [op] at val ⊢
        change (g.inputs.map _).all id = true at val
        apply List.all_eq_true.mpr
        intro b hb
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
        exact h.2 i (List.all_eq_true.mp val _ (List.mem_map.mpr ⟨i,hi,rfl⟩))
      · rw [op] at val ⊢
        change (g.inputs.map _).any id = true at val
        obtain ⟨b,hb,v⟩ := List.any_eq_true.mp val
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
        exact List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,h.2 i v⟩
  have mono (x y : Fin 10 → Bool) (le : ∀ i, x i = true → y i = true) :
      D.eval (List.ofFn x) = true → D.eval (List.ofFn y) = true := by
    have initial : below (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp,?_⟩
      intro i
      by_cases h : i < 10
      · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by simpa using h)]
        simpa only [List.getElem_ofFn] using le ⟨i,h⟩
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
        exact id
    exact (runMono D.gates hD.1 _ _ initial).2 D.output
  have graphMono (x y : Fin 10 → Bool) (le : ∀ i, x i = true → y i = true) :
      target x = true → target y = true := by
    intro h
    obtain ⟨e,he,yes⟩ := List.any_eq_true.mp h
    exact List.any_eq_true.mpr ⟨e,he,Bool.and_eq_true_iff.mpr
      ⟨le e.1 (Bool.and_eq_true_iff.mp yes).1,le e.2 (Bool.and_eq_true_iff.mp yes).2⟩⟩
  have values : positives.all (fun m => target (row m)) = true ∧
      negatives.all (fun m => !target (row m)) = true := by decide +kernel
  have backward {a b : Bool} (inc : a = true → b = true) (hb : b = false) : a = false := by
    cases ha : a with
    | false => rfl
    | true => have bad := inc ha; rw [hb] at bad; contradiction
  have spec : ∀ x : Fin 10 → Bool, target x = true ↔
      ∃ p q : Fin 10, (p.val,q.val) ∈ ([(0, 6), (0, 7), (1, 6), (1, 8), (2, 7), (2, 9), (3, 6), (3, 9), (4, 8), (4, 9), (5, 7), (5, 8)] : List (ℕ × ℕ)) ∧ x p = true ∧ x q = true := by
    decide +kernel
  refine ⟨D,hD,fun _ hg => (shape _ hg).2.2,sizeD,?_⟩
  intro x
  have agrees : D.eval (List.ofFn x) = target x := by
    rcases cover x with ⟨m,hm,le⟩ | ⟨m,hm,le⟩
    · have f := mono (row m) x le (sample true m hm)
      have g := graphMono (row m) x le (List.all_eq_true.mp values.1 m hm)
      exact f.trans g.symm
    · have f := backward (mono x (row m) le) (sample false m hm)
      have v := List.all_eq_true.mp values.2 m hm
      have t : target (row m) = false := by
        cases a : target (row m) with
        | false => rfl
        | true => change (!target (row m)) = true at v; rw [a] at v; contradiction
      exact f.trans (backward (graphMono x (row m) le) t).symm
  rw [agrees]
  exact spec x
