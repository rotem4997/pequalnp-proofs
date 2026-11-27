import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection
open PEqualNP.CrossAnd PEqualNP.MetaComplexity.NestedCover PEqualNP.SyntacticMultilinear

theorem PEqualNP.Outside.R_meta_4594_1
    (localRepair : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      199 ≤ q → N = q^2 + q + 1 → (∀ l, (S l).card = q+1) →
      (∀ l m, l ≠ m → (S l ∩ S m).card ≤ 1) → Monotone2 C → ComputesIncidence S C →
      let M : Finset (Fin (N+N)) := Finset.univ.map (Fin.natAddEmb N)
      2*C.size < N*q → 0 < crossCount (N+N) M C →
      ∃ (j : Fin C.size) (ws : List ℕ) (es : List (Fin N × Fin N)),
        IsCrossAnd (N+N) M C j ∧ ws.length ≤ 2 ∧ es.length ≤ 24 ∧
        let B : Circuit := ⟨C.gates.set j ⟨.or, ws⟩, C.output⟩
        support (N+N) B (N+N+j) ⊆ support (N+N) C (N+N+j) ∧
        (∀ X Y, B.eval (incidenceInput X Y) = true → incidenceFun S X Y = true) ∧
        ∀ p l, p ∈ S l → (p,l) ∉ es → B.eval (incidenceInput {p} {l}) = true)
    (shrink : ∀ (n : ℕ) (M : Finset (Fin n)) (C : Circuit) (j : Fin C.size) (ws : List ℕ),
      IsCrossAnd n M C j →
      support n ⟨C.gates.set j ⟨.or, ws⟩, C.output⟩ (n+j) ⊆ support n C (n+j) →
      crossCount n M ⟨C.gates.set j ⟨.or, ws⟩, C.output⟩ < crossCount n M C)
    :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (199 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → (x3 x8 ∩ x3 x9).card ≤ (1 : ℕ)) →           PEqualNP.MetaComplexity.Monotone2 x4 →             PEqualNP.GenericRejection.ComputesIncidence x3 x4 →               have x11 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := PEqualNP.CrossAnd.crossCount (x2 + x2) (Finset.map (Fin.natAddEmb x2) Finset.univ);               (2 : ℕ) * x4.size < x2 * x1 → (0 : ℕ) < x11 x4 → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x14 ∧ PEqualNP.GenericRejection.ComputesIncidence x3 x14 ∧ x11 x14 < x11 x4 ∧ x14.size ≤ x4.size + (49 : ℕ) := by
  classical
  intro q N S C hq hN degrees thin mono exactC _cost small pos
  let n := N+N
  let M : Finset (Fin (N+N)) := Finset.univ.map (Fin.natAddEmb N)
  let cost := crossCount n M
  obtain ⟨j, ws, es, crossed, arity, bound, localSupport, soundB, covered⟩ :=
    localRepair q N S C hq hN degrees thin mono exactC small pos
  let B : Circuit := ⟨C.gates.set j ⟨.or, ws⟩, C.output⟩
  have sizeEq (K : Circuit) : K.size = K.gates.length := rfl
  have gateEq (K : Circuit) (k : ℕ) : gateAt K k = K.gates.getD k ⟨.or,[]⟩ := rfl
  have inputEq (X Y : Finset (Fin N)) : incidenceInput X Y =
      List.ofFn (fun p : Fin N => decide (p ∈ X)) ++ List.ofFn (fun l : Fin N => decide (l ∈ Y)) := rfl
  have mb : Monotone2 B := by
    intro g hg
    rcases List.mem_or_eq_of_mem_set hg with old | rfl
    · exact mono g old
    · exact ⟨by simp, arity⟩
  have less : cost B < cost C := shrink n M C j ws crossed localSupport
  have sizeB : B.size = C.size := by simp [B, sizeEq]
  have extend {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
      ∃ tail, gs.foldl (fun v g => v ++ [f v g]) w = w ++ tail ∧ tail.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      obtain ⟨t, he, hl⟩ := ih (w ++ [f w g])
      exact ⟨f w g :: t, by simp [he], by simp [hl]⟩
  have left {α : Type} (w t : List α) (i : ℕ) (d : α) (hi : i < w.length) :
      (w ++ t).getD i d = w.getD i d := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have atEnd {α : Type} (w : List α) (v d : α) :
      (w ++ [v]).getD w.length d = v := by simp [List.getD_eq_getElem?_getD]
  -- Appending the conjunction of two primary inputs costs one AND and one output OR.
  -- The new AND joins opposite sides, so it adds no cross AND.
  have patch (D : Circuit) (md : Monotone2 D) (p l : Fin N) :
      ∃ H : Circuit, Monotone2 H ∧ H.size = D.size + 2 ∧ cost H = cost D ∧
      ∀ X Y, H.eval (incidenceInput X Y) =
        (D.eval (incidenceInput X Y) || decide (p ∈ X ∧ l ∈ Y)) := by
    let a : Gate := ⟨.and, [p.val,N+l.val]⟩
    let z := n + D.size
    let b : Gate := ⟨.or, [if D.output < z then D.output else z, z]⟩
    let H : Circuit := ⟨D.gates ++ [a,b], z+1⟩
    refine ⟨H, ?_, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ D.gates ++ [a,b] at hg
      rcases List.mem_append.mp hg with old | new
      · exact md g old
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at new
        rcases new with rfl | rfl <;> simp [a,b]
    · simp [H,sizeEq]
    · let inp := List.ofFn (fun i : Fin n => ({i} : Finset (Fin n)))
      let f (v : List (Finset (Fin n))) (g : Gate) :=
        g.inputs.foldr (fun w acc => v.getD w ∅ ∪ acc) ∅
      obtain ⟨t, ht, lt⟩ := extend f D.gates inp
      change supports n D = inp ++ t at ht
      obtain ⟨u, hu, _⟩ := extend f [a,b] (supports n D)
      have ext : supports n H = supports n D ++ u := by
        delta supports
        simp only [H,List.foldl_append]
        exact hu
      have lens : (supports n D).length = z := by simp [ht, inp, lt, z, sizeEq]
      have oldSupport (w : ℕ) (hw : w < z) : support n H w = support n D w := by
        delta support
        rw [ext]
        exact left _ _ _ _ (lens ▸ hw)
      have old (k : ℕ) (hk : k < D.size) : IsCrossAnd n M H k ↔ IsCrossAnd n M D k := by
        have same : gateAt H k = gateAt D k := left D.gates [a,b] k _ hk
        have opSame (w : ℕ) : operandSupport n H k w = operandSupport n D k w := by
          delta operandSupport
          split <;> first | rfl | exact oldSupport w (by dsimp [z]; omega)
        delta IsCrossAnd
        simp only [same, opSame]
      have primary (v : Fin n) : support n H v.val = {v} := by
        rw [oldSupport v.val (by have := v.isLt; dsimp [z]; omega)]
        delta support
        simp only [ht, left inp t v.val ∅ (by simpa [inp] using v.isLt)]
        simp [inp, List.getD_eq_getElem?_getD, v.isLt]
      let point := Fin.castAdd N p
      let line := Fin.natAdd N l
      have pside : point ∉ M := by
        simp only [M, Finset.mem_map, Finset.mem_univ, true_and, not_exists]
        intro k eq
        have eqv := congrArg Fin.val eq
        change N + k.val = p.val at eqv
        have := p.isLt
        omega
      have lside : line ∈ M := Finset.mem_map.mpr ⟨l, Finset.mem_univ _, rfl⟩
      have primOp (v : Fin n) : operandSupport n H D.size v.val = {v} := by
        delta operandSupport
        rw [if_pos (by have := v.isLt; omega), primary]
      have noA : ¬ IsCrossAnd n M H D.size := by
        have ga : gateAt H D.size = a := by
          simp [gateEq, H, sizeEq, List.getD_eq_getElem?_getD]
        delta IsCrossAnd
        simp only [ga, a, List.getD_cons_zero, List.getD_cons_succ]
        change ¬ (_ ∧ _ ∧ ((_ ∧ _) ∨ (_ ∧ _)))
        rintro ⟨_, _, ⟨hp,_⟩ | ⟨_,hl⟩⟩
        · change (operandSupport n H D.size point.val ∩ M).Nonempty at hp
          simpa [primOp, pside] using hp
        · change (operandSupport n H D.size line.val \ M).Nonempty at hl
          rw [primOp] at hl
          obtain ⟨v,hv⟩ := hl
          obtain ⟨iv,ov⟩ := Finset.mem_sdiff.mp hv
          exact ov ((Finset.mem_singleton.mp iv) ▸ lside)
      have noB : ¬ IsCrossAnd n M H (D.size+1) := by
        have gb : gateAt H (D.size+1) = b := by
          simp [gateEq, H, sizeEq, List.getD_eq_getElem?_getD,
            List.getElem?_append_right]
        intro h
        simpa [gb,b] using h.1
      have eqSets : (Finset.range H.size).filter (IsCrossAnd n M H) =
          (Finset.range D.size).filter (IsCrossAnd n M D) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hk,hc⟩
          have sz : H.size = D.size+2 := by simp [H,sizeEq]
          have hk' : k < D.size := by
            by_contra! h
            rcases (show k = D.size ∨ k = D.size+1 by omega) with rfl | rfl
            · exact noA hc
            · exact noB hc
          exact ⟨hk', (old k hk').mp hc⟩
        · rintro ⟨hk,hc⟩
          exact ⟨by simp [H,sizeEq] at *; omega, (old k hk).mpr hc⟩
      exact congrArg Finset.card eqSets
    · intro X Y
      let x := incidenceInput X Y
      let f (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
      let w := D.wires x
      obtain ⟨t, ht, lt⟩ := extend f D.gates x
      change w = x ++ t at ht
      have lx : x.length = n := by simp [x,inputEq,n]
      have lw : w.length = z := by simp [ht,lx,lt,z,sizeEq]
      have valP : w.getD p.val false = decide (p ∈ X) := by
        rw [ht,left x t _ _ (by rw [lx]; dsimp [n]; have := p.isLt; omega)]
        simp [x,inputEq,List.getD_eq_getElem?_getD,List.getElem?_append_left,p.isLt]
      have valL : w.getD (N+l.val) false = decide (l ∈ Y) := by
        rw [ht,left x t _ _ (by rw [lx]; dsimp [n]; have := l.isLt; omega)]
        simp [x,inputEq,List.getD_eq_getElem?_getD,List.getElem?_append_right,l.isLt]
      let v := decide (p ∈ X ∧ l ∈ Y)
      have av : f w a = v := by
        change (w.getD p.val false && (w.getD (N+l.val) false && true)) = _
        rw [valP,valL]
        simp [v]
      let w' := w ++ [v]
      have vz : w'.getD z false = v := lw ▸ atEnd w v false
      have bv : f w' b = (w.getD D.output false || v) := by
        change (w'.getD (if D.output < z then D.output else z) false ||
          (w'.getD z false || false)) = _
        rw [vz, Bool.or_false]
        by_cases ho : D.output < z
        · rw [if_pos ho,left w [v] D.output false (lw ▸ ho)]
        · have absent := List.getD_eq_default w false (show w.length ≤ D.output by omega)
          rw [if_neg ho,vz,absent]; simp
      have allw : H.wires x = w' ++ [f w' b] := by
        change (D.gates ++ [a,b]).foldl (fun s g => s ++ [f s g]) x = _
        simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
        change w ++ [f w a] ++ [f (w ++ [f w a]) b] = _
        rw [av]
      change (H.wires x).getD (z+1) false = _
      rw [allw, ← show w'.length = z+1 by simp [w',lw], atEnd, bv]
      rfl
  have many (pairs : List (Fin N × Fin N)) :
      ∃ D : Circuit, Monotone2 D ∧ D.size = B.size + 2*pairs.length ∧ cost D = cost B ∧
      ∀ X Y, D.eval (incidenceInput X Y) =
        (B.eval (incidenceInput X Y) || pairs.any (fun e => decide (e.1 ∈ X ∧ e.2 ∈ Y))) := by
    induction pairs with
    | nil => exact ⟨B, mb, by simp, rfl, by simp⟩
    | cons e es ih =>
      obtain ⟨D,md,sz,cs,ev⟩ := ih
      obtain ⟨H,mh,hs,hc,he⟩ := patch D md e.1 e.2
      refine ⟨H,mh,?_,hc.trans cs,?_⟩
      · simp only [List.length_cons]; omega
      · intro X Y
        simp only [he,ev,List.any_cons]
        ac_rfl
  let edges := es.filter fun e => decide (e.1 ∈ S e.2)
  have edgeBound : edges.length ≤ 24 := (List.length_filter_le ..).trans bound
  obtain ⟨D,md,sz,cs,ev⟩ := many edges
  refine ⟨D,md,?_,show cost D < cost C from cs.trans_lt less,by omega⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let rel (a b : List Bool) := a.length=b.length ∧ ∀ i, a.getD i false=true → b.getD i false=true
  have push (w : List Bool) (v : Bool) (i : ℕ) :
      (w++[v]).getD i false = if i=w.length then v else w.getD i false := by
    by_cases hl : i<w.length
    · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hl,Nat.ne_of_lt hl]
    · rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
      by_cases he : i=w.length
      · simp [he]
      · simp [he,List.getElem?_eq_none (by omega : w.length ≤ i),List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp;omega : [v].length ≤ i-w.length)]
  have andLaw (z : List Bool) : GateOp.and.eval z = z.all id := rfl
  have orLaw (z : List Bool) : GateOp.or.eval z = z.any id := rfl
  have grows (gs : List Gate) (good : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) (a b : List Bool)
      (le : rel a b) : rel (gs.foldl step a) (gs.foldl step b) := by
    induction gs generalizing a b with
    | nil => exact le
    | cons g gs ih =>
      apply ih (fun k hk => good k (List.mem_cons_of_mem g hk))
      refine ⟨by simp [step,le.1],?_⟩
      intro i
      simp only [step,push,le.1]
      split
      · have hh := le.2
        rcases good g List.mem_cons_self with op | op
        · simp [op,andLaw]; aesop
        · simp [op,orLaw]; aesop
      · exact le.2 i
  have funMono (x y : Fin (N+N) → Bool) (h : ∀ i, x i=true → y i=true) :
      circuitFun (N+N) D x=true → circuitFun (N+N) D y=true := by
    apply (grows D.gates (fun g hg => (md g hg).1) (List.ofFn x) (List.ofFn y) _).2 D.output
    refine ⟨by simp,?_⟩
    intro i
    by_cases hi : i<N+N
    · simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,dite_true,Option.getD_some] using h ⟨i,hi⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp
  let bits (X Y : Finset (Fin N)) :=
    Fin.append (fun p : Fin N => decide (p ∈ X)) (fun l : Fin N => decide (l ∈ Y))
  have bridge (X Y : Finset (Fin N)) : List.ofFn (bits X Y) = incidenceInput X Y :=
    List.ofFn_fin_append _ _
  have grow {X Y : Finset (Fin N)} {p l : Fin N} (hp : p ∈ X) (hl : l ∈ Y) :
      D.eval (incidenceInput {p} {l}) = true → D.eval (incidenceInput X Y) = true := by
    rw [← bridge, ← bridge]
    apply funMono
    intro i
    refine Fin.addCases (motive := fun i => bits {p} {l} i = true → bits X Y i = true) ?_ ?_ i
    · intro k
      simpa [bits] using (show k = p → k ∈ X from fun h => h ▸ hp)
    · intro k
      simpa only [bits,Fin.append_right,decide_eq_true_eq,Finset.mem_singleton] using (show k = l → k ∈ Y from fun h => h ▸ hl)
  intro X Y
  apply Bool.eq_iff_iff.mpr
  constructor
  · rw [ev, Bool.or_eq_true]
    rintro (hb | he)
    · exact soundB X Y hb
    · obtain ⟨e, mem, hit⟩ := List.any_eq_true.mp he
      obtain ⟨hp,hl⟩ := of_decide_eq_true hit
      exact decide_eq_true ⟨e.1,hp,e.2,hl,of_decide_eq_true (List.mem_filter.mp mem).2⟩
  · intro h
    obtain ⟨p,hp,l,hl,inc⟩ := of_decide_eq_true h
    apply grow hp hl
    rw [ev,Bool.or_eq_true]
    by_cases e : (p,l) ∈ es
    · right
      apply List.any_eq_true.mpr
      exact ⟨(p,l),List.mem_filter.mpr ⟨e,decide_eq_true inc⟩,by simp⟩
    · exact Or.inl (covered p l inc e)
