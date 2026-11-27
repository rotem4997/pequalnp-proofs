import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- A false input forces an AND reader low and a NOT reader high.
-- In the remaining graph case every unmarked input has a direct OR reader.
-- Every NOT on an unmarked input has just one consumer, an AND whose
-- two inputs are both internal wires.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_4107_253
    -- When the two forced gates have the same successor, that successor also
    -- becomes constant. Its own successor can supply the fourth gate.
    (absorbing : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (p q : Fin C.size),
      IsMinimalCircuit n C → ReadsBack n C →
      (∀ g ∈ C.gates, g.inputs.Nodup ∧ g.inputs.length = (if g.op.eval [false] then 1 else 2)) →
      (∃ x y : Fin n → Bool, circuitFun n C (Function.update x v false) ≠ circuitFun n C (Function.update y v false)) →
      p ≠ q → v.val ∈ (C.gates.get p).inputs → v.val ∈ (C.gates.get q).inputs →
      ((C.gates.get p).op = .and ∨ (C.gates.get p).op = .not) →
      ((C.gates.get q).op = .and ∨ (C.gates.get q).op = .not) →
      ∃ s : ℕ, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s)
    (propagate : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (j : ℕ),
      let rd := fun (w : ℕ) => C.gates.filter (fun g => g.inputs.contains w)
      IsMinimalCircuit n C → ReadsBack n C →
      (∀ g ∈ C.gates, g.inputs.Nodup ∧ g.inputs.length = (if g.op.eval [false] then 1 else 2)) →
      (∃ x y : Fin n → Bool, circuitFun n C (Function.update x v false) ≠ circuitFun n C (Function.update y v false)) → (rd v.val).length = 2 → (∃ g ∈ rd v.val, g.op = GateOp.or) →
      j < C.size → (gateAt C j).op = GateOp.not → v.val ∈ (gateAt C j).inputs →
      ¬ (∃ h : Gate, rd (n + j) = [h] ∧ h.op = GateOp.and) →
      ∃ s : ℕ, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s)
    -- Fix the primary input of the AND. Removing the AND leaves its private
    -- predecessor unused. A separate OR reader of the primary input also goes.
    (coinput : ∀ (n : ℕ) (C : Circuit) (w : Fin n) (j : ℕ) (h : Gate),
      let rd := fun (i : ℕ) => C.gates.filter (fun g => g.inputs.contains i)
      IsMinimalCircuit n C → ReadsBack n C →
      (∀ g ∈ C.gates, g.inputs.Nodup ∧ g.inputs.length = (if g.op.eval [false] then 1 else 2)) →
      (∃ x y : Fin n → Bool, circuitFun n C (Function.update x w false) ≠ circuitFun n C (Function.update y w false)) →
      j < C.size → (gateAt C j).op = GateOp.not → rd (n + j) = [h] →
      h.op = GateOp.and → w.val ∈ h.inputs →
      ∃ s : ℕ, s + 2 ≤ C.size ∧ ((∃ g ∈ rd w.val, g.op = GateOp.or) → s + 4 ≤ C.size) ∧
        HasCircuitSize n (fun x => circuitFun n C (Function.update x w false)) s)
    (core : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
      let rd := fun (w : ℕ) => C.gates.filter (fun g => g.inputs.contains w)
      (∀ u ∉ A, (G.neighborSet u).ncard = 3) →
      (∀ (u : Fin n) (p : G.Walk u u), p.IsCycle → 7 ≤ p.length) →
      (∀ u w, G.Adj u w → u ∉ A) → (∃ u w, G.Adj u w) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G A → ReadsBack n C →
      (∀ g ∈ C.gates, g.inputs.Nodup ∧ g.inputs.length = (if g.op.eval [false] then 1 else 2)) →
      (∀ u ∉ A, 2 ≤ (rd u.val).length ∧ (rd u.val).length ≤ 3 ∧
        ((rd u.val).length = 3 → ∀ g ∈ rd u.val, g.op = GateOp.or)) →
      (∀ v ∉ A, ∃ g ∈ rd v.val, g.op = GateOp.or) →
      (∀ (v : Fin n), v ∉ A → ∀ j < C.size, (gateAt C j).op = GateOp.not →
        v.val ∈ (gateAt C j).inputs → ∃ h : Gate, rd (n + j) = [h] ∧ h.op = GateOp.and ∧
          ∀ i ∈ h.inputs, n ≤ i) →
      (∃ v ∉ A, ∃ g ∈ rd v.val, g.op = GateOp.not) →
      ∃ v ∉ A, ∃ s : ℕ, s + 4 ≤ C.size ∧ HasCircuitSize n
        (fun x => graphFun G A (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : List PEqualNP.CircuitLowerBounds.Gate) (x15 : PEqualNP.CircuitLowerBounds.Gate) (x16 : List PEqualNP.CircuitLowerBounds.Gate), x5.gates = x14 ++ x15 :: x16 → (x15.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∃ x18 < x1 + x14.length, x15.inputs = [x18]) ∨ (x15.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ x18 < x1 + x14.length, ∃ x19 < x1 + x14.length, x18 ≠ x19 ∧ x15.inputs = [x18, x19]) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  classical
  intro n G dec A C f readers degree girth unmarked edge minimal computes shape counts hasNot
  have graphValue (x : Fin n → Bool) :
      f x = (decide (∃ a ∈ A, x a = true) ||
             decide (∃ u w, G.Adj u w ∧ x u = true ∧ x w = true)) := rfl
  -- One new OR gate restores a marked literal after its false restriction.
  have markedOr (w : Fin n) (hw : w ∈ A) :
      (fun x => x w || f (Function.update x w false)) = f := by
    funext x
    cases h : x w with
    | false =>
      have same : Function.update x w false = x := by
        rw [← h, Function.update_eq_self]
      simp [same]
    | true =>
      have high : f x = true := by
        rw [graphValue, Bool.or_eq_true]
        exact Or.inl (decide_eq_true ⟨w, hw, h⟩)
      simp [high]
  -- There is an edge avoiding any prescribed vertex, including a marked one.
  have nonconstant (v : Fin n) :
      ∃ x y : Fin n → Bool, f (Function.update x v false) ≠
        f (Function.update y v false) := by
    classical
    obtain ⟨a,b,adj⟩ := edge
    have endpoint : ∃ u : Fin n, u ∉ A ∧ u ≠ v := by
      by_cases h : a = v
      · exact ⟨b,unmarked b a adj.symm,h ▸ adj.symm.ne⟩
      · exact ⟨a,unmarked a b adj,h⟩
    obtain ⟨u,hu,unv⟩ := endpoint
    have exists_other : ∃ w, G.Adj u w ∧ w ≠ v := by
      by_contra h
      have sub : G.neighborSet u ⊆ {v} := by
        intro q hq
        simp only [Set.mem_singleton_iff]
        by_contra hqv
        exact h ⟨q, hq, hqv⟩
      have bound := Set.ncard_le_ncard sub (Set.toFinite {v})
      have hd := degree u hu
      simp only [Set.ncard_singleton] at bound
      omega
    obtain ⟨w, huw, wnv⟩ := exists_other
    let zero : Fin n → Bool := fun _ => false
    let pair : Fin n → Bool := fun i => decide (i = u ∨ i = w)
    have zeroValue : f (Function.update zero v false) = false := by
      rw [graphValue]
      simp [zero]
    have pairValue : f (Function.update pair v false) = true := by
      rw [graphValue]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      right
      refine ⟨u, w, huw, ?_, ?_⟩
      · simp [Function.update_of_ne unv, pair]
      · simp [Function.update_of_ne wnv, pair]
    exact ⟨zero, pair, by rw [zeroValue, pairValue]; decide⟩

  have back : ReadsBack n C := by
    intro j hj w hw
    have split : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
      rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
    have len : (C.gates.take j).length = j := by
      simp [Nat.min_eq_left (Nat.le_of_lt hj)]
    have atEq : gateAt C j = C.gates[j] := List.getD_eq_getElem C.gates _ hj
    rw [atEq] at hw
    rcases shape _ _ _ split with ⟨_,a,ha,e⟩ | ⟨_,a,ha,b,hb,_,e⟩
    · rw [e] at hw
      simp only [List.mem_singleton] at hw
      omega
    · rw [e] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with hw | hw <;> omega
  have arity (g : Gate) (hg : g ∈ C.gates) :
      g.inputs.Nodup ∧ g.inputs.length = (if g.op.eval [false] then 1 else 2) := by
    obtain ⟨pre,post,split⟩ := List.mem_iff_append.mp hg
    rcases shape pre g post split with ⟨op,a,_,pins⟩ | ⟨op,a,_,b,_,ne,pins⟩
    · rw [op,pins]
      exact ⟨by simp,rfl⟩
    · rcases op with op | op <;> rw [op,pins] <;> exact ⟨by simp [ne],rfl⟩
  have twoPositions (C : Circuit) (w : ℕ)
      (h : (C.gates.filter (fun g => g.inputs.contains w)).length = 2) :
      ∃ p q : Fin C.size, p ≠ q ∧
        w ∈ (C.gates.get p).inputs ∧ w ∈ (C.gates.get q).inputs := by
    classical
    have aux (l : List Gate)
        (hl : (l.filter (fun g => g.inputs.contains w)).length = 2) :
        ∃ p q : Fin l.length, p ≠ q ∧
          w ∈ (l.get p).inputs ∧ w ∈ (l.get q).inputs := by
      induction l with
      | nil => simp at hl
      | cons g gs ih =>
        by_cases hg : w ∈ g.inputs
        · have ht : (gs.filter (fun g => g.inputs.contains w)).length = 1 := by
            simpa [List.filter_cons, hg] using hl
          have hn : (gs.filter (fun g => g.inputs.contains w)) ≠ [] := by
            intro he
            rw [he] at ht
            contradiction
          obtain ⟨g', hmem⟩ := List.exists_mem_of_ne_nil _ hn
          have hg' : g' ∈ gs ∧ w ∈ g'.inputs := by
            simpa only [List.mem_filter, List.contains_iff_mem] using hmem
          obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hg'.1
          refine ⟨⟨0, by simp⟩, ⟨j + 1, by simp; omega⟩, ?_, ?_, ?_⟩
          · intro eq
            have hv := congrArg Fin.val eq
            simp at hv
          · exact hg
          · simpa [List.get_eq_getElem, heq] using hg'.2
        · have ht : (gs.filter (fun g => g.inputs.contains w)).length = 2 := by
            simpa [List.filter_cons, hg] using hl
          obtain ⟨p, q, hpq, hp, hq⟩ := ih ht
          refine ⟨⟨p.val + 1, by simp⟩,
            ⟨q.val + 1, by simp⟩, ?_, ?_, ?_⟩
          · intro eq
            apply hpq
            apply Fin.ext
            have hv := congrArg Fin.val eq
            change p.val + 1 = q.val + 1 at hv
            omega
          · simpa [List.get_eq_getElem] using hp
          · simpa [List.get_eq_getElem] using hq
    change ∃ p q : Fin C.gates.length, p ≠ q ∧
      w ∈ (C.gates.get p).inputs ∧ w ∈ (C.gates.get q).inputs
    exact aux C.gates h

  have attach (w : Fin n) (s : ℕ) (f : (Fin n → Bool) → Bool)
      (small : HasCircuitSize n f s) :
      HasCircuitSize n (fun x => x w || f x) (s+1) := by
    obtain ⟨D, hf, hs, heval⟩ := small
    let step (v : List Bool) (g : Gate) :=
      v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]
    let run (gs : List Gate) (v : List Bool) := gs.foldl step v
    have lengthRun (gs : List Gate) (v : List Bool) :
        (run gs v).length = v.length + gs.length := by
      induction gs generalizing v with
      | nil => simp [run]
      | cons g gs ih =>
        change (run gs (step v g)).length = _
        rw [ih]
        simp [step]
        omega
    have inputRun (gs : List Gate) (v : List Bool) (j : ℕ) (hj : j < v.length) :
        (run gs v).getD j false = v.getD j false := by
      induction gs generalizing v with
      | nil => rfl
      | cons g gs ih =>
        change (run gs (step v g)).getD j false = _
        rw [ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hj
    let g : Gate := ⟨GateOp.or, [w.val, D.output]⟩
    let E : Circuit := ⟨D.gates ++ [g], n + D.gates.length⟩
    refine ⟨E, ?_, ?_, ?_⟩
    · intro a ha
      change a ∈ D.gates ++ [g] at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hf a ha
      · simp only [List.mem_singleton] at ha
        subst a
        change GateOp.or ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          [w.val, D.output].length ≤ 2
        simp
    · change (D.gates ++ [g]).length ≤ s + 1
      change D.gates.length ≤ s at hs
      simp only [List.length_append, List.length_singleton]
      omega
    · intro x
      have hv : (run D.gates (List.ofFn x)).length = n + D.gates.length := by
        rw [lengthRun]
        simp only [List.length_ofFn]
      have input : (run D.gates (List.ofFn x)).getD w.val false = x w := by
        rw [inputRun _ _ _ (by simp)]
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      have out : (run D.gates (List.ofFn x)).getD D.output false = f x := heval x
      change (run (D.gates ++ [g]) (List.ofFn x)).getD (n + D.gates.length) false = _
      change ((D.gates ++ [g]).foldl step (List.ofFn x)).getD (n + D.gates.length) false = _
      rw [List.foldl_append]
      change (run [g] (run D.gates (List.ofFn x))).getD (n + D.gates.length) false = _
      change ((run D.gates (List.ofFn x)) ++
        [GateOp.or.eval [ (run D.gates (List.ofFn x)).getD w.val false,
          (run D.gates (List.ofFn x)).getD D.output false ]]).getD
          (n + D.gates.length) false = _
      rw [← hv, List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self, List.getD_cons_zero, input, out]
      change (x w || (f x || false)) = (x w || f x)
      rw [Bool.or_false]

  by_contra noSaving
  have blocked (v : Fin n) (hv : v ∉ A) : ¬ ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n
      (fun x => circuitFun n C (Function.update x v false)) s := by
    intro h
    rw [computes] at h
    exact noSaving ⟨v,hv,h⟩
  have varies (v : Fin n) : ∃ x y : Fin n → Bool,
      circuitFun n C (Function.update x v false) ≠ circuitFun n C (Function.update y v false) := by
    rw [computes]
    exact nonconstant v
  have positive (v : Fin n) (hv : v ∉ A) : ∃ g ∈ readers v, g.op = GateOp.or := by
    by_contra hasOr
    obtain ⟨lower,upper,three⟩ := counts v hv
    have two : (readers v).length = 2 := by
      by_contra notTwo
      have nThree : (readers v).length = 3 := by omega
      obtain ⟨g,member⟩ := List.exists_mem_of_ne_nil (readers v) (by intro e; simp [e] at nThree)
      exact hasOr ⟨g,member,three nThree g member⟩
    obtain ⟨p,q,distinct,hp,hq⟩ := twoPositions C v.val two
    have absorbs (r : Fin C.size) (pin : v.val ∈ (C.gates.get r).inputs) :
        (C.gates.get r).op = .and ∨ (C.gates.get r).op = .not := by
      have memberC : C.gates.get r ∈ C.gates := List.get_mem ..
      have reads : C.gates.get r ∈ readers v :=
        List.mem_filter.mpr ⟨memberC, List.contains_iff_mem.mpr pin⟩
      have basis := (minimal.1 _ memberC).1
      change (C.gates.get r).op = .and ∨ (C.gates.get r).op = .or ∨ (C.gates.get r).op = .not at basis
      rcases basis with h | h | h
      · exact Or.inl h
      · exact (hasOr ⟨_,reads,h⟩).elim
      · exact Or.inr h
    exact blocked v hv (absorbing n C v p q minimal back arity (varies v) distinct hp hq
      (absorbs p hp) (absorbs q hq))
  have single (v : Fin n) (hv : v ∉ A) (j : ℕ) (hj : j < C.size)
      (op : (gateAt C j).op = GateOp.not) (pin : v.val ∈ (gateAt C j).inputs) :
      ∃ h : Gate, C.gates.filter (fun g => g.inputs.contains (n+j)) = [h] ∧ h.op = GateOp.and := by
    have memberC : gateAt C j ∈ C.gates := by
      have eq : gateAt C j = C.gates[j] := List.getD_eq_getElem C.gates _ hj
      rw [eq]
      exact List.getElem_mem hj
    have mem : gateAt C j ∈ readers v :=
      List.mem_filter.mpr ⟨memberC, List.contains_iff_mem.mpr pin⟩
    obtain ⟨lower,upper,three⟩ := counts v hv
    have two : (readers v).length = 2 := by
      by_contra notTwo
      have nThree : (readers v).length = 3 := by omega
      have impossible := three nThree _ mem
      rw [op] at impossible
      contradiction
    by_contra notSingle
    exact blocked v hv (propagate n C v j minimal back arity (varies v) two (positive v hv)
      hj op pin notSingle)
  obtain ⟨v,hv,_,g,member,op⟩ := hasNot
  exact noSaving (core n G A C degree girth unmarked edge minimal computes back arity counts
    positive (fun u hu j hj hnot pin => by
      obtain ⟨h,only,hand⟩ := single u hu j hj hnot pin
      refine ⟨h,only,hand,?_⟩
      intro i hi
      by_contra! primary
      let w : Fin n := ⟨i,primary⟩
      obtain ⟨s,two,four,small⟩ := coinput n C w j h minimal back arity (varies w)
        hj hnot only hand hi
      by_cases marked : w ∈ A
      · rw [computes] at small
        have full := attach w s _ small
        rw [markedOr w marked] at full
        obtain ⟨D,basis,size,eval⟩ := full
        have same : circuitFun n D = circuitFun n C := by
          rw [computes]
          exact funext eval
        have least := minimal.2 D basis same
        omega
      · exact blocked w marked ⟨s,four (positive w marked),small⟩) ⟨v,hv,g,member,op⟩)
