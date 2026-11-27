import PEqualNP.Defs

open PEqualNP PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.PairShadow

-- The cover estimate and construction are the statements of L_meta_4767 and L_meta_4320.
-- The remaining exchange only concerns a circuit with both obstructions.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5284_263
    (coverEstimate : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∨ (∀ a b c d : Fin n, G.Adj a b → G.Adj c d → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun k => decide (k = a ∨ k = b)))).getD (n + (i : ℕ)) false = true → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun k => decide (k = c ∨ k = d)))).getD (n + (i : ℕ)) false = true → (a = c ∧ b = d) ∨ (a = d ∧ b = c))) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1)
    (coverBuilder : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (U : Finset (Fin n)), (∀ a b, G.Adj a b → a ∈ U ∨ b ∈ U) →
        ∃ D : Circuit, Monotone2 D ∧
          (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
            decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) ∧
          D.size ≤ G.edgeFinset.card + U.card - 1 ∧
          ∀ j g, D.gates[j]? = some g → g.op = GateOp.and →
            ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true →
              ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
    (exchange : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → PEqualNP.TopForm.NoFourCycle G →
      let silent (D : Circuit) := ∀ j g, D.gates[j]? = some g → g.op = GateOp.and →
        ∀ S : Finset (Fin n), S.card ≤ 1 → gateVal n D j (fun i => decide (i ∈ S)) = false
      let cost (D : Circuit) := ((PEqualNP.TopForm.junk G D).filter
        fun j => 1 < (PEqualNP.TopForm.gammaE G D j).card).card
      ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ → silent C → 0 < cost C →
        (∃ j a b, (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs = [a,b] ∧
          ∃ u v : Fin n, ¬G.Adj u v ∧ readVal n C j a (unitInput u) = true ∧
            readVal n C j b (unitInput v) = true) →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = circuitFun n C ∧ silent D ∧
          D.size ≤ C.size ∧ cost D < cost C) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x1 → Bool), x9.eval (List.ofFn x11) = x4 x11) → x6 x9 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ x13.size ≤ x9.size ∧ (∀ (x14 x15 : Fin x1), x2.Adj x14 x15 → x13.eval (List.ofFn (x5 {x14, x15})) = Bool.true) ∧ (∀ (x14 : Fin x1), x13.eval (List.ofFn (x5 {x14})) = Bool.false) ∧ ∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x13.gates[x14]? = Option.some x15 → x15.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x18 : Finset (Fin x1)), x18.card ≤ (2 : ℕ) → (x13.wires (List.ofFn (x5 x18))).getD (x1 + x14) Bool.false = Bool.true → ∃ x21 ∈ x18, ∃ x22 ∈ x18, x2.Adj x21 x22 := by
  classical
  have coverCase
      (coverBuilder : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
          (U : Finset (Fin n)), (∀ a b, G.Adj a b → a ∈ U ∨ b ∈ U) →
          ∃ D : Circuit, Monotone2 D ∧
            (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
              decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) ∧
            D.size ≤ G.edgeFinset.card + U.card - 1 ∧
            ∀ j g, D.gates[j]? = some g → g.op = GateOp.and →
              ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true →
                ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
      (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (U : Finset (Fin n)) (hU : ∀ a b, G.Adj a b → a ∈ U ∨ b ∈ U)
      (hBudget : G.edgeFinset.card + U.card - 1 ≤ C.size) :
      let on := fun (S : Finset (Fin n)) (v : Fin n) => decide (v ∈ S)
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧
        (∀ u v, G.Adj u v → D.eval (List.ofFn (on {u, v})) = true) ∧
        (∀ u : Fin n, D.eval (List.ofFn (on {u})) = false) ∧
        ∀ j g, D.gates[j]? = some g → g.op = GateOp.and →
          ∀ S : Finset (Fin n), S.card ≤ 2 →
            (D.wires (List.ofFn (on S))).getD (n+j) false = true →
              ∃ u ∈ S, ∃ v ∈ S, G.Adj u v := by
    classical
    intro on
    obtain ⟨D, hMonoD, hEvalD, hCostD, hCleanD⟩ := coverBuilder n G U hU
    refine ⟨D, hMonoD, hCostD.trans hBudget, ?_, ?_, ?_⟩
    · intro u v huv
      rw [hEvalD, decide_eq_true_eq]
      exact ⟨u, v, huv, by simp [on], by simp [on]⟩
    · intro u
      rw [hEvalD, decide_eq_false_iff_not]
      rintro ⟨a, b, hab, ha, hb⟩
      have hau : a = u := by simpa [on] using ha
      have hbu : b = u := by simpa [on] using hb
      exact G.loopless.irrefl u (by simpa only [hau, hbu] using hab)
    · intro j g hj hop S _ hActive
      obtain ⟨u, v, huv, hu, hv⟩ := hCleanD j g hj hop (on S) hActive
      exact ⟨u, by simpa [on] using hu, v, by simpa [on] using hv, huv⟩
  have rectSound (n : ℕ) (G : SimpleGraph (Fin n)) (D : Circuit) (M : Monotone2 D)
      (clean : ∀ j g, D.gates[j]? = some g → g.op = .and → ∀ S : Finset (Fin n),
        S.card ≤ 1 → EdgeOwnership.gateVal n D j (fun i => decide (i ∈ S)) = false)
      (rect : ∀ j g a b, D.gates[j]? = some g → g.op = .and → g.inputs = [a,b] →
        a < n+j → b < n+j → ∀ p q : Fin n,
        CleanedNonEdge.wireVal n D a (PairShadow.unitInput p) = true →
        CleanedNonEdge.wireVal n D b (PairShadow.unitInput q) = true → G.Adj p q) :
      ∀ j g, D.gates[j]? = some g → g.op = .and → ∀ S : Finset (Fin n), S.card ≤ 2 →
        EdgeOwnership.gateVal n D j (fun i => decide (i ∈ S)) = true →
        ∃ p ∈ S, ∃ q ∈ S, G.Adj p q := by
    classical
    -- The wire evaluation and OR argument follow R_meta_1904_493.
    have and_eval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
    have or_eval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let trace {n} (gs : List Gate) (x : Fin n → Bool) := gs.foldl step (List.ofFn x)
    let pin {n} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) := (trace gs x).getD i false
    let val {n} (gs : List Gate) (g : Gate) (x : Fin n → Bool) := g.op.eval (g.inputs.map (pin gs x))
    let hit {n} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) := ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true
    let mask {n} (S : Finset (Fin n)) (u : Fin n) := decide (u ∈ S)
    have tr_snoc {n} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
        trace (gs++[g]) x = trace gs x ++ [val gs g x] := by
      simp only [trace, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    have tr_len {n} (gs : List Gate) (x : Fin n → Bool) : (trace gs x).length = n + gs.length := by
      induction gs using List.reverseRecOn with
      | nil => simp [trace]
      | append_singleton l g ih => simp [tr_snoc,ih,Nat.add_assoc]
    have prefix_tail (w : List Bool) (rest : List Gate) : ∃ t, rest.foldl step w = w ++ t := by
      induction rest generalizing w with
      | nil => exact ⟨[],by simp⟩
      | cons g gs ih =>
        obtain ⟨t,e⟩ := ih (step w g)
        exact ⟨_ :: t, by simpa [List.foldl_cons,step,List.append_assoc] using e⟩
    have gate_value {n} (pre rest : List Gate) (g : Gate) (x : Fin n → Bool) :
        pin (pre ++ g::rest) x (n + pre.length) = val pre g x := by
      have e : trace (pre ++ g::rest) x = rest.foldl step (trace pre x ++ [val pre g x]) := by
        simp only [trace, List.foldl_append, List.foldl_cons]
        rfl
      obtain ⟨t,et⟩ := prefix_tail (trace pre x ++ [val pre g x]) rest
      dsimp only [pin]
      rw [e,et,List.append_assoc]
      have hl := tr_len pre x
      rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega),← hl,Nat.sub_self]
      rfl
    let roots {n} (gs : List Gate) (x : Fin n → Bool) : Prop := ∀ k, pin gs x k = true →
        ∃ u, x u = true ∧ ∀ z : Fin n → Bool, z u = true → pin gs z k = true
    have reject {x : Fin n → Bool} (bad : ¬hit G x)
        {pre rest : List Gate} {g : Gate} (split : D.gates = pre ++ g :: rest) (hg : g.op = .and)
        (prior : roots pre x) : val pre g x ≠ true := by
      intro lit
      have member : g ∈ D.gates := by simp [split]
      have atGate : D.gates[pre.length]? = some g := by simp [split]
      have ht : ∀ i ∈ g.inputs, pin pre x i = true := by simpa [val,hg,and_eval,or_eval] using lit
      by_cases short : g.inputs.length ≤ 1
      · have each (i : {k // k ∈ g.inputs}) := prior i (ht i i.property)
        choose u on force using each
        let S := (g.inputs.attach.map u).toFinset
        have size : S.card ≤ 1 := (List.toFinset_card_le _).trans (by simpa using short)
        have still : ∀ k ∈ g.inputs, pin pre (mask S) k = true := by
          intro k hk
          let q : {i // i ∈ g.inputs} := ⟨k,hk⟩
          apply force q
          exact decide_eq_true (List.mem_toFinset.mpr (List.mem_map.mpr ⟨q,List.mem_attach _ _,rfl⟩))
        have off := clean pre.length g atGate hg S size
        change pin D.gates (mask S) (n+pre.length) = false at off
        rw [split,gate_value] at off
        have on : val pre g (mask S) = true := by simpa [val,hg,and_eval,or_eval] using still
        rw [on] at off
        contradiction
      have two := (M g member).2
      obtain ⟨a,b,ab⟩ : ∃ a b, g.inputs = [a,b] := by
        rcases hi : g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩
        · simp [hi] at short
        · simp [hi] at short
        · exact ⟨a,b,rfl⟩
        · simp [hi] at two
      have wa := ht a (by simp [ab])
      have wb := ht b (by simp [ab])
      have bound (k : ℕ) (hk : pin pre x k = true) : k < n+pre.length := by
        by_contra! hn
        have hlen : (trace pre x).length ≤ k := by simpa [tr_len] using hn
        simp [pin,List.getD_eq_getElem?_getD,List.getElem?_eq_none hlen] at hk
      have keep (z : Fin n → Bool) (k : ℕ) (hk : k < n+pre.length) :
          CleanedNonEdge.wireVal n D k z = pin pre z k := by
        change pin D.gates z k = pin pre z k
        rw [split]
        have e : trace (pre ++ g :: rest) z = (g :: rest).foldl step (trace pre z) := by
          simp [trace,List.foldl_append]
        obtain ⟨t,et⟩ := prefix_tail (trace pre z) (g :: rest)
        dsimp only [pin]
        rw [e,et]
        exact List.getD_append _ _ _ _ (by simpa [tr_len] using hk)
      obtain ⟨p,hp,fp⟩ := prior a wa
      obtain ⟨q,hq,fq⟩ := prior b wb
      apply bad
      refine ⟨p,q,rect pre.length g a b atGate hg ab (bound a wa) (bound b wb) p q ?_ ?_,hp,hq⟩
      · rw [keep _ _ (bound a wa)]
        exact fp _ (decide_eq_true (rfl : p = p))
      · rw [keep _ _ (bound b wb)]
        exact fq _ (decide_eq_true (rfl : q = q))
    have provenance {x : Fin n → Bool} (bad : ¬hit G x) (pre : List Gate) :
        (∃ rest, D.gates = pre ++ rest) → roots pre x := by
      induction pre using List.reverseRecOn with
      | nil =>
        intro _ k hk
        by_cases h : k < n
        · refine ⟨⟨k,h⟩,by simpa [pin,trace,List.getD,List.getElem?_ofFn,h] using hk,?_⟩
          intro z htrue
          simpa [pin,trace,List.getD,List.getElem?_ofFn,h] using htrue
        · simp [pin,trace,List.getD,h] at hk
      | append_singleton pre g ih =>
        rintro ⟨rest,split⟩
        have total : D.gates = pre ++ g :: rest := by simpa [List.append_assoc] using split
        have prior := ih ⟨_,total⟩
        have member : g ∈ D.gates := by simp [total]
        intro k hk
        by_cases old : k < n+pre.length
        · have keep (y : Fin n → Bool) : pin (pre++[g]) y k = pin pre y k := by
            simp only [pin,tr_snoc]
            exact List.getD_append _ _ _ _ (by rwa [tr_len])
          rw [keep] at hk
          obtain ⟨u,hu,hu'⟩ := prior k hk
          exact ⟨u,hu,fun z hz => (keep z).trans (hu' z hz)⟩
        · have access (y : Fin n → Bool) : pin (pre++[g]) y k = [val pre g y].getD (k-(n+pre.length)) false := by
            dsimp only [pin]
            rw [tr_snoc,List.getD_eq_getElem?_getD,List.getElem?_append_right (by rw [tr_len]; omega),tr_len]
            rfl
          rw [access] at hk
          cases e : k-(n+pre.length) with
          | zero =>
            rw [e] at hk
            change val pre g x = true at hk
            have shape : g.op = .and ∨ g.op = .or := by simpa using (M g member).1
            rcases shape with ha|ho
            · exact False.elim (reject bad total ha prior hk)
            · have many : ∃ i ∈ g.inputs, pin pre x i = true := by simpa [val,ho,and_eval,or_eval] using hk
              obtain ⟨i,hi,uses⟩ := many
              obtain ⟨u,hu,fu⟩ := prior i uses
              refine ⟨u,hu,?_⟩
              intro z hz
              rw [access,e]
              change val pre g z = true
              simpa [val,ho,and_eval,or_eval] using (show ∃ j ∈ g.inputs, pin pre z j = true from ⟨i,hi,fu z hz⟩)
          | succ d => simp [e,List.getD] at hk
    intro j g entry and S _ lit
    by_contra noEdge
    have bad : ¬hit G (mask S) := by
      rintro ⟨a,b,adj,ha,hb⟩
      exact noEdge ⟨a,of_decide_eq_true ha,b,of_decide_eq_true hb,adj⟩
    obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp entry
    let pre := D.gates.take j
    let rest := D.gates.drop (j+1)
    have split : D.gates = pre ++ g :: rest := by
      rw [← hg]
      exact (List.take_append_drop j D.gates).symm.trans (by rw [List.drop_eq_getElem_cons hj])
    have plen : pre.length = j := by simp [pre,Nat.min_eq_left (Nat.le_of_lt hj)]
    have prior := provenance bad pre ⟨_,split⟩
    apply reject bad split and prior
    change pin D.gates (mask S) (n+j) = true at lit
    rwa [← gate_value pre rest g (mask S),← split,plen]
  have noWide (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
      let cost (D : Circuit) := ((junk G D).filter fun j => 1 < (gammaE G D j).card).card
      cost C = 0 →
      ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.and →
        (∀ x : Fin n → Bool, (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true →
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∨
        (∀ a b c d : Fin n, G.Adj a b → G.Adj c d →
          (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn (fun k => decide (k = a ∨ k = b)))).getD (n + (i : ℕ)) false = true →
          (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn (fun k => decide (k = c ∨ k = d)))).getD (n + (i : ℕ)) false = true →
          (a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
    classical
    intro cost zero i hand
    have realOp : (gateAt C i.val).op = GateOp.and := by
      change (C.gates.getD i.val _).op = GateOp.and
      change C.gates[i.val].op = GateOp.and at hand
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt, Option.getD_some] using hand
    by_cases dirty : IsDirtyAnd n G C i.val
    · right
      have ij : i.val ∈ junk G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, dirty⟩
      have small : (gammaE G C i.val).card ≤ 1 := by
        apply Nat.le_of_not_gt
        intro wide
        have hi : i.val ∈ ((junk G C).filter fun j => 1 < (gammaE G C j).card) := Finset.mem_filter.mpr ⟨ij, wide⟩
        have pos : 0 < cost C := Finset.card_pos.mpr ⟨_, hi⟩
        exact (Nat.ne_of_gt pos) zero
      have active {u v : Fin n} (edge : G.Adj u v) (on : gateVal n C i.val (pairInput u v) = true) :
          s(u,v) ∈ gammaE G C i.val :=
        Finset.mem_filter.mpr ⟨G.mem_edgeFinset.mpr edge, u, v, rfl, on⟩
      intro a b c d hab hcd onAB onCD
      exact Sym2.eq_iff.mp (Finset.card_le_one.mp small _ (active hab onAB) _ (active hcd onCD))
    · left
      intro x hx
      by_contra none
      apply dirty
      refine ⟨realOp, i.isLt, x, hx, ?_⟩
      delta graphFun
      simp [none]
  intro n G inst f on one htri hsquare B hBm hBf hBone
  have regular : PEqualNP.TopForm.NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hap, hbp⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨haq, hbq⟩ := (Finset.mem_filter.mp hq).2
    exact (hsquare a p b q hap hbp.symm hbq haq.symm).resolve_left hab
  let cost (D : Circuit) := ((PEqualNP.TopForm.junk G D).filter
    fun j => 1 < (PEqualNP.TopForm.gammaE G D j).card).card
  have gf (x : Fin n → Bool) : graphFun G ∅ x = f x := by
    change (decide (∃ i ∈ (∅ : Finset (Fin n)), x i = true) ||
      decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) = _
    simp [f]
  have hbase : circuitFun n B = graphFun G ∅ := funext fun x => (hBf x).trans (gf x).symm
  let eligible (k : ℕ) := ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
    one D ∧ D.size ≤ B.size ∧ cost D = k
  have hex : ∃ k, eligible k := ⟨_, B, hBm, hbase, hBone, Nat.le_refl _, rfl⟩
  obtain ⟨C, hmon, hfun, hsil, hsize, hcost⟩ := Nat.find_spec hex
  have evalC (x : Fin n → Bool) : C.eval (List.ofFn x) = f x :=
    (congrFun hfun x).trans (gf x)
  by_cases zero : cost C = 0
  · have ops (g : Gate) (hg : g ∈ C.gates) :
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      exact hmon g hg
    have sq : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
      rintro a b c d hac hbd ⟨e1,e2,e3,e4⟩
      exact (hsquare a b c d e1 e2 e3 e4).elim hac hbd
    obtain ⟨U, hU, hbudget⟩ := coverEstimate n G sq C.gates C.output ops evalC
      (noWide n G C zero)
    have room : G.edgeFinset.card + U.card - 1 ≤ B.size := by
      change G.edgeFinset.card + U.card ≤ C.size + 1 at hbudget
      exact (Nat.sub_le_of_le_add hbudget).trans hsize
    exact coverCase coverBuilder n G B U hU room
  · have rectangle (j : ℕ) (g : Gate) (a b : ℕ) (hj : C.gates[j]? = some g)
        (hop : g.op = GateOp.and) (hin : g.inputs = [a,b]) (ha : a < n+j) (hb : b < n+j)
        (u v : Fin n) (hu : wireVal n C a (unitInput u) = true)
        (hv : wireVal n C b (unitInput v) = true) : G.Adj u v := by
      by_contra hnon
      have gate : gateAt C j = g := by
        change C.gates.getD j _ = g
        simp only [List.getD_eq_getElem?_getD, hj, Option.getD_some]
      have ra : readVal n C j a (unitInput u) = true := by
        change (if a < n+j then _ else false) = true
        simpa only [ha, ↓reduceIte] using hu
      have rb : readVal n C j b (unitInput v) = true := by
        change (if b < n+j then _ else false) = true
        simpa only [hb, ↓reduceIte] using hv
      obtain ⟨D, hDm, hDf, hDs, hlen, hdrop⟩ :=
        exchange n G htri regular C hmon hfun hsil (Nat.pos_of_ne_zero zero)
          ⟨j, a, b, gate ▸ hop, gate ▸ hin, u, v, hnon, ra, rb⟩
      have least := Nat.find_min' hex (show eligible (cost D) from
        ⟨D, hDm, hDf.trans hfun, hDs, hlen.trans hsize, rfl⟩)
      change cost D < cost C at hdrop
      exact (Nat.not_lt_of_ge (hcost.trans_le least)) hdrop
    refine ⟨C, hmon, hsize, ?_, ?_, rectSound n G C hmon hsil rectangle⟩
    · intro u v huv
      rw [evalC]
      change decide (∃ a b, G.Adj a b ∧ on {u,v} a = true ∧ on {u,v} b = true) = true
      exact decide_eq_true ⟨u, v, huv, by simp [on], by simp [on]⟩
    · intro u
      rw [evalC]
      change decide (∃ a b, G.Adj a b ∧ on {u} a = true ∧ on {u} b = true) = false
      apply decide_eq_false_iff_not.mpr
      rintro ⟨a, b, hab, ha, hb⟩
      have hau : a = u := by simpa [on] using ha
      have hbu : b = u := by simpa [on] using hb
      exact G.loopless.irrefl u (by simpa only [hau, hbu] using hab)
