import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_8031_401
    (replay : ∀ (gs : List Gate) (xs : List Bool) (s : ℕ → Bool),
      (∀ i : Fin xs.length, xs.get i = s i.val) →
      (∀ i : Fin gs.length, (∀ w ∈ (gs.get i).inputs, w < xs.length+i.val) ∧
        (gs.get i).op.eval ((gs.get i).inputs.map s) = s (xs.length+i.val)) →
      ∀ i : Fin (xs.length+gs.length),
        (({gates := gs, output := 0} : Circuit).wires xs).getD i.val false = s i.val)
    (search : ∃ (k : Fin 22) (op : Fin ↑k → Bool) (a b : Fin ↑k → Fin 33)
        (w : Fin 33) (s : ℕ → ℕ) (d : Fin 3 → Fin ↑k) (q : Fin 3 → Fin 24),
      ↑w < (11 : ℕ)+↑k ∧ s ↑w = 65535 ∧
      (∀ i : Fin 11, s ↑i = ([2147418115,663661903884,34144976944,728266375360,
        21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,
        1065151898146] : List ℕ).getD ↑i 0) ∧
      (∀ i, ↑(a i) < (11 : ℕ)+↑i ∧ ↑(b i) < (11 : ℕ)+↑i ∧ s (11+↑i) =
        if op i = true then s ↑(a i) &&& s ↑(b i) else s ↑(a i) ||| s ↑(b i)) ∧
      Function.Injective d ∧ ∀ i, op (d i) = true ∧
        (s (11+↑(d i))).testBit (16+↑(q i)) = true) :
    have x1 : List (Fin (11 : ℕ) × Fin (11 : ℕ)) := [((0 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((0 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))), ((3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), ((4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((4 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((5 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((5 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((7 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)))]; have x2 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; ∃ (x3 : Fin (22 : ℕ)) (x4 : Fin ↑x3 → Bool) (x5 : Fin ↑x3 → Option (Fin (33 : ℕ)) × Option (Fin (33 : ℕ))) (x6 : Fin (33 : ℕ)),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.ofFn fun (x7 : Fin ↑x3) => { op := if x4 x7 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := List.map Fin.val ((x5 x7).1.toList ++ (x5 x7).2.toList) : PEqualNP.CircuitLowerBounds.Gate }, output := ↑x6 : PEqualNP.CircuitLowerBounds.Circuit };   (∀ x8 ∈ x1, x7.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput x8.1 x8.2)) = Bool.true) ∧ (∀ x8 ∈ x2, x7.eval (List.ofFn fun (x10 : Fin (11 : ℕ)) => x8.testBit ↑x10) = Bool.false) ∧ (3 : ℕ) ≤ (PEqualNP.TopForm.junk (PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x8 : Fin (11 : ℕ) × Fin (11 : ℕ)) => (↑x8.1, ↑x8.2)) x1)) x7).card := by
  let E : List (Fin 11 × Fin 11) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let Q : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,
    582,596,1066,1186,1288,1408,1546]
  let T : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768] ++ Q
  let col : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,
    103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
  let row (u : Fin 40) (i : Fin 11) := T[u.val]!.testBit i.val
  let graph := edgeGraph 11 (E.map fun e => (e.1.val,e.2.val))
  have tab : ∀ (u : Fin 40) (i : Fin 11), row u i = (col.getD i.val 0).testBit u.val := by decide
  have pos : ∀ (e : Fin 11 × Fin 11), e ∈ E → ∃ u : Fin 40,
      (65535 : ℕ).testBit u.val = true ∧ ∀ i, row u i = pairInput e.1 e.2 i := by
    decide +kernel
  have neg : ∀ m ∈ Q, ∃ u : Fin 40, (65535 : ℕ).testBit u.val = false ∧
      ∀ i : Fin 11, row u i = m.testBit i.val := by decide
  have indep : ∀ z : Fin 24, graphFun graph ∅ (row ⟨16+z.val,Nat.add_lt_add_left z.isLt 16⟩) = false := by
    decide +kernel
  obtain ⟨k,op,a,b,w,s,d,q,hw,hout,hinput,hgate,hd,hq⟩ := search
  let g (i : Fin k.val) : Gate := ⟨if op i then .and else .or, [(a i).val,(b i).val]⟩
  let C : Circuit := ⟨List.ofFn g, w.val⟩
  have gate_spec (i : Fin k.val) : C.gates[i.val]'(by simp [C]) = g i := by simp [C]
  have sim (u : Fin 40) (v : ℕ) (hv : v < 11+k.val) :
      (C.wires (List.ofFn (row u))).getD v false = (s v).testBit u.val := by
    let xs := List.ofFn (row u)
    let bit (n : ℕ) := (s n).testBit u.val
    have first (i : Fin xs.length) : xs[i.val] = bit i.val := by
      have hi : i.val < 11 := by simpa [xs] using i.isLt
      let h : Fin 11 := ⟨i.val,hi⟩
      have eqs : s h.val = col.getD h.val 0 := hinput h
      have firstWire : xs[i.val]'i.isLt = row u h := List.getElem_ofFn i.isLt
      exact firstWire.trans ((tab u h).trans (congrArg (fun l : ℕ => l.testBit u.val) eqs.symm))
    have step (i : Fin C.gates.length) :
        (∀ p ∈ C.gates[i.val].inputs, p < xs.length+i.val) ∧
        C.gates[i.val].op.eval (C.gates[i.val].inputs.map bit) = bit (xs.length+i.val) := by
      have hi : i.val < k.val := by simpa [C] using i.isLt
      let j : Fin k.val := ⟨i.val,hi⟩
      rw [show C.gates[i.val] = g j from gate_spec j]
      obtain ⟨la,lb,rule⟩ := hgate j
      constructor
      · intro p hp
        rcases (show p = (a j).val ∨ p = (b j).val by simpa [g] using hp) with rfl | rfl
        · simpa [xs,j] using la
        · simpa [xs,j] using lb
      · change _ = (s (xs.length+i.val)).testBit u.val
        rw [show xs.length+i.val = 11+j.val by simp [xs,j],rule]
        cases hh : op j
        · simp only [g,hh,Bool.false_eq_true,ite_false,Nat.testBit_or,List.map_cons,List.map_nil]
          change (bit (a j).val || (bit (b j).val || false)) = _
          simp only [Bool.or_false,bit]
        · simp only [g,hh,ite_true,Nat.testBit_and,List.map_cons,List.map_nil]
          change (bit (a j).val && (bit (b j).val && true)) = _
          simp only [Bool.and_true,bit]
    exact replay C.gates xs bit first step ⟨v, by simpa [C,xs] using hv⟩
  have outs (u : Fin 40) : C.eval (List.ofFn (row u)) = (65535 : ℕ).testBit u.val := by
    exact (sim u w.val hw).trans (congrArg (fun m : ℕ => m.testBit u.val) hout)
  refine ⟨k,op,(fun j => (some (a j),some (b j))),w,?_,?_,?_⟩
  · change ∀ e ∈ E, C.eval (List.ofFn (pairInput e.1 e.2)) = true
    intro e he
    obtain ⟨u,hu,heq⟩ := pos e he
    rw [← funext heq, outs,hu]
  · change ∀ m ∈ Q, C.eval (List.ofFn (fun i : Fin 11 => m.testBit i.val)) = false
    intro m hm
    obtain ⟨u,hu,heq⟩ := neg m hm
    rw [← funext heq, outs,hu]
  · change 3 ≤ (junk graph C).card
    have hit (i : Fin 3) : (d i).val ∈ junk graph C := by
      let u : Fin 40 := ⟨16+(q i).val,by omega⟩
      have hi : (d i).val < C.gates.length := by simp [C]
      have andGate : (gateAt C (d i).val).op = .and := by
        change (C.gates.getD (d i).val _).op = GateOp.and
        rw [List.getD_eq_getElem _ _ hi,gate_spec]
        change (if op (d i) then GateOp.and else GateOp.or) = GateOp.and
        rw [(hq i).1]
        rfl
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,andGate,hi,row u,
        (sim u (11+(d i).val) (by omega)).trans (hq i).2,indep (q i)⟩
    let f (i : Fin 3) : ↥(junk graph C) := ⟨(d i).val,hit i⟩
    have hf : Function.Injective f := fun _ _ h => hd (Fin.ext (congrArg Subtype.val h))
    calc
      3 = Fintype.card (Fin 3) := (Fintype.card_fin 3).symm
      _ ≤ Fintype.card ↥(junk graph C) := Fintype.card_le_of_injective f hf
      _ = (junk graph C).card := Fintype.card_coe _
