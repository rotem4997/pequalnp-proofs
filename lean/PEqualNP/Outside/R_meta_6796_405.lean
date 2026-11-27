import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_6796_405
  (coordinate : ∀ (C : Circuit) (A : List ℕ) (k t : ℕ),
    (∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) →
    ((C.gates.foldl (fun (w : List ℕ) (g : Gate) =>
        let a := w.getD (g.inputs.getD 0 0) 0
        let b := w.getD (g.inputs.getD 1 0) 0
        w ++ [if g.op.eval [false,true] then a ||| b else a &&& b]) A).getD k 0).testBit t =
    (C.wires (A.map fun a => a.testBit t)).getD k false)
  (packed : ∃ (C : Circuit) (T : List (ℕ × ℕ)),
    let W := C.gates.foldl (fun (w : List ℕ) (g : Gate) =>
        let a := w.getD (g.inputs.getD 0 0) 0
        let b := w.getD (g.inputs.getD 1 0) 0
        w ++ [if g.op.eval [false,true] then a ||| b else a &&& b]) ([2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146] : List ℕ)
    let val := fun i => W.getD i 0
    TopForm.IsAO2 11 C ∧ T ≠ [] ∧ C.size + 2*T.length ≤ 22 ∧ 3 ≤ ReadTwo.nAnd C ∧
    (∀ e ∈ T, e.1 < 11+C.size ∧ e.2 < 11+C.size) ∧
    (∀ j < C.size, (∃ p : Fin 16, (val (11+j)).testBit p = true) ∧
       ∃ q : Fin 24, (val (11+j)).testBit (16+q.val) = true) ∧
    (∀ j < C.size, ReadTwo.isAnd C j → ∃ e ∈ T, ∃ w ∈ [e.1,e.2],
      w = 11+j ∨ 11 ≤ w ∧ EdgeOwnership.InCone 11 C j (w-11)) ∧
    (T.foldl (fun acc e => acc ||| (val e.1 &&& val e.2)) 0) = 65535) : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (ℕ × ℕ)),   have x3 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)];   have x4 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)];   have x5 : ℕ → ℕ → Bool := fun (x5 x6 : ℕ) => PEqualNP.BlindGate.wireValue x1 (11 : ℕ) (fun (x7 : Fin (11 : ℕ)) => x5.testBit ↑x7) x6;   PEqualNP.TopForm.IsAO2 (11 : ℕ) x1 ∧ x2 ≠ [] ∧ x1.size + (2 : ℕ) * x2.length ≤ (22 : ℕ) ∧ (3 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x1 ∧ (∀ x6 ∈ x2, x6.1 < (11 : ℕ) + x1.size ∧ x6.2 < (11 : ℕ) + x1.size) ∧ (∀ x6 < x1.size, (x3.any fun (x8 : ℕ) => x5 x8 ((11 : ℕ) + x6)) = Bool.true ∧ (x4.any fun (x8 : ℕ) => x5 x8 ((11 : ℕ) + x6)) = Bool.true) ∧ (∀ x6 < x1.size, PEqualNP.ReadTwo.isAnd x1 x6 → ∃ x9 ∈ x2, ∃ x10 ∈ [x9.1, x9.2], x10 = (11 : ℕ) + x6 ∨ (11 : ℕ) ≤ x10 ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x1 x6 (x10 - (11 : ℕ))) ∧ ∀ x6 ∈ x3 ++ x4, (x2.any fun (x8 : ℕ × ℕ) => x5 x6 x8.1 && x5 x6 x8.2) = Decidable.decide (x6 ∈ x3) := by
  obtain ⟨C,T,wf,ne,budget,na,valid,live,cone,total⟩ := packed
  let P : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
  let N : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
  let A : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
  let step := (fun (w : List ℕ) (g : Gate) =>
        let a := w.getD (g.inputs.getD 0 0) 0
        let b := w.getD (g.inputs.getD 1 0) 0
        w ++ [if g.op.eval [false,true] then a ||| b else a &&& b])
  let W := C.gates.foldl step A
  let V := fun i => W.getD i 0
  let row := fun r (i : Fin 11) => Nat.testBit r i.val
  have form : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨wf.1 g hg,wf.2.2 g hg⟩
  have encP : ∀ i : Fin 16, A.map (fun a => a.testBit i) = List.ofFn (row (P.getD i 0)) := by decide +kernel
  have encN : ∀ i : Fin 24, A.map (fun a => a.testBit (16+i.val)) = List.ofFn (row (N.getD i 0)) := by decide +kernel
  have VP (i : Fin 16) (k : ℕ) : (V k).testBit i = BlindGate.wireValue C 11 (row (P.getD i 0)) k := by
    exact (coordinate C A k i form).trans (by rw [encP];rfl)
  have VN (i : Fin 24) (k : ℕ) : (V k).testBit (16+i.val) = BlindGate.wireValue C 11 (row (N.getD i 0)) k := by
    exact (coordinate C A k (16+i.val) form).trans (by rw [encN];rfl)
  have bits (L : List (ℕ × ℕ)) (acc t : ℕ) :
      (L.foldl (fun q e => q ||| (V e.1 &&& V e.2)) acc).testBit t =
        (acc.testBit t || L.any fun e => (V e.1).testBit t && (V e.2).testBit t) := by
    induction L generalizing acc with
    | nil => simp
    | cons e es ih => simp only [List.foldl_cons,ih,Nat.testBit_or,Nat.testBit_and,List.any_cons,Bool.or_assoc]
  have quant (t : ℕ) : (T.any fun e => (V e.1).testBit t && (V e.2).testBit t) = (65535 : ℕ).testBit t := by
    have h := bits T 0 t
    change T.foldl (fun q e => q ||| (V e.1 &&& V e.2)) 0 = 65535 at total
    rw [total] at h; simpa using h.symm
  have hp : ∀ i : Fin 16, P.getD i 0 ∈ P ∧ (65535 : ℕ).testBit i = true := by decide +kernel
  have hn : ∀ i : Fin 24, N.getD i 0 ∈ N ∧ N.getD i 0 ∉ P ∧ (65535 : ℕ).testBit (16+i.val) = false := by decide +kernel
  refine ⟨C,T,wf,ne,budget,na,valid,?_,cone,?_⟩
  · intro j hj
    obtain ⟨⟨i,hi⟩,q,hq⟩ := live j hj
    exact ⟨List.any_eq_true.mpr ⟨P.getD i 0,(hp i).1,(VP i _).symm.trans hi⟩,
      List.any_eq_true.mpr ⟨N.getD q 0,(hn q).1,(VN q _).symm.trans hq⟩⟩
  · intro r hr
    change r ∈ P ++ N at hr
    change (T.any fun e => BlindGate.wireValue C 11 (row r) e.1 && BlindGate.wireValue C 11 (row r) e.2) = decide (r ∈ P)
    rcases List.mem_append.mp hr with h | h
    · obtain ⟨i,hi⟩ := List.get_of_mem h
      let ix : Fin 16 := ⟨i.val,by simpa [P] using i.isLt⟩
      have eq : P.getD ix 0 = r := by simpa [ix,List.getD_eq_getElem?_getD,i.isLt] using hi
      have ok := (quant ix).trans (hp ix).2
      simp_rw [VP ix] at ok
      rw [eq] at ok
      rw [decide_eq_true h]; exact ok
    · obtain ⟨i,hi⟩ := List.get_of_mem h
      let ix : Fin 24 := ⟨i.val,by simpa [N] using i.isLt⟩
      have eq : N.getD ix 0 = r := by simpa [ix,List.getD_eq_getElem?_getD,i.isLt] using hi
      have ok := (quant (16+ix.val)).trans (hn ix).2.2
      simp_rw [VN ix] at ok
      rw [eq] at ok
      have notP : r ∉ P := eq ▸ (hn ix).2.1
      rw [decide_eq_false notP]; exact ok
