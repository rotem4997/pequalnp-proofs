import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_4873_731
    (maxrows : have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true; ∀ x : Fin 14 → Bool, Maximal (fun y => ¬ x2 y) x → ∃ m ∈ ([127,244,361,480,595,720,833,1063,1188,1313,1539,2126,2244,2376,2626,3008,3078,4125,4244,4361,4625,5125,5889,6156,7300,8250,8368,8488,8722,9250,9632,10250,11778,12312,12944,14600,16256] : List Nat), ∀ i : Fin 14, x i = m.testBit i.val)
    (compiler : let step := fun (w : List (Nat × Nat)) (g : Gate) =>
      let a := w.getD (g.inputs.getD 0 0) (0,0)
      let b := w.getD (g.inputs.getD 1 0) (0,0)
      w ++ [(if g.op.eval [false,true] then a.1 ||| b.1 else a.1 &&& b.1, a.2+b.2)]
    ∀ (gs : List Gate) (w : List (Nat × Nat)),
      (∀ g∈gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length=2) →
      ∀ i o : Nat, ((gs.foldl step w).getD o (0,0)).1.testBit i =
        (Circuit.mk gs o).eval (w.map fun z => z.1.testBit i))
    (search : let step := fun (w : List (Nat × Nat)) (g : Gate) =>
      let a := w.getD (g.inputs.getD 0 0) (0,0)
      let b := w.getD (g.inputs.getD 1 0) (0,0)
      w ++ [(if g.op.eval [false,true] then a.1 ||| b.1 else a.1 &&& b.1, a.2+b.2)]
    let S := ([288247147372494849, 15270196031913994, 58150374867024, 94946423956570756, 54820275478336544, 3870282840318208, 133410654208, 759033086762549255, 218716039641301048, 189725234880840128, 156548607028235776, 229736628136996864, 270286071508729856, 288160007409369088] : List Nat).map (fun x => (x,1))
    let bound := fun v : Nat × Nat => (∑ j : Fin 39, if v.1.testBit (21+j.val) then 0 else (([99679525959508064, 144982790311510564, 41076143140] : List Nat).getD (j.val / 15) 0 >>> (4*(j.val % 15))) % 16) ≤ 4*v.2
    ∃ (gs : List Gate) (u v : Nat), gs.length≤26 ∧ TopForm.IsAO2 14 ⟨gs,0⟩ ∧
      (∀ g∈gs, g.inputs.Nodup) ∧ u<v ∧ v<14+gs.length ∧
      let W := gs.foldl step S
      let a := W.getD u (0,0)
      let b := W.getD v (0,0)
      a.1 &&& b.1 = 2097151 ∧ a.1 >>> 58 = 0 ∧ b.1 >>> 58 = 0 ∧ 31 ≤ a.2+b.2 ∧ bound a ∧ bound b) :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (27 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (14 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (7 : ℕ)), x1 x7 x8 → x3.eval (List.ofFn fun (x10 : Fin (14 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (7 : ℕ) x7 ∨ x10 = Fin.natAdd (7 : ℕ) x8)) = Bool.true) ∧               (∀ (x7 : Fin (14 : ℕ) → Bool), Maximal (fun (x8 : Fin (14 : ℕ) → Bool) => ¬x2 x8) x7 → x3.eval (List.ofFn x7) = Bool.false) ∧                 ∀ x7 ∈ [(0 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ))],                   have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = x7);                   PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x5 = Bool.false ∧ PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x6 = Bool.false := by
  let E := fun p l : Fin 7 => p=l ∨ p=l+1 ∨ p=l+3
  let F := fun x : Fin 14 → Bool => ∃ p l : Fin 7, E p l ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true
  let step := fun (w : List (Nat × Nat)) (g : Gate) =>
      let a := w.getD (g.inputs.getD 0 0) (0,0)
      let b := w.getD (g.inputs.getD 1 0) (0,0)
      w ++ [(if g.op.eval [false,true] then a.1 ||| b.1 else a.1 &&& b.1, a.2+b.2)]
  let S := ([288247147372494849, 15270196031913994, 58150374867024, 94946423956570756, 54820275478336544, 3870282840318208, 133410654208, 759033086762549255, 218716039641301048, 189725234880840128, 156548607028235776, 229736628136996864, 270286071508729856, 288160007409369088] : List Nat).map (fun x => (x,1))
  let Z : List Nat := [127, 244, 361, 480, 595, 720, 833, 1063, 1188, 1313, 1539, 2126, 2244, 2376, 2626, 3008, 3078, 4125, 4244, 4361, 4625, 5125, 5889, 6156, 7300, 8250, 8368, 8488, 8722, 9250, 9632, 10250, 11778, 12312, 12944, 14600, 16256]
  obtain ⟨gs,u,v,budget,ao,nd,hu,hv,hfork,hU,hV,_tree,_costU,_costV⟩ := search
  let std : Circuit := ⟨gs,0⟩
  let last : Gate := ⟨.and,[u,v]⟩
  let D : Circuit := ⟨gs++[last],14+gs.length⟩
  let W := gs.foldl step S
  let row (j : Nat) := S.map (fun z => z.1.testBit j)
  have szrow (j : Nat) : (row j).length=14 := by simp only [row,List.length_map]; rfl
  have rules := fun g (hg : g∈gs) => And.intro (ao.1 g hg) (ao.2.2 g hg)
  have sim (j o : Nat) : ((W.getD o (0,0)).1).testBit j = (std.wires (row j)).getD o false :=
    compiler gs S rules j o
  have wlen (ks : List Gate) (x : List Bool) : ((Circuit.mk ks 0).wires x).length=x.length+ks.length := by
    induction ks generalizing x with
    | nil => simp only [List.length_nil,Nat.add_zero]; rfl
    | cons g gs ih =>
      change ((Circuit.mk gs 0).wires (x++[_])).length=_
      rw [ih]
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have wires (x : List Bool) : D.wires x = std.wires x ++ [((std.wires x).getD u false && (std.wires x).getD v false)] := by
    change (gs++[last]).foldl _ x = _
    rw [List.foldl_append]
    change _ ++ [last.op.eval (last.inputs.map _)] = _
    change std.wires x ++ [(std.wires x).getD u false && ((std.wires x).getD v false && true)] = _
    rw [Bool.and_true]
  have output (j : Nat) : D.eval (row j) = (2097151:Nat).testBit j := by
    change (D.wires (row j)).getD (14+gs.length) false = _
    rw [wires]
    have len : (std.wires (row j)).length=14+gs.length := (wlen gs _).trans (by rw [szrow])
    rw [←len,List.getD_eq_getElem _ _ (by simp),List.getElem_append_right (by rfl)]
    simp only [Nat.sub_self,List.getElem_cons_zero]
    rw [←sim j u,←sim j v,←Nat.testBit_and]
    exact congrArg (fun m : Nat => m.testBit j) hfork
  have old (j o : Nat) (ho : o<14+gs.length) : (D.wires (row j)).getD o false = ((W.getD o (0,0)).1).testBit j := by
    rw [wires,sim]
    have len : (std.wires (row j)).length=14+gs.length := (wlen gs _).trans (by rw [szrow])
    have hh : o<(std.wires (row j)).length := len ▸ ho
    rw [List.getD_eq_getElem _ _ hh, List.getD_eq_getElem _ _ (by simp; omega : o<((std.wires (row j))++[_]).length),List.getElem_append_left hh]
  have oa : TopForm.IsAO2 14 D := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with h|h
      · exact ao.1 g h
      · obtain rfl : g=last := List.mem_singleton.mp h
        exact Or.inl rfl
    · intro j hj w hw
      change j<(gs++[last]).length at hj
      change w∈((gs++[last]).getD j _).inputs at hw
      by_cases inside : j<gs.length
      · rw [List.getD_eq_getElem _ _ hj,List.getElem_append_left inside] at hw
        apply ao.2.1 j inside w
        change w∈(gs.getD j _).inputs
        rw [List.getD_eq_getElem _ _ inside]
        exact hw
      · have edge : j=gs.length := by simp at hj; omega
        subst j
        rw [List.getD_eq_getElem _ _ hj,List.getElem_append_right (by rfl)] at hw
        simp only [Nat.sub_self,List.getElem_cons_zero,last,List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl|rfl <;> omega
    · intro g hg
      rcases List.mem_append.mp hg with h|h
      · exact ao.2.2 g h
      · obtain rfl : g=last := List.mem_singleton.mp h
        rfl
  refine ⟨D,gs.length,u,v,?_,oa,?_,rfl,?_,?_,?_,?_⟩
  · change (gs++[last]).length≤27
    simp; omega
  · intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact nd g h
    · obtain rfl : g=last := List.mem_singleton.mp h
      simp [last,ne_of_lt hu]
  · change (gs++[last])[gs.length]? = some last
    simp
  · intro p l adj
    have rows : ∀ p l : Fin 7, E p l → ∃ j : Fin 21,
        row j.val = List.ofFn (fun i : Fin 14 => decide (i=Fin.castAdd 7 p ∨ i=Fin.natAdd 7 l)) := by
      decide +kernel
    obtain ⟨j,hr⟩ := rows p l adj
    rw [←hr,output]
    exact (by decide : ∀ j : Fin 21, (2097151:Nat).testBit j.val=true) j
  · intro x hx
    obtain ⟨m,hm,hx⟩ := maxrows x hx
    change m∈Z at hm
    obtain ⟨i,rfl⟩ := List.get_of_mem hm
    have tab : ∀ j : Fin 37, row (21+j.val) = List.ofFn (fun k : Fin 14 => (Z.getD j.val 0).testBit k.val) := by decide +kernel
    let j : Fin 37 := ⟨i.val,i.isLt⟩
    have ir : List.ofFn x = row (21+j.val) := by
      rw [tab]
      apply congrArg List.ofFn
      funext k
      simpa only [j,List.getD_eq_getElem _ _ i.isLt,List.get_eq_getElem] using hx k
    rw [ir,output]
    exact (by decide : ∀ j : Fin 37, (2097151:Nat).testBit (21+j.val)=false) j
  · intro t ht
    have tab : ∀ k∈([0,7] : List (Fin 14)), ∃ j : Fin 2, row (58+j.val) = List.ofFn (fun i : Fin 14 => decide (i=k)) := by decide +kernel
    obtain ⟨j,hr⟩ := tab t ht
    change (D.wires (List.ofFn (fun i : Fin 14 => decide (i=t)))).getD u false = false ∧
      (D.wires (List.ofFn (fun i : Fin 14 => decide (i=t)))).getD v false = false
    rw [←hr,old _ u (lt_trans hu hv),old _ v hv]
    constructor
    · have e := congrArg (fun x : Nat => x.testBit j.val) hU
      simpa only [Nat.testBit_shiftRight,Nat.zero_testBit] using e
    · have e := congrArg (fun x : Nat => x.testBit j.val) hV
      simpa only [Nat.testBit_shiftRight,Nat.zero_testBit] using e
