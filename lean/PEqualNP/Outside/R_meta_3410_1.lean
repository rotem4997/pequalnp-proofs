import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3410_1
    (excluded : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (rawCases : ∀ a b : Fin 9, (9*a.val+b.val) ∈ ([1,2,3,6,11,12,13,14,15,16,17,21,22,24,25,26,31,33,42,61] : List ℕ) → ∀ P D : Circuit,
      Monotone2 P → FanInTwo D → P.size + D.size = 12 → P.output ≤ 24 → D.output = 23 →
      (∀ g ∈ P.gates ++ D.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ x : Fin 9 → Bool,
        let v := P.wires (List.ofFn x ++ [x 0 || x 4] ++ [x a || x b])
        D.eval (v ++ [!(v.getD P.output false)]) ≠ (fun x : Fin 9 → Bool => [1,12,23,34,40,5,16,27,38,57,68,85].any fun e : ℕ =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) x)
    (thirdCases : ∀ a : Fin 9, a ∈ ([1,2,3,6] : List (Fin 9)) → ∀ P D : Circuit,
      Monotone2 P → FanInTwo D → P.size + D.size = 12 → P.output ≤ 24 → D.output = 23 →
      (∀ g ∈ P.gates ++ D.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ x : Fin 9 → Bool,
        let v := P.wires (List.ofFn x ++ [x 0 || x 4] ++ [(x 0 || x 4) || x a])
        D.eval (v ++ [!(v.getD P.output false)]) ≠ (fun x : Fin 9 → Bool => [1,12,23,34,40,5,16,27,38,57,68,85].any fun e : ℕ =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) x) :
∀ (x1 : List (Fin (11 : ℕ))) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x2 →       PEqualNP.MetaComplexity.FanInTwo x3 →         x2.size + x3.size ≤ (12 : ℕ) →           x2.output ≤ (24 : ℕ) →             x3.output ≤ (24 : ℕ) →               (∀ x10 ∈ x2.gates ++ x3.gates, ∀ x12 ∈ x10.inputs, x12 ≤ (24 : ℕ)) →                 ∃ (x11 : Fin (9 : ℕ) → Bool),                   have x12 : List Bool := List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))];                   have x13 : List Bool := x2.wires (x12 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x13 : Fin (11 : ℕ)) => x12.getD (↑x13) Bool.false) x1)]);                   x3.eval (x13 ++ [!x13.getD x2.output Bool.false]) ≠ (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ))) := by
  have sizeDef (C : Circuit) : C.size = C.gates.length := rfl
  have evalDef (C : Circuit) (w : List Bool) : C.eval w = (C.wires w).getD C.output false := rfl
  have wiresDef (C : Circuit) (w : List Bool) : C.wires w = C.gates.foldl
      (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w := rfl
  have orVal (w : List Bool) : GateOp.or.eval w = w.any id := rfl
  have notVal (w : List Bool) : GateOp.not.eval w = !(w.headD false) := rfl

  let firstWires (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
  let extra (pins : List (Fin 11)) (x : Fin 9 → Bool) :=
    GateOp.or.eval (pins.map fun i => (firstWires x).getD i.val false)
  let graph (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let value (pins : List (Fin 11)) (P D : Circuit) (x : Fin 9 → Bool) :=
    let w := P.wires (firstWires x ++ [extra pins x])
    D.eval (w ++ [!(w.getD P.output false)])

  let ren (t i : ℕ) := if i<10 then i else if i=10 then t else i-1
  let renameGate (t : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren t)⟩
  let run (gs : List Gate) (w : List Bool) :=
    gs.foldl (fun old g => old ++ [g.op.eval (g.inputs.map fun i => old.getD i false)]) w

  have readRen (w tail : List Bool) (hw : w.length=10) (hs : tail.length≤14)
      (t : ℕ) (ht : t<10 ∨ t=25) (i : ℕ) :
      (w++tail).getD (ren t i) false = (w++w.getD t false::tail).getD i false := by
    by_cases lo : i<10
    · simp [ren,lo,List.getD_eq_getElem?_getD,List.getElem?_append,hw]
    by_cases eq : i=10
    · subst i
      rcases ht with h|rfl
      · simp [ren,List.getD_eq_getElem?_getD,List.getElem?_append,hw,h]
      · have oob : tail[15]?=none := List.getElem?_eq_none (by omega)
        simp [ren,List.getD_eq_getElem?_getD,List.getElem?_append,hw,oob]
    · obtain ⟨k,rfl⟩ : ∃ k, i=10+(k+1) := ⟨i-11,by omega⟩
      simp [ren,List.getD_eq_getElem?_getD,List.getElem?_append,hw,show ¬10+(k+1)<10 by omega,
        show 10+(k+1)-1=10+k by omega,
        show ¬10+k<10 by omega]

  have runRen (w : List Bool) (hw : w.length=10) (t : ℕ) (ht : t<10 ∨ t=25)
      (gs : List Gate) (hgs : gs.length ≤ 14) : ∃ tail : List Bool, tail.length=gs.length ∧
      run (gs.map (renameGate t)) w = w++tail ∧ run gs (w++[w.getD t false]) = w++w.getD t false::tail := by
    induction gs using List.reverseRecOn with
    | nil => exact ⟨[],rfl,by simp [run],rfl⟩
    | append_singleton gs g ih =>
      have h : gs.length ≤ 14 := by simp at hgs; omega
      obtain ⟨tail,hl,ha,hb⟩ := ih h
      let b := g.op.eval (g.inputs.map fun i => (w++w.getD t false::tail).getD i false)
      have eq : g.inputs.map (fun i => (w++tail).getD (ren t i) false) =
          g.inputs.map (fun i => (w++w.getD t false::tail).getD i false) :=
        List.map_congr_left fun i _ => readRen w tail hw (by omega) t ht i
      have last (l : List Gate) (g : Gate) (base : List Bool) : run (l++[g]) base =
          run l base ++ [g.op.eval (g.inputs.map fun i => (run l base).getD i false)] := by simp [run,List.foldl_append]
      refine ⟨tail++[b],by simp [hl],?_,?_⟩
      · simp only [List.map_append,List.map_cons,List.map_nil,last,ha,renameGate,List.map_map,Function.comp_def]
        rw [eq]; simp [b]
      · rw [last,hb]; simp [b]

  have redundant_or (excluded : ¬ HasCircuitSize 9 graph 14) (pins : List (Fin 11)) (P D : Circuit)
      (hP : Monotone2 P) (hD : FanInTwo D) (hlen : P.size + D.size ≤ 12)
      (t : ℕ) (ht : t<10 ∨ t=25) (sameWire : ∀ x, (firstWires x).getD t false = extra pins x) :
      ∃ x, value pins P D x ≠ graph x := by
    by_contra! agree
    apply excluded
    let first : Gate := ⟨.or,[0,4]⟩
    let neg : Gate := ⟨.not,[P.output]⟩
    let rest := P.gates ++ [neg] ++ D.gates
    let C : Circuit := ⟨first :: rest.map (renameGate t),ren t D.output⟩
    have len : rest.length ≤ 13 := by simp [rest,sizeDef] at hlen ⊢; omega
    refine ⟨C,?_,?_,?_⟩
    · intro g hg
      change g ∈ first :: rest.map (renameGate t) at hg
      rcases List.mem_cons.mp hg with rfl|hg
      · simp [first]
      obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
      simp only [rest,List.mem_append,List.mem_singleton] at hg'
      rcases hg' with (h|rfl)|h
      · obtain ⟨op,h⟩ := hP _ h
        exact ⟨op.elim Or.inl (fun eq => Or.inr (Or.inl eq)),by simpa [renameGate] using h⟩
      · simp [renameGate,neg]
      · simpa [renameGate] using hD g' h
    · simp [C,sizeDef]; omega
    · intro x
      have plen : (firstWires x).length=10 := by simp [firstWires]
      have firstEq : first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 4) := by
        change ((List.ofFn x).getD (0 : Fin 9).val false || ((List.ofFn x).getD (4 : Fin 9).val false || false)) = _
        simp
      obtain ⟨tail,hs,ha,hb⟩ := runRen (firstWires x) plen t ht rest (by omega)
      have left : C.wires (List.ofFn x) = run (rest.map (renameGate t)) (firstWires x) := by
        change run (rest.map (renameGate t)) (List.ofFn x ++ [first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false)]) = _
        rw [firstEq]
      have right : value pins P D x = (run rest (firstWires x ++ [extra pins x])).getD D.output false := by
        simp [value,rest,neg,run,evalDef,wiresDef,List.foldl_append,notVal]
      change (C.wires (List.ofFn x)).getD (ren t D.output) false = _
      rw [left,ha,readRen _ _ plen (by omega) t ht,← hb,sameWire x,← right]
      exact agree x



  let Fresh (a b : Fin 11) := a<b ∧ b.val<10 ∧ ¬(a=0 ∧ b=4) ∧ ¬((a=0 ∨ a=4) ∧ b=9)
  let Repeated (pins : List (Fin 11)) := ∃ t : ℕ, (t<10 ∨ t=25) ∧ ∀ x,
    (firstWires x).getD t false = extra pins x

  have outPin (x : Fin 9 → Bool) {t : ℕ} (h : 10 ≤ t) : (firstWires x).getD t false=false :=
    List.getD_eq_default _ _ (by simpa [firstWires] using h)

  have single_pin (i : Fin 11) (b : (Fin 9 → Bool) → Bool)
      (h : ∀ x, (firstWires x).getD i.val false = b x) :
      ∃ t : ℕ, (t<10 ∨ t=25) ∧ ∀ x, (firstWires x).getD t false = b x := by
    by_cases lo : i.val<10
    · exact ⟨i.val,Or.inl lo,h⟩
    · exact ⟨25,Or.inr rfl,fun x => (outPin x (by decide)).trans ((outPin x (by omega)).symm.trans (h x))⟩

  have pair_sorted (a b : Fin 11) (h : a ≤ b) : Repeated [a,b] ∨ Fresh a b := by
    by_cases out : b.val=10
    · left
      apply single_pin a
      intro x
      simp [extra,orVal,out,firstWires]
    by_cases same : a=b
    · subst b
      left
      apply single_pin a
      simp [extra,orVal]
    have lt : a<b := lt_of_le_of_ne h same
    have live : b.val < 10 := by omega
    by_cases edge : a=0 ∧ b=4
    · obtain ⟨rfl,rfl⟩ := edge
      left; refine ⟨9,Or.inl (by decide),?_⟩; intro x
      simp [extra,firstWires,orVal,List.getD_eq_getElem?_getD]
    by_cases absorbed : (a=0 ∨ a=4) ∧ b=9
    · obtain ⟨aa,rfl⟩ := absorbed
      left; refine ⟨9,Or.inl (by decide),?_⟩; intro x
      rcases aa with rfl|rfl <;>
        simp [extra,firstWires,orVal,List.getD_eq_getElem?_getD,Bool.or_left_comm,Bool.or_comm]
    exact Or.inr ⟨lt,live,edge,absorbed⟩

  have normalize_or (pins : List (Fin 11)) (h : pins.length≤2) : Repeated pins ∨
      ∃ a b : Fin 11, Fresh a b ∧ ∀ x, extra pins x = extra [a,b] x := by
    cases pins with
    | nil => exact Or.inl ⟨25,Or.inr rfl,fun x => outPin x (by decide)⟩
    | cons a L =>
      cases L with
      | nil => exact Or.inl (single_pin a _ (by simp [extra,orVal]))
      | cons b L =>
        cases L with
        | cons _ _ => simp at h
        | nil =>
          rcases le_total a b with h|h
          · rcases pair_sorted a b h with hit|fresh
            · exact Or.inl hit
            · exact Or.inr ⟨a,b,fresh,fun _ => rfl⟩
          · have eq (x) : extra [a,b] x = extra [b,a] x := by simp [extra,orVal,Bool.or_comm]
            rcases pair_sorted b a h with ⟨t,ht,he⟩|fresh
            · exact Or.inl ⟨t,ht,fun x => (he x).trans (eq x).symm⟩
            · exact Or.inr ⟨b,a,fresh,eq⟩



  have assembled (pins : List (Fin 11)) (P D : Circuit) (hp : pins.length≤2)
      (hP : Monotone2 P) (hD : FanInTwo D) : ∃ C : Circuit, FanInTwo C ∧
      C.size = P.size+D.size+3 ∧ C.output=D.output ∧ ∀ x, C.eval (List.ofFn x) = value pins P D x := by
    let first : Gate := ⟨.or,[0,4]⟩
    let second : Gate := ⟨.or,pins.map Fin.val⟩
    let neg : Gate := ⟨.not,[P.output]⟩
    let C : Circuit := ⟨[first,second] ++ P.gates ++ [neg] ++ D.gates,D.output⟩
    refine ⟨C,?_,?_,rfl,?_⟩
    · intro g hg
      simp only [C,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with (((rfl|rfl)|h)|rfl)|h
      · simp [first]
      · simpa [second] using hp
      · obtain ⟨op,h⟩ := hP _ h
        exact ⟨op.elim Or.inl (fun ne => Or.inr (Or.inl ne)),h⟩
      · simp [neg]
      · exact hD _ h
    · simp [C,sizeDef]; omega
    · intro x
      simp [C,evalDef,wiresDef,first,second,neg,value,extra,firstWires,List.foldl_append,
        orVal,notVal,List.map_map,Function.comp_def,List.getD_eq_getElem?_getD]

  have short_impossible (excluded : ¬ HasCircuitSize 9 graph 14) (pins : List (Fin 11)) (P D : Circuit)
      (hp : pins.length≤2) (hP : Monotone2 P) (hD : FanInTwo D) (hlen : P.size+D.size<12) :
      ∃ x, value pins P D x ≠ graph x := by
    by_contra! agree
    obtain ⟨C,fan,size,_,hv⟩ := assembled pins P D hp hP hD
    exact excluded ⟨C,fan,by omega,fun x => (hv x).trans (agree x)⟩

  have wireListLen (gs : List Gate) (w : List Bool) :
      (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) w).length =
          w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      simp only [List.length_append,List.length_cons,List.length_nil]; omega

  have exact_last_gate (excluded : ¬ HasCircuitSize 9 graph 14) (C : Circuit)
      (fan : FanInTwo C) (sz : C.size≤15) (correct : ∀ x, C.eval (List.ofFn x) = graph x) :
      C.size=15 ∧ C.output=23 := by
    have size : C.size=15 := by
      by_contra! h
      exact excluded ⟨C,fan,by omega,correct⟩
    refine ⟨size,?_⟩
    by_contra bad
    have nonempty : C.gates ≠ [] := by intro h; simp [sizeDef,h] at size
    let post := C.gates.getLast nonempty
    let C' : Circuit := ⟨C.gates.dropLast,C.output⟩
    have endEq : C.gates = C'.gates ++ [post] := (List.dropLast_append_getLast nonempty).symm
    have smaller : C'.size=14 := by
      have h := congrArg List.length endEq
      simp only [List.length_append,List.length_singleton] at h
      change C.gates.length=15 at size
      change C'.gates.length=14
      omega
    apply excluded
    refine ⟨C',fun g hg => fan g (endEq ▸ List.mem_append_left [post] hg),by omega,?_⟩
    intro x
    rw [←correct x]
    have wr : C.wires (List.ofFn x) = C'.wires (List.ofFn x) ++
        [post.op.eval (post.inputs.map fun i => (C'.wires (List.ofFn x)).getD i false)] := by
      change C.gates.foldl _ _ = _
      rw [endEq,List.foldl_append]
      rfl
    have len : (C'.wires (List.ofFn x)).length=23 := by
      rw [wiresDef,wireListLen,List.length_ofFn]
      change 9+C'.size=23
      omega
    change (C'.wires (List.ofFn x)).getD C.output false = (C.wires (List.ofFn x)).getD C.output false
    rw [wr]
    by_cases lo : C.output<23
    · rw [List.getD_append _ _ _ _ (by omega : C.output < (C'.wires _).length)]
    · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by rw [List.length_append,len,List.length_singleton]; omega)]

  have exact_shape (excluded : ¬ HasCircuitSize 9 graph 14) (pins : List (Fin 11)) (P D : Circuit)
      (hp : pins.length≤2) (hP : Monotone2 P) (hD : FanInTwo D) (budget : P.size+D.size≤12)
      (correct : ∀ x, value pins P D x=graph x) : P.size+D.size=12 ∧ D.output=23 := by
    obtain ⟨C,fan,size,output,hv⟩ := assembled pins P D hp hP hD
    obtain ⟨full,last⟩ := exact_last_gate excluded C fan (by omega) (fun x => (hv x).trans (correct x))
    exact ⟨by omega,output ▸ last⟩
  let target (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5

  let base (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]

  let bad (f : (Fin 9 → Bool) → Bool) :=
    ∀ P D : Circuit, Monotone2 P → FanInTwo D → P.size + D.size = 12 →
      P.output ≤ 24 → D.output = 23 → (∀ g ∈ P.gates ++ D.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ x : Fin 9 → Bool, let v := P.wires (base x ++ [f x])
        D.eval (v ++ [!(v.getD P.output false)]) ≠ target x

  let maps : Fin 2 → Fin 9 → Fin 9 := ![![0,1,2,3,4,5,6,7,8],![0,5,8,3,4,1,7,6,2]]
  let rawReps : List (Fin 9 × Fin 9) :=
    [(0,1),(0,2),(0,3),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),
     (2,3),(2,4),(2,6),(2,7),(2,8),(3,4),(3,6),(4,6),(6,7)]
  let thirdReps : List (Fin 9) := [1,2,3,6]
  have graphInvariant (k : Fin 2) (x : Fin 9 → Bool) : target (x ∘ maps k) = target x := by
    fin_cases k
    · rfl
    · change ((x 0 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 5 && x 7) || (x 8 && x 6) || (x 3 && x 2) || (x 1 && x 6) || (x 7 && x 2) || (x 2 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl

  have fixedEndpoints : ∀ k : Fin 2, maps k 0 = 0 ∧ maps k 4 = 4 := by
    dsimp only [maps]
    decide +kernel

  have orbitRaw : ∀ a b : Fin 9, a ≠ b → ¬((a=0 ∧ b=4) ∨ (a=4 ∧ b=0)) →
      ∃ k : Fin 2, (min (maps k a) (maps k b),max (maps k a) (maps k b)) ∈ rawReps := by
    dsimp only [maps,rawReps]
    decide +kernel

  have orbitThird : ∀ a : Fin 9, a ≠ 0 → a ≠ 4 → ∃ k : Fin 2, maps k a ∈ thirdReps := by
    dsimp only [maps,thirdReps]
    decide +kernel

  have transport (k : Fin 2) (f rep : (Fin 9 → Bool) → Bool)
      (translated : ∀ x, f (x ∘ maps k) = rep x) (hb : bad rep) : bad f := by
    let idx (i : ℕ) := if h : i < 9 then (maps k ⟨i,h⟩).val else i
    let gate (g : Gate) : Gate := ⟨g.op,g.inputs.map idx⟩
    let ren (C : Circuit) : Circuit := ⟨C.gates.map gate,idx C.output⟩
    let agree (w v : List Bool) := ∀ i : ℕ, w.getD i false = v.getD (idx i) false
    have bigIndex {i j : ℕ} (hj : 9 ≤ j) (small : i < j) : idx i < j := by
      dsimp only [idx]
      split
      · rename_i hi; have := (maps k ⟨i,hi⟩).isLt; omega
      · exact small
    have indexLimit (i : ℕ) (hi : i ≤ 24) : idx i ≤ 24 := by
      have := bigIndex (j:=25) (by decide) (by omega : i < 25)
      omega
    have append (w v : List Bool) (z : Bool) (len : w.length = v.length)
        (big : 9 ≤ w.length) (old : agree w v) : agree (w++[z]) (v++[z]) := by
      intro i
      by_cases hi : i < w.length
      · have hp : idx i < v.length := len ▸ bigIndex big hi
        simpa only [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ hp] using old i
      · rw [show idx i = i by simp [idx,show ¬ i < 9 by omega],
            List.getD_append_right _ _ false i (by omega),
            List.getD_append_right _ _ false i (by omega),len]
    have lengths (gs : List Gate) (w : List Bool) :
        ((Circuit.mk gs 0).wires w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp [wiresDef]
      | cons g gs ih =>
        change ((Circuit.mk gs 0).wires (w++[_])).length = _
        rw [ih]
        simp [Nat.add_comm,Nat.add_left_comm]
    have lift (gs : List Gate) (w v : List Bool) (len : w.length = v.length)
        (big : 9 ≤ w.length) (old : agree w v) :
        agree ((Circuit.mk gs 0).wires w) ((Circuit.mk (gs.map gate) 0).wires v) := by
      induction gs generalizing w v with
      | nil => exact old
      | cons g gs ih =>
        let b := g.op.eval (g.inputs.map fun i => w.getD i false)
        have val : (gate g).op.eval ((gate g).inputs.map fun i => v.getD i false) = b := by
          apply congrArg g.op.eval
          simp only [gate,List.map_map,Function.comp_def]
          exact List.map_congr_left (fun i _ => (old i).symm)
        change agree ((Circuit.mk gs 0).wires (w++[b])) ((Circuit.mk (gs.map gate) 0).wires (v++[_]))
        rw [val]
        exact ih _ _ (by simp [len]) (by simp; omega) (append _ _ _ len big old)
    intro P D hP hD sizeP outP outD lim
    have mon : Monotone2 (ren P) := by
      intro g hg
      change g ∈ P.gates.map gate at hg
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
      simpa only [gate,List.length_map] using hP a ha
    have fan : FanInTwo (ren D) := by
      intro g hg
      change g ∈ D.gates.map gate at hg
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
      simpa only [gate,List.length_map] using hD a ha
    have total : (ren P).size + (ren D).size = 12 := by simpa [ren,sizeDef] using sizeP
    have bounded : ∀ g ∈ (ren P).gates ++ (ren D).gates, ∀ i ∈ g.inputs, i ≤ 24 := by
      intro g hg i hi
      change g ∈ P.gates.map gate ++ D.gates.map gate at hg
      rw [← List.map_append] at hg
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hi
      exact indexLimit _ (lim _ ha _ hb)
    obtain ⟨x,hx⟩ := hb (ren P) (ren D) mon fan total (indexLimit _ outP) (by change idx D.output = 23; simp [idx,outD]) bounded
    let y := x ∘ maps k
    have raw : agree (List.ofFn y) (List.ofFn x) := by
      intro i
      by_cases hi : i < 9
      · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,idx,hi,dite_eq_left,
          (maps k ⟨i,hi⟩).isLt,Option.getD_some]
        rfl
      · simp [idx,hi,List.getD_eq_getElem?_getD]
    have one : agree (base y) (base x) := by
      have e : (y 0 || y 4) = (x 0 || x 4) := by simp [y,Function.comp_def,(fixedEndpoints k).1,(fixedEndpoints k).2]
      change agree (List.ofFn y ++ [y 0 || y 4]) (List.ofFn x ++ [x 0 || x 4])
      rw [e]
      exact append _ _ _ (by simp) (by simp) raw
    let w := base y ++ [f y]
    let v := base x ++ [rep x]
    have init : agree w v := by
      dsimp [w,v]
      rw [show f y = rep x from translated x]
      exact append _ _ _ (by simp [base]) (by simp [base]) one
    have phase : agree (P.wires w) ((ren P).wires v) :=
      lift P.gates _ _ (by simp [w,v,base]) (by simp [w,base]) init
    have plen : (P.wires w).length = ((ren P).wires v).length := by
      change ((Circuit.mk P.gates 0).wires w).length = ((Circuit.mk (P.gates.map gate) 0).wires v).length
      simp [lengths,w,v,base]
    have pbig : 9 ≤ (P.wires w).length := by
      change 9 ≤ ((Circuit.mk P.gates 0).wires w).length
      rw [lengths]
      simp [w,base]
      omega
    let nw := P.wires w ++ [!((P.wires w).getD P.output false)]
    let nv := (ren P).wires v ++ [!(((ren P).wires v).getD (ren P).output false)]
    have neg : agree nw nv := by
      dsimp only [nw,nv]
      rw [phase P.output]
      exact append _ _ _ plen pbig phase
    have suffix : D.eval nw = (ren D).eval nv :=
      lift D.gates nw nv (by simp [nw,nv,plen]) (by simp [nw]; omega) neg D.output
    refine ⟨y,?_⟩
    change D.eval nw ≠ target y
    rw [show target y = target x from graphInvariant k x,suffix]
    exact hx

  have reduceRaw (cases : ∀ ab ∈ rawReps, bad (fun x => x ab.1 || x ab.2))
      (a b : Fin 9) (ne : a ≠ b) (fresh : ¬((a=0 ∧ b=4) ∨ (a=4 ∧ b=0))) :
      bad (fun x => x a || x b) := by
    obtain ⟨k,hk⟩ := orbitRaw a b ne fresh
    apply transport k _ _ _ (cases _ hk)
    intro x
    change (x (maps k a) || x (maps k b)) = (x (min _ _) || x (max _ _))
    rcases le_total (maps k a) (maps k b) with h|h
    · rw [min_eq_left h,max_eq_right h]
    · rw [min_eq_right h,max_eq_left h,Bool.or_comm]

  have reduceThird (cases : ∀ a ∈ thirdReps, bad (fun x => (x 0 || x 4) || x a))
      (a : Fin 9) (h0 : a ≠ 0) (h4 : a ≠ 4) : bad (fun x => (x 0 || x 4) || x a) := by
    obtain ⟨k,hk⟩ := orbitThird a h0 h4
    apply transport k _ _ _ (cases _ hk)
    intro x
    simp [(fixedEndpoints k).1,(fixedEndpoints k).2]
  have freshReduction
      (rawCases : ∀ (a b : Fin 9), 9*a.val+b.val ∈ ([1,2,3,6,11,12,13,14,15,16,17,21,22,24,25,26,31,33,42,61] : List ℕ) →
        bad (fun x => x a || x b))
      (thirdCases : ∀ (a : Fin 9), a ∈ ([1,2,3,6] : List (Fin 9)) →
        bad (fun x => (x 0 || x 4) || x a))
      (a b : Fin 11) (fresh : Fresh a b) : bad (extra [a,b]) := by
    have validCode : ∀ z : Fin 9 × Fin 9, z ∈ rawReps → 9*z.1.val+z.2.val ∈
        ([1,2,3,6,11,12,13,14,15,16,17,21,22,24,25,26,31,33,42,61] : List ℕ) := by
      dsimp only [rawReps]
      decide +kernel
    have raw (i : Fin 11) (h : i.val < 9) (x : Fin 9 → Bool) :
        (firstWires x).getD i.val false = x ⟨i.val,h⟩ := by
      rw [List.getD_append _ _ _ _ (by simpa using h)]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,h,dite_eq_left,Option.getD_some]
    have nine (x : Fin 9 → Bool) : (firstWires x).getD 9 false = (x 0 || x 4) := by
      simp [firstWires,List.getD_eq_getElem?_getD]
    obtain ⟨lt,live,pair,absorb⟩ := fresh
    have aLive : a.val < 9 := by omega
    let a' : Fin 9 := ⟨a.val,aLive⟩
    by_cases bLive : b.val < 9
    · let b' : Fin 9 := ⟨b.val,bLive⟩
      have n : a' ≠ b' := fun e => by have he := congrArg Fin.val e; change a.val=b.val at he; omega
      have distinct : ¬((a'=0 ∧ b'=4) ∨ (a'=4 ∧ b'=0)) := by
        rintro (⟨aa,bb⟩|⟨aa,bb⟩)
        · apply pair
          exact ⟨Fin.ext (congrArg (fun v : Fin 9 => v.val) aa),Fin.ext (congrArg (fun v : Fin 9 => v.val) bb)⟩
        · have xa : a.val=4 := congrArg (fun v : Fin 9 => v.val) aa
          have xb : b.val=0 := congrArg (fun v : Fin 9 => v.val) bb
          omega
      have eq : extra [a,b] = (fun x => x a' || x b') := by
        funext x
        simp only [extra,orVal,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false]
        rw [raw a aLive,raw b bLive]
      rw [eq]
      exact reduceRaw (fun ab h => rawCases _ _ (validCode ab h)) a' b' n distinct
    · have bn : b = 9 := Fin.ext (by omega)
      have far : a' ≠ 0 ∧ a' ≠ 4 := by
        constructor
        · intro aa
          exact absorb ⟨Or.inl (Fin.ext (congrArg (fun v : Fin 9 => v.val) aa)),bn⟩
        · intro aa
          exact absorb ⟨Or.inr (Fin.ext (congrArg (fun v : Fin 9 => v.val) aa)),bn⟩
      have eq : extra [a,b] = (fun x => (x 0 || x 4) || x a') := by
        funext x
        rw [bn]
        simp only [extra,orVal,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false]
        rw [raw a aLive]
        change (x a' || (firstWires x).getD 9 false) = _
        rw [nine x,Bool.or_comm]
      rw [eq]
      exact reduceThird thirdCases a' far.1 far.2
  have graphEq : graph = (fun x : Fin 9 → Bool => [1,12,23,34,40,5,16,27,38,57,68,85].any fun e : ℕ =>
      x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) := by
    funext x
    simp only [graph,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    rfl
  have lower : ¬ HasCircuitSize 9 graph 14 := graphEq ▸ excluded
  intro pins P D hp hP hD budget hpo _ bounds
  change ∃ x, value pins P D x ≠ graph x
  by_contra! agree
  obtain ⟨size,last⟩ := exact_shape lower pins P D hp hP hD budget agree
  rcases normalize_or pins hp with repeated | ⟨a,b,fresh,eq⟩
  · obtain ⟨t,ht,same⟩ := repeated
    obtain ⟨x,miss⟩ := redundant_or lower pins P D hP hD budget t ht same
    exact miss (agree x)
  · have hraw (i j : Fin 9) (hr : 9*i.val+j.val ∈ ([1,2,3,6,11,12,13,14,15,16,17,21,22,24,25,26,31,33,42,61] : List ℕ)) : bad (fun x => x i || x j) := by
      intro A B ha hb hs hao hbo hbound
      obtain ⟨x,hx⟩ := rawCases i j hr A B ha hb hs hao hbo hbound
      refine ⟨x,?_⟩
      change _ ≠ graph x
      rw [graphEq]
      exact hx
    have hthird (i : Fin 9) (hr : i ∈ ([1,2,3,6] : List (Fin 9))) : bad (fun x => (x 0 || x 4) || x i) := by
      intro A B ha hb hs hao hbo hbound
      obtain ⟨x,hx⟩ := thirdCases i hr A B ha hb hs hao hbo hbound
      refine ⟨x,?_⟩
      change _ ≠ graph x
      rw [graphEq]
      exact hx
    obtain ⟨x,miss⟩ := freshReduction hraw hthird a b fresh P D hP hD size hpo last bounds
    apply miss
    change (let w := P.wires (firstWires x ++ [extra [a,b] x]); D.eval (w ++ [!(w.getD P.output false)])) = graph x
    rw [←eq x]
    exact agree x
