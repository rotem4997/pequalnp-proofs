import PEqualNP.Defs
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_5882_317
    (front : ∃ w : ℕ → ℕ, (∀ i : Fin 26, w i.val = (let u := (if i.val < 13 then [9820805366576,3697915243686326406,3772072151941599339,8659025085589474860,762494670591627578,9998186360218198862,7813898889586405971,2492579563743896212,8260024526693886294,9773907680645894422,2402781631192498177] else [1231427982286,4772337669408815584,1455263899191340963,9832454934276868335,925941497934626908,2690850975655642988,2184208476895364767,3353807136187280627,2669759675931372401,6826416250394358953,6258748122593763329] : List ℕ).foldl (fun x y => 10^19*x+y) 0; let n := i.val % 13; let p := (2^676-1)/8191; ((u >>> (13-n)) &&& ((2^n-1)*p)) ||| ((u <<< n) &&& ((8192-2^n)*p)))) ∧
      (∀ j : Fin 6, w (26+j.val) = w j.val ||| w (j.val+1) ∧ w (32+j.val) = w (j.val+3) ||| w ((j.val+9)%13) ∧ w (38+j.val) = w (26+j.val) ||| w (32+j.val)) ∧
      w 54 = 34638844649535 ∧ ∀ j : Fin 29, ∃ a b : Fin (26+j.val),
        (w (26+j.val) = w a.val &&& w b.val ∨ w (26+j.val) = w a.val ||| w b.val))
    (back : ∃ w : ℕ → ℕ, (∀ i : Fin 26, w i.val = (let u := (if i.val < 13 then [9820805366576,3697915243686326406,3772072151941599339,8659025085589474860,762494670591627578,9998186360218198862,7813898889586405971,2492579563743896212,8260024526693886294,9773907680645894422,2402781631192498177] else [1231427982286,4772337669408815584,1455263899191340963,9832454934276868335,925941497934626908,2690850975655642988,2184208476895364767,3353807136187280627,2669759675931372401,6826416250394358953,6258748122593763329] : List ℕ).foldl (fun x y => 10^19*x+y) 0; let n := i.val % 13; let p := (2^676-1)/8191; ((u >>> (13-n)) &&& ((2^n-1)*p)) ||| ((u <<< n) &&& ((8192-2^n)*p)))) ∧
      (∀ j : Fin 6, w (26+j.val) = w j.val ||| w (j.val+1) ∧ w (32+j.val) = w (j.val+3) ||| w ((j.val+9)%13) ∧ w (38+j.val) = w (26+j.val) ||| w (32+j.val)) ∧
      w 54 = 34638844649535 ∧ w 88 = 4503599627370495 ∧ ∀ j : Fin 34, ∃ a b : Fin (55+j.val),
        (a.val < 44 ∨ 54 ≤ a.val) ∧ (b.val < 44 ∨ 54 ≤ b.val) ∧ (w (55+j.val) = w a.val &&& w b.val ∨ w (55+j.val) = w a.val ||| w b.val))
    : (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧ x4.size ≤ (63 : ℕ) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), x5 - x6 ∈ x1 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ x5 ∈ x2, ∀ x7 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x9 : Fin (13 : ℕ)) (x10 : Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 (x3 x5 x7 x9 x10) = Bool.false) := by
  let col (i : Fin 26) : ℕ := (let u := (if i.val < 13 then [9820805366576,3697915243686326406,3772072151941599339,8659025085589474860,762494670591627578,9998186360218198862,7813898889586405971,2492579563743896212,8260024526693886294,9773907680645894422,2402781631192498177] else [1231427982286,4772337669408815584,1455263899191340963,9832454934276868335,925941497934626908,2690850975655642988,2184208476895364767,3353807136187280627,2669759675931372401,6826416250394358953,6258748122593763329] : List ℕ).foldl (fun x y => 10^19*x+y) 0; let n := i.val % 13; let p := (2^676-1)/8191; ((u >>> (13-n)) &&& ((2^n-1)*p)) ||| ((u <<< n) &&& ((8192-2^n)*p)))
  let D : Finset (Fin 13) := {0,1,3,9}
  let seeds : List (ℕ × ℕ) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
  let scales : List (Fin 13) := [1,3,9]
  let row (s : ℕ × ℕ) (a b : Fin 13) (c : Bool) : Fin (13+13) → Bool :=
    let p (l r : ℕ) (i : Fin 13) := if c = true then r.testBit (-(a*i+b) : Fin 13).val else l.testBit (a*i+b).val
    Fin.append (p s.1 s.2) (p s.2 s.1)
  let mask : ℕ := 4503599627370495
  obtain ⟨f, fbase, fshare, fout, fstep⟩ := front
  obtain ⟨b, bbase, bshare, bin, bout, bstep⟩ := back
  let w (i : ℕ) := if i < 55 then f i else b i
  have frontWire (i : ℕ) (h : i < 55) : w i = f i := ite_eq_left h
  have backWire (i : ℕ) (h : i < 44 ∨ 54 ≤ i) : w i = b i := by
    by_cases hi : i < 55
    · rw [frontWire i hi]
      rcases h with hl | hl
      · by_cases low : i < 26
        · exact (fbase ⟨i,low⟩).trans (bbase ⟨i,low⟩).symm
        · have same (u : ℕ) (hu : u < 26) : f u = b u :=
            (fbase ⟨u,hu⟩).trans (bbase ⟨u,hu⟩).symm
          have s1 (j : Fin 6) : f (26+j.val) = b (26+j.val) := by
            rw [(fshare j).1,(bshare j).1,same j.val (by omega),same (j.val+1) (by omega)]
          have s2 (j : Fin 6) : f (32+j.val) = b (32+j.val) := by
            rw [(fshare j).2.1,(bshare j).2.1,same (j.val+3) (by omega),same ((j.val+9)%13) (by omega)]
          by_cases hi1 : i < 32
          · let j : Fin 6 := ⟨i-26,by omega⟩
            have eq : 26+j.val = i := by dsimp [j]; omega
            exact eq ▸ s1 j
          by_cases hi2 : i < 38
          · let j : Fin 6 := ⟨i-32,by omega⟩
            have eq : 32+j.val = i := by dsimp [j]; omega
            exact eq ▸ s2 j
          · let j : Fin 6 := ⟨i-38,by omega⟩
            have eq : 38+j.val = i := by dsimp [j]; omega
            rw [← eq,(fshare j).2.2,(bshare j).2.2,s1 j,s2 j]
      · have : i = 54 := by omega
        subst i
        exact fout.trans bin.symm
    · exact ite_eq_right hi
  have base (i : Fin 26) : w i.val = col i := (frontWire _ (by omega)).trans (fbase i)
  have output : w 88 = mask := (backWire _ (by decide)).trans bout
  have steps (j : Fin 63) : ∃ a b : Fin (26+j.val),
      w (26+j.val) = w a.val &&& w b.val ∨ w (26+j.val) = w a.val ||| w b.val := by
    by_cases h : j.val < 29
    · obtain ⟨a,b,r⟩ := fstep ⟨j.val,h⟩
      refine ⟨a,b,?_⟩
      rw [frontWire _ (by omega), frontWire a.val (by have := a.isLt; change a.val < 26+j.val at this; omega),
        frontWire b.val (by have := b.isLt; change b.val < 26+j.val at this; omega)]
      exact r
    · let k : Fin 34 := ⟨j.val-29,by omega⟩
      have hk : 55+k.val = 26+j.val := by dsimp [k]; omega
      obtain ⟨a,b,ha,hb,rule⟩ := bstep k
      refine ⟨⟨a.val, hk ▸ a.isLt⟩, ⟨b.val, hk ▸ b.isLt⟩, ?_⟩
      change w (26+j.val) = w a.val &&& w b.val ∨ w (26+j.val) = w a.val ||| w b.val
      rw [backWire _ (by omega), backWire _ ha, backWire _ hb, ← hk]
      exact rule

  have make (j : Fin 63) : ∃ g : Gate,
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧
      (∀ i ∈ g.inputs, i < 26+j.val) ∧
      ∀ k : ℕ, g.op.eval (g.inputs.map fun i => (w i).testBit k) = (w (26+j.val)).testBit k := by
    obtain ⟨a,b,h | h⟩ := steps j
    · refine ⟨⟨.and,[a.val,b.val]⟩,Or.inl rfl,rfl,?_,?_⟩
      · intro i hi
        rcases (show i = a.val ∨ i = b.val by simpa using hi) with rfl | rfl
        exact a.isLt
        exact b.isLt
      · intro k
        change ((w a.val).testBit k && ((w b.val).testBit k && true)) = _
        rw [h,Nat.testBit_and,Bool.and_true]
    · refine ⟨⟨.or,[a.val,b.val]⟩,Or.inr rfl,rfl,?_,?_⟩
      · intro i hi
        rcases (show i = a.val ∨ i = b.val by simpa using hi) with rfl | rfl
        exact a.isLt
        exact b.isLt
      · intro k
        change ((w a.val).testBit k || ((w b.val).testBit k || false)) = _
        rw [h,Nat.testBit_or,Bool.or_false]
  let g (j : Fin 63) : Gate := (make j).choose
  have spec (j : Fin 63) := (make j).choose_spec
  let C : Circuit := ⟨List.ofFn g,88⟩
  have gateEq (j : ℕ) (hj : j < C.gates.length) :
      C.gates[j] = g ⟨j,by simpa [C] using hj⟩ := List.getElem_ofFn hj
  have field (q : Gate) (hq : q ∈ C.gates) : (q.op = .and ∨ q.op = .or) ∧ q.inputs.length = 2 := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨(spec j).1,(spec j).2.1⟩
  have syntaxOk : IsAO2 26 C := by
    refine ⟨fun q hq => (field q hq).1, ?_,fun q hq => (field q hq).2⟩
    intro j hj i hi
    change i ∈ (C.gates.getD j _).inputs at hi
    rw [List.getD_eq_getElem _ _ hj,gateEq] at hi
    exact (spec ⟨j,by simpa [C] using hj⟩).2.2.1 i hi
  let ev (xs : List Bool) (q : Gate) := xs ++ [q.op.eval (q.inputs.map fun i => xs.getD i false)]
  have run (gs : List Gate) (m : ℕ) (v : ℕ → Bool)
      (h : ∀ j (hj : j < gs.length), (∀ i ∈ gs[j].inputs, i < m+j) ∧
        gs[j].op.eval (gs[j].inputs.map v) = v (m+j)) :
      gs.foldl ev ((List.range m).map v) = (List.range (m+gs.length)).map v := by
    induction gs generalizing m with
    | nil => simp
    | cons q gs ih =>
      have head := h 0 (by simp)
      change (∀ i ∈ q.inputs, i < m+0) ∧ q.op.eval (q.inputs.map v) = v (m+0) at head
      simp only [Nat.add_zero] at head
      have vals : q.inputs.map (fun i => ((List.range m).map v).getD i false) = q.inputs.map v := by
        refine List.map_congr_left fun i hi => ?_
        have bound := head.1 i hi
        rw [List.getD_eq_getElem _ _ (by simpa using bound)]
        simp
      have eq : ev ((List.range m).map v) q = (List.range (m+1)).map v := by
        simp only [ev, vals, head.2, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [List.foldl_cons,eq,ih (m+1)]
      · congr 2; simp; omega
      · intro j hj
        have a := h (j+1) (by simp [hj])
        simpa [Nat.add_assoc, Nat.add_comm 1] using a
  have replay (x : Fin 26 → Bool) (k : ℕ) (hx : ∀ i, x i = (col i).testBit k) :
      circuitFun 26 C x = mask.testBit k := by
    let v (i : ℕ) := (w i).testBit k
    have init : List.ofFn x = (List.range 26).map v := by
      apply List.ext_getElem
      · simp
      · intro i hi hj
        rw [List.getElem_ofFn]
        simp only [List.getElem_map,List.getElem_range]
        change x _ = (w i).testBit k
        rw [hx,base ⟨i,by simpa using hi⟩]
    have rules (j : ℕ) (hj : j < C.gates.length) :
        (∀ i ∈ C.gates[j].inputs, i < 26+j) ∧
        C.gates[j].op.eval (C.gates[j].inputs.map v) = v (26+j) := by
      rw [gateEq]
      exact ⟨(spec _).2.2.1,(spec _).2.2.2 k⟩
    change (C.gates.foldl ev (List.ofFn x)).getD 88 false = _
    rw [init,run _ _ _ rules,List.getD_eq_getElem _ _ (by simp [C])]
    simpa [v] using congrArg (fun z : ℕ => z.testBit k) output
  let pidx (a b : Fin 13) := 13*(if a-b=0 then 0 else if a-b=1 then 1 else if a-b=3 then 2 else 3) + b.val
  let nidx (s : Fin 8) (a : Fin 3) (b : Fin 13) (c : Bool) :=
    13*(4+2*(s.val*3+a.val)+c.toNat) +
      (-(if a.val = 0 then b else if a.val = 1 then 9*b else 3*b) : Fin 13).val
  have pos : ∀ (a b : Fin 13), a-b ∈ D →
      (∀ i : Fin 26, decide (i = Fin.castAdd 13 a ∨ i = Fin.natAdd 13 b) =
        (col i).testBit (pidx a b)) ∧ mask.testBit (pidx a b) = true := by decide +kernel
  have neg : ∀ (s : Fin 8) (a : Fin 3) (b : Fin 13) (c : Bool),
      (∀ i : Fin 26, row (seeds.get s) (scales.get a) b c i =
        (col i).testBit (nidx s a b c)) ∧ mask.testBit (nidx s a b c) = false := by decide +kernel
  refine ⟨C,syntaxOk,?_,?_,?_⟩
  · change (List.ofFn g).length ≤ 63
    simp
  · intro a b h
    exact (replay _ _ (pos a b h).1).trans (pos a b h).2
  · intro s hs a ha b c
    change s ∈ seeds at hs
    change a ∈ scales at ha
    obtain ⟨si,rfl⟩ := List.mem_iff_get.mp hs
    obtain ⟨ai,rfl⟩ := List.mem_iff_get.mp ha
    exact (replay _ _ (neg si ai b c).1).trans (neg si ai b c).2
