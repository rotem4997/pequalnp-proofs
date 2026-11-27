import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

-- The edge codes and comparison with graphFun follow WuChenyu in R_meta_8994_219.
-- The seven truth words represent the terminal six-gate circuits left after positive formula simplification.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_8994_607
    (sixGates : ∀ (n : Nat) (T : Circuit), IsAO2 n T → T.size ≤ 6 → T.output < n+T.size →
      (∃ φ : DMFormula n, φ.leaves ≤ 7 ∧ ∀ x : Fin n → Bool,
        T.eval (List.ofFn x) = (DMFormula.rec (motive := fun _ => Bool) (fun i _ => x i) (fun _ _ a b => a && b) (fun _ _ a b => a || b) φ)) ∨
      ∃ m ∈ ([16909538860378144768,16909539410841305088,16927600263721314816,17213020425657819296,17215830820325998784,17216961118282247904,18374403832151997952] : List Nat), ∃ c : Fin 6 → Fin n, ∀ x : Fin n → Bool,
        T.eval (List.ofFn x) = m.testBit (∑ j : Fin 6, if x (c j) then ([1,2,4,8,16,32] : List Nat).getD j.val 0 else 0))
    (formulaCase : ∀ (v : Fin 11) (P : Circuit), v.val < 4 → IsAO2 10 P → P.size ≤ 12 →
      ∀ φ : DMFormula (10+P.size), φ.leaves ≤ 7 → ∃ x : Fin 10 → Bool,
        let w (i : Fin (10+P.size)) := (P.wires (List.ofFn x)).getD i.val false
        (DMFormula.rec (motive := fun _ => Bool) (fun i _ => w i) (fun _ _ a b => a && b) (fun _ _ a b => a || b) φ) ≠ (let y : Fin 11 → Bool := v.insertNth false x; ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).any (fun t => y (Fin.ofNat 11 (t/11)) && y (Fin.ofNat 11 (t%11)))))
    (exceptionCase : ∀ (v : Fin 11) (P : Circuit), v.val < 4 → IsAO2 10 P → P.size ≤ 12 →
      ∀ m ∈ ([16909538860378144768,16909539410841305088,16927600263721314816,17213020425657819296,17215830820325998784,17216961118282247904,18374403832151997952] : List Nat), ∀ c : Fin 6 → Fin (10+P.size), ∃ x : Fin 10 → Bool,
        m.testBit (∑ j : Fin 6, if (P.wires (List.ofFn x)).getD (c j).val false then ([1,2,4,8,16,32] : List Nat).getD j.val 0 else 0) ≠
          (let y : Fin 11 → Bool := v.insertNth false x; ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).any (fun t => y (Fin.ofNat 11 (t/11)) && y (Fin.ofNat 11 (t%11))))) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (10 : ℕ) x3 → (∀ (x6 : Fin (10 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ (x2.insertNth Bool.false x6)) → (19 : ℕ) ≤ x3.size := by
  intro G v C hv legal correct
  by_contra! small
  let es : List (Fin 11 × Fin 11) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let value (y : Fin 11 → Bool) := ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).any (fun t =>
    y (Fin.ofNat 11 (t/11)) && y (Fin.ofNat 11 (t%11)))
  have adj : ∀ a b : Fin 11, G.Adj a b ↔ (a,b) ∈ es ∨ (b,a) ∈ es := by decide +kernel
  have graph (y : Fin 11 → Bool) : graphFun G ∅ y = value y := by
    have h : graphFun G ∅ y = es.any (fun e => y e.1 && y e.2) := by
      apply Bool.eq_iff_iff.mpr
      delta graphFun
      simp only [Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
        decide_eq_true_eq,List.any_eq_true,Bool.and_eq_true]
      constructor
      · rintro ⟨a,b,h,ha,hb⟩
        rcases (adj a b).mp h with h | h
        · exact ⟨(a,b),h,ha,hb⟩
        · exact ⟨(b,a),h,hb,ha⟩
      · rintro ⟨⟨a,b⟩,h,ha,hb⟩
        exact ⟨a,b,(adj a b).mpr (Or.inl h),ha,hb⟩
    exact h.trans (by rfl)
  let k := C.size-6
  let P : Circuit := ⟨C.gates.take k,0⟩
  let T : Circuit := ⟨C.gates.drop k,C.output⟩
  have kt : k ≤ C.gates.length := Nat.sub_le _ _
  have plen : P.size = k := by
    change (C.gates.take k).length = k
    rw [List.length_take,Nat.min_eq_left kt]
  have tlen : T.size = C.size-k := by
    change (C.gates.drop k).length = C.gates.length-k
    exact List.length_drop
  have kmax : P.size ≤ 12 := by rw [plen]; dsimp [k]; omega
  have tmax : T.size ≤ 6 := by rw [tlen]; dsimp [k]; omega
  have backP : ReadsBack 10 P := by
    intro j hj i hi
    have hjp : j < (C.gates.take k).length := hj
    have hjc : j < C.gates.length := (hjp.trans_le (List.length_take_le _ _)).trans_le kt
    have eq : gateAt P j = gateAt C j := by
      change (C.gates.take k).getD j _ = C.gates.getD j _
      rw [List.getD_eq_getElem _ _ hjp,List.getD_eq_getElem _ _ hjc,List.getElem_take]
    exact legal.2.1 j hjc i (eq ▸ hi)
  have backT : ReadsBack (10+P.size) T := by
    intro j hj i hi
    have hjt : j < (C.gates.drop k).length := hj
    have hjc : k+j < C.gates.length := by rw [List.length_drop] at hjt;omega
    have eq : gateAt T j = gateAt C (k+j) := by
      change (C.gates.drop k).getD j _ = C.gates.getD (k+j) _
      rw [List.getD_eq_getElem _ _ hjt,List.getD_eq_getElem _ _ hjc,List.getElem_drop]
    have h := legal.2.1 (k+j) hjc i (eq ▸ hi)
    rw [plen]
    omega
  have pok : IsAO2 10 P := ⟨fun g hg => legal.1 g (List.mem_of_mem_take hg),backP,
    fun g hg => legal.2.2 g (List.mem_of_mem_take hg)⟩
  have tok : IsAO2 (10+P.size) T := ⟨fun g hg => legal.1 g (List.mem_of_mem_drop hg),backT,
    fun g hg => legal.2.2 g (List.mem_of_mem_drop hg)⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
  have length (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      simp only [step,List.length_append,List.length_cons,List.length_nil]
      omega
  have wiresLen (D : Circuit) (x : Fin 10 → Bool) : (D.wires (List.ofFn x)).length = 10+D.size := by
    change (D.gates.foldl step (List.ofFn x)).length = 10+D.gates.length
    rw [length,List.length_ofFn]
  let bank (x : Fin 10 → Bool) (i : Fin (10+P.size)) := (P.wires (List.ofFn x)).getD i.val false
  have bankEq (x : Fin 10 → Bool) : List.ofFn (bank x) = P.wires (List.ofFn x) := by
    apply List.ext_getElem
    · rw [List.length_ofFn,wiresLen]
    · intro j h1 h2
      rw [List.getElem_ofFn]
      exact List.getD_eq_getElem _ _ h2
  have simulates (x : Fin 10 → Bool) : T.eval (List.ofFn (bank x)) = C.eval (List.ofFn x) := by
    rw [bankEq]
    change ((C.gates.drop k).foldl step ((C.gates.take k).foldl step (List.ofFn x))).getD C.output false = _
    rw [← List.foldl_append,List.take_append_drop]
    rfl
  have trueVal : ∀ i : Fin 11, i.val < 4 → value (i.insertNth false (fun _ => true)) = true := by decide +kernel
  have out : T.output < 10+P.size+T.size := by
    have pos := (correct (fun _ => true)).trans ((graph _).trans (trueVal v hv))
    by_contra! bad
    have tooBig : (C.wires (List.ofFn (fun _ : Fin 10 => true))).length ≤ C.output := by
      rw [wiresLen]
      change 10+P.size+T.size ≤ C.output at bad
      rw [plen,tlen] at bad
      change k ≤ C.size at kt
      omega
    change (C.wires (List.ofFn (fun _ : Fin 10 => true))).getD C.output false = true at pos
    rw [List.getD_eq_default _ _ tooBig] at pos
    contradiction
  have answer (x : Fin 10 → Bool) : T.eval (List.ofFn (bank x)) = value (v.insertNth false x) :=
    (simulates x).trans ((correct x).trans (graph _))
  rcases sixGates _ T tok tmax out with ⟨φ,hφ,h⟩ | ⟨m,hm,c,h⟩
  · obtain ⟨x,hx⟩ := formulaCase v P hv pok kmax φ hφ
    exact hx ((h (bank x)).symm.trans (answer x))
  · obtain ⟨x,hx⟩ := exceptionCase v P hv pok kmax m hm c
    exact hx ((h (bank x)).symm.trans (answer x))
