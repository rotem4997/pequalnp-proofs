import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

-- Two distinct maximal negative inputs have different AND-operand signatures since
-- their union contains an edge. The 24 signatures rule out four or fewer ANDs.
-- The first search budget allows arbitrarily many ORs. The second has at most 14.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4065_24
    (few :
      let N : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
      let P : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768]
      let a := fun (C : Circuit) j => (gateAt C j).op = GateOp.and
      let k := fun (C : Circuit) j =>
        ∀ r ∈ N, gateVal 11 C j (fun i => r.testBit i.val) = false
      let c := InCone 11
      ∀ (C : Circuit) (p q : ℕ),
        IsAO2 11 C → 5 ≤ PEqualNP.ReadTwo.nAnd C → PEqualNP.ReadTwo.nAnd C ≤ 6 → p < q → q < C.size → a C p → a C q →
        (∀ i < C.size, a C i → (k C i ↔ i ≠ p ∧ i ≠ q)) →
        (∀ i < C.size, a C i → k C i → ∀ j < C.size, a C j → ¬ c C i j) →
        ¬ c C p q → ¬ c C q p →
        (∃ j < C.size, a C j ∧ k C j ∧ c C p j ∧ c C q j) →
        (∀ r ∈ P, circuitFun 11 C (fun i => r.testBit i.val) = true) →
        (∀ r ∈ N, circuitFun 11 C (fun i => r.testBit i.val) = false) →
        False)
    (many :
      let N : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
      let P : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768]
      let a := fun (C : Circuit) j => (gateAt C j).op = GateOp.and
      let k := fun (C : Circuit) j =>
        ∀ r ∈ N, gateVal 11 C j (fun i => r.testBit i.val) = false
      let c := InCone 11
      ∀ (C : Circuit) (p q : ℕ),
        IsAO2 11 C → C.size ≤ 21 → 7 ≤ PEqualNP.ReadTwo.nAnd C → PEqualNP.ReadTwo.nOr C ≤ 14 → p < q → q < C.size → a C p → a C q →
        (∀ i < C.size, a C i → (k C i ↔ i ≠ p ∧ i ≠ q)) →
        (∀ i < C.size, a C i → k C i → ∀ j < C.size, a C j → ¬ c C i j) →
        ¬ c C p q → ¬ c C q p →
        (∃ j < C.size, a C j ∧ k C j ∧ c C p j ∧ c C q j) →
        (∀ r ∈ P, circuitFun 11 C (fun i => r.testBit i.val) = true) →
        (∀ r ∈ N, circuitFun 11 C (fun i => r.testBit i.val) = false) →
        False) :
    have x1 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)]; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => ∀ x6 ∈ x1, (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x4 x5 fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false; have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 → x6.size ≤ (21 : ℕ) → x7 < x8 → x8 < x6.size → x3 x6 x7 → x3 x6 x8 → (∀ x15 < x6.size, x3 x6 x15 → (x4 x6 x15 ↔ x15 ≠ x7 ∧ x15 ≠ x8)) → (∀ x16 < x6.size, x3 x6 x16 → x4 x6 x16 → ∀ x20 < x6.size, x3 x6 x20 → ¬x5 x6 x16 x20) → ¬x5 x6 x7 x8 → ¬x5 x6 x8 x7 → (∃ x19 < x6.size, x3 x6 x19 ∧ x4 x6 x19 ∧ x5 x6 x7 x19 ∧ x5 x6 x8 x19) → (∀ x20 ∈ x2, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x22 : Fin (11 : ℕ)) => x20.testBit ↑x22) = Bool.true) → (∀ x21 ∈ x1, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x23 : Fin (11 : ℕ)) => x21.testBit ↑x23) = Bool.false) → False := by
  have separation (N P : List ℕ) (big : 17 ≤ N.toFinset.card)
      (pairCover : ∀ s ∈ N, ∀ t ∈ N, s ≠ t → ∃ e ∈ P, ∀ i : Fin 11, e.testBit i.val ≤ (s.testBit i.val || t.testBit i.val))
      (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 11 C)
      (pos : ∀ e ∈ P, circuitFun 11 C (fun i => e.testBit i.val) = true)
      (neg : ∀ e ∈ N, circuitFun 11 C (fun i => e.testBit i.val) = false) : 5 ≤ PEqualNP.ReadTwo.nAnd C := by
    clear few many
    classical
    letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let sig := fun (gs : List Gate) => List.rec (motive := fun _ => List Bool → List Bool)
      (fun _ => []) (fun g _ rest w => if g.op = .and then
        w.getD (g.inputs.headD 0) false :: rest (step w g) else rest (step w g)) gs
    have lengths (gs : List Gate) (w : List Bool) : (sig gs w).length =
        (gs.filter (fun g => decide (g.op = .and))).length := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        change (if g.op = .and then _ :: sig gs (step w g) else sig gs (step w g)).length = _
        by_cases h : g.op = .and <;> simp [h,ih]
    have cross (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
        (u v w : List Bool) (luv : u.length = v.length) (luw : u.length = w.length)
        (h : ∀ i, u.getD i false ≤ (v.getD i false || w.getD i false))
        (hs : sig gs v = sig gs w) :
        ∀ i, (gs.foldl step u).getD i false ≤
          ((gs.foldl step v).getD i false || (gs.foldl step w).getD i false) := by
      induction gs generalizing u v w with
      | nil => exact h
      | cons g gs ih =>
        obtain ⟨hop,hg2⟩ := hg g List.mem_cons_self
        obtain ⟨a,b,hpair⟩ := List.length_eq_two.mp hg2
        have ht : sig gs (step v g) = sig gs (step w g) := by
          rcases hop with ho | ho
          · exact (List.cons.inj (by simpa [sig,ho] using hs :
              v.getD (g.inputs.headD 0) false :: sig gs (step v g) =
              w.getD (g.inputs.headD 0) false :: sig gs (step w g))).2
          · simpa [sig,ho] using hs
        apply ih (fun k hk => hg k (List.mem_cons_of_mem _ hk)) _ _ _
          (by simp [step,luv]) (by simp [step,luw]) _ ht
        intro i
        by_cases hi : i < u.length
        · unfold step
          rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega)]
          exact h i
        by_cases he : i = u.length
        · unfold step
          rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega),← luv,← luw,he,Nat.sub_self]
          simp only [List.getD_cons_zero,hpair,List.map_cons,List.map_nil]
          rcases hop with ho | ho
          · have hh : v.getD a false = w.getD a false := by
              have eq : v.getD a false :: sig gs (step v g) = w.getD a false :: sig gs (step w g) := by
                simpa [sig,ho,hpair] using hs
              exact (List.cons.inj eq).1
            rw [ho]
            change (_ && (_ && true)) ≤ ((_ && (_ && true)) || (_ && (_ && true)))
            simp only [Bool.and_true]
            have algebra : ∀ a b c d e f : Bool, a ≤ (c || e) → b ≤ (d || f) → c=e →
                (a && b) ≤ ((c && d) || (e && f)) := by decide
            exact algebra _ _ _ _ _ _ (h a) (h b) hh
          · rw [ho]
            change (_ || (_ || false)) ≤ ((_ || (_ || false)) || (_ || (_ || false)))
            simp only [Bool.or_false]
            have algebra : ∀ a b c d e f : Bool, a ≤ (c || e) → b ≤ (d || f) →
                (a || b) ≤ ((c || d) || (e || f)) := by decide
            exact algebra _ _ _ _ _ _ (h a) (h b)
        · rw [List.getD_eq_default _ _ (by simp [step]; omega)]
          exact bot_le
    let input := fun (s : ℕ) => List.ofFn (fun i : Fin 11 => s.testBit i.val)
    let codes := fun (s : ↥N.toFinset) (i : Fin (PEqualNP.ReadTwo.nAnd C)) =>
      (sig C.gates (input s.val)).getD i.val false
    have lengthC (s : ℕ) : (sig C.gates (input s)).length = PEqualNP.ReadTwo.nAnd C := by exact lengths C.gates (input s)
    have inj : Function.Injective codes := by
      intro s t eq
      by_contra ne
      have st : s.val ≠ t.val := fun e => ne (Subtype.ext e)
      obtain ⟨e,hep,hcover⟩ := pairCover s.val (List.mem_toFinset.mp s.property) t.val (List.mem_toFinset.mp t.property) st
      have hsig : sig C.gates (input s.val) = sig C.gates (input t.val) := by
        apply List.ext_getElem (by rw [lengthC,lengthC])
        intro i hi hj
        have hh := congrFun eq (⟨i, by rwa [lengthC] at hi⟩ : Fin (PEqualNP.ReadTwo.nAnd C))
        change (sig C.gates (input s.val)).getD i false = (sig C.gates (input t.val)).getD i false at hh
        simpa only [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] using hh
      have base (i : ℕ) : (input e).getD i false ≤ ((input s.val).getD i false || (input t.val).getD i false) := by
        by_cases hi : i < 11
        · have get (r : ℕ) : (input r).getD i false = r.testBit i := by
            unfold input
            rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi),List.getElem_ofFn]
          rw [get,get,get]
          exact hcover ⟨i,hi⟩
        · rw [List.getD_eq_default _ _ (by simp [input]; omega)]
          exact bot_le
      have hh := cross C.gates (fun g hg => ⟨hAO.1 g hg,hAO.2.2 g hg⟩) (input e) (input s.val) (input t.val)
        (by simp [input]) (by simp [input]) base hsig C.output
      change circuitFun 11 C (fun i => e.testBit i.val) ≤
        (circuitFun 11 C (fun i => s.val.testBit i.val) || circuitFun 11 C (fun i => t.val.testBit i.val)) at hh
      rw [pos e hep,neg s.val (List.mem_toFinset.mp s.property),neg t.val (List.mem_toFinset.mp t.property)] at hh
      contradiction
    have hc := Fintype.card_le_of_injective codes inj
    rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Fintype.card_coe] at hc
    by_contra! hlt
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show PEqualNP.ReadTwo.nAnd C ≤ 4 by omega)
    omega
  let N : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
  let P : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
  dsimp only
  intro C p q hAO budget hpq hq ap aq quiet top npq nqp share pos neg
  have big : 17 ≤ N.toFinset.card := by decide +kernel
  have masks : ∀ s ∈ N, ∀ t ∈ N, s ≠ t → ∃ e ∈ P, e &&& (s ||| t) = e := by
    have check : N.all (fun s => N.all (fun t => s == t || P.any (fun e => (e &&& (s ||| t)) == e))) = true := by decide +kernel
    intro s hs t ht hne
    have h := List.all_eq_true.1 (List.all_eq_true.1 check s hs) t ht
    simpa [hne,List.any_eq_true] using h
  have pairCover : ∀ s ∈ N, ∀ t ∈ N, s ≠ t → ∃ e ∈ P, ∀ i : Fin 11, e.testBit i.val ≤ (s.testBit i.val || t.testBit i.val) := by
    intro s hs t ht hne
    obtain ⟨e,he,inc⟩ := masks s hs t ht hne
    refine ⟨e,he,fun i => ?_⟩
    have hb := congrArg (fun n : ℕ => n.testBit i.val) inc
    simp only [Nat.testBit_and,Nat.testBit_or] at hb
    exact (show ∀ a b : Bool, (a && b) = a → a ≤ b by decide) _ _ hb
  have five := separation N P big pairCover C hAO pos neg
  by_cases low : PEqualNP.ReadTwo.nAnd C ≤ 6
  · exact few C p q hAO five low hpq hq ap aq quiet top npq nqp share pos neg
  · have both (gs : List Gate) (hk : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
        PEqualNP.ReadTwo.nOr ⟨gs,0⟩ + PEqualNP.ReadTwo.nAnd ⟨gs,0⟩ = gs.length := by
      letI : DecidableEq GateOp := gateOpDecEq
      change (gs.filter (fun g => decide (g.op = .or))).length +
        (gs.filter (fun g => decide (g.op = .and))).length = gs.length
      induction gs with
      | nil => rfl
      | cons g gs ih =>
        have h := ih (fun k hm => hk k (List.mem_cons_of_mem _ hm))
        rcases hk g List.mem_cons_self with hg | hg <;> simp [hg] <;> omega
    have total : PEqualNP.ReadTwo.nOr C + PEqualNP.ReadTwo.nAnd C = C.size := both C.gates hAO.1
    exact many C p q hAO budget (by omega) (by omega) hpq hq ap aq quiet top npq nqp share pos neg
