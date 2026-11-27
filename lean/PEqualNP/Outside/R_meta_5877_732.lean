import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership PEqualNP.ReadTwo

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_5877_732
    (specializeFlag : ∀ (C : Circuit) (p l : Fin 42) (ρ : Fin 42 → Fin 32),
      let e (i j : Fin 42) := decide (i.val < 21 ∧ 21 ≤ j.val ∧
        (j.val + 21 - i.val) % 21 ∈ ([0,5,7,17,20] : List Nat))
      let cut (i : Fin 42) := e i l || e p i
      let flag (i : Fin 42) := cut i && decide (i ≠ p ∧ i ≠ l)
      Monotone2 C → C.size ≤ 124 → e p l = true →
      (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ a b, e a b = true ∧ x a = true ∧ x b = true) →
      (∃ j, isAnd C j ∧ gateVal 42 C j flag = true) →
      33 ≤ ((Finset.range C.size).filter (fun j =>
        ((C.gates[j]?.map (fun g => GateOp.rec false true false (fun _ => false) false g.op)).getD false &&
        !gateVal 42 C j flag) = true)).card →
      ∃ D : Circuit, Monotone2 D ∧ D.size + 46 ≤ C.size ∧
        ∀ x : Fin 32 → Bool, D.eval (List.ofFn x) =
          C.eval (List.ofFn (fun i => if cut i then false else x (ρ i))))
    (coreBound : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 32 → Bool, D.eval (List.ofFn x) = true ↔ ∃ a b : Fin 32,
        (a.val < 16 ∧ 16 ≤ b.val ∧ (([195,32908,281,562,1124,2464,12608,25216,34560,19457,38914,4613,9226,10260,20520,49232] : List Nat).getD a.val 0).testBit (b.val-16) = true) ∧
        x a = true ∧ x b = true) → 79 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (124 : ℕ) →       (∀ (x4 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) →         have x5 : List ℕ := [(693637218693 : ℕ), (214750724172 : ℕ), (43100670213 : ℕ), (2201724715076 : ℕ), (429513539622 : ℕ), (10838245382 : ℕ), (1718003696225 : ℕ), (1387274437386 : ℕ), (3436007392450 : ℕ), (214756769811 : ℕ), (412337856832 : ℕ), (3436108316976 : ℕ), (154640061441 : ℕ), (1168315262978 : ℕ)];         have x6 : ℕ → Fin (42 : ℕ) → Bool := fun (x6 : ℕ) (x7 : Fin (42 : ℕ)) => x6.testBit ↑x7;         have x7 : (Fin (42 : ℕ) → Bool) → Prop := fun (x7 : Fin (42 : ℕ) → Bool) => ∃ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x8]? = Option.some x9 ∧ x9.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn x7)).getD ((42 : ℕ) + x8) Bool.false = Bool.true;         have x8 : ℕ → Finset ℕ := fun (x8 : ℕ) => {x9 ∈ Finset.range x1.size | ((Option.map (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x11 : ℕ) => Bool.false) Bool.false x10.op) x1.gates[x9]?).getD Bool.false && !(x1.wires (List.ofFn (x6 x8))).getD ((42 : ℕ) + x9) Bool.false) = Bool.true};         (x7 fun (x9 : Fin (42 : ℕ)) => Decidable.decide (↑x9 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)])) → ((∃ x10 ∈ x5, x7 (x6 x10)) ∧ ∀ x10 ∈ x5, (33 : ℕ) ≤ (x8 x10).card) → False := by
  intro C mono small correct ms word hit silent _ more
  obtain ⟨⟨m,hm,active⟩,off⟩ := more
  let e (i j : Fin 42) := decide (i.val < 21 ∧ 21 ≤ j.val ∧
    (j.val+21-i.val)%21 ∈ ([0,5,7,17,20] : List Nat))
  let masks : List Nat := [693637218693,214750724172,43100670213,2201724715076,429513539622,10838245382,1718003696225,1387274437386,3436007392450,214756769811,412337856832,3436108316976,154640061441,1168315262978]
  let centers : List (Fin 42 × Fin 42) := [(11,28),(16,23),(7,28),(3,23),(17,22),(5,22),(19,26),(12,29),(20,27),(16,21),(17,34),(20,25),(17,38),(19,39)]
  let p (t : Fin 14) := (centers.getD t.val (0,0)).1
  let l (t : Fin 14) := (centers.getD t.val (0,0)).2
  let cut (t : Fin 14) (i : Fin 42) := e i (l t) || e (p t) i
  let flag (t : Fin 14) (i : Fin 42) := cut t i && decide (i ≠ p t ∧ i ≠ l t)
  let packRows : List (List (Fin 32)) := [[0,0,0,1,2,3,4,0,0,5,6,0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,0,23,24,0,0,25,26,27,28,0,29,0,30,31],[0,14,0,0,13,15,0,12,3,4,1,10,5,11,8,9,0,7,0,6,2,0,30,0,29,20,22,19,17,21,18,31,27,0,25,26,0,0,23,28,24,16],[0,1,0,14,13,5,6,0,0,2,3,0,12,15,4,7,11,0,10,8,9,18,23,28,0,27,24,0,0,19,20,21,29,0,22,0,25,16,17,31,26,30],[7,14,0,0,15,6,0,5,0,13,3,1,8,2,9,10,0,11,0,12,4,30,28,0,0,22,29,21,23,0,20,0,31,24,16,27,17,18,25,19,26,0],[14,0,0,9,6,0,2,3,4,12,13,5,8,7,10,0,11,0,0,1,15,28,0,16,0,22,19,20,21,26,29,27,24,25,0,17,18,0,0,23,31,30],[8,0,0,12,7,0,0,6,2,14,15,5,1,9,11,0,3,0,10,13,4,25,0,17,29,0,0,22,24,19,30,0,23,0,16,28,20,21,31,27,18,26],[0,14,10,5,15,0,0,12,3,0,1,0,4,8,7,6,9,11,13,0,2,30,28,27,0,20,0,19,17,21,31,23,22,26,25,29,0,16,18,0,0,24],[15,0,0,0,1,2,3,4,0,0,5,6,0,7,8,9,10,11,12,13,14,31,16,17,18,19,20,21,22,0,23,24,0,0,25,26,27,28,0,29,0,30],[2,0,14,10,5,15,0,0,12,3,0,1,0,4,8,7,6,9,11,13,0,24,30,28,27,0,20,0,19,17,21,31,23,22,26,25,29,0,16,18,0,0],[0,0,13,14,0,2,0,7,6,11,1,12,10,4,0,3,0,15,8,9,5,0,20,0,30,24,16,23,29,28,18,19,17,0,22,25,0,0,31,26,27,21],[7,3,1,15,11,6,0,5,0,13,4,0,2,0,0,9,8,0,10,12,14,25,0,31,0,28,29,21,23,20,18,22,16,24,0,27,26,0,0,17,19,30],[4,11,3,2,0,0,15,5,0,0,12,14,9,10,1,7,13,8,0,6,0,18,25,20,24,0,22,0,21,16,17,19,30,27,31,23,29,0,26,28,0,0],[0,14,13,4,10,0,1,2,3,5,0,15,0,9,6,8,11,0,0,7,12,28,0,18,0,17,23,19,20,21,27,22,31,16,0,24,25,0,0,30,29,26],[15,0,14,6,1,5,11,9,7,12,2,0,13,0,8,4,10,3,0,0,0,31,21,28,0,23,0,16,30,29,19,24,18,27,25,26,0,17,20,0,0,22]]
  let unpackRows : List (List (Fin 42)) := [[1,3,4,5,6,9,10,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,29,30,33,34,35,36,38,40,41],[0,10,20,8,9,12,19,17,14,15,11,13,7,4,1,5,41,28,30,27,25,29,26,38,40,34,35,32,39,24,22,31],[17,1,9,10,14,5,6,15,19,20,18,16,12,4,3,13,37,38,21,29,30,31,34,22,26,36,40,25,23,32,41,39],[8,11,13,10,20,7,5,0,12,14,15,17,19,9,1,4,34,36,37,39,30,27,25,28,33,38,40,35,22,26,21,32],[18,19,6,7,8,11,4,13,12,3,14,16,9,10,0,20,23,35,36,26,27,28,25,39,32,33,29,31,21,30,41,40],[6,12,8,16,20,11,7,4,0,13,18,14,3,19,9,10,34,23,40,29,36,37,27,32,28,21,41,39,35,24,30,38],[11,10,20,8,12,3,15,14,13,16,2,17,7,18,1,4,37,28,38,27,25,29,32,31,41,34,33,23,22,35,21,30],[2,4,5,6,7,10,11,13,14,15,16,17,18,19,20,0,22,23,24,25,26,27,28,30,31,34,35,36,37,39,41,21],[12,11,0,9,13,4,16,15,14,17,3,18,8,19,2,5,38,29,39,28,26,30,33,32,21,35,34,24,23,36,22,31],[6,10,5,15,13,20,8,7,18,19,12,9,11,2,3,17,26,32,30,31,22,41,34,27,25,35,39,40,29,28,24,38],[11,2,12,1,10,7,5,0,16,15,18,4,19,9,20,3,32,39,30,40,29,27,31,28,33,21,36,35,25,26,41,23],[9,14,3,2,0,7,19,15,17,12,13,1,10,16,11,6,29,30,21,31,23,28,26,35,24,22,38,33,39,36,32,34],[5,6,7,8,3,9,14,19,15,13,4,16,20,2,1,11,33,25,23,27,28,29,31,26,35,36,41,30,21,40,39,32],[20,4,10,17,15,5,3,8,14,7,16,6,9,12,2,0,27,37,32,30,38,22,41,25,31,34,35,33,23,29,28,21]]
  let pack (t : Fin 14) (i : Fin 42) : Fin 32 := (packRows.getD t.val []).getD i.val 0
  let unpack (t : Fin 14) (i : Fin 32) : Fin 42 := (unpackRows.getD t.val []).getD i.val 0
  let core (a b : Fin 32) := decide (a.val < 16 ∧ 16 ≤ b.val ∧
    (([195,32908,281,562,1124,2464,12608,25216,34560,19457,38914,4613,9226,10260,20520,49232] : List Nat).getD a.val 0).testBit (b.val-16) = true)
  have represented : ∀ m ∈ masks, ∃ t : Fin 14, masks.getD t.val 0 = m := by decide
  obtain ⟨t,ht⟩ := represented m hm
  have inc : ∀ u : Fin 14, e (p u) (l u) = true := by decide
  have samples : ∀ (u : Fin 14) (i : Fin 42), flag u i = (masks.getD u.val 0).testBit i.val := by decide
  have fword : flag t = word m := by
    funext i
    change flag t i = m.testBit i.val
    rw [← ht, samples]
  have live : ∀ (u : Fin 14) (k : Fin 32), cut u (unpack u k) = false := by decide
  have reindex : ∀ (u : Fin 14) (k : Fin 32), pack u (unpack u k) = k := by decide
  have inverse : ∀ (u : Fin 14) (i : Fin 42), cut u i = false → unpack u (pack u i) = i := by decide
  have edges : ∀ (u : Fin 14) (a b : Fin 32), e (unpack u a) (unpack u b) = core a b := by decide
  have computes : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ a b, e a b = true ∧ x a = true ∧ x b = true := by
    intro x
    simpa only [e,decide_eq_true_eq] using correct x
  have fired : ∃ j, isAnd C j ∧ gateVal 42 C j (flag t) = true := by
    obtain ⟨j,g,hg,op,value⟩ := active
    obtain ⟨h,rfl⟩ := List.getElem?_eq_some_iff.mp hg
    refine ⟨j,⟨h,?_⟩,?_⟩
    · change (C.gates.getD j _).op = .and
      rw [List.getD_eq_getElem _ _ h]
      exact op
    · rw [fword]
      exact value
  have quiet := off m hm
  obtain ⟨D,mb,saved,agrees⟩ := specializeFlag C (p t) (l t) (pack t) mono small (inc t) computes fired
    (by change 33 ≤ ((Finset.range C.size).filter (fun j =>
          ((C.gates[j]?.map (fun g => GateOp.rec false true false (fun _ => false) false g.op)).getD false &&
          !gateVal 42 C j (flag t)) = true)).card
        rw [fword]
        exact quiet)
  have lower := coreBound D mb (by
    intro x
    let assign (i : Fin 42) := if cut t i then false else x (pack t i)
    change D.eval (List.ofFn x) = true ↔ ∃ a b, _ ∧ x a = true ∧ x b = true
    rw [show D.eval (List.ofFn x) = C.eval (List.ofFn assign) from agrees x, computes]
    constructor
    · rintro ⟨a,b,edge,ha,hb⟩
      have outside (i : Fin 42) (h : assign i = true) : cut t i = false := by
        cases hv : cut t i
        · rfl
        · simp [assign,hv] at h
      have na := outside a ha
      have nb := outside b hb
      refine ⟨pack t a,pack t b,?_,by simpa [assign,na] using ha,by simpa [assign,nb] using hb⟩
      have v := edges t (pack t a) (pack t b)
      rw [inverse t a na,inverse t b nb,edge] at v
      exact of_decide_eq_true v.symm
    · rintro ⟨a,b,h,ha,hb⟩
      have v : core a b = true := decide_eq_true h
      refine ⟨unpack t a,unpack t b,(edges t a b).trans v,?_,?_⟩
      · simpa [assign,live,reindex] using ha
      · simpa [assign,live,reindex] using hb)
  omega
