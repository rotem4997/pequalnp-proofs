import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Both final arguments must be distinct intermediate gates.
-- Each has an input on which the other contributes false.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3869_481
    (short : ∀ C : Circuit, FanInTwo C → C.size ≤ 14 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ (([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (ℕ × ℕ)).any (fun e => x (Fin.ofNat 9 e.1) && x (Fin.ofNat 9 e.2))))
    (core : ∀ (gs : List Gate) (a b : ℕ),
      gs.length = 13 → FanInTwo (⟨gs, 0⟩ : Circuit) →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 →
      10 ≤ a → a < b → b ≤ 22 →
      (∀ w ∈ ([0, 3] : List ℕ),
        let count := gs.countP (fun g => g.op.eval [false] && g.inputs.head? == some w ||
          !g.op.eval [false] && g.inputs.contains w)
        1 ≤ count ∧ count ≤ 2) →
      let value := fun (i : ℕ) (x : Fin 9 → Bool) =>
        (⟨gs, i⟩ : Circuit).eval (List.ofFn x ++ [x 0 || x 3])
      (∃ x, value a x = true ∧ value b x = false) →
      (∃ x, value b x = true ∧ value a x = false) →
      ∃ x : Fin 9 → Bool, (value a x || value b x) ≠ (([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (ℕ × ℕ)).any (fun e => x (Fin.ofNat 9 e.1) && x (Fin.ofNat 9 e.2)))) :
  ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             (∀ x9 ∈ [(0 : ℕ), (3 : ℕ)],                 have x11 : ℕ := List.countP (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.false] && x11.inputs.head? == Option.some x9 || !x11.op.eval [Bool.false] && x11.inputs.contains x9) (x1 ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate }]);                 (1 : ℕ) ≤ x11 ∧ x11 ≤ (2 : ℕ)) →               ∃ (x10 : Fin (9 : ℕ) → Bool),                 have x11 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]);                 (x11.getD x2 Bool.false || x11.getD x3 Bool.false) ≠ (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  intro gs a b hlength hfan hnot _ha _hb hread
  by_contra absent
  let F (x : Fin 9 → Bool) := (([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (ℕ × ℕ)).any (fun e => x (Fin.ofNat 9 e.1) && x (Fin.ofNat 9 e.2)))
  have truth (x : Fin 9 → Bool) :
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) = F x := by
    simp [F, List.any_cons, List.any_nil, Bool.or_assoc] <;> rfl
  let start (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 3]
  let wires (x : Fin 9 → Bool) := (⟨gs, 0⟩ : Circuit).wires (start x)
  let value (w : ℕ) (x : Fin 9 → Bool) := (wires x).getD w false
  have agrees (x : Fin 9 → Bool) : (value a x || value b x) = F x := by
    by_contra bad
    apply absent
    refine ⟨x, ?_⟩
    dsimp only
    intro original
    exact bad (original.trans (truth x))
  let step (xs : List Bool) (g : Gate) :=
    xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]
  have foldLength (gates : List Gate) (xs : List Bool) :
      (gates.foldl step xs).length = xs.length + gates.length := by
    induction gates generalizing xs with
    | nil => simp
    | cons g rest ih =>
        rw [List.foldl_cons, ih]
        simp [step, Nat.add_comm, Nat.add_left_comm]
  have earlier (gates : List Gate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
      (gates.foldl step xs).getD w false = xs.getD w false := by
    induction gates generalizing xs with
    | nil => rfl
    | cons g rest ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hw
  have wireLength (x : Fin 9 → Bool) : (wires x).length = 23 := by
    change (gs.foldl step (start x)).length = 23
    rw [foldLength]
    simp [start, hlength]
  have readInput {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
      (List.ofFn x).getD i.val false = x i := by
    simp [List.getD_eq_getElem?_getD]
  have primary (x : Fin 9 → Bool) (w : ℕ) (hw : w < 9) :
      value w x = x ⟨w, hw⟩ := by
    change (gs.foldl step (start x)).getD w false = _
    rw [earlier _ _ _ (by simp [start]; omega)]
    dsimp only [start]
    rw [List.getD_append _ _ _ _ (by simpa using hw)]
    exact readInput x ⟨w, hw⟩
  have seeded (x : Fin 9 → Bool) : value 9 x = (x 0 || x 3) := by
    change (gs.foldl step (start x)).getD 9 false = _
    rw [earlier _ _ _ (by simp [start])]
    simp [start, List.getD_eq_getElem?_getD]
  have singletonFalse : ∀ p : Fin 9, F (fun i => decide (i = p)) = false := by decide
  have smallWitness (w : ℕ) (hw : w < 10) :
      ∃ x : Fin 9 → Bool, value w x = true ∧ F x = false := by
    by_cases primaryInput : w < 9
    · let p : Fin 9 := ⟨w, primaryInput⟩
      exact ⟨fun i => decide (i = p),
        (primary _ _ primaryInput).trans (by simp [p]), singletonFalse p⟩
    · have h9 : w = 9 := by omega
      subst w
      refine ⟨fun i => decide (i = 0), ?_, singletonFalse 0⟩
      rw [seeded]
      decide
  have aLow : 10 ≤ a := by
    by_contra! small
    obtain ⟨x, hvalue, hfalse⟩ := smallWitness a small
    exact Bool.false_ne_true (by simpa only [hvalue, hfalse, Bool.true_or] using (agrees x).symm)
  have bLow : 10 ≤ b := by
    by_contra! small
    obtain ⟨x, hvalue, hfalse⟩ := smallWitness b small
    exact Bool.false_ne_true (by simpa only [hvalue, hfalse, Bool.or_true] using (agrees x).symm)
  have cannotAlias (w : ℕ) (agree : ∀ x : Fin 9 → Bool, value w x = F x) : False := by
    let seed : Gate := ⟨.or, [0, 3]⟩
    let C : Circuit := ⟨seed :: gs, w⟩
    have fan : FanInTwo C := by
      intro g hg
      change g ∈ seed :: gs at hg
      rcases List.mem_cons.mp hg with rfl | h
      · simp [seed]
      · exact hfan g h
    have size : C.size ≤ 14 := by
      change (seed :: gs).length ≤ 14
      simp [hlength]
    obtain ⟨x, bad⟩ := short C fan size
    have stepSeed : step (List.ofFn x) seed = start x := by
      change (List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 0 false,
        (List.ofFn x).getD 3 false]]) = start x
      rw [show (List.ofFn x).getD 0 false = x 0 from readInput x 0,
        show (List.ofFn x).getD 3 false = x 3 from readInput x 3]
      change List.ofFn x ++ [x 0 || (x 3 || false)] = start x
      simp only [Bool.or_false, start]
    have equal : C.eval (List.ofFn x) = value w x := by
      change (gs.foldl step (step (List.ofFn x) seed)).getD w false = _
      rw [stepSeed]
      rfl
    exact bad (equal.trans (agree x))
  have aHigh : a ≤ 22 := by
    by_contra! large
    apply cannotAlias b
    intro x
    have off : value a x = false := List.getD_eq_default _ _ (by rw [wireLength]; omega)
    simpa only [off, Bool.false_or] using agrees x
  have bHigh : b ≤ 22 := by
    by_contra! large
    apply cannotAlias a
    intro x
    have off : value b x = false := List.getD_eq_default _ _ (by rw [wireLength]; omega)
    simpa only [off, Bool.or_false] using agrees x
  have exclusive (u v : ℕ) (h : ∀ x, (value u x || value v x) = F x) :
      ∃ x : Fin 9 → Bool, value u x = true ∧ value v x = false := by
    by_contra no
    apply cannotAlias v
    intro x
    have equal : (value u x || value v x) = value v x := by
      cases hu : value u x <;> cases hv : value v x <;> try rfl
      exact (no ⟨x, hu, hv⟩).elim
    exact equal.symm.trans (h x)
  have reverse (x : Fin 9 → Bool) : (value b x || value a x) = F x := by
    rw [Bool.or_comm]
    exact agrees x
  have one := exclusive a b agrees
  have other := exclusive b a reverse
  have different : a ≠ b := by
    rintro rfl
    obtain ⟨x, yes, notYes⟩ := one
    rw [yes] at notYes
    contradiction
  have simpleCount (u : ℕ) (asInput : u ∈ ([0, 3] : List ℕ)) :
      let count := gs.countP (fun g => g.op.eval [false] && g.inputs.head? == some u ||
        !g.op.eval [false] && g.inputs.contains u)
      1 ≤ count ∧ count ≤ 2 := by
    have low : u < 10 := by
      rcases List.mem_cons.mp asInput with rfl | rest
      · decide
      · have hthree : u = 3 := by simpa using rest
        omega
    have neqA : a ≠ u := by omega
    have neqB : b ≠ u := by omega
    have raw := hread u asInput
    dsimp only at raw ⊢
    rw [List.countP_append] at raw
    have nilCount : ([⟨.or, [a, b]⟩] : List Gate).countP
        (fun g => g.op.eval [false] && g.inputs.head? == some u ||
          !g.op.eval [false] && g.inputs.contains u) = 0 := by
      change (if ([a,b] : List ℕ).contains u then 1 else 0) = 0
      have absentInput : ([a,b] : List ℕ).contains u = false := by
        simp [Ne.symm neqA, Ne.symm neqB]
      simp only [absentInput, Bool.false_eq_true, ite_false]
    rw [nilCount, Nat.add_zero] at raw
    exact raw
  rcases lt_or_gt_of_ne different with ordered | reversed
  · obtain ⟨x, bad⟩ := core gs a b hlength hfan hnot aLow ordered bHigh simpleCount one other
    exact bad (agrees x)
  · obtain ⟨x, bad⟩ := core gs b a hlength hfan hnot bLow reversed aHigh simpleCount other one
    exact bad (reverse x)
