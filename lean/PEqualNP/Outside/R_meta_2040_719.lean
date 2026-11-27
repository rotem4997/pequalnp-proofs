import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2040_719
    (encode :
      let reads := fun g : Gate =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any
          (fun i => i == 4 || i == 9)
      let uses := fun g : Fin 3 × Fin 25 × Fin 25 =>
        [g.2.1, g.2.2].any (fun i => i.val == 4 || i.val == 9)
      let op := fun i : Fin 3 =>
        if i = 0 then GateOp.and else if i = 1 then GateOp.or else GateOp.not
      ∀ C : Circuit, FanInTwo C → C.size ≤ 14 →
        ∃ (s : List (Fin 3 × Fin 25 × Fin 25)) (o : Fin 25),
          s.length = C.size ∧ s.countP uses = C.gates.countP reads ∧
          ∀ x : List Bool, x.length = 10 →
            (s.foldl (fun w g => w ++
              [(op g.1).eval [w.getD g.2.1.val false, w.getD g.2.2.val false]]) x).getD o.val false =
              C.eval x)
    (search :
      let op := fun i : Fin 3 =>
        if i = 0 then GateOp.and else if i = 1 then GateOp.or else GateOp.not
      ∀ (s : List (Fin 3 × Fin 25 × Fin 25)) (o : Fin 25),
        s.length ≤ 14 →
        s.countP (fun g => [g.2.1, g.2.2].any (fun i => i.val == 4 || i.val == 9)) ≤ 1 →
        ∃ (b : Bool) (x : Fin 8 → Bool),
          let w := [x 0, x 1, x 2, x 3, b, x 4, x 5, x 6, x 7, !b]
          (s.foldl (fun v g => v ++
            [(op g.1).eval [v.getD g.2.1.val false, v.getD g.2.2.val false]]) w).getD o.val false ≠
            (([8,17,26,32,41,50,59,52,61,39] : List ℕ).any
              (fun e => x (Fin.ofNat 8 (e % 8)) && x (Fin.ofNat 8 (e / 8))) ||
              (b && (x 0 || x 3)))) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => x2 == (4 : ℕ) || x2 == (9 : ℕ); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (0 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x2, x3 (4 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (6 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), !x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∀ (x8 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x8) = x3 x8) → ∃ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x9) ≠ (x3 x9 || x9 (0 : Fin (8 : ℕ)) || x9 (3 : Fin (8 : ℕ))) := by
  dsimp only
  intro C hGate hSize hOnce hlo
  obtain ⟨s, o, hLen, hReaders, hEval⟩ := encode C hGate hSize
  obtain ⟨b, x, hbad⟩ := search s o (hLen.trans_le hSize) (hReaders.trans_le hOnce)
  let w := fun b : Bool => [x 0, x 1, x 2, x 3, b, x 4, x 5, x 6, x 7, !b]
  let f := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)
  have htable (y : Fin 8 → Bool) :
      (([8,17,26,32,41,50,59,52,61,39] : List ℕ).any
        (fun e => y (Fin.ofNat 8 (e % 8)) && y (Fin.ofNat 8 (e / 8)))) = f y := by
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    <;> rfl
  dsimp only at hbad
  rw [hEval (w b) (by rfl), htable x] at hbad
  cases b
  · exact False.elim (hbad (by simpa only [Bool.false_and, Bool.or_false] using hlo x))
  · refine ⟨x, ?_⟩
    change C.eval (w true) ≠ (f x || x 0 || x 3)
    simpa only [Bool.true_and, Bool.or_assoc] using hbad
