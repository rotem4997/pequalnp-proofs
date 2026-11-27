import Mathlib.Data.Fin.SuccPred
import PEqualNP.Defs

-- Remove point 9 and line 0, which meet at the removed incidence.
-- The core keeps two reserve wires for the remaining neighbors of these vertices.
-- On an input already accepted by the core, those two wires need no specification.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3773_1
    (findCore :
      let offsets : Finset (Fin 13) := {0, 1, 3, 9}
      let I := fun (p l : Fin 13) => p + l ∈ offsets
      let inside := fun (y : Fin 24 → Bool) =>
        ∃ p l : Fin 12, I ((9 : Fin 13).succAbove p) ((0 : Fin 13).succAbove l) ∧
          y (Fin.castAdd 12 p) = true ∧ y (Fin.natAdd 12 l) = true
      ∃ (D : Circuit) (a b : ℕ), Monotone2 D ∧ D.size ≤ 58 ∧
        D.gates.head? = some ⟨.or, [0, 1]⟩ ∧
        D.output < 24 + D.size ∧ a < 24 + D.size ∧ b < 24 + D.size ∧
        (∀ y : Fin 24 → Bool, D.eval (List.ofFn y) = true ↔ inside y) ∧
        ∀ y : Fin 24 → Bool, D.eval (List.ofFn y) = false →
          (D.wires (List.ofFn y)).getD a false = (y 0 || y 1 || y 3) ∧
          (D.wires (List.ofFn y)).getD b false = (y 15 || y 16 || y 18))
    (insertInputs :
      let rename := fun i : ℕ => if i < 9 then i else if i < 12 then i + 1 else i + 2
      ∀ D : Circuit, Monotone2 D → D.gates.head? = some ⟨.or, [0, 1]⟩ →
        ∃ E : Circuit, Monotone2 E ∧ E.size = D.size ∧ E.gates.head? = some ⟨.or, [0, 1]⟩ ∧
          ∀ (x : Fin 26 → Bool) (i : ℕ),
            let y := fun j : Fin 24 => x (Fin.ofNat 26 (rename j.val))
            (E.wires (List.ofFn x)).getD (rename i) false = (D.wires (List.ofFn y)).getD i false) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∃ (x3 : PEqualNP.CircuitLowerBounds.Gate), x2.gates.head? = Option.some x3 ∧ (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3.inputs = [(0 : ℕ), (13 : ℕ)] ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs ∈ [[(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(2 : ℕ), (13 : ℕ)]])) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 + x4 ∈ x1 → x2.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) x3) (Fin.natAdd (13 : ℕ) x4))) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card ≤ (3 : ℕ) → x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 + x6 ∉ x1)) x5) = Bool.false ∧ x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x6 + x7 ∉ x1)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) x5) = Bool.false := by
  obtain ⟨D, a, b, okD, sizeD, headD, outD, boundA, boundB, evD, reserves⟩ := findCore
  obtain ⟨E, okE, sizeE, headE, transfer⟩ := insertInputs D okD headD
  let I := fun (p l : Fin 13) => p + l ∈ ({0, 1, 3, 9} : Finset (Fin 13))
  let P := fun (x : Fin 26 → Bool) (p : Fin 13) => x (Fin.castAdd 13 p)
  let L := fun (x : Fin 26 → Bool) (l : Fin 13) => x (Fin.natAdd 13 l)
  let rename := fun i : ℕ => if i < 9 then i else if i < 12 then i + 1 else i + 2
  let restrict := fun (x : Fin 26 → Bool) (j : Fin 24) => x (Fin.ofNat 26 (rename j.val))
  have pointAddress : ∀ p : Fin 12,
      Fin.ofNat 26 (rename (Fin.castAdd 12 p).val) =
        Fin.castAdd 13 ((9 : Fin 13).succAbove p) := by decide +kernel
  have lineAddress : ∀ l : Fin 12,
      Fin.ofNat 26 (rename (Fin.natAdd 12 l).val) =
        Fin.natAdd 13 ((0 : Fin 13).succAbove l) := by decide +kernel
  let n := 26 + E.size
  let suffix : List Gate :=
    [⟨.or, [13, rename b]⟩, ⟨.and, [9, n]⟩, ⟨.and, [13, rename a]⟩,
     ⟨.or, [rename D.output, n + 2]⟩, ⟨.or, [n + 3, n + 1]⟩]
  let C : Circuit := ⟨E.gates ++ suffix, n + 4⟩
  have okC : Monotone2 C := by
    intro g hg
    change g ∈ E.gates ++ suffix at hg
    rcases List.mem_append.mp hg with inside | added
    · exact okE g inside
    · simp only [suffix, List.mem_cons, List.not_mem_nil, or_false] at added
      rcases added with rfl | rfl | rfl | rfl | rfl <;> simp
  have sizeC : C.size = D.size + 5 := by
    change (E.gates ++ suffix).length = D.size + 5
    rw [List.length_append]
    change E.size + 5 = D.size + 5
    rw [sizeE]
  have headC : C.gates.head? = some ⟨.or, [0, 1]⟩ := by
    change (E.gates ++ suffix).head? = _
    cases h : E.gates with
    | nil => simp only [h, List.head?_nil, reduceCtorEq] at headE
    | cons g gs =>
      rw [h] at headE
      exact headE
  let run : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len (gs : List Gate) (w : List Bool) : (gs.foldl run w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [run, List.length_append, List.length_cons, List.length_nil]
      omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl run w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (run w g) (by simp [run]; omega)]
      exact List.getD_append _ _ _ _ hi
  have runOr (w : List Bool) (i j : ℕ) :
      run w ⟨.or, [i, j]⟩ = w ++ [w.getD i false || w.getD j false] := by
    change w ++ [w.getD i false || (w.getD j false || false)] = _
    simp only [Bool.or_false]
  have runAnd (w : List Bool) (i j : ℕ) :
      run w ⟨.and, [i, j]⟩ = w ++ [w.getD i false && w.getD j false] := by
    change w ++ [w.getD i false && (w.getD j false && true)] = _
    simp only [Bool.and_true]
  have mappedBound (i : ℕ) (hi : i < 24 + D.size) : rename i < n := by
    dsimp only [rename, n]
    rw [sizeE]
    split
    · omega
    · split <;> omega
  have evC (x : Fin 26 → Bool) :
      let y := restrict x
      let v := D.wires (List.ofFn y)
      C.eval (List.ofFn x) =
        (D.eval (List.ofFn y) || (x 13 && v.getD a false) ||
          (x 9 && (x 13 || v.getD b false))) := by
    let w := E.wires (List.ofFn x)
    let y := restrict x
    have wlen : w.length = n := by
      exact (len E.gates (List.ofFn x)).trans (by simp only [List.length_ofFn, n]; rfl)
    have old (extra : List Bool) (i : ℕ) (hi : i < n) :
        (w ++ extra).getD i false = w.getD i false :=
      List.getD_append _ _ _ _ (by omega)
    have new (extra : List Bool) (k : ℕ) :
        (w ++ extra).getD (n + k) false = extra.getD k false := by
      rw [List.getD_append_right _ _ _ _ (by omega), wlen, Nat.add_sub_cancel_left]
    have firstNew (extra : List Bool) :
        (w ++ extra).getD n false = extra.getD 0 false := by
      simpa only [Nat.add_zero] using new extra 0
    have raw (i : Fin 26) : w.getD i.val false = x i := by
      rw [show w.getD i.val false = (List.ofFn x).getD i.val false from
        keep E.gates (List.ofFn x) i.val (by simpa only [List.length_ofFn] using i.isLt)]
      rw [List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn _
    have raw9 : w.getD 9 false = x 9 := raw 9
    have raw13 : w.getD 13 false = x 13 := raw 13
    have aSim : w.getD (rename a) false = (D.wires (List.ofFn y)).getD a false :=
      transfer x a
    have bSim : w.getD (rename b) false = (D.wires (List.ofFn y)).getD b false :=
      transfer x b
    have outSim : w.getD (rename D.output) false = D.eval (List.ofFn y) :=
      transfer x D.output
    change ((E.gates ++ suffix).foldl run (List.ofFn x)).getD (n + 4) false = _
    rw [List.foldl_append]
    change (suffix.foldl run w).getD (n + 4) false = _
    simp only [suffix, List.foldl_cons, List.foldl_nil, runOr, runAnd,
      List.append_assoc, List.cons_append, List.nil_append,
      old _ 9 (by dsimp [n]; omega), old _ 13 (by dsimp [n]; omega),
      old _ _ (mappedBound a boundA), old _ _ (mappedBound b boundB),
      old _ _ (mappedBound D.output outD),
      firstNew, new, List.getD_cons_zero, List.getD_cons_succ, raw9, raw13, aSim, bSim, outSim]
    rfl
  have throughLine : ∀ p : Fin 13, I p 0 ↔ p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9 := by
    decide +kernel
  have throughPoint : ∀ l : Fin 13, I 9 l ↔ l = 0 ∨ l = 4 ∨ l = 5 ∨ l = 7 := by
    decide +kernel
  have value (x : Fin 26 → Bool) :
      C.eval (List.ofFn x) =
        (D.eval (List.ofFn (restrict x)) || (L x 0 && (P x 0 || P x 1 || P x 3)) ||
          (P x 9 && (L x 0 || (L x 4 || L x 5 || L x 7)))) := by
    let y := restrict x
    rw [evC x]
    change
      (D.eval (List.ofFn y) || (L x 0 && (D.wires (List.ofFn y)).getD a false) ||
          (P x 9 && (L x 0 || (D.wires (List.ofFn y)).getD b false))) =
        (D.eval (List.ofFn y) || (L x 0 && (P x 0 || P x 1 || P x 3)) ||
          (P x 9 && (L x 0 || (L x 4 || L x 5 || L x 7))))
    cases hd : D.eval (List.ofFn y) with
    | false =>
      obtain ⟨ha, hb⟩ := reserves y hd
      rw [ha, hb]
      rfl
    | true => simp only [Bool.true_or]
  have correct (x : Fin 26 → Bool) :
      C.eval (List.ofFn x) = true ↔
        ∃ (p l : Fin 13), I p l ∧ P x p = true ∧ L x l = true := by
    rw [value]
    simp only [Bool.or_eq_true, Bool.and_eq_true, evD, restrict, pointAddress, lineAddress]
    constructor
    · rintro ((⟨p, l, hI, hp, hl⟩ | ⟨hl, (hp | hp) | hp⟩) |
        ⟨hp, hl | (hl | hl) | hl⟩)
      · exact ⟨_, _, hI, hp, hl⟩
      · exact ⟨0, 0, by decide, hp, hl⟩
      · exact ⟨1, 0, by decide, hp, hl⟩
      · exact ⟨3, 0, by decide, hp, hl⟩
      · exact ⟨9, 0, by decide, hp, hl⟩
      · exact ⟨9, 4, by decide, hp, hl⟩
      · exact ⟨9, 5, by decide, hp, hl⟩
      · exact ⟨9, 7, by decide, hp, hl⟩
    · rintro ⟨p, l, hI, hp, hl⟩
      by_cases p9 : p = 9
      · subst p
        refine Or.inr ⟨hp, ?_⟩
        rcases (throughPoint l).mp hI with rfl | rfl | rfl | rfl
        · exact Or.inl hl
        · exact Or.inr (Or.inl (Or.inl hl))
        · exact Or.inr (Or.inl (Or.inr hl))
        · exact Or.inr (Or.inr hl)
      · by_cases l0 : l = 0
        · subst l
          refine Or.inl (Or.inr ⟨hl, ?_⟩)
          rcases (throughLine p).mp hI with rfl | rfl | rfl | bad
          · exact Or.inl (Or.inl hp)
          · exact Or.inl (Or.inr hp)
          · exact Or.inr hp
          · exact (p9 bad).elim
        · obtain ⟨p', hp'⟩ := Fin.exists_succAbove_eq p9
          obtain ⟨l', hl'⟩ := Fin.exists_succAbove_eq l0
          exact Or.inl (Or.inl ⟨p', l',
            by rw [hp', hl']; exact hI, by rw [hp']; exact hp, by rw [hl']; exact hl⟩)
  have pairValue (u v w : Fin 26) :
      PEqualNP.EdgeOwnership.pairInput u v w = decide (w = u ∨ w = v) := rfl
  refine ⟨C, okC, by omega, ⟨⟨.or, [0, 1]⟩, headC, Or.inr ⟨rfl, by simp⟩⟩, ?_, ?_⟩
  · intro p l hit
    apply (correct _).2
    exact ⟨p, l, hit, by simp [P, pairValue],
      by simp [L, pairValue]⟩
  · intro S _
    constructor
    · apply Bool.eq_false_iff.mpr
      intro hit
      obtain ⟨p, l, incident, hp, hl⟩ := (correct _).1 hit
      simp only [P, L, Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq] at hp hl
      exact hl p hp incident
    · apply Bool.eq_false_iff.mpr
      intro hit
      obtain ⟨p, l, incident, hp, hl⟩ := (correct _).1 hit
      simp only [P, L, Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq] at hp hl
      exact hp l hl incident
