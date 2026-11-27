import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves PEqualNP.EdgeOwnership PEqualNP.SharedOr

-- By strong induction on circuit size, sanitize out-of-bounds reads and extra NOT inputs,
-- eliminate dead gates, wire aliases, and constant gates, then apply the automorphism group
-- S_5 of the Petersen graph (as the Kneser graph KG(5, 2)) to normalize the first gate to
-- one of 5 concrete gates: AND(0,1), AND(0,2), OR(0,1), OR(0,2), or NOT(0).
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2373_2
    (firstAndEdge :
      ∀ (D : Circuit) (u v : ℕ),
        let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
          (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
          (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
        let W := fun (x : Fin 10 → Bool) (w : ℕ) => (D.wires (List.ofFn x)).getD w false
        ReadsBack 10 D → D.size ≤ 18 →
        D.gates[0]? = some ⟨.and, [0, 1]⟩ →
        (∀ k < D.size,
          let g := gateAt D k
          (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup) ∨
            (g.op = .not ∧ g.inputs.length = 1)) ∧
          (InOutCone 10 D (10 + k) u ∨ InOutCone 10 D (10 + k) v) ∧
          (∀ p < 10 + k, ∃ x : Fin 10 → Bool, W x (10 + k) ≠ W x p) ∧
          ∀ b : Bool, ∃ x : Fin 10 → Bool, W x (10 + k) = b) →
        (∀ b : Bool, ∃ x : Fin 10 → Bool, W x u = b ∧ W x v = !b) →
        (∀ x, G x = false → W x u = false ∧ W x v = false) →
        ∃ x, G x = true ∧ W x u = false ∧ W x v = false)
    (firstAndNonEdge :
      ∀ (D : Circuit) (u v : ℕ),
        let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
          (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
          (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
        let W := fun (x : Fin 10 → Bool) (w : ℕ) => (D.wires (List.ofFn x)).getD w false
        ReadsBack 10 D → D.size ≤ 18 →
        D.gates[0]? = some ⟨.and, [0, 2]⟩ →
        (∀ k < D.size,
          let g := gateAt D k
          (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup) ∨
            (g.op = .not ∧ g.inputs.length = 1)) ∧
          (InOutCone 10 D (10 + k) u ∨ InOutCone 10 D (10 + k) v) ∧
          (∀ p < 10 + k, ∃ x : Fin 10 → Bool, W x (10 + k) ≠ W x p) ∧
          ∀ b : Bool, ∃ x : Fin 10 → Bool, W x (10 + k) = b) →
        (∀ b : Bool, ∃ x : Fin 10 → Bool, W x u = b ∧ W x v = !b) →
        (∀ x, G x = false → W x u = false ∧ W x v = false) →
        ∃ x, G x = true ∧ W x u = false ∧ W x v = false)
    (firstOr :
      ∀ (D : Circuit) (u v : ℕ),
        let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
          (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
          (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
        let W := fun (x : Fin 10 → Bool) (w : ℕ) => (D.wires (List.ofFn x)).getD w false
        ReadsBack 10 D → D.size ≤ 18 →
        (∃ b : Bool, D.gates[0]? = some ⟨.or, [0, if b then 1 else 2]⟩) →
        (∀ k < D.size,
          let g := gateAt D k
          (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup) ∨
            (g.op = .not ∧ g.inputs.length = 1)) ∧
          (InOutCone 10 D (10 + k) u ∨ InOutCone 10 D (10 + k) v) ∧
          (∀ p < 10 + k, ∃ x : Fin 10 → Bool, W x (10 + k) ≠ W x p) ∧
          ∀ b : Bool, ∃ x : Fin 10 → Bool, W x (10 + k) = b) →
        (∀ b : Bool, ∃ x : Fin 10 → Bool, W x u = b ∧ W x v = !b) →
        (∀ x, G x = false → W x u = false ∧ W x v = false) →
        ∃ x, G x = true ∧ W x u = false ∧ W x v = false)
    (firstNot :
      ∀ (D : Circuit) (u v : ℕ),
        let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
          (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
          (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
        let W := fun (x : Fin 10 → Bool) (w : ℕ) => (D.wires (List.ofFn x)).getD w false
        ReadsBack 10 D → D.size ≤ 18 →
        D.gates[0]? = some ⟨.not, [0]⟩ →
        (∀ k < D.size,
          let g := gateAt D k
          (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup) ∨
            (g.op = .not ∧ g.inputs.length = 1)) ∧
          (InOutCone 10 D (10 + k) u ∨ InOutCone 10 D (10 + k) v) ∧
          (∀ p < 10 + k, ∃ x : Fin 10 → Bool, W x (10 + k) ≠ W x p) ∧
          ∀ b : Bool, ∃ x : Fin 10 → Bool, W x (10 + k) = b) →
        (∀ b : Bool, ∃ x : Fin 10 → Bool, W x u = b ∧ W x v = !b) →
        (∀ x, G x = false → W x u = false ∧ W x v = false) →
        ∃ x, G x = true ∧ W x u = false ∧ W x v = false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  -- Decidable Petersen graph & S_5 automorphism lemmas (before `classical`)
  let F := fun x : Fin 10 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
    (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
    (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
    (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
    (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
  let toPair (i : Fin 10) : Fin 5 × Fin 5 :=
    if i = 0 then (0, 1) else if i = 1 then (2, 3) else if i = 2 then (0, 4) else
    if i = 3 then (1, 2) else if i = 4 then (3, 4) else if i = 5 then (2, 4) else
    if i = 6 then (1, 4) else if i = 7 then (1, 3) else if i = 8 then (0, 3) else (0, 2)
  let ofPair (a b : Fin 5) : Fin 10 :=
    if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 0
    else if (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then 1
    else if (a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 0) then 2
    else if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then 3
    else if (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) then 4
    else if (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) then 5
    else if (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) then 6
    else if (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) then 7
    else if (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) then 8
    else 9
  let adj (i j : Fin 10) : Bool :=
    decide ((toPair i).1 ≠ (toPair j).1 ∧ (toPair i).1 ≠ (toPair j).2 ∧
            (toPair i).2 ≠ (toPair j).1 ∧ (toPair i).2 ≠ (toPair j).2)
  let edgeList : List (Fin 10 × Fin 10) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  let liftP (π : Fin 5 → Fin 5) (i : Fin 10) : Fin 10 := ofPair (π (toPair i).1) (π (toPair i).2)
  let fifth5 (a b c d : Fin 5) : Fin 5 := 0 - a - b - c - d
  let mkP4 (a b c d : Fin 5) (k : Fin 5) : Fin 5 :=
    if k = a then 0 else if k = b then 1 else if k = c then 2 else if k = d then 3 else 4
  let mkQ4 (a b c d : Fin 5) (k : Fin 5) : Fin 5 :=
    if k = 0 then a else if k = 1 then b else if k = 2 then c else if k = 3 then d else fifth5 a b c d
  have hAdjEdge : ∀ i j : Fin 10, adj i j = true ↔ (i, j) ∈ edgeList ∨ (j, i) ∈ edgeList := by decide
  have hOfTo : ∀ i : Fin 10, ofPair (toPair i).1 (toPair i).2 = i := by decide
  have hToOf : ∀ a b : Fin 5, a ≠ b →
      ((toPair (ofPair a b)).1 = a ∧ (toPair (ofPair a b)).2 = b) ∨
      ((toPair (ofPair a b)).1 = b ∧ (toPair (ofPair a b)).2 = a) := by decide
  have hPairNe : ∀ i : Fin 10, (toPair i).1 ≠ (toPair i).2 := by decide
  have hSym : ∀ a b : Fin 5, ofPair a b = ofPair b a := by decide
  have hP4 : ∀ a b c d k : Fin 5,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      mkP4 a b c d (mkQ4 a b c d k) = k ∧ mkQ4 a b c d (mkP4 a b c d k) = k := by decide
  have hEx2 : ∀ a b : Fin 5, a ≠ b → ∃ c d : Fin 5,
      a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by decide
  have hEx3 : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
      ∃ d : Fin 5, a ≠ d ∧ b ≠ d ∧ c ≠ d := by decide
  have hEdgeMap : ∀ a b : Fin 10, adj a b = true →
      liftP (mkP4 (toPair a).1 (toPair a).2 (toPair b).1 (toPair b).2) a = 0 ∧
      liftP (mkP4 (toPair a).1 (toPair a).2 (toPair b).1 (toPair b).2) b = 1 := by decide
  have hNonEdgeShare : ∀ a b : Fin 10, a ≠ b → adj a b = false →
      ∃ c s t : Fin 5, c ≠ s ∧ c ≠ t ∧ s ≠ t ∧ ofPair c s = a ∧ ofPair c t = b := by decide
  have hNonEdgeMap : ∀ c s t d : Fin 5,
      (c != s && c != t && s != t && c != d && s != d && t != d) = true →
      c ≠ fifth5 c s t d ∧ s ≠ fifth5 c s t d ∧ d ≠ fifth5 c s t d ∧
      liftP (mkP4 c s d (fifth5 c s t d)) (ofPair c s) = 0 ∧
      liftP (mkP4 c s d (fifth5 c s t d)) (ofPair c t) = 2 := by decide
  have hNotMap : ∀ a : Fin 10, ∀ c d : Fin 5,
      (toPair a).1 ≠ c → (toPair a).1 ≠ d → (toPair a).2 ≠ c → (toPair a).2 ≠ d → c ≠ d →
      liftP (mkP4 (toPair a).1 (toPair a).2 c d) a = 0 := by decide
  have hUnitF : ∀ i : Fin 10, F (fun j => decide (j = i)) = false := by decide
  have hZeroF : F (fun _ => false) = false := by decide
  classical
  have hGF (x : Fin 10 → Bool) : G x = F x := by
    change (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) ||
      (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) ||
      (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) ||
      (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) ||
      (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false))))) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
      (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
    simp only [Bool.or_false]
    ac_rfl
  have hF_iff (x : Fin 10 → Bool) :
      F x = true ↔ ∃ i j : Fin 10, adj i j = true ∧ x i = true ∧ x j = true := by
    have hE : F x = edgeList.any (fun e => x e.1 && x e.2) := by
      change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
        (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) =
        ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) ||
        ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) ||
        ((x 3 && x 8) || ((x 4 && x 9) || ((x 5 && x 7) || ((x 7 && x 9) ||
        ((x 9 && x 6) || ((x 6 && x 8) || ((x 8 && x 5) || false)))))))))))))))
      simp only [Bool.or_false]; ac_rfl
    rw [hE, List.any_eq_true]
    constructor
    · rintro ⟨⟨i, j⟩, hmem, hxy⟩
      simp only [Bool.and_eq_true] at hxy
      exact ⟨i, j, (hAdjEdge i j).mpr (Or.inl hmem), hxy.1, hxy.2⟩
    · rintro ⟨i, j, hadj, hi, hj⟩
      rcases (hAdjEdge i j).mp hadj with h1 | h2
      · exact ⟨(i, j), h1, by simp [hi, hj]⟩
      · exact ⟨(j, i), h2, by simp [hi, hj]⟩
  have liftP_bij (π π' : Fin 5 → Fin 5) (h1 : ∀ k, π (π' k) = k) (h2 : ∀ k, π' (π k) = k) :
      (∀ i, liftP π (liftP π' i) = i) ∧ (∀ i, liftP π' (liftP π i) = i) ∧
      (∀ i j, adj (liftP π i) (liftP π j) = adj i j) := by
    have hInj (f g : Fin 5 → Fin 5) (hfg : ∀ k, g (f k) = k) (a b : Fin 5) (hab : f a = f b) : a = b := by
      have := congrArg g hab; rwa [hfg, hfg] at this
    have hInv (f g : Fin 5 → Fin 5) (hfg : ∀ k, f (g k) = k) (hgf : ∀ k, g (f k) = k) (i : Fin 10) :
        liftP f (liftP g i) = i := by
      have hne : g (toPair i).1 ≠ g (toPair i).2 := fun h => hPairNe i (hInj g f hfg _ _ h)
      rcases hToOf (g (toPair i).1) (g (toPair i).2) hne with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · dsimp only [liftP]; rw [ha, hb, hfg, hfg, hOfTo]
      · dsimp only [liftP]; rw [ha, hb, hfg, hfg, hSym, hOfTo]
    refine ⟨hInv π π' h1 h2, hInv π' π h2 h1, ?_⟩
    intro i j
    have hneI : π (toPair i).1 ≠ π (toPair i).2 := fun h => hPairNe i (hInj π π' h2 _ _ h)
    have hneJ : π (toPair j).1 ≠ π (toPair j).2 := fun h => hPairNe j (hInj π π' h2 _ _ h)
    have hI := hToOf (π (toPair i).1) (π (toPair i).2) hneI
    have hJ := hToOf (π (toPair j).1) (π (toPair j).2) hneJ
    apply Bool.eq_iff_iff.mpr
    simp only [adj, decide_eq_true_eq, liftP]
    have hEqNe (a b : Fin 5) : π a ≠ π b ↔ a ≠ b :=
      ⟨fun h hab => h (by rw [hab]), fun h hab => h (hInj π π' h2 _ _ hab)⟩
    rcases hI with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;> rcases hJ with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩ <;>
      rw [hi1, hi2, hj1, hj2] <;> simp only [hEqNe]
    · exact ⟨fun h => ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩, fun h => ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩⟩
    · exact ⟨fun h => ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩, fun h => ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩⟩
    · exact ⟨fun h => ⟨h.2.2.2, h.2.2.1, h.2.1, h.1⟩, fun h => ⟨h.2.2.2, h.2.2.1, h.2.1, h.1⟩⟩
  have hAutoF (σ τ : Fin 10 → Fin 10) (hst : ∀ i, σ (τ i) = i) (hts : ∀ i, τ (σ i) = i)
      (hadj : ∀ i j, adj (σ i) (σ j) = adj i j) (x : Fin 10 → Bool) : F (x ∘ σ) = F x := by
    apply Bool.eq_iff_iff.mpr
    rw [hF_iff, hF_iff]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      exact ⟨σ i, σ j, by rw [hadj]; exact hij, hi, hj⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      refine ⟨τ i, τ j, ?_, ?_, ?_⟩
      · have := hadj (τ i) (τ j); rw [hst, hst] at this; rw [← this]; exact hij
      · change x (σ (τ i)) = true; rw [hst]; exact hi
      · change x (σ (τ j)) = true; rw [hst]; exact hj
  -- Basic wire helpers (zero extra decls)
  let stepWire (ws : List Bool) (g : Gate) : List Bool :=
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let wf (gs : List Gate) (ws : List Bool) : List Bool := gs.foldl stepWire ws
  let val (D : Circuit) (w : ℕ) (x : Fin 10 → Bool) : Bool := (D.wires (List.ofFn x)).getD w false
  have wf_len : ∀ (gs : List Gate) (ws : List Bool), (wf gs ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; simp [wf]
    | cons g gs ih =>
      intro ws
      change (wf gs (stepWire ws g)).length = ws.length + (gs.length + 1)
      rw [ih]; simp [stepWire]; omega
  have wf_getD_lt : ∀ (gs : List Gate) (ws : List Bool), ∀ w < ws.length,
      (wf gs ws).getD w false = ws.getD w false := by
    intro gs
    induction gs with
    | nil => intro ws w _; rfl
    | cons g gs ih =>
      intro ws w hw
      change (wf gs (stepWire ws g)).getD w false = ws.getD w false
      rw [ih _ w (by simp [stepWire]; omega)]
      simp only [stepWire, List.getD_append _ _ _ _ hw]
  have wf_append (gs1 gs2 : List Gate) (ws : List Bool) :
      wf (gs1 ++ gs2) ws = wf gs2 (wf gs1 ws) := List.foldl_append
  have gateAt_mem (D : Circuit) (k : ℕ) (hk : k < D.gates.length) : gateAt D k ∈ D.gates := by
    change D.gates.getD k ⟨GateOp.or, []⟩ ∈ D.gates
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have gateAt_eq_getElem (D : Circuit) (k : ℕ) (hk : k < D.gates.length) :
      gateAt D k = D.gates[k] := by
    change D.gates.getD k ⟨GateOp.or, []⟩ = D.gates[k]
    exact List.getD_eq_getElem _ _ hk
  have val_gate (D : Circuit) (k : ℕ) (hk : k < D.gates.length) (x : Fin 10 → Bool) :
      val D (10 + k) x =
        (gateAt D k).op.eval ((gateAt D k).inputs.map fun w =>
          if w < 10 + k then val D w x else false) := by
    have hsplit : D.gates = D.gates.take k ++ [D.gates[k]] ++ D.gates.drop (k + 1) := by
      have h1 := List.take_append_drop k D.gates
      have h2 : D.gates[k] :: D.gates.drop (k + 1) = D.gates.drop k := List.cons_getElem_drop_succ
      rw [← h2] at h1
      simp only [List.append_assoc, List.singleton_append]
      exact h1.symm
    let ws := wf (D.gates.take k) (List.ofFn x)
    have hwsLen : ws.length = 10 + k := by
      simp only [ws, wf_len, List.length_ofFn, List.length_take]; omega
    have hD : D.wires (List.ofFn x) = wf (D.gates.drop (k + 1)) (stepWire ws D.gates[k]) := by
      change wf D.gates (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [wf_append, wf_append]
      rfl
    have hget : val D (10 + k) x = (stepWire ws D.gates[k]).getD (10 + k) false := by
      change (D.wires (List.ofFn x)).getD (10 + k) false = _
      rw [hD, wf_getD_lt _ _ (10 + k) (by simp [stepWire, hwsLen])]
    rw [hget]
    have hlast : (stepWire ws D.gates[k]).getD (10 + k) false =
        D.gates[k].op.eval (D.gates[k].inputs.map fun w => ws.getD w false) := by
      simp only [stepWire, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hwsLen, Nat.sub_self]
      rfl
    rw [hlast, gateAt_eq_getElem D k hk]
    congr 1
    apply List.map_congr_left
    intro w _
    by_cases hwk : w < 10 + k
    · simp only [hwk, ↓reduceIte]
      change ws.getD w false = (D.wires (List.ofFn x)).getD w false
      have hwsLen1 : (stepWire ws D.gates[k]).length = 10 + k + 1 := by
        simp only [stepWire, List.length_append, List.length_cons, List.length_nil, hwsLen]
      rw [hD, wf_getD_lt (D.gates.drop (k + 1)) (stepWire ws D.gates[k]) w (by omega)]
      exact (List.getD_append _ _ _ _ (by rw [hwsLen]; omega)).symm
    · simp only [hwk, ↓reduceIte]
      exact List.getD_eq_default _ _ (by rw [hwsLen]; omega)
  have val_gate_rb (D : Circuit) (hb : ReadsBack 10 D) (k : ℕ) (hk : k < D.gates.length)
      (x : Fin 10 → Bool) :
      val D (10 + k) x = (gateAt D k).op.eval ((gateAt D k).inputs.map fun w => val D w x) := by
    rw [val_gate D k hk x]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hlt : w < 10 + k := hb k hk w hw
    simp [hlt]
  have val_in (D : Circuit) (x : Fin 10 → Bool) (i : Fin 10) : val D i.val x = x i := by
    change (wf D.gates (List.ofFn x)).getD i.val false = x i
    rw [wf_getD_lt D.gates (List.ofFn x) i.val (by simp),
        List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have val_oob (D : Circuit) (x : Fin 10 → Bool) (w : ℕ) (hw : 10 + D.gates.length ≤ w) :
      val D w x = false := by
    change (wf D.gates (List.ofFn x)).getD w false = false
    apply List.getD_eq_default
    rw [wf_len, List.length_ofFn]
    exact hw
  -- Cone helpers for n = 10
  have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep 10) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      change (gs.foldl (coneStep 10) (coneStep 10 cs g)).length = cs.length + (gs.length + 1)
      rw [ih]; change (cs ++ _).length + gs.length = _; simp; omega
  have cones_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)), ∀ k < cs.length,
      (gs.foldl (coneStep 10) cs).getD k [] = cs.getD k [] := by
    intro gs
    induction gs with
    | nil => intro cs k _; rfl
    | cons g gs ih =>
      intro cs k hk
      change (gs.foldl (coneStep 10) (coneStep 10 cs g)).getD k [] = cs.getD k []
      rw [ih _ k (by change k < (cs ++ _).length; simp; omega)]
      change (cs ++ _).getD k [] = cs.getD k []
      exact List.getD_append _ _ _ _ hk
  have inCone_lt_len (D : Circuit) (i k : ℕ) (h : InCone 10 D i k) : k < D.gates.length := by
    by_contra hge
    have hlen : (cones 10 D).length = D.gates.length := by
      change (D.gates.foldl (coneStep 10) []).length = D.gates.length
      rw [cones_len]; simp
    have hnil : (cones 10 D).getD k [] = [] := List.getD_eq_default _ _ (by omega)
    change i ∈ (cones 10 D).getD k [] at h
    rw [hnil] at h
    exact List.not_mem_nil h
  have inCone_iff (D : Circuit) (i k : ℕ) (hk : k < D.gates.length) :
      InCone 10 D i k ↔ ∃ w ∈ (gateAt D k).inputs, 10 ≤ w ∧ w < 10 + k ∧
        (i = w - 10 ∨ InCone 10 D i (w - 10)) := by
    have hsplit : D.gates = D.gates.take k ++ [D.gates[k]] ++ D.gates.drop (k + 1) := by
      have h1 := List.take_append_drop k D.gates
      have h2 : D.gates[k] :: D.gates.drop (k + 1) = D.gates.drop k := List.cons_getElem_drop_succ
      rw [← h2] at h1
      simp only [List.append_assoc, List.singleton_append]
      exact h1.symm
    let cs := (D.gates.take k).foldl (coneStep 10) []
    have hcsLen : cs.length = k := by
      simp only [cs, cones_len, List.length_nil, zero_add, List.length_take]; omega
    have hC : cones 10 D = (D.gates.drop (k + 1)).foldl (coneStep 10) (coneStep 10 cs D.gates[k]) := by
      change D.gates.foldl (coneStep 10) [] = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append]
      rfl
    have hget : (cones 10 D).getD k [] = (coneStep 10 cs D.gates[k]).getD k [] := by
      rw [hC, cones_getD_lt _ _ k (by change k < (cs ++ _).length; simp [hcsLen])]
    have hlast : (coneStep 10 cs D.gates[k]).getD k [] =
        (D.gates[k].inputs.filter (fun w => decide (10 ≤ w ∧ w < 10 + k))).flatMap
          (fun w => (w - 10) :: cs.getD (w - 10) []) := by
      change (cs ++ [_]).getD k [] = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hcsLen, Nat.sub_self]
      simp
    change i ∈ (cones 10 D).getD k [] ↔ _
    rw [hget, hlast, gateAt_eq_getElem D k hk, List.mem_flatMap]
    constructor
    · rintro ⟨w, hwF, hi⟩
      obtain ⟨hw, hcondB⟩ := List.mem_filter.mp hwF
      obtain ⟨h10, hlt⟩ := of_decide_eq_true hcondB
      rw [List.mem_cons] at hi
      refine ⟨w, hw, h10, hlt, ?_⟩
      rcases hi with rfl | hmem
      · exact Or.inl rfl
      · right
        change i ∈ (cones 10 D).getD (w - 10) []
        rw [hC, cones_getD_lt _ _ (w - 10) (by change w - 10 < (cs ++ _).length; simp [hcsLen]; omega)]
        change i ∈ (cs ++ _).getD (w - 10) []
        rw [List.getD_append _ _ _ _ (by omega : w - 10 < cs.length)]
        exact hmem
    · rintro ⟨w, hw, h10, hlt, hcase⟩
      refine ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨h10, hlt⟩⟩, ?_⟩
      rw [List.mem_cons]
      rcases hcase with rfl | hmem
      · exact Or.inl rfl
      · right
        change i ∈ (cones 10 D).getD (w - 10) [] at hmem
        rw [hC, cones_getD_lt _ _ (w - 10) (by change w - 10 < (cs ++ _).length; simp [hcsLen]; omega)] at hmem
        change i ∈ (cs ++ _).getD (w - 10) [] at hmem
        rw [List.getD_append _ _ _ _ (by omega : w - 10 < cs.length)] at hmem
        exact hmem
  have inCone_trans (D : Circuit) : ∀ k i j, InCone 10 D i j → InCone 10 D j k → InCone 10 D i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i j hij hjk
      have hk := inCone_lt_len D j k hjk
      obtain ⟨w, hw, h10, hlt, hcase⟩ := (inCone_iff D j k hk).mp hjk
      refine (inCone_iff D i k hk).mpr ⟨w, hw, h10, hlt, Or.inr ?_⟩
      rcases hcase with rfl | hsub
      · exact hij
      · exact ih (w - 10) (by omega) i j hij hsub
  have inOutCone_step (D : Circuit) (hb : ReadsBack 10 D) (k u a : ℕ) (hk : k < D.gates.length)
      (hu : u ∈ (gateAt D k).inputs) (h10 : 10 ≤ u) (hka : InOutCone 10 D (10 + k) a) :
      InOutCone 10 D u a := by
    have huLt : u < 10 + k := hb k hk u hu
    have huk : InCone 10 D (u - 10) k :=
      (inCone_iff D (u - 10) k hk).mpr ⟨u, hu, h10, huLt, Or.inl rfl⟩
    rcases hka with hEq | ⟨_, ha10, hka'⟩
    · refine Or.inr ⟨h10, by omega, ?_⟩
      have : a - 10 = k := by omega
      rw [this]; exact huk
    · refine Or.inr ⟨h10, ha10, ?_⟩
      have hEq : (10 + k) - 10 = k := by omega
      rw [hEq] at hka'
      exact inCone_trans D (a - 10) (u - 10) k huk hka'
  -- Sanitize pass: guarantees ReadsBack 10 and every .not gate has length 1
  let sanitizeGate (k : ℕ) (g : Gate) : Gate :=
    if g.op = .and then
      if g.inputs.all (fun w => decide (w < 10 + k)) then g else ⟨.or, []⟩
    else if g.op = .or then
      ⟨.or, g.inputs.filter (fun w => decide (w < 10 + k))⟩
    else
      if g.inputs.length = 0 then ⟨.and, []⟩
      else if g.inputs.headD 0 < 10 + k then ⟨.not, [g.inputs.headD 0]⟩ else ⟨.and, []⟩
  let sanitize (D : Circuit) : Circuit :=
    ⟨(List.range D.gates.length).map (fun k => sanitizeGate k (gateAt D k)), D.output⟩
  have sanitize_len (D : Circuit) : (sanitize D).gates.length = D.gates.length := by
    change ((List.range D.gates.length).map _).length = D.gates.length
    simp
  have sanitize_gateAt (D : Circuit) (k : ℕ) (hk : k < D.gates.length) :
      gateAt (sanitize D) k = sanitizeGate k (gateAt D k) := by
    have hkS : k < (sanitize D).gates.length := by rw [sanitize_len]; exact hk
    rw [gateAt_eq_getElem (sanitize D) k hkS]
    change ((List.range D.gates.length).map (fun k => sanitizeGate k (gateAt D k)))[k]'(by simp [hk]) = _
    simp
  have sanitize_meta (D : Circuit) (hf : FanInTwo D) :
      FanInTwo (sanitize D) ∧ ReadsBack 10 (sanitize D) ∧
      (∀ k < (sanitize D).gates.length, (gateAt (sanitize D) k).op = .not →
        (gateAt (sanitize D) k).inputs.length = 1) := by
    have hmem_iff (g : Gate) (hg : g ∈ (sanitize D).gates) :
        ∃ k < D.gates.length, g = sanitizeGate k (gateAt D k) := by
      change g ∈ (List.range D.gates.length).map _ at hg
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
      exact ⟨k, List.mem_range.mp hk, rfl⟩
    have hgate_ok (k : ℕ) (hk : k < D.gates.length) :
        ((sanitizeGate k (gateAt D k)).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          (sanitizeGate k (gateAt D k)).inputs.length ≤ 2) ∧
        (∀ w ∈ (sanitizeGate k (gateAt D k)).inputs, w < 10 + k) ∧
        ((sanitizeGate k (gateAt D k)).op = .not → (sanitizeGate k (gateAt D k)).inputs.length = 1) := by
      obtain ⟨hop, hlen⟩ := hf (gateAt D k) (gateAt_mem D k hk)
      dsimp only [sanitizeGate]
      split_ifs with h1 h2 h3 h4 h5
      · refine ⟨⟨hop, hlen⟩, ?_, fun hn => by rw [h1] at hn; cases hn⟩
        intro w hw
        exact of_decide_eq_true (List.all_eq_true.mp h2 w hw)
      · refine ⟨⟨by simp, by simp⟩, by simp, fun hn => by cases hn⟩
      · refine ⟨⟨by simp, (List.length_filter_le _ _).trans hlen⟩, ?_, fun hn => by cases hn⟩
        intro w hw
        exact of_decide_eq_true (List.mem_filter.mp hw).2
      · refine ⟨⟨by simp, by simp⟩, by simp, fun hn => by cases hn⟩
      · refine ⟨⟨by simp, by simp⟩, ?_, fun _ => rfl⟩
        intro w hw
        simp only [List.mem_singleton] at hw
        rw [hw]; exact h5
      · refine ⟨⟨by simp, by simp⟩, by simp, fun hn => by cases hn⟩
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨k, hk, rfl⟩ := hmem_iff g hg
      exact (hgate_ok k hk).1
    · intro k hk w hw
      have hkD : k < D.gates.length := by rw [← sanitize_len D]; exact hk
      rw [sanitize_gateAt D k hkD] at hw
      exact (hgate_ok k hkD).2.1 w hw
    · intro k hk hn
      have hkD : k < D.gates.length := by rw [← sanitize_len D]; exact hk
      rw [sanitize_gateAt D k hkD] at hn ⊢
      exact (hgate_ok k hkD).2.2 hn
  have sanitize_val (D : Circuit) (hf : FanInTwo D) (x : Fin 10 → Bool) :
      ∀ w, val (sanitize D) w x = val D w x := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases hw10 : w < 10
      · let i : Fin 10 := ⟨w, hw10⟩
        change val (sanitize D) i.val x = val D i.val x
        rw [val_in, val_in]
      · by_cases hwLt : w < 10 + D.gates.length
        · let k := w - 10
          have hk : k < D.gates.length := by omega
          have hwEq : w = 10 + k := by omega
          rw [hwEq, val_gate (sanitize D) k (by rw [sanitize_len]; exact hk) x,
              val_gate D k hk x, sanitize_gateAt D k hk]
          have hIH : ∀ u < 10 + k, val (sanitize D) u x = val D u x :=
            fun u hu => ih u (by omega)
          have hmap : ∀ (l : List ℕ),
              (l.map fun u => if u < 10 + k then val (sanitize D) u x else false) =
              (l.map fun u => if u < 10 + k then val D u x else false) := by
            intro l
            apply List.map_congr_left
            intro u _
            by_cases hu : u < 10 + k
            · simp [hu, hIH u hu]
            · simp [hu]
          obtain ⟨hop, _⟩ := hf (gateAt D k) (gateAt_mem D k hk)
          dsimp only [sanitizeGate]
          rcases hop with hAnd | hOr | hNot
          · rw [hAnd]; simp only [↓reduceIte]
            split_ifs with hall
            · rw [hAnd, hmap]
            · change false = ((gateAt D k).inputs.map fun u =>
                  if u < 10 + k then val D u x else false).all id
              symm
              rw [List.all_eq_false]
              have hnotAll : ¬ ∀ u ∈ (gateAt D k).inputs, decide (u < 10 + k) = true := by
                intro ha; exact hall (List.all_eq_true.mpr ha)
              push Not at hnotAll
              obtain ⟨u, huMem, huGe⟩ := hnotAll
              have huNotLt : ¬ u < 10 + k := fun hlt => huGe (decide_eq_true hlt)
              refine ⟨false, List.mem_map.mpr ⟨u, huMem, by simp [huNotLt]⟩, by decide⟩
          · rw [hOr]; simp only [reduceCtorEq, ↓reduceIte]
            change (((gateAt D k).inputs.filter fun u => decide (u < 10 + k)).map fun u =>
                if u < 10 + k then val (sanitize D) u x else false).any id =
              ((gateAt D k).inputs.map fun u => if u < 10 + k then val D u x else false).any id
            rw [hmap]
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true, List.mem_map, List.mem_filter, id_eq]
            constructor
            · rintro ⟨_, ⟨u, ⟨huMem, _⟩, rfl⟩, hb⟩
              exact ⟨_, ⟨u, huMem, rfl⟩, hb⟩
            · rintro ⟨b, ⟨u, huMem, rfl⟩, hb⟩
              by_cases huLt : u < 10 + k
              · exact ⟨true, ⟨u, ⟨huMem, decide_eq_true huLt⟩, by simpa [huLt] using hb⟩, rfl⟩
              · simp [huLt] at hb
          · rw [hNot]; simp only [reduceCtorEq, ↓reduceIte]
            cases hIns : (gateAt D k).inputs with
            | nil =>
              simp only [List.length_nil, ↓reduceIte]; rfl
            | cons a rest =>
              simp only [List.length_cons, Nat.add_one_ne_zero, ↓reduceIte, List.headD_cons]
              by_cases haLt : a < 10 + k
              · simp only [haLt, ↓reduceIte]
                change (!(if a < 10 + k then val (sanitize D) a x else false)) =
                  (!(if a < 10 + k then val D a x else false))
                simp [haLt, hIH a haLt]
              · simp only [haLt, ↓reduceIte]
                change true = (!(if a < 10 + k then val D a x else false))
                simp [haLt]
        · rw [val_oob (sanitize D) x w (by rw [sanitize_len]; omega),
              val_oob D x w (by omega)]
  -- eraseGate helpers for n = 10
  have erase_meta (D : Circuit) (hf : FanInTwo D) (hb : ReadsBack 10 D)
      (hnot1 : ∀ k < D.gates.length, (gateAt D k).op = .not → (gateAt D k).inputs.length = 1)
      (m p : ℕ) (hm : m < D.gates.length) (hp : p < 10 + m) :
      FanInTwo (eraseGate 10 D m p) ∧ ReadsBack 10 (eraseGate 10 D m p) ∧
      (∀ k < (eraseGate 10 D m p).gates.length,
        (gateAt (eraseGate 10 D m p) k).op = .not → (gateAt (eraseGate 10 D m p) k).inputs.length = 1) ∧
      (eraseGate 10 D m p).gates.length + 1 = D.gates.length := by
    have hgs : (eraseGate 10 D m p).gates =
        D.gates.take m ++ (D.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect 10 m p)⟩) := by
      dsimp only [eraseGate]; simp only [hm, ↓reduceIte]
    have hsz : (eraseGate 10 D m p).gates.length + 1 = D.gates.length := by
      rw [hgs, List.length_append, List.length_take, List.length_map, List.length_drop]; omega
    have hgateAt (k : ℕ) (hk : k < (eraseGate 10 D m p).gates.length) :
        (k < m ∧ gateAt (eraseGate 10 D m p) k = gateAt D k) ∨
        (m ≤ k ∧ gateAt (eraseGate 10 D m p) k =
          ⟨(gateAt D (k + 1)).op, (gateAt D (k + 1)).inputs.map (eraseRedirect 10 m p)⟩) := by
      rw [gateAt_eq_getElem _ k hk]
      have htakeLen : (D.gates.take m).length = m := by rw [List.length_take]; omega
      by_cases hkm : k < m
      · left; refine ⟨hkm, ?_⟩
        simp only [hgs, List.getElem_append_left (by omega : k < (D.gates.take m).length),
          List.getElem_take, gateAt_eq_getElem D k (by omega)]
      · right; refine ⟨by omega, ?_⟩
        simp only [hgs, List.getElem_append_right (by omega : (D.gates.take m).length ≤ k),
          htakeLen, List.getElem_map, List.getElem_drop]
        have hIdx : m + 1 + (k - m) = k + 1 := by omega
        simp only [hIdx, gateAt_eq_getElem D (k + 1) (by omega)]
    have hfE : FanInTwo (eraseGate 10 D m p) := by
      intro g hg
      rw [hgs, List.mem_append] at hg
      rcases hg with h1 | h2
      · exact hf g (List.mem_of_mem_take h1)
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp h2
        obtain ⟨hop, hlen⟩ := hf g' (List.mem_of_mem_drop hg')
        exact ⟨hop, by simp [hlen]⟩
    have hbE : ReadsBack 10 (eraseGate 10 D m p) := by
      intro k hk u hu
      rcases hgateAt k hk with ⟨hkm, heq⟩ | ⟨hmk, heq⟩
      · rw [heq] at hu; exact hb k (by omega) u hu
      · rw [heq] at hu
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
        have hvLt : v < 10 + (k + 1) := hb (k + 1) (by omega) v hv
        dsimp only [eraseRedirect]; split_ifs <;> omega
    have hnotE : ∀ k < (eraseGate 10 D m p).gates.length,
        (gateAt (eraseGate 10 D m p) k).op = .not → (gateAt (eraseGate 10 D m p) k).inputs.length = 1 := by
      intro k hk hn
      rcases hgateAt k hk with ⟨hkm, heq⟩ | ⟨hmk, heq⟩
      · rw [heq] at hn ⊢; exact hnot1 k (by omega) hn
      · rw [heq] at hn ⊢
        simp only [List.length_map]
        exact hnot1 (k + 1) (by omega) hn
    exact ⟨hfE, hbE, hnotE, hsz⟩
  have erase_eval (D : Circuit) (hf : FanInTwo D) (hb : ReadsBack 10 D)
      (hnot1 : ∀ k < D.gates.length, (gateAt D k).op = .not → (gateAt D k).inputs.length = 1)
      (m p : ℕ) (hm : m < D.gates.length) (hp : p < 10 + m)
      (P : ℕ → Prop)
      (hDown : ∀ k < D.gates.length, P (10 + k) → ∀ u ∈ (gateAt D k).inputs, P u)
      (hMode : ¬ P (10 + m) ∨ ((∀ x : Fin 10 → Bool, val D (10 + m) x = val D p x) ∧ P p)) :
      ∀ x : Fin 10 → Bool, ∀ w, P w → val (eraseGate 10 D m p) (eraseRedirect 10 m p w) x = val D w x := by
    obtain ⟨_, hbE, _, hszE⟩ := erase_meta D hf hb hnot1 m p hm hp
    have hgs : (eraseGate 10 D m p).gates =
        D.gates.take m ++ (D.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect 10 m p)⟩) := by
      dsimp only [eraseGate]; simp only [hm, ↓reduceIte]
    have htakeLen : (D.gates.take m).length = m := by rw [List.length_take]; omega
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hPw
      by_cases hw10 : w < 10
      · have hr : eraseRedirect 10 m p w = w := by dsimp only [eraseRedirect]; split_ifs <;> omega
        rw [hr]
        let i : Fin 10 := ⟨w, hw10⟩
        change val (eraseGate 10 D m p) i.val x = val D i.val x
        rw [val_in, val_in]
      · by_cases hwLt : w < 10 + D.gates.length
        · let k := w - 10
          have hk : k < D.gates.length := by omega
          have hwEq : w = 10 + k := by omega
          rw [hwEq] at hPw ⊢
          by_cases hkm : k < m
          · have hr : eraseRedirect 10 m p (10 + k) = 10 + k := by
              dsimp only [eraseRedirect]; split_ifs <;> omega
            rw [hr, val_gate_rb (eraseGate 10 D m p) hbE k (by omega) x, val_gate_rb D hb k hk x]
            have hgk : gateAt (eraseGate 10 D m p) k = gateAt D k := by
              rw [gateAt_eq_getElem _ k (by omega), gateAt_eq_getElem D k hk]
              simp only [hgs, List.getElem_append_left (by omega : k < (D.gates.take m).length), List.getElem_take]
            rw [hgk]
            congr 1
            apply List.map_congr_left
            intro u hu
            have huLt : u < 10 + k := hb k hk u hu
            have hru : eraseRedirect 10 m p u = u := by dsimp only [eraseRedirect]; split_ifs <;> omega
            conv_lhs => rw [← hru]
            exact ih u (by omega) (hDown k hk hPw u hu)
          · by_cases hkeq : k = m
            · rw [hkeq] at hPw ⊢
              rcases hMode with hnot | ⟨heq, hPp⟩
              · exact False.elim (hnot hPw)
              · have hr : eraseRedirect 10 m p (10 + m) = p := by dsimp only [eraseRedirect]; simp
                have hrp : eraseRedirect 10 m p p = p := by dsimp only [eraseRedirect]; split_ifs <;> omega
                rw [hr]
                have hih := ih p (by omega) hPp
                rw [hrp] at hih
                exact hih.trans (heq x).symm
            · have hmk : m < k := by omega
              have hr : eraseRedirect 10 m p (10 + k) = 10 + (k - 1) := by
                dsimp only [eraseRedirect]; split_ifs <;> omega
              rw [hr, val_gate_rb (eraseGate 10 D m p) hbE (k - 1) (by omega) x, val_gate_rb D hb k hk x]
              have hgk : gateAt (eraseGate 10 D m p) (k - 1) =
                  ⟨(gateAt D k).op, (gateAt D k).inputs.map (eraseRedirect 10 m p)⟩ := by
                rw [gateAt_eq_getElem _ (k - 1) (by omega), gateAt_eq_getElem D k hk]
                simp only [hgs, List.getElem_append_right (by omega : (D.gates.take m).length ≤ k - 1),
                  htakeLen, List.getElem_map, List.getElem_drop]
                have hIdx : m + 1 + (k - 1 - m) = k := by omega
                simp only [hIdx]
              rw [hgk, List.map_map]
              congr 1
              apply List.map_congr_left
              intro u hu
              have huLt : u < 10 + k := hb k hk u hu
              exact ih u (by omega) (hDown k hk hPw u hu)
        · have hr : eraseRedirect 10 m p w = w - 1 := by
            dsimp only [eraseRedirect]; split_ifs <;> omega
          rw [hr, val_oob (eraseGate 10 D m p) x (w - 1) (by omega), val_oob D x w (by omega)]
  have redirect_lt (sz sz' m r w : ℕ) (hsz : sz' + 1 = sz) (hm : m < sz) (hr : r < 10 + m)
      (hw : w < 10 + sz) : eraseRedirect 10 m r w < 10 + sz' := by
    dsimp only [eraseRedirect]; split_ifs <;> omega
  -- Circuit permutation by σ : Fin 10 → Fin 10
  let mapWire (σ : Fin 10 → Fin 10) (w : ℕ) : ℕ :=
    if h : w < 10 then (σ ⟨w, h⟩).val else w
  let permCircuit (σ : Fin 10 → Fin 10) (D : Circuit) : Circuit :=
    ⟨D.gates.map (fun g => ⟨g.op, g.inputs.map (mapWire σ)⟩), mapWire σ D.output⟩
  have perm_len (σ : Fin 10 → Fin 10) (D : Circuit) : (permCircuit σ D).gates.length = D.gates.length := by
    change (D.gates.map _).length = D.gates.length; simp
  have perm_gateAt (σ : Fin 10 → Fin 10) (D : Circuit) (k : ℕ) (hk : k < D.gates.length) :
      gateAt (permCircuit σ D) k = ⟨(gateAt D k).op, (gateAt D k).inputs.map (mapWire σ)⟩ := by
    have hkP : k < (permCircuit σ D).gates.length := by rw [perm_len]; exact hk
    rw [gateAt_eq_getElem _ k hkP, gateAt_eq_getElem D k hk]
    change (D.gates.map (fun g => (⟨g.op, g.inputs.map (mapWire σ)⟩ : Gate)))[k]'(by simp [hk]) = _
    simp
  have perm_val (σ : Fin 10 → Fin 10) (D : Circuit) (hb : ReadsBack 10 D) (x : Fin 10 → Bool) :
      ∀ k < D.gates.length, val (permCircuit σ D) (10 + k) x = val D (10 + k) (x ∘ σ) := by
    have hbP : ReadsBack 10 (permCircuit σ D) := by
      intro k hk w hw
      have hkD : k < D.gates.length := by rw [← perm_len σ D]; exact hk
      rw [perm_gateAt σ D k hkD] at hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      have huLt := hb k hkD u hu
      dsimp only [mapWire]; split_ifs with h10
      · exact Nat.lt_of_lt_of_le (σ ⟨u, h10⟩).isLt (by omega)
      · exact huLt
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rw [val_gate_rb (permCircuit σ D) hbP k (by rw [perm_len]; exact hk) x,
          val_gate_rb D hb k hk (x ∘ σ), perm_gateAt σ D k hk, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have huLt := hb k hk u hu
      dsimp only [Function.comp, mapWire]
      split_ifs with h10
      · rw [val_in (permCircuit σ D) x (σ ⟨u, h10⟩)]
        change x (σ ⟨u, h10⟩) = val D (⟨u, h10⟩ : Fin 10).val (x ∘ σ)
        rw [val_in D (x ∘ σ) ⟨u, h10⟩]
        rfl
      · have hEq : u = 10 + (u - 10) := by omega
        rw [hEq]; exact ih (u - 10) (by omega) (by omega)
  have perm_inCone (σ : Fin 10 → Fin 10) (D : Circuit) :
      ∀ k i, InCone 10 (permCircuit σ D) i k ↔ InCone 10 D i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i
      by_cases hk : k < D.gates.length
      · rw [inCone_iff (permCircuit σ D) i k (by rw [perm_len]; exact hk),
            inCone_iff D i k hk, perm_gateAt σ D k hk]
        constructor
        · rintro ⟨w, hw, h10, hlt, hcase⟩
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
          have huGe : ¬ u < 10 := by
            intro hu10; dsimp only [mapWire] at h10; simp only [hu10, ↓reduceDIte] at h10
            have := (σ ⟨u, hu10⟩).isLt; omega
          have hEq : mapWire σ u = u := by dsimp only [mapWire]; simp [huGe]
          rw [hEq] at h10 hlt hcase
          refine ⟨u, hu, h10, hlt, hcase.imp id fun hsub => (ih (u - 10) (by omega) i).mp hsub⟩
        · rintro ⟨u, hu, h10, hlt, hcase⟩
          have hEq : mapWire σ u = u := by dsimp only [mapWire]; simp [show ¬ u < 10 by omega]
          refine ⟨u, List.mem_map.mpr ⟨u, hu, hEq⟩, h10, hlt,
            hcase.imp id fun hsub => (ih (u - 10) (by omega) i).mpr hsub⟩
      · constructor
        · intro h; have := inCone_lt_len (permCircuit σ D) i k h; rw [perm_len] at this; omega
        · intro h; have := inCone_lt_len D i k h; omega
  -- Main strong induction on circuit size
  let valid (D : Circuit) (u v : ℕ) : Prop :=
    FanInTwo D ∧ ReadsBack 10 D ∧
    (∀ k < D.gates.length, (gateAt D k).op = .not → (gateAt D k).inputs.length = 1) ∧
    10 ≤ u ∧ u < 10 + D.gates.length ∧ 10 ≤ v ∧ v < 10 + D.gates.length ∧
    (∃ x : Fin 10 → Bool, val D u x = true ∧ val D v x = false) ∧
    (∃ x : Fin 10 → Bool, val D u x = false ∧ val D v x = true) ∧
    (∀ x : Fin 10 → Bool, F x = false → val D u x = false ∧ val D v x = false) ∧
    (∀ x : Fin 10 → Bool, F x = true → val D u x = true ∨ val D v x = true)
  have main_ind : ∀ s : ℕ, ∀ D : Circuit, ∀ u v : ℕ, D.gates.length = s → s ≤ 18 → valid D u v → False := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro D u v hDs hSmall hVal
      obtain ⟨hfD, hbD, hnotD, huGe, huLt, hvGe, hvLt, hExU, hExV, hSound, hComp⟩ := hVal
      have shrink_of_eq (E : Circuit) (u' v' : ℕ)
          (hfE : FanInTwo E) (hbE : ReadsBack 10 E)
          (hnotE : ∀ k < E.gates.length, (gateAt E k).op = .not → (gateAt E k).inputs.length = 1)
          (hszE : E.gates.length < D.gates.length) (hu' : u' < 10 + E.gates.length) (hv' : v' < 10 + E.gates.length)
          (heqU : ∀ x : Fin 10 → Bool, val E u' x = val D u x)
          (heqV : ∀ x : Fin 10 → Bool, val E v' x = val D v x) : False := by
        have hu'Ge : 10 ≤ u' := by
          by_contra hlt
          let i : Fin 10 := ⟨u', by omega⟩
          have h1 : val E i.val (fun j => decide (j = i)) = true := by rw [val_in]; simp
          have h2 : val D u (fun j => decide (j = i)) = false := (hSound _ (hUnitF i)).1
          rw [heqU] at h1; rw [h2] at h1; cases h1
        have hv'Ge : 10 ≤ v' := by
          by_contra hlt
          let i : Fin 10 := ⟨v', by omega⟩
          have h1 : val E i.val (fun j => decide (j = i)) = true := by rw [val_in]; simp
          have h2 : val D v (fun j => decide (j = i)) = false := (hSound _ (hUnitF i)).2
          rw [heqV] at h1; rw [h2] at h1; cases h1
        have hExU' : ∃ x, val E u' x = true ∧ val E v' x = false := by
          obtain ⟨x, h1, h2⟩ := hExU; exact ⟨x, by rw [heqU]; exact h1, by rw [heqV]; exact h2⟩
        have hExV' : ∃ x, val E u' x = false ∧ val E v' x = true := by
          obtain ⟨x, h1, h2⟩ := hExV; exact ⟨x, by rw [heqU]; exact h1, by rw [heqV]; exact h2⟩
        have hSound' : ∀ x, F x = false → val E u' x = false ∧ val E v' x = false := by
          intro x hx; rw [heqU, heqV]; exact hSound x hx
        have hComp' : ∀ x, F x = true → val E u' x = true ∨ val E v' x = true := by
          intro x hx; rw [heqU, heqV]; exact hComp x hx
        exact ih E.gates.length (by omega) E u' v' rfl (by omega)
          ⟨hfE, hbE, hnotE, hu'Ge, hu', hv'Ge, hv', hExU', hExV', hSound', hComp'⟩
      -- Step 1: eliminate dead gates
      by_cases hDead : ∃ k < D.gates.length, ¬ InOutCone 10 D (10 + k) u ∧ ¬ InOutCone 10 D (10 + k) v
      · obtain ⟨k, hk, hnu, hnv⟩ := hDead
        obtain ⟨hfE, hbE, hnotE, hszE⟩ := erase_meta D hfD hbD hnotD k 0 hk (by omega)
        let P' (w : ℕ) : Prop := w < 10 ∨ InOutCone 10 D w u ∨ InOutCone 10 D w v
        have hDown' : ∀ m < D.gates.length, P' (10 + m) → ∀ w ∈ (gateAt D m).inputs, P' w := by
          intro m hm hPm w hw
          by_cases hw10 : 10 ≤ w
          · rcases hPm with hlt | h1 | h2
            · omega
            · exact Or.inr (Or.inl (inOutCone_step D hbD m w u hm hw hw10 h1))
            · exact Or.inr (Or.inr (inOutCone_step D hbD m w v hm hw hw10 h2))
          · exact Or.inl (by omega)
        have hNotP : ¬ P' (10 + k) := by
          rintro (hlt | h1 | h2)
          · omega
          · exact hnu h1
          · exact hnv h2
        have hEv := erase_eval D hfD hbD hnotD k 0 hk (by omega) P' hDown' (Or.inl hNotP)
        exact shrink_of_eq (eraseGate 10 D k 0) (eraseRedirect 10 k 0 u) (eraseRedirect 10 k 0 v)
          hfE hbE hnotE (by omega)
          (redirect_lt D.gates.length _ k 0 u hszE hk (by omega) huLt)
          (redirect_lt D.gates.length _ k 0 v hszE hk (by omega) hvLt)
          (fun x => hEv x u (Or.inr (Or.inl (Or.inl rfl))))
          (fun x => hEv x v (Or.inr (Or.inr (Or.inl rfl))))
      have hNoDead : ∀ k < D.gates.length, InOutCone 10 D (10 + k) u ∨ InOutCone 10 D (10 + k) v := by
        intro k hk; by_contra h; push Not at h; exact hDead ⟨k, hk, h⟩
      -- Step 2: eliminate wire aliases
      by_cases hSameWire : ∃ k < D.gates.length, ∃ p < 10 + k, ∀ x : Fin 10 → Bool, val D (10 + k) x = val D p x
      · obtain ⟨k, hk, p, hp, heq⟩ := hSameWire
        obtain ⟨hfE, hbE, hnotE, hszE⟩ := erase_meta D hfD hbD hnotD k p hk hp
        have hEv := erase_eval D hfD hbD hnotD k p hk hp (fun _ => True)
          (fun _ _ _ _ _ => trivial) (Or.inr ⟨heq, trivial⟩)
        exact shrink_of_eq (eraseGate 10 D k p) (eraseRedirect 10 k p u) (eraseRedirect 10 k p v)
          hfE hbE hnotE (by omega)
          (redirect_lt D.gates.length _ k p u hszE hk hp huLt)
          (redirect_lt D.gates.length _ k p v hszE hk hp hvLt)
          (fun x => hEv x u trivial)
          (fun x => hEv x v trivial)
      have hNoSame : ∀ k < D.gates.length, ∀ p < 10 + k, ∃ x : Fin 10 → Bool, val D (10 + k) x ≠ val D p x := by
        intro k hk p hp; by_contra h; push Not at h; exact hSameWire ⟨k, hk, p, hp, h⟩
      have hNotLen1 (k : ℕ) (hk : k < D.gates.length) (hAO : (gateAt D k).op = .and ∨ (gateAt D k).op = .or) :
          (gateAt D k).inputs.length ≠ 1 := by
        intro hlen
        obtain ⟨p, hp_eq⟩ := List.length_eq_one_iff.mp hlen
        have hp_lt : p < 10 + k := hbD k hk p (by rw [hp_eq]; simp)
        obtain ⟨x, hne⟩ := hNoSame k hk p hp_lt
        apply hne
        rw [val_gate_rb D hbD k hk x, hp_eq]
        rcases hAO with h | h
        · rw [h]; change ([val D p x]).all id = val D p x; simp
        · rw [h]; change ([val D p x]).any id = val D p x; simp
      have hDistinctOfLen2 (k : ℕ) (hk : k < D.gates.length)
          (hAO : (gateAt D k).op = .and ∨ (gateAt D k).op = .or)
          (hlen : (gateAt D k).inputs.length = 2) : (gateAt D k).inputs.Nodup := by
        obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
        rw [hpq]
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
          not_false_eq_true, and_true]
        intro heq; subst heq
        have hp_lt : p < 10 + k := hbD k hk p (by rw [hpq]; simp)
        obtain ⟨x, hne⟩ := hNoSame k hk p hp_lt
        apply hne
        rw [val_gate_rb D hbD k hk x, hpq]
        rcases hAO with h | h
        · rw [h]; change ([val D p x, val D p x]).all id = val D p x; simp
        · rw [h]; change ([val D p x, val D p x]).any id = val D p x; simp
      -- Step 3: eliminate ANY constant gate (either constant false or constant true)
      by_cases hConst : ∃ k < D.gates.length, ∃ c : Bool, ∀ x : Fin 10 → Bool, val D (10 + k) x = c
      · let Cs := (Finset.range D.gates.length).filter fun k =>
          ∃ c : Bool, ∀ x : Fin 10 → Bool, val D (10 + k) x = c
        have hCsNE : Cs.Nonempty := by
          obtain ⟨k, hk, hc⟩ := hConst
          exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hc⟩⟩
        let m := Cs.max' hCsNE
        have hmMem := Finset.mem_filter.mp (Finset.max'_mem Cs hCsNE)
        have hmLt : m < D.gates.length := Finset.mem_range.mp hmMem.1
        obtain ⟨c, hmC⟩ := hmMem.2
        have hmu : u ≠ 10 + m := by
          intro h
          cases c with
          | false =>
            obtain ⟨x, hxU, _⟩ := hExU
            rw [h, hmC x] at hxU; cases hxU
          | true =>
            have h0 := (hSound (fun _ => false) hZeroF).1
            rw [h, hmC _] at h0; cases h0
        have hmv : v ≠ 10 + m := by
          intro h
          cases c with
          | false =>
            obtain ⟨x, _, hxV⟩ := hExV
            rw [h, hmC x] at hxV; cases hxV
          | true =>
            have h0 := (hSound (fun _ => false) hZeroF).2
            rw [h, hmC _] at h0; cases h0
        have hNoRead : ∀ k < D.gates.length, 10 + m ∉ (gateAt D k).inputs := by
          intro k hk hmem
          have hmk : m < k := by have := hbD k hk (10 + m) hmem; omega
          obtain ⟨hop, hlenLe⟩ := hfD (gateAt D k) (gateAt_mem D k hk)
          rcases hop with hand | hor | hnot
          · have hlenNe0 : (gateAt D k).inputs.length ≠ 0 := by
              intro h0; rw [List.length_eq_zero_iff.mp h0] at hmem; exact List.not_mem_nil hmem
            have hlen2 : (gateAt D k).inputs.length = 2 := by
              have := hNotLen1 k hk (Or.inl hand); omega
            obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen2
            rw [hpq] at hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            cases c with
            | false =>
              have hkF : ∀ x : Fin 10 → Bool, val D (10 + k) x = false := by
                intro x
                rw [val_gate_rb D hbD k hk x, hand, hpq]
                rcases hmem with rfl | rfl
                · change (val D (10 + m) x && (val D q x && true)) = false; rw [hmC x]; rfl
                · change (val D p x && (val D (10 + m) x && true)) = false; rw [hmC x]; simp
              have hle := Finset.le_max' Cs k
                (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, false, hkF⟩)
              omega
            | true =>
              rcases hmem with rfl | rfl
              · obtain ⟨x, hne⟩ := hNoSame k hk q (hbD k hk q (by rw [hpq]; simp))
                apply hne; rw [val_gate_rb D hbD k hk x, hand, hpq]
                change (val D (10 + m) x && (val D q x && true)) = val D q x; rw [hmC x]; simp
              · obtain ⟨x, hne⟩ := hNoSame k hk p (hbD k hk p (by rw [hpq]; simp))
                apply hne; rw [val_gate_rb D hbD k hk x, hand, hpq]
                change (val D p x && (val D (10 + m) x && true)) = val D p x; rw [hmC x]; simp
          · have hlenNe0 : (gateAt D k).inputs.length ≠ 0 := by
              intro h0; rw [List.length_eq_zero_iff.mp h0] at hmem; exact List.not_mem_nil hmem
            have hlen2 : (gateAt D k).inputs.length = 2 := by
              have := hNotLen1 k hk (Or.inr hor); omega
            obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen2
            rw [hpq] at hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            cases c with
            | true =>
              have hkT : ∀ x : Fin 10 → Bool, val D (10 + k) x = true := by
                intro x
                rw [val_gate_rb D hbD k hk x, hor, hpq]
                rcases hmem with rfl | rfl
                · change (val D (10 + m) x || (val D q x || false)) = true; rw [hmC x]; rfl
                · change (val D p x || (val D (10 + m) x || false)) = true; rw [hmC x]; simp
              have hle := Finset.le_max' Cs k
                (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, true, hkT⟩)
              omega
            | false =>
              rcases hmem with rfl | rfl
              · obtain ⟨x, hne⟩ := hNoSame k hk q (hbD k hk q (by rw [hpq]; simp))
                apply hne; rw [val_gate_rb D hbD k hk x, hor, hpq]
                change (val D (10 + m) x || (val D q x || false)) = val D q x; rw [hmC x]; simp
              · obtain ⟨x, hne⟩ := hNoSame k hk p (hbD k hk p (by rw [hpq]; simp))
                apply hne; rw [val_gate_rb D hbD k hk x, hor, hpq]
                change (val D p x || (val D (10 + m) x || false)) = val D p x; rw [hmC x]; simp
          · have hlen1 := hnotD k hk hnot
            obtain ⟨p, hp_eq⟩ := List.length_eq_one_iff.mp hlen1
            rw [hp_eq] at hmem
            have hpEq : 10 + m = p := List.mem_singleton.mp hmem
            have hkC : ∀ x : Fin 10 → Bool, val D (10 + k) x = !c := by
              intro x
              rw [val_gate_rb D hbD k hk x, hnot, hp_eq, ← hpEq]
              change (!(val D (10 + m) x)) = !c
              rw [hmC x]
            have hle := Finset.le_max' Cs k
              (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, !c, hkC⟩)
            omega
        obtain ⟨hfE, hbE, hnotE, hszE⟩ := erase_meta D hfD hbD hnotD m 0 hmLt (by omega)
        have hEv := erase_eval D hfD hbD hnotD m 0 hmLt (by omega) (fun w => w ≠ 10 + m)
          (fun k hk _ w hw hEq => hNoRead k hk (hEq ▸ hw)) (Or.inl (fun h => h rfl))
        exact shrink_of_eq (eraseGate 10 D m 0) (eraseRedirect 10 m 0 u) (eraseRedirect 10 m 0 v)
          hfE hbE hnotE (by omega)
          (redirect_lt D.gates.length _ m 0 u hszE hmLt (by omega) huLt)
          (redirect_lt D.gates.length _ m 0 v hszE hmLt (by omega) hvLt)
          (fun x => hEv x u hmu)
          (fun x => hEv x v hmv)
      have hNonConstT (k : ℕ) (hk : k < D.gates.length) : ∃ x : Fin 10 → Bool, val D (10 + k) x = true := by
        by_contra h
        push Not at h
        exact hConst ⟨k, hk, false, fun x => Bool.eq_false_iff.mpr (h x)⟩
      have hNonConstF (k : ℕ) (hk : k < D.gates.length) : ∃ x : Fin 10 → Bool, val D (10 + k) x = false := by
        by_contra h
        push Not at h
        exact hConst ⟨k, hk, true, fun x => Bool.eq_true_of_not_eq_false (h x)⟩
      have hShape (k : ℕ) (hk : k < D.gates.length) :
          (((gateAt D k).op = .and ∨ (gateAt D k).op = .or) ∧
            (gateAt D k).inputs.length = 2 ∧ (gateAt D k).inputs.Nodup) ∨
          ((gateAt D k).op = .not ∧ (gateAt D k).inputs.length = 1) := by
        obtain ⟨hop, hle⟩ := hfD (gateAt D k) (gateAt_mem D k hk)
        rcases hop with hand | hor | hnot
        · have hne0 : (gateAt D k).inputs.length ≠ 0 := by
            intro h0
            have hnil := List.length_eq_zero_iff.mp h0
            exact hConst ⟨k, hk, true, fun x => by rw [val_gate_rb D hbD k hk x, hand, hnil]; rfl⟩
          have hne1 := hNotLen1 k hk (Or.inl hand)
          have hlen2 : (gateAt D k).inputs.length = 2 := by omega
          exact Or.inl ⟨Or.inl hand, hlen2, hDistinctOfLen2 k hk (Or.inl hand) hlen2⟩
        · have hne0 : (gateAt D k).inputs.length ≠ 0 := by
            intro h0
            have hnil := List.length_eq_zero_iff.mp h0
            exact hConst ⟨k, hk, false, fun x => by rw [val_gate_rb D hbD k hk x, hor, hnil]; rfl⟩
          have hne1 := hNotLen1 k hk (Or.inr hor)
          have hlen2 : (gateAt D k).inputs.length = 2 := by omega
          exact Or.inl ⟨Or.inr hor, hlen2, hDistinctOfLen2 k hk (Or.inr hor) hlen2⟩
        · exact Or.inr ⟨hnot, hnotD k hk hnot⟩
      -- Helper: transport the clean counterexample by any Petersen automorphism (σ, τ)
      have apply_auto (σ τ : Fin 10 → Fin 10) (hst : ∀ i, σ (τ i) = i) (hts : ∀ i, τ (σ i) = i)
          (hadj : ∀ i j, adj (σ i) (σ j) = adj i j) :
          let D' := permCircuit σ D
          let W' := fun (x : Fin 10 → Bool) (w : ℕ) => (D'.wires (List.ofFn x)).getD w false
          ReadsBack 10 D' ∧ D'.size ≤ 18 ∧
          (∀ k < D'.size,
            let g := gateAt D' k
            (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup) ∨
              (g.op = .not ∧ g.inputs.length = 1)) ∧
            (InOutCone 10 D' (10 + k) u ∨ InOutCone 10 D' (10 + k) v) ∧
            (∀ p < 10 + k, ∃ x : Fin 10 → Bool, W' x (10 + k) ≠ W' x p) ∧
            ∀ b : Bool, ∃ x : Fin 10 → Bool, W' x (10 + k) = b) ∧
          (∀ b : Bool, ∃ x : Fin 10 → Bool, W' x u = b ∧ W' x v = !b) ∧
          (∀ x, G x = false → W' x u = false ∧ W' x v = false) ∧
          (∀ x, G x = true → W' x u = true ∨ W' x v = true) := by
        have hMapInj : Function.Injective (mapWire σ) := by
          intro a b hab
          dsimp only [mapWire] at hab
          split_ifs at hab with ha hb hb
          · have hFin : σ ⟨a, ha⟩ = σ ⟨b, hb⟩ := Fin.ext hab
            have := congrArg τ hFin
            rw [hts, hts] at this
            exact congrArg Fin.val this
          · have := (σ ⟨a, ha⟩).isLt; omega
          · have := (σ ⟨b, hb⟩).isLt; omega
          · exact hab
        have hLenP : (permCircuit σ D).gates.length = D.gates.length := perm_len σ D
        have hbP : ReadsBack 10 (permCircuit σ D) := by
          intro k hk w hw
          have hkD : k < D.gates.length := by omega
          rw [perm_gateAt σ D k hkD] at hw
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hw
          have haLt := hbD k hkD a ha
          dsimp only [mapWire]; split_ifs with ha10
          · exact Nat.lt_of_lt_of_le (σ ⟨a, ha10⟩).isLt (by omega)
          · exact haLt
        have hValU (x : Fin 10 → Bool) : val (permCircuit σ D) u x = val D u (x ∘ σ) := by
          have hEq : u = 10 + (u - 10) := by omega
          rw [hEq]; exact perm_val σ D hbD x (u - 10) (by omega)
        have hValV (x : Fin 10 → Bool) : val (permCircuit σ D) v x = val D v (x ∘ σ) := by
          have hEq : v = 10 + (v - 10) := by omega
          rw [hEq]; exact perm_val σ D hbD x (v - 10) (by omega)
        have hCleanP : ∀ k < (permCircuit σ D).size,
            let g := gateAt (permCircuit σ D) k
            (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup) ∨
              (g.op = .not ∧ g.inputs.length = 1)) ∧
            (InOutCone 10 (permCircuit σ D) (10 + k) u ∨ InOutCone 10 (permCircuit σ D) (10 + k) v) ∧
            (∀ p < 10 + k, ∃ x : Fin 10 → Bool, val (permCircuit σ D) (10 + k) x ≠ val (permCircuit σ D) p x) ∧
            ∀ b : Bool, ∃ x : Fin 10 → Bool, val (permCircuit σ D) (10 + k) x = b := by
          intro k hk
          change k < (permCircuit σ D).gates.length at hk
          have hkD : k < D.gates.length := by omega
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [perm_gateAt σ D k hkD]
            rcases hShape k hkD with ⟨hAO, hlen, hnd⟩ | ⟨hN, hlen⟩
            · exact Or.inl ⟨hAO, by simp [hlen], List.Nodup.map hMapInj hnd⟩
            · exact Or.inr ⟨hN, by simp [hlen]⟩
          · rcases hNoDead k hkD with h1 | h2
            · left
              rcases h1 with hEq | ⟨h10, hu10, hcone⟩
              · exact Or.inl hEq
              · exact Or.inr ⟨h10, hu10, (perm_inCone σ D _ _).mpr hcone⟩
            · right
              rcases h2 with hEq | ⟨h10, hv10, hcone⟩
              · exact Or.inl hEq
              · exact Or.inr ⟨h10, hv10, (perm_inCone σ D _ _).mpr hcone⟩
          · intro p hp
            by_cases hp10 : p < 10
            · let i : Fin 10 := ⟨p, hp10⟩
              obtain ⟨y, hne⟩ := hNoSame k hkD (τ i).val (by have := (τ i).isLt; omega)
              refine ⟨y ∘ τ, ?_⟩
              rw [perm_val σ D hbD (y ∘ τ) k hkD]
              have hcomp : (y ∘ τ) ∘ σ = y := by funext j; exact congrArg y (hts j)
              rw [hcomp]
              change val D (10 + k) y ≠ val (permCircuit σ D) i.val (y ∘ τ)
              rw [val_in (permCircuit σ D) (y ∘ τ) i]
              change val D (10 + k) y ≠ y (τ i)
              rw [← val_in D y (τ i)]
              exact hne
            · obtain ⟨y, hne⟩ := hNoSame k hkD p hp
              refine ⟨y ∘ τ, ?_⟩
              have hcomp : (y ∘ τ) ∘ σ = y := by funext j; exact congrArg y (hts j)
              have hpEq : p = 10 + (p - 10) := by omega
              rw [perm_val σ D hbD (y ∘ τ) k hkD, hpEq, perm_val σ D hbD (y ∘ τ) (p - 10) (by omega),
                  hcomp, ← hpEq]
              exact hne
          · intro b
            cases b with
            | true =>
              obtain ⟨y, hy⟩ := hNonConstT k hkD
              refine ⟨y ∘ τ, ?_⟩
              have hcomp : (y ∘ τ) ∘ σ = y := by funext j; exact congrArg y (hts j)
              rw [perm_val σ D hbD (y ∘ τ) k hkD, hcomp]; exact hy
            | false =>
              obtain ⟨y, hy⟩ := hNonConstF k hkD
              refine ⟨y ∘ τ, ?_⟩
              have hcomp : (y ∘ τ) ∘ σ = y := by funext j; exact congrArg y (hts j)
              rw [perm_val σ D hbD (y ∘ τ) k hkD, hcomp]; exact hy
        refine ⟨hbP, by change (permCircuit σ D).gates.length ≤ 18; omega, hCleanP, ?_, ?_, ?_⟩
        · intro b
          cases b with
          | true =>
            obtain ⟨y, h1, h2⟩ := hExU
            refine ⟨y ∘ τ, ?_, ?_⟩
            · have hcomp : (y ∘ τ) ∘ σ = y := by funext j; exact congrArg y (hts j)
              change val (permCircuit σ D) u (y ∘ τ) = true; rw [hValU, hcomp]; exact h1
            · have hcomp : (y ∘ τ) ∘ σ = y := by funext j; exact congrArg y (hts j)
              change val (permCircuit σ D) v (y ∘ τ) = false; rw [hValV, hcomp]; exact h2
          | false =>
            obtain ⟨y, h1, h2⟩ := hExV
            refine ⟨y ∘ τ, ?_, ?_⟩
            · have hcomp : (y ∘ τ) ∘ σ = y := by funext j; exact congrArg y (hts j)
              change val (permCircuit σ D) u (y ∘ τ) = false; rw [hValU, hcomp]; exact h1
            · have hcomp : (y ∘ τ) ∘ σ = y := by funext j; exact congrArg y (hts j)
              change val (permCircuit σ D) v (y ∘ τ) = true; rw [hValV, hcomp]; exact h2
        · intro x hx
          rw [hGF, ← hAutoF σ τ hst hts hadj x] at hx
          change val (permCircuit σ D) u x = false ∧ val (permCircuit σ D) v x = false
          rw [hValU, hValV]; exact hSound (x ∘ σ) hx
        · intro x hx
          rw [hGF, ← hAutoF σ τ hst hts hadj x] at hx
          change val (permCircuit σ D) u x = true ∨ val (permCircuit σ D) v x = true
          rw [hValU, hValV]; exact hComp (x ∘ σ) hx
      -- Step 4: normalize gate 0 by Aut(Petersen) = S_5 and dispatch to the 4 children!
      have h0Lt : 0 < D.gates.length := by omega
      have hGet0 (σ : Fin 10 → Fin 10) :
          (permCircuit σ D).gates[0]? = some (gateAt (permCircuit σ D) 0) := by
        have h0P : 0 < (permCircuit σ D).gates.length := by rw [perm_len]; exact h0Lt
        rw [List.getElem?_eq_getElem h0P, gateAt_eq_getElem _ 0 h0P]
      rcases hShape 0 h0Lt with ⟨hAO, hlen2, hnd⟩ | ⟨hNot, hlen1⟩
      · obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen2
        have haLt : a < 10 := hbD 0 h0Lt a (by rw [hab]; simp)
        have hbLt : b < 10 := hbD 0 h0Lt b (by rw [hab]; simp)
        have habNe : a ≠ b := by
          rw [hab] at hnd
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
          exact hnd.1
        let aF : Fin 10 := ⟨a, haLt⟩
        let bF : Fin 10 := ⟨b, hbLt⟩
        have habFNe : aF ≠ bF := fun h => habNe (congrArg Fin.val h)
        cases hEdge : adj aF bF with
        | true =>
          have hDisj := of_decide_eq_true (show decide ((toPair aF).1 ≠ (toPair bF).1 ∧
            (toPair aF).1 ≠ (toPair bF).2 ∧ (toPair aF).2 ≠ (toPair bF).1 ∧
            (toPair aF).2 ≠ (toPair bF).2) = true from hEdge)
          obtain ⟨h13, h14, h23, h24⟩ := hDisj
          have h12 := hPairNe aF
          have h34 := hPairNe bF
          let π := mkP4 (toPair aF).1 (toPair aF).2 (toPair bF).1 (toPair bF).2
          let π' := mkQ4 (toPair aF).1 (toPair aF).2 (toPair bF).1 (toPair bF).2
          have hπ1 : ∀ k, π (π' k) = k := fun k => (hP4 _ _ _ _ k h12 h13 h14 h23 h24 h34).1
          have hπ2 : ∀ k, π' (π k) = k := fun k => (hP4 _ _ _ _ k h12 h13 h14 h23 h24 h34).2
          obtain ⟨hst, hts, hadj⟩ := liftP_bij π π' hπ1 hπ2
          obtain ⟨hMapA, hMapB⟩ := hEdgeMap aF bF hEdge
          have hGate0 : (permCircuit (liftP π) D).gates[0]? =
              some ⟨(gateAt D 0).op, [0, 1]⟩ := by
            rw [hGet0, perm_gateAt _ D 0 h0Lt, hab]
            simp only [List.map_cons, List.map_nil]
            have hmA : mapWire (liftP π) a = 0 := by
              dsimp only [mapWire]; simp only [haLt, ↓reduceDIte]; exact congrArg Fin.val hMapA
            have hmB : mapWire (liftP π) b = 1 := by
              dsimp only [mapWire]; simp only [hbLt, ↓reduceDIte]; exact congrArg Fin.val hMapB
            rw [hmA, hmB]
          obtain ⟨hbP, hszP, hCl, hEUV, hSo, hCo⟩ :=
            apply_auto (liftP π) (liftP π') hst hts hadj
          rcases hAO with hand | hor
          · rw [hand] at hGate0
            obtain ⟨x, hxG, hxU, hxV⟩ :=
              firstAndEdge (permCircuit (liftP π) D) u v hbP hszP hGate0 hCl hEUV hSo
            rcases hCo x hxG with h | h
            · rw [hxU] at h; cases h
            · rw [hxV] at h; cases h
          · rw [hor] at hGate0
            obtain ⟨x, hxG, hxU, hxV⟩ :=
              firstOr (permCircuit (liftP π) D) u v hbP hszP ⟨true, hGate0⟩ hCl hEUV hSo
            rcases hCo x hxG with h | h
            · rw [hxU] at h; cases h
            · rw [hxV] at h; cases h
        | false =>
          obtain ⟨c, s1, t1, hcs, hct, hst1, hca, hcb⟩ := hNonEdgeShare aF bF habFNe hEdge
          obtain ⟨d, hcd, hsd, htd⟩ := hEx3 c s1 t1 hcs hct hst1
          let e5 : Fin 5 := fifth5 c s1 t1 d
          obtain ⟨hce, hse, hde, hMapA', hMapB'⟩ := hNonEdgeMap c s1 t1 d
            (by simp [hcs, hct, hst1, hcd, hsd, htd])
          let π := mkP4 c s1 d e5
          let π' := mkQ4 c s1 d e5
          have hπ1 : ∀ k, π (π' k) = k := fun k => (hP4 c s1 d e5 k hcs hcd hce hsd hse hde).1
          have hπ2 : ∀ k, π' (π k) = k := fun k => (hP4 c s1 d e5 k hcs hcd hce hsd hse hde).2
          obtain ⟨hst, hts, hadj⟩ := liftP_bij π π' hπ1 hπ2
          have hMapA : liftP π aF = 0 := by rw [← hca]; exact hMapA'
          have hMapB : liftP π bF = 2 := by rw [← hcb]; exact hMapB'
          have hGate0 : (permCircuit (liftP π) D).gates[0]? =
              some ⟨(gateAt D 0).op, [0, 2]⟩ := by
            rw [hGet0, perm_gateAt _ D 0 h0Lt, hab]
            simp only [List.map_cons, List.map_nil]
            have hmA : mapWire (liftP π) a = 0 := by
              dsimp only [mapWire]; simp only [haLt, ↓reduceDIte]; exact congrArg Fin.val hMapA
            have hmB : mapWire (liftP π) b = 2 := by
              dsimp only [mapWire]; simp only [hbLt, ↓reduceDIte]; exact congrArg Fin.val hMapB
            rw [hmA, hmB]
          obtain ⟨hbP, hszP, hCl, hEUV, hSo, hCo⟩ :=
            apply_auto (liftP π) (liftP π') hst hts hadj
          rcases hAO with hand | hor
          · rw [hand] at hGate0
            obtain ⟨x, hxG, hxU, hxV⟩ :=
              firstAndNonEdge (permCircuit (liftP π) D) u v hbP hszP hGate0 hCl hEUV hSo
            rcases hCo x hxG with h | h
            · rw [hxU] at h; cases h
            · rw [hxV] at h; cases h
          · rw [hor] at hGate0
            obtain ⟨x, hxG, hxU, hxV⟩ :=
              firstOr (permCircuit (liftP π) D) u v hbP hszP ⟨false, hGate0⟩ hCl hEUV hSo
            rcases hCo x hxG with h | h
            · rw [hxU] at h; cases h
            · rw [hxV] at h; cases h
      · -- NOT gate: vertex aF ↦ 0
        obtain ⟨a, haEq⟩ := List.length_eq_one_iff.mp hlen1
        have haLt : a < 10 := hbD 0 h0Lt a (by rw [haEq]; simp)
        let aF : Fin 10 := ⟨a, haLt⟩
        have h12 := hPairNe aF
        obtain ⟨c, d, h13, h14, h23, h24, h34⟩ := hEx2 (toPair aF).1 (toPair aF).2 h12
        let π := mkP4 (toPair aF).1 (toPair aF).2 c d
        let π' := mkQ4 (toPair aF).1 (toPair aF).2 c d
        have hπ1 : ∀ k, π (π' k) = k := fun k => (hP4 _ _ _ _ k h12 h13 h14 h23 h24 h34).1
        have hπ2 : ∀ k, π' (π k) = k := fun k => (hP4 _ _ _ _ k h12 h13 h14 h23 h24 h34).2
        obtain ⟨hst, hts, hadj⟩ := liftP_bij π π' hπ1 hπ2
        have hMapA : liftP π aF = 0 := hNotMap aF c d h13 h14 h23 h24 h34
        have hGate0 : (permCircuit (liftP π) D).gates[0]? = some ⟨.not, [0]⟩ := by
          rw [hGet0, perm_gateAt _ D 0 h0Lt, hNot, haEq]
          simp only [List.map_cons, List.map_nil]
          have hmA : mapWire (liftP π) a = 0 := by
            dsimp only [mapWire]; simp only [haLt, ↓reduceDIte]; exact congrArg Fin.val hMapA
          rw [hmA]
        obtain ⟨hbP, hszP, hCl, hEUV, hSo, hCo⟩ :=
          apply_auto (liftP π) (liftP π') hst hts hadj
        obtain ⟨x, hxG, hxU, hxV⟩ :=
          firstNot (permCircuit (liftP π) D) u v hbP hszP hGate0 hCl hEUV hSo
        rcases hCo x hxG with h | h
        · rw [hxU] at h; cases h
        · rw [hxV] at h; cases h
  -- Entry point: combine x1 :: x2.gates, sanitize, and call main_ind
  intro g0 C u v hg0 hC hCsz _ _ hExU hExV hSound
  let D0 : Circuit := ⟨g0 :: C.gates, 0⟩
  change (∃ x, val D0 u x = true ∧ val D0 v x = false) at hExU
  change (∃ x, val D0 u x = false ∧ val D0 v x = true) at hExV
  change (∀ x, F x = false → val D0 u x = false ∧ val D0 v x = false) at hSound
  by_contra hNoMiss
  push Not at hNoMiss
  have hComp : ∀ x : Fin 10 → Bool, F x = true → val D0 u x = true ∨ val D0 v x = true := by
    intro x hx
    have h := hNoMiss x hx
    cases hu : val D0 u x with
    | true => exact Or.inl rfl
    | false =>
      cases hv : val D0 v x with
      | true => exact Or.inr rfl
      | false => exact False.elim (h hu hv)
  have hfD0 : FanInTwo D0 := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hmem
    · exact hg0 g List.mem_cons_self
    · exact hC g hmem
  have hSz0 : D0.gates.length ≤ 18 := by
    change (g0 :: C.gates).length ≤ 18
    change C.gates.length ≤ 17 at hCsz
    simp only [List.length_cons]; omega
  let Ds := sanitize D0
  obtain ⟨hfS, hbS, hnotS⟩ := sanitize_meta D0 hfD0
  have hSzS : Ds.gates.length = D0.gates.length := sanitize_len D0
  have hValS (x : Fin 10 → Bool) (w : ℕ) : val Ds w x = val D0 w x := sanitize_val D0 hfD0 x w
  have huGe : 10 ≤ u := by
    by_contra hlt
    let i : Fin 10 := ⟨u, by omega⟩
    have h1 : val D0 i.val (fun j => decide (j = i)) = true := by rw [val_in]; simp
    have h2 : val D0 u (fun j => decide (j = i)) = false := (hSound _ (hUnitF i)).1
    change val D0 u (fun j => decide (j = i)) = true at h1
    rw [h2] at h1; cases h1
  have hvGe : 10 ≤ v := by
    by_contra hlt
    let i : Fin 10 := ⟨v, by omega⟩
    have h1 : val D0 i.val (fun j => decide (j = i)) = true := by rw [val_in]; simp
    have h2 : val D0 v (fun j => decide (j = i)) = false := (hSound _ (hUnitF i)).2
    change val D0 v (fun j => decide (j = i)) = true at h1
    rw [h2] at h1; cases h1
  have huLt : u < 10 + Ds.gates.length := by
    by_contra hge
    obtain ⟨x, hxU, _⟩ := hExU
    rw [← hValS, val_oob Ds x u (by omega)] at hxU; cases hxU
  have hvLt : v < 10 + Ds.gates.length := by
    by_contra hge
    obtain ⟨x, _, hxV⟩ := hExV
    rw [← hValS, val_oob Ds x v (by omega)] at hxV; cases hxV
  exact main_ind Ds.gates.length Ds u v rfl (by omega)
    ⟨hfS, hbS, hnotS, huGe, huLt, hvGe, hvLt,
      by obtain ⟨x, h1, h2⟩ := hExU; exact ⟨x, by rw [hValS]; exact h1, by rw [hValS]; exact h2⟩,
      by obtain ⟨x, h1, h2⟩ := hExV; exact ⟨x, by rw [hValS]; exact h1, by rw [hValS]; exact h2⟩,
      fun x hx => by rw [hValS, hValS]; exact hSound x hx,
      fun x hx => by rw [hValS, hValS]; exact hComp x hx⟩
