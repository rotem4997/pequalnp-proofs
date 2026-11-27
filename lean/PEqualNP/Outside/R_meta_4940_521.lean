import Mathlib.Tactic.ByContra
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.SharedOr PEqualNP.NotBracket

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_4940_521
    (hBound17 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)))) → (17 : ℕ) + PEqualNP.NotBracket.notCount x1 ≤ x1.size))
    (hBound15 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ) → Bool), x3 (9 : Fin (10 : ℕ)) = Bool.false → x1.eval (List.ofFn x3) = [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x5 : ℕ) => x3 (Fin.ofNat (10 : ℕ) (x5 / (10 : ℕ))) && x3 (Fin.ofNat (10 : ℕ) (x5 % (10 : ℕ)))) → (15 : ℕ) + PEqualNP.NotBracket.notCount x1 ≤ x1.size)
    (hMono : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x5 : ℕ) => x4 (Fin.ofNat (10 : ℕ) (x5 / (10 : ℕ))) && x4 (Fin.ofNat (10 : ℕ) (x5 % (10 : ℕ))))
    (hNonMono :
      let t := (10 : ℕ)
      let opN := PEqualNP.CircuitLowerBounds.GateOp.not
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        let n := PEqualNP.NotBracket.notCount C
        let s := C.size
        let ga := PEqualNP.MetaComplexity.NestedCover.gateAt C
        let isN : ℕ → ℕ → Prop := fun j u => (ga j).op = opN ∧ (ga j).inputs = [u]
        let w : ℕ → (Fin t → Bool) → Bool := fun i x => (C.wires (List.ofFn x)).getD i false
        PEqualNP.MetaComplexity.FanInTwo C →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack t C →
        C.output = 9 + s →
        (∀ x : Fin t → Bool, w C.output x =
          ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any fun e =>
            x (Fin.ofNat t (e / t)) && x (Fin.ofNat t (e % t))) →
        (∀ k < s,
          ((ga k).inputs.length = 1 ↔ (ga k).op = opN) ∧ (ga k).inputs.Nodup ∧
          PEqualNP.SharedOr.InOutCone t C (t + k) C.output ∧
          (∀ p < t + k, w (t + k) ≠ w p) ∧
          ∀ b : Bool, w (t + k) ≠ fun _ => b) →
        (∀ (v : Fin t) (S : Finset (Fin s)),
          (∀ k ∈ S, (ga k.val).op ≠ opN ∧
            (v.val ∈ (ga k.val).inputs ∨ ∃ j < s, isN j v.val ∧ t + j ∈ (ga k.val).inputs)) →
          S.card + 15 + n ≤ s) →
        ((s = 19 ∧ n = 1 ∧ (ga 18).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∀ j u, j < s → u < t → isN j u → u = 0) ∨
         (s = 17 + n ∧ 1 ≤ n ∧ n ≤ 2 ∧ ∃ k0 < s,
           (∀ j < k0, (ga j).op = opN) ∧
           (((ga k0).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
             (ga k0).inputs ∈ [[0, 1], [0, 2]]) ∨
            (k0 = 2 ∧ isN 0 0 ∧ (isN 1 1 ∨ isN 1 2) ∧
             (ga 2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (ga 2).inputs = [t, 11])))) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size = (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  -- Decidable Petersen & S_5 automorphism block BEFORE `classical`
  let F : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let Plist : (Fin 10 → Bool) → Bool := fun x =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any fun e =>
      x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))
  have hF_eq_P : ∀ x : Fin 10 → Bool, F x = Plist x := by
    intro x
    change F x = (((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) ||
      ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 4 && x 9) ||
      ((x 5 && x 7) || ((x 7 && x 9) || ((x 9 && x 6) || ((x 6 && x 8) || ((x 8 && x 5) || false))))))))))))))))
    dsimp only [F]
    simp only [Bool.or_false]
    ac_rfl
  let toPair : Fin 10 → Fin 5 × Fin 5 := fun v =>
    if v = 0 then (0, 1) else if v = 1 then (2, 3) else if v = 2 then (0, 4) else
    if v = 3 then (1, 2) else if v = 4 then (3, 4) else if v = 5 then (2, 4) else
    if v = 6 then (1, 4) else if v = 7 then (1, 3) else if v = 8 then (0, 3) else (0, 2)
  let fromPair : Fin 5 → Fin 5 → Fin 10 := fun a b =>
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
  let pAdj : Fin 10 → Fin 10 → Bool := fun u v =>
    let p := toPair u; let q := toPair v
    decide (p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2)
  have hP_iff_adj : ∀ x : Fin 10 → Bool, Plist x = true ↔ ∃ u v : Fin 10, pAdj u v = true ∧ x u = true ∧ x v = true := by
    have hEdgeAdj : ∀ e ∈ ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ),
        pAdj (Fin.ofNat 10 (e / 10)) (Fin.ofNat 10 (e % 10)) = true := by decide
    have hAdjMem : ∀ u v : Fin 10, pAdj u v = true →
        ∃ e ∈ ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ),
          (Fin.ofNat 10 (e / 10) = u ∧ Fin.ofNat 10 (e % 10) = v) ∨
          (Fin.ofNat 10 (e / 10) = v ∧ Fin.ofNat 10 (e % 10) = u) := by decide
    intro x
    dsimp only [Plist]
    rw [List.any_eq_true]
    constructor
    · rintro ⟨e, he, hval⟩
      rw [Bool.and_eq_true] at hval
      exact ⟨Fin.ofNat 10 (e / 10), Fin.ofNat 10 (e % 10), hEdgeAdj e he, hval.1, hval.2⟩
    · rintro ⟨u, v, huv, hxu, hxv⟩
      obtain ⟨e, he, hc⟩ := hAdjMem u v huv
      refine ⟨e, he, (Bool.and_eq_true _ _).mpr ?_⟩
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact ⟨hxu, hxv⟩
      · rw [h1, h2]; exact ⟨hxv, hxu⟩
  have hAdj_irrefl : ∀ v : Fin 10, pAdj v v = false := by decide
  have hAdj_symm : ∀ u v : Fin 10, pAdj u v = pAdj v u := by decide
  have hSepWitness : ∀ u w : Fin 10, u ≠ w → ∃ z : Fin 10, z ≠ u ∧ z ≠ w ∧ pAdj u z = true ∧ pAdj w z = false := by decide
  have hAvoidEdge : ∀ v : Fin 10, ∃ a b : Fin 10, a ≠ v ∧ b ≠ v ∧ pAdj a b = true := by decide
  have hPair_inv : ∀ v : Fin 10, (toPair v).1 ≠ (toPair v).2 ∧ fromPair (toPair v).1 (toPair v).2 = v := by decide
  have hFromPair_symm : ∀ a b : Fin 5, fromPair a b = fromPair b a := by decide
  have hFromPair_toPair : ∀ a b : Fin 5, a ≠ b →
      (toPair (fromPair a b) = (a, b) ∨ toPair (fromPair a b) = (b, a)) := by decide
  -- Build S_5 permutations mapping any ordered (u,w) to (0,1) or (0,2), and any v to 9
  let liftS5 : (Fin 5 → Fin 5) → Fin 10 → Fin 10 := fun π v => fromPair (π (toPair v).1) (π (toPair v).2)
  let mkPerm5 : Fin 5 → Fin 5 → Fin 5 → Fin 5 → Fin 5 → (Fin 5 → Fin 5) := fun a0 a1 a2 a3 a4 i =>
    if i = a0 then 0 else if i = a1 then 1 else if i = a2 then 2 else if i = a3 then 3 else 4
  let mkPerm5Inv : Fin 5 → Fin 5 → Fin 5 → Fin 5 → Fin 5 → (Fin 5 → Fin 5) := fun a0 a1 a2 a3 a4 i =>
    if i = 0 then a0 else if i = 1 then a1 else if i = 2 then a2 else if i = 3 then a3 else a4
  let findOut : List (Fin 5) → Fin 5 := fun banned =>
    if !(banned.contains (0 : Fin 5)) then 0
    else if !(banned.contains (1 : Fin 5)) then 1
    else if !(banned.contains (2 : Fin 5)) then 2
    else if !(banned.contains (3 : Fin 5)) then 3
    else 4
  let pairPerm5 : Fin 10 → Fin 10 → (Fin 5 → Fin 5) × (Fin 5 → Fin 5) := fun u w =>
    let p := toPair u; let q := toPair w
    if p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 then
      let e := findOut [p.1, p.2, q.1, q.2]
      (mkPerm5 p.1 p.2 q.1 q.2 e, mkPerm5Inv p.1 p.2 q.1 q.2 e)
    else
      let m := if p.1 = q.1 ∨ p.1 = q.2 then p.1 else p.2
      let a' := if p.1 = m then p.2 else p.1
      let c' := if q.1 = m then q.2 else q.1
      let e1 := findOut [m, a', c']
      let e2 := findOut [m, a', c', e1]
      (mkPerm5 m a' e1 e2 c', mkPerm5Inv m a' e1 e2 c')
  have hPairPerm_ok : ∀ u w : Fin 10, u ≠ w →
      let pp := pairPerm5 u w
      (∀ i : Fin 5, pp.2 (pp.1 i) = i ∧ pp.1 (pp.2 i) = i) ∧
      liftS5 pp.1 u = 0 ∧ (liftS5 pp.1 w = 1 ∨ liftS5 pp.1 w = 2) := by decide
  let to9Perm5 : Fin 10 → (Fin 5 → Fin 5) × (Fin 5 → Fin 5) := fun v =>
    let p := toPair v
    let e1 := findOut [p.1, p.2]
    let e2 := findOut [p.1, p.2, e1]
    let e3 := findOut [p.1, p.2, e1, e2]
    (mkPerm5 p.1 e1 p.2 e2 e3, mkPerm5Inv p.1 e1 p.2 e2 e3)
  have hTo9Perm_ok : ∀ v : Fin 10,
      let pp := to9Perm5 v
      (∀ i : Fin 5, pp.2 (pp.1 i) = i ∧ pp.1 (pp.2 i) = i) ∧ liftS5 pp.1 v = 9 := by decide
  have hLift_props : ∀ (π πi : Fin 5 → Fin 5), (∀ i : Fin 5, πi (π i) = i ∧ π (πi i) = i) →
      (∀ v : Fin 10, liftS5 πi (liftS5 π v) = v ∧ liftS5 π (liftS5 πi v) = v) ∧
      (∀ u v : Fin 10, pAdj (liftS5 π u) (liftS5 π v) = pAdj u v) ∧
      (∀ x : Fin 10 → Bool, Plist (x ∘ liftS5 π) = Plist x) := by
    intro π πi hbi
    have hInj : Function.Injective π := fun a b hab => by
      have := congrArg πi hab; rw [(hbi a).1, (hbi b).1] at this; exact this
    have hInjI : Function.Injective πi := fun a b hab => by
      have := congrArg π hab; rw [(hbi a).2, (hbi b).2] at this; exact this
    have hBi10 : ∀ v : Fin 10, liftS5 πi (liftS5 π v) = v ∧ liftS5 π (liftS5 πi v) = v := by
      intro v
      have hne := (hPair_inv v).1
      constructor
      · dsimp only [liftS5]
        rcases hFromPair_toPair (π (toPair v).1) (π (toPair v).2) (fun h => hne (hInj h)) with h | h
        · rw [h, (hbi _).1, (hbi _).1, (hPair_inv v).2]
        · rw [h, (hbi _).1, (hbi _).1, hFromPair_symm, (hPair_inv v).2]
      · dsimp only [liftS5]
        rcases hFromPair_toPair (πi (toPair v).1) (πi (toPair v).2) (fun h => hne (hInjI h)) with h | h
        · rw [h, (hbi _).2, (hbi _).2, (hPair_inv v).2]
        · rw [h, (hbi _).2, (hbi _).2, hFromPair_symm, (hPair_inv v).2]
    have hAdjPres : ∀ u v : Fin 10, pAdj (liftS5 π u) (liftS5 π v) = pAdj u v := by
      intro u v
      have h1 := hFromPair_toPair (π (toPair u).1) (π (toPair u).2) (fun h => (hPair_inv u).1 (hInj h))
      have h2 := hFromPair_toPair (π (toPair v).1) (π (toPair v).2) (fun h => (hPair_inv v).1 (hInj h))
      dsimp only [pAdj, liftS5]
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, decide_eq_true_eq]
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2]
      · constructor
        · rintro ⟨a, b, c, d⟩; exact ⟨fun e => a (congrArg π e), fun e => b (congrArg π e), fun e => c (congrArg π e), fun e => d (congrArg π e)⟩
        · rintro ⟨a, b, c, d⟩; exact ⟨fun e => a (hInj e), fun e => b (hInj e), fun e => c (hInj e), fun e => d (hInj e)⟩
      · constructor
        · rintro ⟨a, b, c, d⟩; exact ⟨fun e => b (congrArg π e), fun e => a (congrArg π e), fun e => d (congrArg π e), fun e => c (congrArg π e)⟩
        · rintro ⟨a, b, c, d⟩; exact ⟨fun e => b (hInj e), fun e => a (hInj e), fun e => d (hInj e), fun e => c (hInj e)⟩
      · constructor
        · rintro ⟨a, b, c, d⟩; exact ⟨fun e => c (congrArg π e), fun e => d (congrArg π e), fun e => a (congrArg π e), fun e => b (congrArg π e)⟩
        · rintro ⟨a, b, c, d⟩; exact ⟨fun e => c (hInj e), fun e => d (hInj e), fun e => a (hInj e), fun e => b (hInj e)⟩
      · constructor
        · rintro ⟨a, b, c, d⟩; exact ⟨fun e => d (congrArg π e), fun e => c (congrArg π e), fun e => b (congrArg π e), fun e => a (congrArg π e)⟩
        · rintro ⟨a, b, c, d⟩; exact ⟨fun e => d (hInj e), fun e => c (hInj e), fun e => b (hInj e), fun e => a (hInj e)⟩
    refine ⟨hBi10, hAdjPres, fun x => ?_⟩
    apply Bool.eq_iff_iff.mpr
    rw [hP_iff_adj, hP_iff_adj]
    constructor
    · rintro ⟨u, v, huv, hxu, hxv⟩
      exact ⟨liftS5 π u, liftS5 π v, (hAdjPres u v).trans huv, hxu, hxv⟩
    · rintro ⟨u, v, huv, hxu, hxv⟩
      refine ⟨liftS5 πi u, liftS5 πi v, ?_, ?_, ?_⟩
      · rw [← hAdjPres (liftS5 πi u) (liftS5 πi v), (hBi10 u).2, (hBi10 v).2]; exact huv
      · change x (liftS5 π (liftS5 πi u)) = true; rw [(hBi10 u).2]; exact hxu
      · change x (liftS5 π (liftS5 πi v)) = true; rw [(hBi10 v).2]; exact hxv
  -- Switch to classical for circuit proofs
  classical
  let _ : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hEvalAnd : ∀ bs : List Bool, GateOp.and.eval bs = bs.all id := fun _ => rfl
  have hEvalOr : ∀ bs : List Bool, GateOp.or.eval bs = bs.any id := fun _ => rfl
  have hEvalNot : ∀ bs : List Bool, GateOp.not.eval bs = !(bs.headD false) := fun _ => rfl
  have hConeStep_def : ∀ (cs : List (List ℕ)) (g : Gate), coneStep 10 cs g =
      cs ++ [(g.inputs.filter (fun w => decide (10 ≤ w ∧ w < 10 + cs.length))).flatMap (fun w => (w - 10) :: cs.getD (w - 10) [])] := fun _ _ => rfl
  let stepWire : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_len : ∀ (gs : List Gate) (w : List Bool), (gs.foldl stepWire w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp only [stepWire, List.length_append, List.length_cons, List.length_nil]; omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro _ _ _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (stepWire w g) i (by simp only [stepWire, List.length_append, List.length_singleton]; omega)]
      simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := fun w i hi => by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have getD_step_at : ∀ (w : List Bool) (g : Gate),
      (stepWire w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := fun w g => by
    simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
  have foldl_gate_val : ∀ (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length),
      (gs.foldl stepWire w).getD (w.length + k) false =
        (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i =>
          if i < w.length + k then (gs.foldl stepWire w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro _ k hk; exact False.elim (Nat.not_lt_zero k hk)
    | cons g gs ih =>
      intro w k hk
      cases k with
      | zero =>
        rw [List.foldl_cons, Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length
          (by simp only [stepWire, List.length_append, List.length_singleton]; omega), getD_step_at]
        simp only [List.getElem_cons_zero]
        congr 1; apply List.map_congr_left; intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i
            (by simp only [stepWire, List.length_append, List.length_singleton]; omega)]
          simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi, getD_ge w i (by omega)]
      | succ k' =>
        have hk' : k' < gs.length := by simp only [List.length_cons] at hk; omega
        have hl : (stepWire w g).length = w.length + 1 := by simp only [stepWire, List.length_append, List.length_singleton]
        have h1 := ih (stepWire w g) k' hk'
        rw [hl] at h1
        have hidx : w.length + (k' + 1) = w.length + 1 + k' := by omega
        rw [List.foldl_cons, hidx, h1]
        simp only [List.getElem_cons_succ]
  have gateAt_eq : ∀ {C : Circuit} {k : ℕ} (hk : k < C.gates.length), gateAt C k = C.gates[k]'hk := fun {C} {k} hk => by
    change C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  have wire_ofFn : ∀ (C : Circuit) (x : Fin 10 → Bool) (i : Fin 10),
      (C.wires (List.ofFn x)).getD i.val false = x i := fun C x i => by
    change (C.gates.foldl stepWire (List.ofFn x)).getD i.val false = x i
    rw [foldl_getD_lt C.gates (List.ofFn x) i.val (by rw [List.length_ofFn]; exact i.isLt)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]
  have wire_gate : ∀ (C : Circuit) (x : Fin 10 → Bool) (k : ℕ), k < C.size →
      (C.wires (List.ofFn x)).getD (10 + k) false =
        (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
          if i < 10 + k then (C.wires (List.ofFn x)).getD i false else false) := fun C x k hk => by
    have h := foldl_gate_val C.gates (List.ofFn x) k hk
    rw [List.length_ofFn] at h
    rw [gateAt_eq hk]; exact h
  have wires_len : ∀ (C : Circuit) (x : Fin 10 → Bool), (C.wires (List.ofFn x)).length = 10 + C.size := fun C x => by
    change (C.gates.foldl stepWire (List.ofFn x)).length = 10 + C.gates.length
    rw [foldl_len, List.length_ofFn]
  -- InCone helpers
  have coneStep_len : ∀ (gs : List Gate) (cs : List (List ℕ)), (gs.foldl (coneStep 10) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs ih => intro cs; rw [List.foldl_cons, ih]; simp only [hConeStep_def, List.length_append, List.length_cons, List.length_nil]; omega
  have coneStep_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (i : ℕ), i < cs.length →
      (gs.foldl (coneStep 10) cs).getD i [] = cs.getD i [] := by
    intro gs
    induction gs with
    | nil => intro _ _ _; rfl
    | cons g gs ih =>
      intro cs i hi
      rw [List.foldl_cons, ih (coneStep 10 cs g) i (by simp only [hConeStep_def, List.length_append, List.length_singleton]; omega)]
      simp only [hConeStep_def, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have inCone_iff : ∀ (C : Circuit) (i j : ℕ),
      InCone 10 C i j ↔ j < C.gates.length ∧ ∃ k < j, (10 + k) ∈ (gateAt C j).inputs ∧ (k = i ∨ InCone 10 C i k) := by
    intro C
    have hGen : ∀ (gs : List Gate) (cs : List (List ℕ)) (i j : ℕ),
        (i ∈ (gs.foldl (coneStep 10) cs).getD j []) ↔
          (j < cs.length ∧ i ∈ cs.getD j []) ∨
          (cs.length ≤ j ∧ j < cs.length + gs.length ∧
            ∃ k < j, (10 + k) ∈ (gs.getD (j - cs.length) ⟨GateOp.or, []⟩).inputs ∧
              (k = i ∨ i ∈ (gs.foldl (coneStep 10) cs).getD k [])) := by
      intro gs
      induction gs with
      | nil =>
        intro cs i j; simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
        constructor
        · intro h; left
          refine ⟨?_, h⟩
          by_contra hge
          have : cs.getD j [] = [] := by simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hge), Option.getD_none]
          rw [this] at h; exact List.not_mem_nil h
        · rintro (⟨_, h⟩ | ⟨h1, h2, _⟩); exact h; omega
      | cons g gs ih =>
        intro cs i j
        rw [List.foldl_cons, ih (coneStep 10 cs g) i j]
        have hlen : (coneStep 10 cs g).length = cs.length + 1 := by simp only [hConeStep_def, List.length_append, List.length_singleton]
        by_cases hjlt : j < cs.length
        · have hlt1 : j < (coneStep 10 cs g).length := by omega
          have hget : (coneStep 10 cs g).getD j [] = cs.getD j [] := by
            simp only [hConeStep_def, List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt]
          constructor
          · rintro (⟨_, h⟩ | ⟨hge, _⟩); exact Or.inl ⟨hjlt, hget ▸ h⟩; omega
          · rintro (⟨_, h⟩ | ⟨hge, _⟩); exact Or.inl ⟨hlt1, hget.symm ▸ h⟩; omega
        · by_cases hjeq : j = cs.length
          · subst j
            have hlt1 : cs.length < (coneStep 10 cs g).length := by omega
            have hget : (coneStep 10 cs g).getD cs.length [] =
                (g.inputs.filter (fun w => decide (10 ≤ w ∧ w < 10 + cs.length))).flatMap (fun w => (w - 10) :: cs.getD (w - 10) []) := by
              simp only [hConeStep_def, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
                Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            constructor
            · rintro (⟨_, h⟩ | ⟨hge, _⟩)
              · rw [hget, List.mem_flatMap] at h
                obtain ⟨w, hwf, hwm⟩ := h
                rw [List.mem_filter, decide_eq_true_eq] at hwf
                right
                refine ⟨le_refl _, by simp only [List.length_cons]; omega, w - 10, by omega, ?_, ?_⟩
                · simp only [Nat.sub_self, List.getD_cons_zero]
                  have : 10 + (w - 10) = w := by omega
                  rw [this]; exact hwf.1
                · rcases List.mem_cons.mp hwm with rfl | hm
                  · exact Or.inl rfl
                  · right
                    have hltw : w - 10 < (coneStep 10 cs g).length := by omega
                    rw [coneStep_getD_lt gs (coneStep 10 cs g) (w - 10) hltw]
                    have hge2 : (coneStep 10 cs g).getD (w - 10) [] = cs.getD (w - 10) [] := by
                      simp only [hConeStep_def, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w - 10 < cs.length)]
                    rw [hge2]; exact hm
              · omega
            · rintro (⟨h1, _⟩ | ⟨_, _, k, hk, hkin, hkm⟩)
              · omega
              · left; refine ⟨hlt1, ?_⟩
                rw [hget, List.mem_flatMap]
                simp only [Nat.sub_self, List.getD_cons_zero] at hkin
                refine ⟨10 + k, List.mem_filter.mpr ⟨hkin, decide_eq_true ⟨by omega, by omega⟩⟩, ?_⟩
                have hsub : 10 + k - 10 = k := by omega
                rw [hsub]
                rcases hkm with rfl | hm
                · exact List.mem_cons_self
                · apply List.mem_cons_of_mem
                  have hltw : k < (coneStep 10 cs g).length := by omega
                  rw [coneStep_getD_lt gs (coneStep 10 cs g) k hltw] at hm
                  have hge2 : (coneStep 10 cs g).getD k [] = cs.getD k [] := by
                    simp only [hConeStep_def, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
                  rw [← hge2]; exact hm
          · have hgt : cs.length + 1 ≤ j := by omega
            constructor
            · rintro (⟨hlt1, _⟩ | ⟨_, hlt2, k, hk, hkin, hkm⟩)
              · omega
              · right; refine ⟨by omega, by simp only [List.length_cons]; omega, k, hk, ?_, hkm⟩
                have heq : j - cs.length = (j - (coneStep 10 cs g).length) + 1 := by omega
                rw [heq, List.getD_cons_succ]; exact hkin
            · rintro (⟨h1, _⟩ | ⟨_, hlt2, k, hk, hkin, hkm⟩)
              · omega
              · right; refine ⟨by omega, by simp only [List.length_cons] at hlt2; omega, k, hk, ?_, hkm⟩
                have heq : j - cs.length = (j - (coneStep 10 cs g).length) + 1 := by omega
                rw [heq, List.getD_cons_succ] at hkin; exact hkin
    intro i j
    change i ∈ (C.gates.foldl (coneStep 10) []).getD j [] ↔ _
    rw [hGen C.gates [] i j]
    simp only [List.length_nil, Nat.not_lt_zero, false_and, false_or, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]
    constructor
    · rintro ⟨hj, k, hk, hkin, hkm⟩
      exact ⟨hj, k, hk, hkin, hkm⟩
    · rintro ⟨hj, k, hk, hkin, hkm⟩
      exact ⟨hj, k, hk, hkin, hkm⟩
  have inCone_lt : ∀ (C : Circuit) {i j : ℕ}, InCone 10 C i j → i < j ∧ j < C.gates.length := by
    intro C i j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro h
      obtain ⟨hj, k, hkj, _, hc⟩ := (inCone_iff C i j).mp h
      rcases hc with rfl | hik
      · exact ⟨hkj, hj⟩
      · have := ih k hkj hik; exact ⟨by omega, hj⟩
  have inCone_trans : ∀ (C : Circuit) {a b c : ℕ}, InCone 10 C a b → InCone 10 C b c → InCone 10 C a c := by
    intro C a b c
    induction c using Nat.strong_induction_on with
    | ind c ih =>
      intro hab hbc
      obtain ⟨hc, k, hkc, hkin, hbk⟩ := (inCone_iff C b c).mp hbc
      refine (inCone_iff C a c).mpr ⟨hc, k, hkc, hkin, Or.inr ?_⟩
      rcases hbk with rfl | hbk'
      · exact hab
      · exact ih k hkc hab hbk'
  have inCone_fwd : ∀ (C : Circuit) {i j : ℕ}, InCone 10 C i j →
      ∃ h, i < h ∧ h ≤ j ∧ (10 + i) ∈ (gateAt C h).inputs ∧ (h = j ∨ InCone 10 C h j) := by
    intro C i j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hij
      obtain ⟨hj, k, hkj, hkin, hk⟩ := (inCone_iff C i j).mp hij
      rcases hk with rfl | hik
      · exact ⟨j, hkj, le_refl j, hkin, Or.inl rfl⟩
      · obtain ⟨h, hih, hhk, hhin, hhj⟩ := ih k hkj hik
        refine ⟨h, hih, by omega, hhin, Or.inr ?_⟩
        exact (inCone_iff C h j).mpr ⟨hj, k, hkj, hkin, hhj.imp Eq.symm id⟩
  have inOutCone_trans : ∀ (C : Circuit) {a b c : ℕ}, InOutCone 10 C a b → InOutCone 10 C b c → InOutCone 10 C a c := by
    intro C a b c hab hbc
    rcases hab with rfl | ⟨ha, hb, hab'⟩
    · exact hbc
    · rcases hbc with rfl | ⟨_, hc, hbc'⟩
      · exact Or.inr ⟨ha, hb, hab'⟩
      · exact Or.inr ⟨ha, hc, inCone_trans C hab' hbc'⟩
  -- Helper: notCount lemmas
  have notCount_le_size : ∀ (C : Circuit), notCount C ≤ C.size := fun C => by
    change (C.gates.filter fun g => decide (g.op = GateOp.not)).length ≤ C.gates.length
    exact List.length_filter_le _ _
  have notCount_cons : ∀ (g : Gate) (gs : List Gate),
      notCount ⟨g :: gs, 0⟩ = (if g.op = GateOp.not then 1 else 0) + notCount ⟨gs, 0⟩ := fun g gs => by
    change ((g :: gs).filter fun h => decide (h.op = GateOp.not)).length =
      (if g.op = GateOp.not then 1 else 0) + (gs.filter fun h => decide (h.op = GateOp.not)).length
    by_cases h : g.op = GateOp.not
    · rw [ite_eq_left h]; simp only [List.filter_cons, decide_eq_true h, ite_true, List.length_cons]; omega
    · rw [ite_eq_right h]; simp only [List.filter_cons, decide_eq_false h, Bool.false_eq_true, ite_false, Nat.zero_add]
  have notCount_append : ∀ (gs1 gs2 : List Gate) (o1 o2 o3 : ℕ),
      notCount ⟨gs1 ++ gs2, o1⟩ = notCount ⟨gs1, o2⟩ + notCount ⟨gs2, o3⟩ := fun gs1 gs2 _ _ _ => by
    change ((gs1 ++ gs2).filter fun h => decide (h.op = GateOp.not)).length =
      (gs1.filter fun h => decide (h.op = GateOp.not)).length + (gs2.filter fun h => decide (h.op = GateOp.not)).length
    rw [List.filter_append, List.length_append]
  have notCount_eraseIdx_le : ∀ (gs : List Gate) (k : ℕ),
      notCount ⟨gs.eraseIdx k, 0⟩ ≤ notCount ⟨gs, 0⟩ := by
    intro gs
    induction gs with
    | nil => intro k; simp only [List.eraseIdx_nil, le_refl]
    | cons g gs ih =>
      intro k
      cases k with
      | zero => rw [List.eraseIdx_cons_zero, notCount_cons]; omega
      | succ k' =>
        rw [List.eraseIdx_cons_succ, notCount_cons, notCount_cons]
        have := ih k'; omega
  have notCount_map_same_op : ∀ (gs : List Gate) (f : Gate → Gate),
      (∀ g ∈ gs, (f g).op = g.op) → notCount ⟨gs.map f, 0⟩ = notCount ⟨gs, 0⟩ := by
    intro gs f hf
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.map_cons, notCount_cons, notCount_cons, hf g List.mem_cons_self,
        ih (fun h hh => hf h (List.mem_cons_of_mem g hh))]
  have notCount_map_le : ∀ (gs : List Gate) (f : Gate → Gate),
      (∀ g ∈ gs, (f g).op = GateOp.not → g.op = GateOp.not) → notCount ⟨gs.map f, 0⟩ ≤ notCount ⟨gs, 0⟩ := by
    intro gs f hf
    induction gs with
    | nil => exact le_refl 0
    | cons g gs ih =>
      rw [List.map_cons, notCount_cons, notCount_cons]
      have hih := ih (fun h hh => hf h (List.mem_cons_of_mem g hh))
      by_cases h1 : (f g).op = GateOp.not
      · rw [ite_eq_left h1, ite_eq_left (hf g List.mem_cons_self h1)]; omega
      · rw [ite_eq_right h1]; omega
  have notCount_unique : ∀ (gs : List Gate), notCount ⟨gs, 0⟩ ≤ 1 →
      ∀ (i j : ℕ) (hi : i < gs.length) (hj : j < gs.length),
        (gs[i]'hi).op = GateOp.not → (gs[j]'hj).op = GateOp.not → i = j := by
    intro gs
    induction gs with
    | nil => intro _ i _ hi; exact False.elim (Nat.not_lt_zero i hi)
    | cons g gs ih =>
      intro hnc i j hi hj hgi hgj
      rw [notCount_cons] at hnc
      cases i with
      | zero =>
        cases j with
        | zero => rfl
        | succ j' =>
          simp only [List.getElem_cons_zero] at hgi
          simp only [List.getElem_cons_succ] at hgj
          rw [ite_eq_left hgi] at hnc
          have h0 : notCount ⟨gs, 0⟩ = 0 := by omega
          have hmem : gs[j']'(by simp only [List.length_cons] at hj; omega) ∈ gs.filter (fun h => decide (h.op = GateOp.not)) :=
            List.mem_filter.mpr ⟨List.getElem_mem _, decide_eq_true hgj⟩
          have hnil : gs.filter (fun h => decide (h.op = GateOp.not)) = [] := List.length_eq_zero_iff.mp h0
          rw [hnil] at hmem; exact False.elim (List.not_mem_nil hmem)
      | succ i' =>
        cases j with
        | zero =>
          simp only [List.getElem_cons_succ] at hgi
          simp only [List.getElem_cons_zero] at hgj
          rw [ite_eq_left hgj] at hnc
          have h0 : notCount ⟨gs, 0⟩ = 0 := by omega
          have hmem : gs[i']'(by simp only [List.length_cons] at hi; omega) ∈ gs.filter (fun h => decide (h.op = GateOp.not)) :=
            List.mem_filter.mpr ⟨List.getElem_mem _, decide_eq_true hgi⟩
          have hnil : gs.filter (fun h => decide (h.op = GateOp.not)) = [] := List.length_eq_zero_iff.mp h0
          rw [hnil] at hmem; exact False.elim (List.not_mem_nil hmem)
        | succ j' =>
          simp only [List.getElem_cons_succ] at hgi hgj
          exact congrArg Nat.succ (ih (by omega) i' j' (by simp only [List.length_cons] at hi; omega) (by simp only [List.length_cons] at hj; omega) hgi hgj)
  -- Helper: relabel inputs of a circuit by a permutation σ of Fin 10
  let relabelW : (Fin 10 → Fin 10) → ℕ → ℕ := fun σ w => if h : w < 10 then (σ ⟨w, h⟩).val else w
  let relabelG : (Fin 10 → Fin 10) → Gate → Gate := fun σ g => ⟨g.op, g.inputs.map (relabelW σ)⟩
  let relabelC : (Fin 10 → Fin 10) → Circuit → Circuit := fun σ C => ⟨C.gates.map (relabelG σ), relabelW σ C.output⟩
  have relabel_wires : ∀ (σ : Fin 10 → Fin 10) (gs : List Gate) (w1 w2 : List Bool),
      w1.length = w2.length → 10 ≤ w1.length →
      (∀ i : ℕ, i < w1.length → w1.getD (relabelW σ i) false = w2.getD i false) →
      (∀ i : ℕ, 10 ≤ i → i < w1.length → w1.getD i false = w2.getD i false) →
      ∀ k : ℕ, k < gs.length →
        ((gs.map (relabelG σ)).foldl stepWire w1).getD (w1.length + k) false =
          (gs.foldl stepWire w2).getD (w2.length + k) false := by
    intro σ gs
    induction gs with
    | nil => intro _ _ _ _ _ _ k hk; exact False.elim (Nat.not_lt_zero k hk)
    | cons g gs ih =>
      intro w1 w2 hlen hge10 hrel hgate k hk
      have hStepEq : (relabelG σ g).op.eval ((relabelG σ g).inputs.map fun i => w1.getD i false) =
          g.op.eval (g.inputs.map fun i => w2.getD i false) := by
        dsimp only [relabelG]; rw [List.map_map]
        congr 1; apply List.map_congr_left; intro i _
        change w1.getD (relabelW σ i) false = w2.getD i false
        by_cases hi : i < w1.length
        · exact hrel i hi
        · have hge1 : w1.length ≤ relabelW σ i := by
            dsimp only [relabelW]; rw [dite_eq_right (by omega : ¬ i < 10)]; omega
          rw [getD_ge w1 _ hge1, getD_ge w2 i (by omega)]
      cases k with
      | zero =>
        rw [List.map_cons, List.foldl_cons, List.foldl_cons, Nat.add_zero, Nat.add_zero]
        rw [foldl_getD_lt (gs.map (relabelG σ)) (stepWire w1 (relabelG σ g)) w1.length
          (by simp only [stepWire, List.length_append, List.length_singleton]; omega)]
        rw [foldl_getD_lt gs (stepWire w2 g) w2.length
          (by simp only [stepWire, List.length_append, List.length_singleton]; omega)]
        rw [getD_step_at, getD_step_at, hStepEq]
      | succ k' =>
        have hk' : k' < gs.length := by simp only [List.length_cons] at hk; omega
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        have hl1 : (stepWire w1 (relabelG σ g)).length = w1.length + 1 := by simp only [stepWire, List.length_append, List.length_singleton]
        have hl2 : (stepWire w2 g).length = w2.length + 1 := by simp only [stepWire, List.length_append, List.length_singleton]
        have h1 : w1.length + (k' + 1) = (stepWire w1 (relabelG σ g)).length + k' := by omega
        have h2 : w2.length + (k' + 1) = (stepWire w2 g).length + k' := by omega
        rw [h1, h2]
        refine ih (stepWire w1 (relabelG σ g)) (stepWire w2 g) (by omega) (by omega) ?_ ?_ k' hk'
        · intro i hi
          by_cases hilt : i < w1.length
          · have hri : relabelW σ i < w1.length := by
              dsimp only [relabelW]
              by_cases h10 : i < 10
              · rw [dite_eq_left h10]; have := (σ ⟨i, h10⟩).isLt; omega
              · rw [dite_eq_right h10]; exact hilt
            simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hri,
              List.getElem?_append_left (by omega : i < w2.length)]
            exact hrel i hilt
          · have hieq : i = w1.length := by omega
            have hri : relabelW σ i = w1.length := by dsimp only [relabelW]; rw [dite_eq_right (by omega : ¬ i < 10)]; exact hieq
            rw [hri, hieq, getD_step_at, hlen, getD_step_at, hStepEq]
        · intro i hi10 hilt
          by_cases hiw : i < w1.length
          · simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hiw,
              List.getElem?_append_left (by omega : i < w2.length)]
            exact hgate i hi10 hiw
          · have hieq : i = w1.length := by omega
            rw [hieq, getD_step_at, hlen, getD_step_at, hStepEq]
  have relabel_eval : ∀ (σ : Fin 10 → Fin 10) (C : Circuit) (x : Fin 10 → Bool),
      ((relabelC σ C).wires (List.ofFn x)).getD (relabelW σ C.output) false =
        (C.wires (List.ofFn (x ∘ σ))).getD C.output false := by
    intro σ C x
    have hInitRel : ∀ i < (List.ofFn x).length,
        (List.ofFn x).getD (relabelW σ i) false = (List.ofFn (x ∘ σ)).getD i false := by
      intro i hi
      rw [List.length_ofFn] at hi
      dsimp only [relabelW]; rw [dite_eq_left hi]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left (σ ⟨i, hi⟩).isLt,
        dite_eq_left hi, Option.getD_some, Function.comp_apply]
    by_cases ho : C.output < 10
    · have hro : relabelW σ C.output < 10 := by dsimp only [relabelW]; rw [dite_eq_left ho]; exact (σ ⟨C.output, ho⟩).isLt
      change ((C.gates.map (relabelG σ)).foldl stepWire (List.ofFn x)).getD (relabelW σ C.output) false =
        (C.gates.foldl stepWire (List.ofFn (x ∘ σ))).getD C.output false
      rw [foldl_getD_lt _ _ _ (by rw [List.length_ofFn]; exact hro),
        foldl_getD_lt _ _ _ (by rw [List.length_ofFn]; exact ho)]
      exact hInitRel C.output (by rw [List.length_ofFn]; exact ho)
    · by_cases hlt : C.output < 10 + C.gates.length
      · have hro : relabelW σ C.output = 10 + (C.output - 10) := by
          dsimp only [relabelW]; rw [dite_eq_right ho]; omega
        have heq : C.output = 10 + (C.output - 10) := by omega
        change ((C.gates.map (relabelG σ)).foldl stepWire (List.ofFn x)).getD (relabelW σ C.output) false =
          (C.gates.foldl stepWire (List.ofFn (x ∘ σ))).getD C.output false
        rw [hro]
        conv_rhs => rw [heq]
        have h := relabel_wires σ C.gates (List.ofFn x) (List.ofFn (x ∘ σ))
          (by rw [List.length_ofFn, List.length_ofFn]) (by rw [List.length_ofFn]) hInitRel
          (fun i hi10 hilt => by rw [List.length_ofFn] at hilt; omega) (C.output - 10) (by omega)
        rw [List.length_ofFn, List.length_ofFn] at h
        exact h
      · have hro : relabelW σ C.output = C.output := by dsimp only [relabelW]; rw [dite_eq_right ho]
        rw [hro]
        change ((C.gates.map (relabelG σ)).foldl stepWire (List.ofFn x)).getD C.output false =
          (C.gates.foldl stepWire (List.ofFn (x ∘ σ))).getD C.output false
        rw [getD_ge _ C.output (by rw [foldl_len, List.length_ofFn, List.length_map]; omega),
          getD_ge _ C.output (by rw [foldl_len, List.length_ofFn]; omega)]
  have relabel_wire_any : ∀ (σ : Fin 10 → Fin 10) (C : Circuit) (x : Fin 10 → Bool) (i : ℕ),
      i < 10 + C.size →
      ((relabelC σ C).wires (List.ofFn x)).getD (relabelW σ i) false =
        (C.wires (List.ofFn (x ∘ σ))).getD i false := by
    intro σ C x i hi
    have hInitRel : ∀ j < (List.ofFn x).length,
        (List.ofFn x).getD (relabelW σ j) false = (List.ofFn (x ∘ σ)).getD j false := by
      intro j hj; rw [List.length_ofFn] at hj; dsimp only [relabelW]; rw [dite_eq_left hj]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left (σ ⟨j, hj⟩).isLt,
        dite_eq_left hj, Option.getD_some, Function.comp_apply]
    by_cases h10 : i < 10
    · have hri : relabelW σ i = (σ ⟨i, h10⟩).val := by dsimp only [relabelW]; rw [dite_eq_left h10]
      rw [hri, wire_ofFn (relabelC σ C) x (σ ⟨i, h10⟩), wire_ofFn C (x ∘ σ) ⟨i, h10⟩]; rfl
    · change i < 10 + C.gates.length at hi
      have hri : relabelW σ i = 10 + (i - 10) := by dsimp only [relabelW]; rw [dite_eq_right h10]; omega
      have heq : i = 10 + (i - 10) := by omega
      change ((C.gates.map (relabelG σ)).foldl stepWire (List.ofFn x)).getD (relabelW σ i) false =
        (C.gates.foldl stepWire (List.ofFn (x ∘ σ))).getD i false
      rw [hri]
      conv_rhs => rw [heq]
      have h := relabel_wires σ C.gates (List.ofFn x) (List.ofFn (x ∘ σ))
        (by rw [List.length_ofFn, List.length_ofFn]) (by rw [List.length_ofFn]) hInitRel
        (fun j hj10 hjlt => by rw [List.length_ofFn] at hjlt; omega) (i - 10) (by omega)
      rw [List.length_ofFn, List.length_ofFn] at h; exact h
  have relabel_inCone : ∀ (σ : Fin 10 → Fin 10) (C : Circuit) (i j : ℕ),
      InCone 10 (relabelC σ C) i j ↔ InCone 10 C i j := by
    intro σ C i j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      rw [inCone_iff, inCone_iff]
      have hlen : (relabelC σ C).gates.length = C.gates.length := List.length_map _
      rw [hlen]
      constructor
      · rintro ⟨hj, k, hkj, hkin, hc⟩
        refine ⟨hj, k, hkj, ?_, hc.imp id (ih k hkj).mp⟩
        rw [gateAt_eq (by rw [hlen]; exact hj)] at hkin
        dsimp only [relabelC] at hkin
        simp only [List.getElem_map] at hkin
        dsimp only [relabelG] at hkin
        obtain ⟨w, hw, hweq⟩ := List.mem_map.mp hkin
        have hwk : w = 10 + k := by
          dsimp only [relabelW] at hweq
          by_cases h10 : w < 10
          · rw [dite_eq_left h10] at hweq; have := (σ ⟨w, h10⟩).isLt; omega
          · rw [dite_eq_right h10] at hweq; exact hweq
        rw [gateAt_eq hj, ← hwk]; exact hw
      · rintro ⟨hj, k, hkj, hkin, hc⟩
        refine ⟨hj, k, hkj, ?_, hc.imp id (ih k hkj).mpr⟩
        rw [gateAt_eq (by rw [hlen]; exact hj)]
        dsimp only [relabelC]; simp only [List.getElem_map]; dsimp only [relabelG]
        rw [gateAt_eq hj] at hkin
        exact List.mem_map.mpr ⟨10 + k, hkin, by dsimp only [relabelW]; rw [dite_eq_right (by omega : ¬ 10 + k < 10)]⟩
  -- Constant-propagation restrictor on `x v = false`
  let rStep : (List (Bool × Bool × ℕ) × List Gate × ℕ) → Gate → (List (Bool × Bool × ℕ) × List Gate × ℕ) :=
    fun st g =>
      let mp := st.1; let gs := st.2.1; let eb := st.2.2
      if g.op = GateOp.not then
        let s := mp.getD (g.inputs.getD 0 0) (true, false, 0)
        if s.1 then (mp ++ [(true, !s.2.1, 0)], gs, eb)
        else (mp ++ [(false, false, 10 + gs.length)], gs ++ [⟨GateOp.not, [s.2.2]⟩], eb)
      else if g.op = GateOp.and then
        let s1 := mp.getD (g.inputs.getD 0 0) (true, false, 0)
        let s2 := mp.getD (g.inputs.getD 1 0) (true, false, 0)
        if s1.1 then
          if s1.2.1 then (mp ++ [s2], gs, eb + 1)
          else (mp ++ [(true, false, 0)], gs, eb + 1)
        else if s2.1 then
          if s2.2.1 then (mp ++ [s1], gs, eb + 1)
          else (mp ++ [(true, false, 0)], gs, eb + 1)
        else (mp ++ [(false, false, 10 + gs.length)], gs ++ [⟨GateOp.and, [s1.2.2, s2.2.2]⟩], eb)
      else
        let s1 := mp.getD (g.inputs.getD 0 0) (true, false, 0)
        let s2 := mp.getD (g.inputs.getD 1 0) (true, false, 0)
        if s1.1 then
          if s1.2.1 then (mp ++ [(true, true, 0)], gs, eb + 1)
          else (mp ++ [s2], gs, eb + 1)
        else if s2.1 then
          if s2.2.1 then (mp ++ [(true, true, 0)], gs, eb + 1)
          else (mp ++ [s1], gs, eb + 1)
        else (mp ++ [(false, false, 10 + gs.length)], gs ++ [⟨GateOp.or, [s1.2.2, s2.2.2]⟩], eb)
  let rInit : Fin 10 → List (Bool × Bool × ℕ) := fun v =>
    List.ofFn fun i : Fin 10 => if i = v then (true, false, 0) else (false, false, i.val)
  let rRun : Fin 10 → List Gate → (List (Bool × Bool × ℕ) × List Gate × ℕ) := fun v gs =>
    gs.foldl rStep (rInit v, [], 0)
  have rStep_struct : ∀ (gs : List Gate) (st : List (Bool × Bool × ℕ) × List Gate × ℕ),
      (gs.foldl rStep st).1.length = st.1.length + gs.length ∧
      (∀ i < st.1.length, (gs.foldl rStep st).1.getD i (true, false, 0) = st.1.getD i (true, false, 0)) ∧
      st.2.2 ≤ (gs.foldl rStep st).2.2 := by
    have hOne : ∀ (st : List (Bool × Bool × ℕ) × List Gate × ℕ) (g : Gate),
        (rStep st g).1.length = st.1.length + 1 ∧
        (∀ i < st.1.length, (rStep st g).1.getD i (true, false, 0) = st.1.getD i (true, false, 0)) ∧
        st.2.2 ≤ (rStep st g).2.2 := by
      intro st g
      have hApp : ∀ (a : Bool × Bool × ℕ) (gs' : List Gate) (eb' : ℕ), st.2.2 ≤ eb' →
          (st.1 ++ [a], gs', eb').1.length = st.1.length + 1 ∧
          (∀ i < st.1.length, (st.1 ++ [a], gs', eb').1.getD i (true, false, 0) = st.1.getD i (true, false, 0)) ∧
          st.2.2 ≤ (st.1 ++ [a], gs', eb').2.2 := fun a _ _ heb =>
        ⟨by simp only [List.length_append, List.length_singleton],
         fun i hi => by simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi], heb⟩
      dsimp only [rStep]
      by_cases hnot : g.op = GateOp.not
      · rw [ite_eq_left hnot]
        by_cases hs : (st.1.getD (g.inputs.getD 0 0) (true, false, 0)).1 = true
        · rw [ite_eq_left hs]; exact hApp _ _ _ (le_refl _)
        · rw [ite_eq_right hs]; exact hApp _ _ _ (le_refl _)
      · rw [ite_eq_right hnot]
        by_cases hand : g.op = GateOp.and
        · rw [ite_eq_left hand]
          by_cases hs1 : (st.1.getD (g.inputs.getD 0 0) (true, false, 0)).1 = true
          · rw [ite_eq_left hs1]
            by_cases hv1 : (st.1.getD (g.inputs.getD 0 0) (true, false, 0)).2.1 = true
            · rw [ite_eq_left hv1]; exact hApp _ _ _ (Nat.le_succ _)
            · rw [ite_eq_right hv1]; exact hApp _ _ _ (Nat.le_succ _)
          · rw [ite_eq_right hs1]
            by_cases hs2 : (st.1.getD (g.inputs.getD 1 0) (true, false, 0)).1 = true
            · rw [ite_eq_left hs2]
              by_cases hv2 : (st.1.getD (g.inputs.getD 1 0) (true, false, 0)).2.1 = true
              · rw [ite_eq_left hv2]; exact hApp _ _ _ (Nat.le_succ _)
              · rw [ite_eq_right hv2]; exact hApp _ _ _ (Nat.le_succ _)
            · rw [ite_eq_right hs2]; exact hApp _ _ _ (le_refl _)
        · rw [ite_eq_right hand]
          by_cases hs1 : (st.1.getD (g.inputs.getD 0 0) (true, false, 0)).1 = true
          · rw [ite_eq_left hs1]
            by_cases hv1 : (st.1.getD (g.inputs.getD 0 0) (true, false, 0)).2.1 = true
            · rw [ite_eq_left hv1]; exact hApp _ _ _ (Nat.le_succ _)
            · rw [ite_eq_right hv1]; exact hApp _ _ _ (Nat.le_succ _)
          · rw [ite_eq_right hs1]
            by_cases hs2 : (st.1.getD (g.inputs.getD 1 0) (true, false, 0)).1 = true
            · rw [ite_eq_left hs2]
              by_cases hv2 : (st.1.getD (g.inputs.getD 1 0) (true, false, 0)).2.1 = true
              · rw [ite_eq_left hv2]; exact hApp _ _ _ (Nat.le_succ _)
              · rw [ite_eq_right hv2]; exact hApp _ _ _ (Nat.le_succ _)
            · rw [ite_eq_right hs2]; exact hApp _ _ _ (le_refl _)
    intro gs
    induction gs with
    | nil => intro st; exact ⟨by simp only [List.foldl_nil, List.length_nil, Nat.add_zero], fun _ _ => rfl, le_refl _⟩
    | cons g gs ih =>
      intro st
      obtain ⟨hl1, hg1, he1⟩ := hOne st g
      obtain ⟨hl2, hg2, he2⟩ := ih (rStep st g)
      rw [List.foldl_cons]
      exact ⟨by rw [hl2, hl1, List.length_cons]; omega,
        fun i hi => by rw [hg2 i (by omega), hg1 i hi], le_trans he1 he2⟩
  have rStep_inv : ∀ (v : Fin 10) (gs pref : List Gate) (st : List (Bool × Bool × ℕ) × List Gate × ℕ),
      st.1.length = 10 + pref.length →
      (∀ g ∈ gs, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
        ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) →
      (∀ (k : ℕ) (hk : k < gs.length), ∀ i ∈ (gs[k]'hk).inputs, i < st.1.length + k) →
      FanInTwo ⟨st.2.1, 0⟩ →
      (∀ s ∈ st.1, s.1 = false → s.2.2 < 10 + st.2.1.length) →
      (∀ x : Fin 10 → Bool, x v = false → ∀ i < st.1.length,
        let s := st.1.getD i (true, false, 0)
        (if s.1 then s.2.1 else (st.2.1.foldl stepWire (List.ofFn x)).getD s.2.2 false) =
          (pref.foldl stepWire (List.ofFn x)).getD i false) →
      let st' := gs.foldl rStep st
      FanInTwo ⟨st'.2.1, 0⟩ ∧
      (st'.2.1.length - notCount ⟨st'.2.1, 0⟩) + (st'.2.2 - st.2.2) =
        (st.2.1.length - notCount ⟨st.2.1, 0⟩) + (gs.length - notCount ⟨gs, 0⟩) ∧
      notCount ⟨st'.2.1, 0⟩ ≤ notCount ⟨st.2.1, 0⟩ + notCount ⟨gs, 0⟩ ∧
      (∀ s ∈ st'.1, s.1 = false → s.2.2 < 10 + st'.2.1.length) ∧
      (∀ x : Fin 10 → Bool, x v = false → ∀ i < st'.1.length,
        let s := st'.1.getD i (true, false, 0)
        (if s.1 then s.2.1 else (st'.2.1.foldl stepWire (List.ofFn x)).getD s.2.2 false) =
          ((pref ++ gs).foldl stepWire (List.ofFn x)).getD i false) := by
    intro v gs
    induction gs with
    | nil =>
      intro pref st _ _ _ hfan hbnd hev
      refine ⟨hfan, by simp only [List.foldl_nil, List.length_nil, Nat.sub_self, Nat.add_zero]; rfl,
        by simp only [List.foldl_nil]; change notCount ⟨st.2.1, 0⟩ ≤ notCount ⟨st.2.1, 0⟩ + 0; omega,
        hbnd, fun x hxv i hi => by dsimp only; rw [List.foldl_nil, List.append_nil]; exact hev x hxv i hi⟩
    | cons g gs ih =>
      intro pref st hlen hshape hrb hfan hbnd hev
      let st1 := rStep st g
      have hrb0 : ∀ i ∈ g.inputs, i < st.1.length := fun i hi => by
        have := hrb 0 (Nat.zero_lt_succ gs.length) i hi; simp only [Nat.add_zero] at this; exact this
      have hrb_tail : ∀ (k : ℕ) (hk : k < gs.length), ∀ i ∈ (gs[k]'hk).inputs, i < st.1.length + 1 + k := fun k hk i hi => by
        have := hrb (k + 1) (Nat.succ_lt_succ hk) i hi; omega
      have hLookupMem : ∀ i < st.1.length, st.1.getD i (true, false, 0) ∈ st.1 := fun i hi => by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]; exact List.getElem_mem hi
      have hPrefLen : ∀ x : Fin 10 → Bool, (pref.foldl stepWire (List.ofFn x)).length = st.1.length := fun x => by
        rw [foldl_len, List.length_ofFn, hlen]
      have hAppendEv : ∀ (x : Fin 10 → Bool) (hxv : x v = false) (gnew : Gate) (i : ℕ) (hi : i < st.1.length),
          let s := st.1.getD i (true, false, 0)
          (if s.1 then s.2.1 else ((st.2.1 ++ [gnew]).foldl stepWire (List.ofFn x)).getD s.2.2 false) =
            (pref.foldl stepWire (List.ofFn x)).getD i false := by
        intro x hxv gnew i hi; dsimp only
        by_cases hs1 : (st.1.getD i (true, false, 0)).1 = true
        · rw [ite_eq_left hs1]; have h := hev x hxv i hi; dsimp only at h; rw [ite_eq_left hs1] at h; exact h
        · rw [ite_eq_right hs1]
          have hb := hbnd _ (hLookupMem i hi) (Bool.eq_false_iff.mpr hs1)
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hltw : (st.1.getD i (true, false, 0)).2.2 < (st.2.1.foldl stepWire (List.ofFn x)).length := by
            rw [foldl_len, List.length_ofFn]; exact hb
          have hstep : (stepWire (st.2.1.foldl stepWire (List.ofFn x)) gnew).getD (st.1.getD i (true, false, 0)).2.2 false =
              (st.2.1.foldl stepWire (List.ofFn x)).getD (st.1.getD i (true, false, 0)).2.2 false := by
            change ((st.2.1.foldl stepWire (List.ofFn x)) ++ [gnew.op.eval (gnew.inputs.map fun j => (st.2.1.foldl stepWire (List.ofFn x)).getD j false)]).getD (st.1.getD i (true, false, 0)).2.2 false = _
            conv_lhs => rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hltw]
            conv_rhs => rw [List.getD_eq_getElem?_getD]
          rw [hstep]
          have h := hev x hxv i hi; dsimp only at h; rw [ite_eq_right hs1] at h; exact h
      have hNotLe := notCount_le_size ⟨st.2.1, 0⟩; change notCount ⟨st.2.1, 0⟩ ≤ st.2.1.length at hNotLe
      have hst1_props : st1.1.length = st.1.length + 1 ∧
          FanInTwo ⟨st1.2.1, 0⟩ ∧
          (st1.2.1.length - notCount ⟨st1.2.1, 0⟩) + (st1.2.2 - st.2.2) =
            (st.2.1.length - notCount ⟨st.2.1, 0⟩) + (if g.op = GateOp.not then 0 else 1) ∧
          st.2.2 ≤ st1.2.2 ∧
          notCount ⟨st1.2.1, 0⟩ ≤ notCount ⟨st.2.1, 0⟩ + (if g.op = GateOp.not then 1 else 0) ∧
          (∀ s ∈ st1.1, s.1 = false → s.2.2 < 10 + st1.2.1.length) ∧
          (∀ x : Fin 10 → Bool, x v = false → ∀ i < st1.1.length,
            let s := st1.1.getD i (true, false, 0)
            (if s.1 then s.2.1 else (st1.2.1.foldl stepWire (List.ofFn x)).getD s.2.2 false) =
              ((pref ++ [g]).foldl stepWire (List.ofFn x)).getD i false) := by
        rcases hshape g List.mem_cons_self with ⟨hgn, hgl⟩ | ⟨hgbo, hgl⟩
        · have hgins : g.inputs = [g.inputs.getD 0 0] := by
            cases hl : g.inputs with
            | nil => rw [hl] at hgl; exact False.elim (Nat.noConfusion hgl)
            | cons a t =>
              cases t with
              | nil => simp only [List.getD_cons_zero]
              | cons _ _ => rw [hl] at hgl; simp only [List.length_cons] at hgl; omega
          have hi0 : g.inputs.getD 0 0 < st.1.length := hrb0 _ (by rw [hgins]; exact List.mem_cons_self)
          let s := st.1.getD (g.inputs.getD 0 0) (true, false, 0)
          have hst1_def : st1 = (if s.1 then (st.1 ++ [(true, !s.2.1, 0)], st.2.1, st.2.2)
              else (st.1 ++ [(false, false, 10 + st.2.1.length)], st.2.1 ++ [⟨GateOp.not, [s.2.2]⟩], st.2.2)) := by
            dsimp only [st1, rStep, s]; rw [ite_eq_left hgn]
          by_cases hs1 : s.1 = true
          · have hst1_eq : st1 = (st.1 ++ [(true, !s.2.1, 0)], st.2.1, st.2.2) := by rw [hst1_def, ite_eq_left hs1]
            rw [hst1_eq, ite_eq_left hgn, ite_eq_left hgn]
            dsimp only
            refine ⟨by simp only [List.length_append, List.length_singleton], hfan, by omega, le_refl _, by omega,
              fun t ht ht0 => (List.mem_append.mp ht).elim (fun h1 => hbnd t h1 ht0)
                (fun h2 => by rw [List.mem_singleton.mp h2] at ht0; exact False.elim (Bool.noConfusion ht0)),
              fun x hxv i hi => ?_⟩
            rw [List.length_append, List.length_singleton] at hi
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            by_cases hilt : i < st.1.length
            · have hget : (st.1 ++ [(true, !s.2.1, 0)]).getD i (true, false, 0) = st.1.getD i (true, false, 0) := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt]
              rw [hget]
              have hstep : (stepWire (pref.foldl stepWire (List.ofFn x)) g).getD i false = (pref.foldl stepWire (List.ofFn x)).getD i false := by
                change ((pref.foldl stepWire (List.ofFn x)) ++ [_]).getD i false = _
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hPrefLen x]; exact hilt)]
              rw [hstep]; exact hev x hxv i hilt
            · have hieq : i = st.1.length := by omega
              subst i
              have hget : (st.1 ++ [(true, !s.2.1, 0)]).getD st.1.length (true, false, 0) = (true, !s.2.1, 0) := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              rw [hget, ite_eq_left rfl, ← hPrefLen x, getD_step_at, hgn, hgins]
              simp only [List.map_cons, List.map_nil]
              have h0 := hev x hxv _ hi0; dsimp only at h0; change (if s.1 then s.2.1 else _) = _ at h0
              rw [ite_eq_left hs1] at h0; rw [← h0]; rfl
          · have hst1_eq : st1 = (st.1 ++ [(false, false, 10 + st.2.1.length)], st.2.1 ++ [⟨GateOp.not, [s.2.2]⟩], st.2.2) := by
              rw [hst1_def, ite_eq_right hs1]
            have hnc : notCount ⟨st.2.1 ++ [⟨GateOp.not, [s.2.2]⟩], 0⟩ = notCount ⟨st.2.1, 0⟩ + 1 := by
              rw [notCount_append _ _ 0 0 0, notCount_cons, ite_eq_left rfl]; rfl
            rw [hst1_eq, ite_eq_left hgn, ite_eq_left hgn]
            dsimp only
            refine ⟨by simp only [List.length_append, List.length_singleton],
              fun h hh => (List.mem_append.mp hh).elim (hfan h) (fun h1 => by rw [List.mem_singleton.mp h1]; exact ⟨Or.inr (Or.inr rfl), by simp⟩),
              by rw [List.length_append, List.length_singleton, hnc]; omega, le_refl _, by rw [hnc], ?_, ?_⟩
            · intro t ht ht0
              rcases List.mem_append.mp ht with h1 | h2
              · have := hbnd t h1 ht0; rw [List.length_append, List.length_singleton]; omega
              · rw [List.mem_singleton.mp h2]; dsimp only; rw [List.length_append, List.length_singleton]; omega
            · intro x hxv i hi
              rw [List.length_append, List.length_singleton] at hi
              conv_rhs => rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
              by_cases hilt : i < st.1.length
              · have hget : (st.1 ++ [(false, false, 10 + st.2.1.length)]).getD i (true, false, 0) = st.1.getD i (true, false, 0) := by
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt]
                rw [hget]
                have hstep : (stepWire (pref.foldl stepWire (List.ofFn x)) g).getD i false = (pref.foldl stepWire (List.ofFn x)).getD i false := by
                  change ((pref.foldl stepWire (List.ofFn x)) ++ [_]).getD i false = _
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hPrefLen x]; exact hilt)]
                rw [hstep]; exact hAppendEv x hxv _ i hilt
              · have hieq : i = st.1.length := by omega
                subst i
                have hget : (st.1 ++ [(false, false, 10 + st.2.1.length)]).getD st.1.length (true, false, 0) = (false, false, 10 + st.2.1.length) := by
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
                rw [hget, ite_eq_right Bool.false_ne_true]
                conv_rhs => rw [← hPrefLen x, getD_step_at, hgn, hgins]
                rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                dsimp only
                have hlw : (st.2.1.foldl stepWire (List.ofFn x)).length = 10 + st.2.1.length := by rw [foldl_len, List.length_ofFn]
                rw [← hlw, getD_step_at]
                simp only [List.map_cons, List.map_nil]
                have h0 := hev x hxv _ hi0; dsimp only at h0; change (if s.1 then s.2.1 else _) = _ at h0
                rw [ite_eq_right hs1] at h0; rw [← h0]
        · have hgNot : g.op ≠ GateOp.not := by rcases hgbo with h | h <;> rw [h] <;> exact GateOp.noConfusion
          have hgins : g.inputs = [g.inputs.getD 0 0, g.inputs.getD 1 0] := by
            cases hl : g.inputs with
            | nil => rw [hl] at hgl; exact False.elim (Nat.noConfusion hgl)
            | cons a t =>
              cases t with
              | nil => rw [hl] at hgl; simp only [List.length_cons, List.length_nil] at hgl; omega
              | cons b t' =>
                cases t' with
                | nil => simp only [List.getD_cons_zero, List.getD_cons_succ]
                | cons _ _ => rw [hl] at hgl; simp only [List.length_cons] at hgl; omega
          have hi0 : g.inputs.getD 0 0 < st.1.length := hrb0 _ (by rw [hgins]; exact List.mem_cons_self)
          have hi1 : g.inputs.getD 1 0 < st.1.length := hrb0 _ (by rw [hgins]; exact List.mem_cons_of_mem _ List.mem_cons_self)
          let s1 := st.1.getD (g.inputs.getD 0 0) (true, false, 0)
          let s2 := st.1.getD (g.inputs.getD 1 0) (true, false, 0)
          have hs1ev : ∀ x : Fin 10 → Bool, x v = false →
              (if s1.1 then s1.2.1 else (st.2.1.foldl stepWire (List.ofFn x)).getD s1.2.2 false) =
                (pref.foldl stepWire (List.ofFn x)).getD (g.inputs.getD 0 0) false :=
            fun x hxv => hev x hxv _ hi0
          have hs2ev : ∀ x : Fin 10 → Bool, x v = false →
              (if s2.1 then s2.2.1 else (st.2.1.foldl stepWire (List.ofFn x)).getD s2.2.2 false) =
                (pref.foldl stepWire (List.ofFn x)).getD (g.inputs.getD 1 0) false :=
            fun x hxv => hev x hxv _ hi1
          have hNoEmit : ∀ (newS : Bool × Bool × ℕ),
              st1 = (st.1 ++ [newS], st.2.1, st.2.2 + 1) →
              (newS.1 = false → newS.2.2 < 10 + st.2.1.length) →
              (∀ x : Fin 10 → Bool, x v = false →
                (if newS.1 then newS.2.1 else (st.2.1.foldl stepWire (List.ofFn x)).getD newS.2.2 false) =
                  g.op.eval (g.inputs.map fun i => (pref.foldl stepWire (List.ofFn x)).getD i false)) →
              st1.1.length = st.1.length + 1 ∧
              FanInTwo ⟨st1.2.1, 0⟩ ∧
              (st1.2.1.length - notCount ⟨st1.2.1, 0⟩) + (st1.2.2 - st.2.2) =
                (st.2.1.length - notCount ⟨st.2.1, 0⟩) + (if g.op = GateOp.not then 0 else 1) ∧
              st.2.2 ≤ st1.2.2 ∧
              notCount ⟨st1.2.1, 0⟩ ≤ notCount ⟨st.2.1, 0⟩ + (if g.op = GateOp.not then 1 else 0) ∧
              (∀ s ∈ st1.1, s.1 = false → s.2.2 < 10 + st1.2.1.length) ∧
              (∀ x : Fin 10 → Bool, x v = false → ∀ i < st1.1.length,
                let s := st1.1.getD i (true, false, 0)
                (if s.1 then s.2.1 else (st1.2.1.foldl stepWire (List.ofFn x)).getD s.2.2 false) =
                  ((pref ++ [g]).foldl stepWire (List.ofFn x)).getD i false) := by
            intro newS hst1_eq hnewB hnewEv
            rw [hst1_eq, ite_eq_right hgNot, ite_eq_right hgNot]
            dsimp only
            refine ⟨by simp only [List.length_append, List.length_singleton], hfan, by omega, by omega, by omega,
              fun t ht ht0 => (List.mem_append.mp ht).elim (fun h1 => hbnd t h1 ht0) (fun h2 => by rw [List.mem_singleton.mp h2] at ht0 ⊢; exact hnewB ht0),
              fun x hxv i hi => ?_⟩
            rw [List.length_append, List.length_singleton] at hi
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            by_cases hilt : i < st.1.length
            · have hget : (st.1 ++ [newS]).getD i (true, false, 0) = st.1.getD i (true, false, 0) := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt]
              rw [hget]
              have hstep : (stepWire (pref.foldl stepWire (List.ofFn x)) g).getD i false = (pref.foldl stepWire (List.ofFn x)).getD i false := by
                change ((pref.foldl stepWire (List.ofFn x)) ++ [_]).getD i false = _
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hPrefLen x]; exact hilt)]
              rw [hstep]; exact hev x hxv i hilt
            · have hieq : i = st.1.length := by omega
              subst i
              have hget : (st.1 ++ [newS]).getD st.1.length (true, false, 0) = newS := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              rw [hget, ← hPrefLen x, getD_step_at]; exact hnewEv x hxv
          have hEmitBin : ∀ (op : GateOp), g.op = op → (op = GateOp.and ∨ op = GateOp.or) →
              s1.1 = false → s2.1 = false →
              st1 = (st.1 ++ [(false, false, 10 + st.2.1.length)], st.2.1 ++ [⟨op, [s1.2.2, s2.2.2]⟩], st.2.2) →
              st1.1.length = st.1.length + 1 ∧
              FanInTwo ⟨st1.2.1, 0⟩ ∧
              (st1.2.1.length - notCount ⟨st1.2.1, 0⟩) + (st1.2.2 - st.2.2) =
                (st.2.1.length - notCount ⟨st.2.1, 0⟩) + (if g.op = GateOp.not then 0 else 1) ∧
              st.2.2 ≤ st1.2.2 ∧
              notCount ⟨st1.2.1, 0⟩ ≤ notCount ⟨st.2.1, 0⟩ + (if g.op = GateOp.not then 1 else 0) ∧
              (∀ s ∈ st1.1, s.1 = false → s.2.2 < 10 + st1.2.1.length) ∧
              (∀ x : Fin 10 → Bool, x v = false → ∀ i < st1.1.length,
                let s := st1.1.getD i (true, false, 0)
                (if s.1 then s.2.1 else (st1.2.1.foldl stepWire (List.ofFn x)).getD s.2.2 false) =
                  ((pref ++ [g]).foldl stepWire (List.ofFn x)).getD i false) := by
            intro op hop hbo hs1f hs2f hst1_eq
            have hopNot : op ≠ GateOp.not := by rcases hbo with rfl | rfl <;> exact GateOp.noConfusion
            have hnc : notCount ⟨st.2.1 ++ [⟨op, [s1.2.2, s2.2.2]⟩], 0⟩ = notCount ⟨st.2.1, 0⟩ := by
              rw [notCount_append _ _ 0 0 0, notCount_cons, ite_eq_right hopNot]; change _ + (0 + 0) = _; omega
            rw [hst1_eq, ite_eq_right hgNot, ite_eq_right hgNot]
            dsimp only
            refine ⟨by simp only [List.length_append, List.length_singleton],
              fun h hh => (List.mem_append.mp hh).elim (hfan h) (fun h1 => by
                rw [List.mem_singleton.mp h1]
                exact ⟨hbo.elim (fun e => e ▸ Or.inl rfl) (fun e => e ▸ Or.inr (Or.inl rfl)), by simp⟩),
              by rw [List.length_append, List.length_singleton, hnc]; omega, le_refl _, by rw [hnc]; omega, ?_, ?_⟩
            · intro t ht ht0
              rcases List.mem_append.mp ht with h1 | h2
              · have := hbnd t h1 ht0; rw [List.length_append, List.length_singleton]; omega
              · rw [List.mem_singleton.mp h2]; dsimp only; rw [List.length_append, List.length_singleton]; omega
            · intro x hxv i hi
              rw [List.length_append, List.length_singleton] at hi
              conv_rhs => rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
              by_cases hilt : i < st.1.length
              · have hget : (st.1 ++ [(false, false, 10 + st.2.1.length)]).getD i (true, false, 0) = st.1.getD i (true, false, 0) := by
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt]
                rw [hget]
                have hstep : (stepWire (pref.foldl stepWire (List.ofFn x)) g).getD i false = (pref.foldl stepWire (List.ofFn x)).getD i false := by
                  change ((pref.foldl stepWire (List.ofFn x)) ++ [_]).getD i false = _
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hPrefLen x]; exact hilt)]
                rw [hstep]; exact hAppendEv x hxv _ i hilt
              · have hieq : i = st.1.length := by omega
                subst i
                have hget : (st.1 ++ [(false, false, 10 + st.2.1.length)]).getD st.1.length (true, false, 0) = (false, false, 10 + st.2.1.length) := by
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
                rw [hget, ite_eq_right Bool.false_ne_true]
                conv_rhs => rw [← hPrefLen x, getD_step_at, hop, hgins]
                rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                dsimp only
                have hlw : (st.2.1.foldl stepWire (List.ofFn x)).length = 10 + st.2.1.length := by rw [foldl_len, List.length_ofFn]
                rw [← hlw, getD_step_at]
                simp only [List.map_cons, List.map_nil]
                have h1 := hs1ev x hxv; rw [hs1f, ite_eq_right Bool.false_ne_true] at h1
                have h2 := hs2ev x hxv; rw [hs2f, ite_eq_right Bool.false_ne_true] at h2
                rw [← h1, ← h2]
          rcases hgbo with hgand | hgor
          · have hst1_def : st1 = (if s1.1 then (if s1.2.1 then (st.1 ++ [s2], st.2.1, st.2.2 + 1) else (st.1 ++ [(true, false, 0)], st.2.1, st.2.2 + 1))
                else if s2.1 then (if s2.2.1 then (st.1 ++ [s1], st.2.1, st.2.2 + 1) else (st.1 ++ [(true, false, 0)], st.2.1, st.2.2 + 1))
                else (st.1 ++ [(false, false, 10 + st.2.1.length)], st.2.1 ++ [⟨GateOp.and, [s1.2.2, s2.2.2]⟩], st.2.2)) := by
              dsimp only [st1, rStep, s1, s2]; rw [ite_eq_right hgNot, ite_eq_left hgand]
            cases hs1 : s1.1 with
            | true =>
              cases hs1v : s1.2.1 with
              | true =>
                apply hNoEmit s2 (by rw [hst1_def, hs1, hs1v]; rfl) (hbnd s2 (hLookupMem _ hi1))
                intro x hxv; rw [hgand, hgins]; simp only [List.map_cons, List.map_nil]; rw [← hs1ev x hxv, ← hs2ev x hxv, hs1, hs1v]; simp only [hEvalAnd, hEvalOr, hEvalNot, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.true_and, ite_true]
              | false =>
                apply hNoEmit (true, false, 0) (by rw [hst1_def, hs1, hs1v]; rfl) (fun h => False.elim (Bool.noConfusion h))
                intro x hxv; rw [hgand, hgins]; simp only [List.map_cons, List.map_nil]; rw [← hs1ev x hxv, hs1, hs1v]; rfl
            | false =>
              cases hs2 : s2.1 with
              | true =>
                cases hs2v : s2.2.1 with
                | true =>
                  apply hNoEmit s1 (by rw [hst1_def, hs1, hs2, hs2v]; rfl) (hbnd s1 (hLookupMem _ hi0))
                  intro x hxv; rw [hgand, hgins]; simp only [List.map_cons, List.map_nil]; rw [← hs1ev x hxv, ← hs2ev x hxv, hs1, hs2, hs2v]
                  simp only [hEvalAnd, hEvalOr, hEvalNot, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ite_false, ite_true]
                | false =>
                  apply hNoEmit (true, false, 0) (by rw [hst1_def, hs1, hs2, hs2v]; rfl) (fun h => False.elim (Bool.noConfusion h))
                  intro x hxv; rw [hgand, hgins]; simp only [List.map_cons, List.map_nil]; rw [← hs2ev x hxv, hs2, hs2v]
                  simp only [hEvalAnd, hEvalOr, hEvalNot, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_false, ite_true]
              | false =>
                exact hEmitBin GateOp.and hgand (Or.inl rfl) hs1 hs2 (by rw [hst1_def, hs1, hs2]; rfl)
          · have hgNotAnd : g.op ≠ GateOp.and := by rw [hgor]; exact GateOp.noConfusion
            have hst1_def : st1 = (if s1.1 then (if s1.2.1 then (st.1 ++ [(true, true, 0)], st.2.1, st.2.2 + 1) else (st.1 ++ [s2], st.2.1, st.2.2 + 1))
                else if s2.1 then (if s2.2.1 then (st.1 ++ [(true, true, 0)], st.2.1, st.2.2 + 1) else (st.1 ++ [s1], st.2.1, st.2.2 + 1))
                else (st.1 ++ [(false, false, 10 + st.2.1.length)], st.2.1 ++ [⟨GateOp.or, [s1.2.2, s2.2.2]⟩], st.2.2)) := by
              dsimp only [st1, rStep, s1, s2]; rw [ite_eq_right hgNot, ite_eq_right hgNotAnd]
            cases hs1 : s1.1 with
            | true =>
              cases hs1v : s1.2.1 with
              | true =>
                apply hNoEmit (true, true, 0) (by rw [hst1_def, hs1, hs1v]; rfl) (fun h => False.elim (Bool.noConfusion h))
                intro x hxv; rw [hgor, hgins]; simp only [List.map_cons, List.map_nil]; rw [← hs1ev x hxv, hs1, hs1v]; rfl
              | false =>
                apply hNoEmit s2 (by rw [hst1_def, hs1, hs1v]; rfl) (hbnd s2 (hLookupMem _ hi1))
                intro x hxv; rw [hgor, hgins]; simp only [List.map_cons, List.map_nil]; rw [← hs1ev x hxv, ← hs2ev x hxv, hs1, hs1v]
                simp only [hEvalAnd, hEvalOr, hEvalNot, List.any_cons, List.any_nil, id_eq, Bool.false_or, Bool.or_false, ite_true]
            | false =>
              cases hs2 : s2.1 with
              | true =>
                cases hs2v : s2.2.1 with
                | true =>
                  apply hNoEmit (true, true, 0) (by rw [hst1_def, hs1, hs2, hs2v]; rfl) (fun h => False.elim (Bool.noConfusion h))
                  intro x hxv; rw [hgor, hgins]; simp only [List.map_cons, List.map_nil]; rw [← hs2ev x hxv, hs2, hs2v]
                  simp only [hEvalAnd, hEvalOr, hEvalNot, List.any_cons, List.any_nil, id_eq, Bool.or_true, Bool.or_false, ite_true]
                | false =>
                  apply hNoEmit s1 (by rw [hst1_def, hs1, hs2, hs2v]; rfl) (hbnd s1 (hLookupMem _ hi0))
                  intro x hxv; rw [hgor, hgins]; simp only [List.map_cons, List.map_nil]; rw [← hs1ev x hxv, ← hs2ev x hxv, hs1, hs2, hs2v]
                  simp only [hEvalAnd, hEvalOr, hEvalNot, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ite_false, ite_true]
              | false =>
                exact hEmitBin GateOp.or hgor (Or.inr rfl) hs1 hs2 (by rw [hst1_def, hs1, hs2]; rfl)
      obtain ⟨hl1, hfan1, hbin1, heb1, hnc1, hbnd1, hev1⟩ := hst1_props
      have hih := ih (pref ++ [g]) st1
        (by rw [hl1, hlen, List.length_append, List.length_singleton]; omega)
        (fun h hh => hshape h (List.mem_cons_of_mem g hh))
        (fun k hk i hi => by rw [hl1]; exact hrb_tail k hk i hi)
        hfan1 hbnd1 hev1
      obtain ⟨hfan2, hbin2, hnc2, hbnd2, hev2⟩ := hih
      have heb2 := (rStep_struct gs st1).2.2
      rw [List.foldl_cons]
      have hncGs := notCount_le_size ⟨gs, 0⟩; change notCount ⟨gs, 0⟩ ≤ gs.length at hncGs
      have hncG : notCount ⟨g :: gs, 0⟩ = (if g.op = GateOp.not then 1 else 0) + notCount ⟨gs, 0⟩ := notCount_cons g gs
      have happ : pref ++ g :: gs = (pref ++ [g]) ++ gs := by simp only [List.append_assoc, List.singleton_append]
      refine ⟨hfan2, ?_, ?_, hbnd2, by rw [happ]; exact hev2⟩
      · dsimp only [st1] at hbin1 hbin2 heb1 heb2
        have hlenG : (g :: gs).length = gs.length + 1 := List.length_cons
        by_cases hg : g.op = GateOp.not
        · rw [ite_eq_left hg] at hbin1 hncG; omega
        · rw [ite_eq_right hg] at hbin1 hncG; omega
      · dsimp only [st1] at hnc1 hnc2
        rw [hncG]; omega
  -- Exact lookup of rRun at gate k, and counting eliminated binary gates
  have rRun_at_step : ∀ (v : Fin 10) (C : Circuit) (k : ℕ), k < C.size →
      let stK := rRun v (C.gates.take k)
      stK.1.length = 10 + k ∧
      (∀ i < 10 + k, (rRun v C.gates).1.getD i (true, false, 0) = stK.1.getD i (true, false, 0)) ∧
      (rRun v C.gates).1.getD (10 + k) (true, false, 0) = (rStep stK (gateAt C k)).1.getD (10 + k) (true, false, 0) := by
    intro v C k hk
    have hInitL : (rInit v).length = 10 := by dsimp only [rInit]; exact List.length_ofFn
    have hSplit : C.gates = C.gates.take k ++ (gateAt C k :: C.gates.drop (k + 1)) := by
      rw [gateAt_eq hk]
      conv_lhs => rw [← List.take_append_drop k C.gates]
      rw [List.drop_eq_getElem_cons hk]
    have hL : (rRun v (C.gates.take k)).1.length = 10 + k := by
      have := (rStep_struct (C.gates.take k) (rInit v, [], 0)).1
      rw [hInitL, List.length_take_of_le (le_of_lt hk)] at this; exact this
    have hFold : rRun v C.gates = (C.gates.drop (k + 1)).foldl rStep (rStep (rRun v (C.gates.take k)) (gateAt C k)) := by
      dsimp only [rRun]; conv_lhs => rw [hSplit]
      rw [List.foldl_append, List.foldl_cons]
    have h1 := rStep_struct [gateAt C k] (rRun v (C.gates.take k))
    rw [List.foldl_cons, List.foldl_nil] at h1
    have h2 := rStep_struct (C.gates.drop (k + 1)) (rStep (rRun v (C.gates.take k)) (gateAt C k))
    have h1len : (rStep (rRun v (C.gates.take k)) (gateAt C k)).1.length = 10 + k + 1 := by
      have := h1.1; simp only [List.length_singleton] at this; omega
    refine ⟨hL, fun i hi => ?_, ?_⟩
    · rw [hFold, h2.2.1 i (by omega), h1.2.1 i (by omega)]
    · rw [hFold, h2.2.1 (10 + k) (by omega)]
  have rRun_init_at : ∀ (v : Fin 10) (C : Circuit) (i : Fin 10),
      (rRun v C.gates).1.getD i.val (true, false, 0) = if i = v then (true, false, 0) else (false, false, i.val) := by
    intro v C i
    have hInitL : (rInit v).length = 10 := by dsimp only [rInit]; exact List.length_ofFn
    have h := (rStep_struct C.gates (rInit v, [], 0)).2.1 i.val (by rw [hInitL]; exact i.isLt)
    dsimp only [rRun]; rw [h]
    dsimp only [rInit]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]
  have rRun_elim_card : ∀ (v : Fin 10) (C : Circuit) (S : Finset (Fin C.size)),
      ReadsBack 10 C →
      (∀ g ∈ C.gates, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
        ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) →
      (∀ k ∈ S, (C.gates.get k).op ≠ GateOp.not ∧
        ∃ i ∈ (C.gates.get k).inputs, ((rRun v C.gates).1.getD i (true, false, 0)).1 = true) →
      S.card ≤ (rRun v C.gates).2.2 := by
    intro v C S hrb hshape hS
    have hPref : ∀ m ≤ C.gates.length, (S.filter (fun k : Fin C.size => k.val < m)).card ≤ (rRun v (C.gates.take m)).2.2 := by
      intro m
      induction m with
      | zero =>
        intro _
        have hEmp : S.filter (fun k : Fin C.size => k.val < 0) = ∅ :=
          Finset.eq_empty_iff_forall_notMem.mpr (fun k hk => Nat.not_lt_zero k.val (Finset.mem_filter.mp hk).2)
        rw [hEmp, Finset.card_empty]; exact Nat.zero_le _
      | succ m ih =>
        intro hm
        have hmLt : m < C.gates.length := by omega
        have hTake : C.gates.take (m + 1) = C.gates.take m ++ [gateAt C m] := by
          rw [gateAt_eq hmLt, List.take_succ_eq_append_getElem hmLt]
        have hStepEq : rRun v (C.gates.take (m + 1)) = rStep (rRun v (C.gates.take m)) (gateAt C m) := by
          dsimp only [rRun]; rw [hTake, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hih := ih (by omega)
        let km : Fin C.size := ⟨m, hmLt⟩
        by_cases hkmS : km ∈ S
        · have hSub : S.filter (fun k : Fin C.size => k.val < m + 1) ⊆ insert km (S.filter (fun k : Fin C.size => k.val < m)) := by
            intro k hk
            obtain ⟨hkS, hklt⟩ := Finset.mem_filter.mp hk
            by_cases hkeq : k.val = m
            · have hke : k = km := Fin.ext hkeq; rw [hke]; exact Finset.mem_insert_self km _
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hkS, by omega⟩)
          have hCardLe : (S.filter (fun k : Fin C.size => k.val < m + 1)).card ≤ (S.filter (fun k : Fin C.size => k.val < m)).card + 1 :=
            le_trans (Finset.card_le_card hSub) (Finset.card_insert_le _ _)
          obtain ⟨hNot, i, hiIn, hiC⟩ := hS km hkmS
          have hgEq : C.gates.get km = gateAt C m := (gateAt_eq hmLt).symm
          rw [hgEq] at hNot hiIn
          have hgm := hshape (gateAt C m) (by rw [gateAt_eq hmLt]; exact List.getElem_mem hmLt)
          have hgbo : (gateAt C m).op = GateOp.and ∨ (gateAt C m).op = GateOp.or := by
            rcases hgm with ⟨h1, _⟩ | ⟨h2, _⟩; exact False.elim (hNot h1); exact h2
          have hgl : (gateAt C m).inputs.length = 2 := by
            rcases hgm with ⟨h1, _⟩ | ⟨_, h2⟩; exact False.elim (hNot h1); exact h2
          have hgins : (gateAt C m).inputs = [(gateAt C m).inputs.getD 0 0, (gateAt C m).inputs.getD 1 0] := by
            cases hl : (gateAt C m).inputs with
            | nil => rw [hl] at hgl; exact False.elim (Nat.noConfusion hgl)
            | cons a t =>
              cases t with
              | nil => rw [hl] at hgl; simp only [List.length_cons, List.length_nil] at hgl; omega
              | cons b t' =>
                cases t' with
                | nil => simp only [List.getD_cons_zero, List.getD_cons_succ]
                | cons _ _ => rw [hl] at hgl; simp only [List.length_cons] at hgl; omega
          have hiLt : i < 10 + m := hrb m hmLt i hiIn
          have hAt := rRun_at_step v C m hmLt
          rw [hAt.2.1 i hiLt] at hiC
          have hi01 : i = (gateAt C m).inputs.getD 0 0 ∨ i = (gateAt C m).inputs.getD 1 0 := by
            rw [hgins] at hiIn
            rcases List.mem_cons.mp hiIn with rfl | h1
            · exact Or.inl rfl
            · exact Or.inr (List.mem_singleton.mp h1)
          have hInc : (rStep (rRun v (C.gates.take m)) (gateAt C m)).2.2 = (rRun v (C.gates.take m)).2.2 + 1 := by
            dsimp only [rStep]; rw [ite_eq_right hNot]
            rcases hgbo with hand | hor
            · rw [ite_eq_left hand]
              rcases hi01 with h1 | h2
              · rw [← h1, ite_eq_left hiC]
                by_cases hv1 : ((rRun v (C.gates.take m)).1.getD i (true, false, 0)).2.1 = true
                · rw [ite_eq_left hv1]
                · rw [ite_eq_right hv1]
              · by_cases hs1 : ((rRun v (C.gates.take m)).1.getD ((gateAt C m).inputs.getD 0 0) (true, false, 0)).1 = true
                · rw [ite_eq_left hs1]
                  by_cases hv1 : ((rRun v (C.gates.take m)).1.getD ((gateAt C m).inputs.getD 0 0) (true, false, 0)).2.1 = true
                  · rw [ite_eq_left hv1]
                  · rw [ite_eq_right hv1]
                · rw [ite_eq_right hs1, ← h2, ite_eq_left hiC]
                  by_cases hv2 : ((rRun v (C.gates.take m)).1.getD i (true, false, 0)).2.1 = true
                  · rw [ite_eq_left hv2]
                  · rw [ite_eq_right hv2]
            · have hNotAnd : (gateAt C m).op ≠ GateOp.and := by rw [hor]; exact GateOp.noConfusion
              rw [ite_eq_right hNotAnd]
              rcases hi01 with h1 | h2
              · rw [← h1, ite_eq_left hiC]
                by_cases hv1 : ((rRun v (C.gates.take m)).1.getD i (true, false, 0)).2.1 = true
                · rw [ite_eq_left hv1]
                · rw [ite_eq_right hv1]
              · by_cases hs1 : ((rRun v (C.gates.take m)).1.getD ((gateAt C m).inputs.getD 0 0) (true, false, 0)).1 = true
                · rw [ite_eq_left hs1]
                  by_cases hv1 : ((rRun v (C.gates.take m)).1.getD ((gateAt C m).inputs.getD 0 0) (true, false, 0)).2.1 = true
                  · rw [ite_eq_left hv1]
                  · rw [ite_eq_right hv1]
                · rw [ite_eq_right hs1, ← h2, ite_eq_left hiC]
                  by_cases hv2 : ((rRun v (C.gates.take m)).1.getD i (true, false, 0)).2.1 = true
                  · rw [ite_eq_left hv2]
                  · rw [ite_eq_right hv2]
          rw [hStepEq, hInc]; omega
        · have hEq : S.filter (fun k : Fin C.size => k.val < m + 1) = S.filter (fun k : Fin C.size => k.val < m) := by
            apply Finset.ext; intro k; simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hkS, hklt⟩
              refine ⟨hkS, ?_⟩
              by_contra hge
              have hkeq : k = km := Fin.ext (by dsimp only [km]; omega)
              exact hkmS (hkeq ▸ hkS)
            · rintro ⟨hkS, hklt⟩; exact ⟨hkS, by omega⟩
          rw [hEq, hStepEq]
          have hMonoStep := (rStep_struct [gateAt C m] (rRun v (C.gates.take m))).2.2
          rw [List.foldl_cons, List.foldl_nil] at hMonoStep
          omega
    have hAll := hPref C.gates.length (le_refl _)
    have hFilt : S.filter (fun k : Fin C.size => k.val < C.gates.length) = S :=
      Finset.filter_true_of_mem (fun k _ => k.isLt)
    rw [hFilt, List.take_length] at hAll
    exact hAll
  -- Bound on eliminated binary gates from hBound15 via S_5
  have rRun_main : ∀ (v : Fin 10) (C : Circuit),
      ReadsBack 10 C →
      (∀ g ∈ C.gates, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
        ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) →
      C.output < 10 + C.size →
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Plist x) →
      (rRun v C.gates).2.2 + 15 + notCount C ≤ C.size ∧
      ((rRun v C.gates).1.getD C.output (true, false, 0)).1 = false := by
    intro v C hrb hshape hout hcomp
    have hInitL : (rInit v).length = 10 := by dsimp only [rInit]; exact List.length_ofFn
    have hInv := rStep_inv v C.gates [] (rInit v, [], 0) (by rw [hInitL]; rfl) hshape
      (fun k hk i hi => by rw [hInitL]; exact hrb k hk i (gateAt_eq hk ▸ hi))
      (fun _ h => False.elim (List.not_mem_nil h))
      (fun s hs hs0 => by
        dsimp only [rInit] at hs; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
        by_cases hiv : i = v
        · rw [ite_eq_left hiv] at hs0; exact False.elim (Bool.noConfusion hs0)
        · rw [ite_eq_right hiv]; have := i.isLt; omega)
      (fun x hxv i hi => by
        rw [hInitL] at hi; dsimp only [rInit]
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]
        dsimp only
        by_cases hiv : (⟨i, hi⟩ : Fin 10) = v
        · rw [ite_eq_left hiv, ite_eq_left rfl, List.foldl_nil]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]
          rw [hiv, hxv]
        · rw [ite_eq_right hiv, ite_eq_right Bool.false_ne_true, List.foldl_nil])
    obtain ⟨hFan', hBinEq, _, _, hEv'⟩ := hInv
    have hLen' : (rRun v C.gates).1.length = 10 + C.size := by
      have := (rStep_struct C.gates (rInit v, [], 0)).1; rw [hInitL] at this; exact this
    have hOutNC : ((rRun v C.gates).1.getD C.output (true, false, 0)).1 = false := by
      apply Bool.eq_false_iff.mpr; intro hc
      have h0 := hEv' (fun _ => false) rfl C.output (by rw [hLen']; exact hout)
      dsimp only at h0; rw [ite_eq_left hc, List.nil_append] at h0
      have h0p : Plist (fun _ => false) = false := by
        apply Bool.eq_false_iff.mpr; intro ht
        obtain ⟨a, b, _, ha, _⟩ := (hP_iff_adj (fun _ => false)).mp ht; exact Bool.noConfusion ha
      change ((rRun v C.gates).1.getD C.output (true, false, 0)).2.1 = C.eval (List.ofFn (fun _ => false)) at h0
      rw [hcomp, h0p] at h0
      obtain ⟨a, b, hav, hbv, hab⟩ := hAvoidEdge v
      let x1 : Fin 10 → Bool := fun u => decide (u = a ∨ u = b)
      have hx1v : x1 v = false := decide_eq_false (fun h => h.elim hav.symm hbv.symm)
      have h1 := hEv' x1 hx1v C.output (by rw [hLen']; exact hout)
      dsimp only at h1; rw [ite_eq_left hc, List.nil_append] at h1
      change ((rRun v C.gates).1.getD C.output (true, false, 0)).2.1 = C.eval (List.ofFn x1) at h1
      have h1p : Plist x1 = true := (hP_iff_adj x1).mpr ⟨a, b, hab, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
      rw [hcomp, h1p, h0] at h1; exact Bool.noConfusion h1
    let C' : Circuit := ⟨(rRun v C.gates).2.1, ((rRun v C.gates).1.getD C.output (true, false, 0)).2.2⟩
    have hC'ev : ∀ x : Fin 10 → Bool, x v = false → C'.eval (List.ofFn x) = Plist x := by
      intro x hxv
      have h := hEv' x hxv C.output (by rw [hLen']; exact hout)
      dsimp only at h; rw [hOutNC, ite_eq_right Bool.false_ne_true, List.nil_append] at h
      exact h.trans (hcomp x)
    have hTo9 := hTo9Perm_ok v
    let τ : Fin 10 → Fin 10 := liftS5 (to9Perm5 v).1
    have hLift := hLift_props (to9Perm5 v).1 (to9Perm5 v).2 hTo9.1
    let C9' : Circuit := relabelC τ C'
    have hC9'fan : FanInTwo C9' := fun g hg => by
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
      have hf := hFan' h hh
      exact ⟨hf.1, by dsimp only [relabelG]; rw [List.length_map]; exact hf.2⟩
    have hC9'ev : ∀ y : Fin 10 → Bool, y 9 = false → C9'.eval (List.ofFn y) = Plist y := by
      intro y hy9
      change ((relabelC τ C').wires (List.ofFn y)).getD (relabelW τ C'.output) false = Plist y
      rw [relabel_eval τ C' y]
      have hvy : (y ∘ τ) v = false := by change y (liftS5 (to9Perm5 v).1 v) = false; rw [hTo9.2]; exact hy9
      exact (hC'ev (y ∘ τ) hvy).trans (hLift.2.2 y)
    have hB15 := hBound15 C9' hC9'fan hC9'ev
    have hC9'sz : C9'.size = C'.size := List.length_map _
    have hC9'nc : notCount C9' = notCount C' := notCount_map_same_op C'.gates (relabelG τ) (fun _ _ => rfl)
    have hBinEq' : (C'.size - notCount C') + (rRun v C.gates).2.2 = C.size - notCount C := by
      change ((rRun v C.gates).2.1.length - notCount ⟨(rRun v C.gates).2.1, 0⟩) + (rRun v C.gates).2.2 = C.gates.length - notCount C
      dsimp only [rRun] at hBinEq ⊢
      have h0 : notCount ⟨[], 0⟩ = 0 := rfl
      have h1 : notCount ⟨C.gates, 0⟩ = notCount C := rfl
      rw [h1, h0, List.length_nil, Nat.sub_zero, Nat.sub_zero, Nat.zero_add] at hBinEq
      exact hBinEq
    have hNcLe := notCount_le_size C
    exact ⟨by omega, hOutNC⟩
  -- Helper: from a constant wire in rRun, walk forward through InOutCone to a binary elim gate
  have hConstHasElimReader : ∀ (v : Fin 10) (C : Circuit),
      ReadsBack 10 C →
      (∀ g ∈ C.gates, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
        ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) →
      C.output + 1 = 10 + C.size →
      ((rRun v C.gates).1.getD C.output (true, false, 0)).1 = false →
      (∀ k < C.size, InOutCone 10 C (10 + k) C.output) →
      ∀ k < C.size, ((rRun v C.gates).1.getD (10 + k) (true, false, 0)).1 = true →
        ∃ h < C.size, k < h ∧ (gateAt C h).op ≠ GateOp.not ∧
          ∃ w ∈ (gateAt C h).inputs, InOutCone 10 C (10 + k) w ∧
            ((rRun v C.gates).1.getD w (true, false, 0)).1 = true := by
    intro v C hrb hshape hout hOutNC hLive k
    induction hrem : C.size - k using Nat.strong_induction_on generalizing k with
    | ind d ih =>
      intro hk hkc
      have hneOut : 10 + k ≠ C.output := fun heq => by
        rw [heq, hOutNC] at hkc; exact Bool.noConfusion hkc
      have hCone : InCone 10 C k (C.output - 10) := by
        rcases hLive k hk with heq | ⟨_, _, hcone⟩
        · exact False.elim (hneOut heq)
        · have hsub : 10 + k - 10 = k := by omega
          rw [hsub] at hcone; exact hcone
      obtain ⟨h, hkh, hle, hkin, hstep⟩ := inCone_fwd C hCone
      have hhlt : h < C.size := by omega
      by_cases hbin : (gateAt C h).op ≠ GateOp.not
      · exact ⟨h, hhlt, hkh, hbin, 10 + k, hkin, Or.inl rfl, hkc⟩
      · have hhop : (gateAt C h).op = GateOp.not := Classical.not_not.mp hbin
        have hhl : (gateAt C h).inputs.length = 1 := by
          rcases hshape (gateAt C h) (by rw [gateAt_eq hhlt]; exact List.getElem_mem hhlt) with ⟨_, hl⟩ | ⟨hbo, _⟩
          · exact hl
          · rcases hbo with h1 | h1 <;> rw [hhop] at h1 <;> exact False.elim (GateOp.noConfusion h1)
        have hhins : (gateAt C h).inputs = [10 + k] := by
          cases hl : (gateAt C h).inputs with
          | nil => rw [hl] at hhl; exact False.elim (Nat.noConfusion hhl)
          | cons a t =>
            cases t with
            | nil => rw [hl] at hkin; rw [List.mem_singleton.mp hkin]
            | cons _ _ => rw [hl] at hhl; simp only [List.length_cons] at hhl; omega
        have hhc : ((rRun v C.gates).1.getD (10 + h) (true, false, 0)).1 = true := by
          have hAt := rRun_at_step v C h hhlt
          rw [hAt.2.2]
          dsimp only [rStep]
          rw [ite_eq_left hhop, hhins, List.getD_cons_zero]
          have hkc' : ((rRun v (C.gates.take h)).1.getD (10 + k) (true, false, 0)).1 = true := by
            rw [← hAt.2.1 (10 + k) (by omega)]; exact hkc
          rw [ite_eq_left hkc']
          rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        obtain ⟨h', hh'lt, hhh', hbin', w, hwin, hcone', hwc⟩ := ih (C.size - h) (by omega) h rfl hhlt hhc
        have hkhCone : InOutCone 10 C (10 + k) (10 + h) := Or.inr ⟨by omega, by omega, by
          have hs1 : 10 + k - 10 = k := by omega
          have hs2 : 10 + h - 10 = h := by omega
          rw [hs1, hs2]
          exact (inCone_iff C k h).mpr ⟨hhlt, k, hkh, hkin, Or.inl rfl⟩⟩
        exact ⟨h', hh'lt, by omega, hbin', w, hwin, inOutCone_trans C hkhCone hcone', hwc⟩
  -- If elimBin ≤ 2 and binary gate k becomes const, NO binary gate g ≠ k reads a const wire outside k's cone
  have hNoConstWithOther : ∀ (v : Fin 10) (C : Circuit),
      ReadsBack 10 C →
      (∀ g ∈ C.gates, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
        ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) →
      C.output + 1 = 10 + C.size →
      ((rRun v C.gates).1.getD C.output (true, false, 0)).1 = false →
      (∀ k < C.size, InOutCone 10 C (10 + k) C.output) →
      (rRun v C.gates).2.2 ≤ 2 →
      ∀ k < C.size, (gateAt C k).op ≠ GateOp.not →
        (∃ i ∈ (gateAt C k).inputs, ((rRun v C.gates).1.getD i (true, false, 0)).1 = true) →
        ((rRun v C.gates).1.getD (10 + k) (true, false, 0)).1 = true →
        ∀ g < C.size, g ≠ k → (gateAt C g).op ≠ GateOp.not →
          ∀ w0 ∈ (gateAt C g).inputs, ((rRun v C.gates).1.getD w0 (true, false, 0)).1 = true →
            ¬ InOutCone 10 C (10 + k) w0 → False := by
    intro v C hrb hshape hout hOutNC hLive hElim2 k hk hkBin hkIn hkc g hg hgk hgBin w0 hw0In hw0c hw0NotCone
    obtain ⟨h, hhlt, hkh, hhBin, w, hwin, hwCone, hwc⟩ := hConstHasElimReader v C hrb hshape hout hOutNC hLive k hk hkc
    by_cases hgh : g = h
    · subst hgh
      have hww0ne : w ≠ w0 := fun heq => hw0NotCone (heq ▸ hwCone)
      have hgShape := hshape (gateAt C g) (by rw [gateAt_eq hg]; exact List.getElem_mem hg)
      have hgbo : (gateAt C g).op = GateOp.and ∨ (gateAt C g).op = GateOp.or := by
        rcases hgShape with ⟨h1, _⟩ | ⟨h2, _⟩; exact False.elim (hgBin h1); exact h2
      have hgl : (gateAt C g).inputs.length = 2 := by
        rcases hgShape with ⟨h1, _⟩ | ⟨_, h2⟩; exact False.elim (hgBin h1); exact h2
      have hgins : (gateAt C g).inputs = [(gateAt C g).inputs.getD 0 0, (gateAt C g).inputs.getD 1 0] := by
        cases hl : (gateAt C g).inputs with
        | nil => rw [hl] at hgl; exact False.elim (Nat.noConfusion hgl)
        | cons a t =>
          cases t with
          | nil => rw [hl] at hgl; simp only [List.length_cons, List.length_nil] at hgl; omega
          | cons b t' =>
            cases t' with
            | nil => simp only [List.getD_cons_zero, List.getD_cons_succ]
            | cons _ _ => rw [hl] at hgl; simp only [List.length_cons] at hgl; omega
      have hBothC : ((rRun v C.gates).1.getD ((gateAt C g).inputs.getD 0 0) (true, false, 0)).1 = true ∧
          ((rRun v C.gates).1.getD ((gateAt C g).inputs.getD 1 0) (true, false, 0)).1 = true := by
        rw [hgins] at hwin hw0In
        rcases List.mem_cons.mp hwin with h1 | h1 <;> rcases List.mem_cons.mp hw0In with h2 | h2
        · exact False.elim (hww0ne (h1.trans h2.symm))
        · rw [List.mem_singleton.mp h2] at hw0c; rw [h1] at hwc; exact ⟨hwc, hw0c⟩
        · rw [List.mem_singleton.mp h1] at hwc; rw [h2] at hw0c; exact ⟨hw0c, hwc⟩
        · exact False.elim (hww0ne ((List.mem_singleton.mp h1).trans (List.mem_singleton.mp h2).symm))
      have hgc : ((rRun v C.gates).1.getD (10 + g) (true, false, 0)).1 = true := by
        have hAt := rRun_at_step v C g hg
        have hi0lt : (gateAt C g).inputs.getD 0 0 < 10 + g := hrb g hg _ (by rw [hgins]; exact List.mem_cons_self)
        have hi1lt : (gateAt C g).inputs.getD 1 0 < 10 + g := hrb g hg _ (by rw [hgins]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        have h0c : ((rRun v (C.gates.take g)).1.getD ((gateAt C g).inputs.getD 0 0) (true, false, 0)).1 = true := by
          rw [← hAt.2.1 _ hi0lt]; exact hBothC.1
        have h1c : ((rRun v (C.gates.take g)).1.getD ((gateAt C g).inputs.getD 1 0) (true, false, 0)).1 = true := by
          rw [← hAt.2.1 _ hi1lt]; exact hBothC.2
        rw [hAt.2.2]
        dsimp only [rStep]; rw [ite_eq_right hgBin]
        rcases hgbo with hand | hor
        · rw [ite_eq_left hand, ite_eq_left h0c]
          by_cases hv0 : ((rRun v (C.gates.take g)).1.getD ((gateAt C g).inputs.getD 0 0) (true, false, 0)).2.1 = true
          · rw [ite_eq_left hv0]
            rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]; exact h1c
          · rw [ite_eq_right hv0]
            rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        · have hNotAnd : (gateAt C g).op ≠ GateOp.and := by rw [hor]; exact GateOp.noConfusion
          rw [ite_eq_right hNotAnd, ite_eq_left h0c]
          by_cases hv0 : ((rRun v (C.gates.take g)).1.getD ((gateAt C g).inputs.getD 0 0) (true, false, 0)).2.1 = true
          · rw [ite_eq_left hv0]
            rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          · rw [ite_eq_right hv0]
            rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]; exact h1c
      obtain ⟨h', hh'lt, hgh', hh'Bin, w', hw'in, _, hw'c⟩ := hConstHasElimReader v C hrb hshape hout hOutNC hLive g hg hgc
      let fk : Fin C.size := ⟨k, hk⟩
      let fg : Fin C.size := ⟨g, hg⟩
      let fh' : Fin C.size := ⟨h', hh'lt⟩
      let S3 : Finset (Fin C.size) := {fk, fg, fh'}
      have hcard3 : S3.card = 3 := by
        have h1 : fk ≠ fg := fun e => hgk (congrArg Fin.val e).symm
        have h2 : fk ≠ fh' := fun e => by have := congrArg Fin.val e; dsimp only [fk, fh'] at this; omega
        have h3 : fg ≠ fh' := fun e => by have := congrArg Fin.val e; dsimp only [fg, fh'] at this; omega
        rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1, h2⟩),
          Finset.card_pair h3]
      have hle := rRun_elim_card v C S3 hrb hshape (fun idx hidx => by
        rcases Finset.mem_insert.mp hidx with rfl | h1
        · exact ⟨by change (C.gates[k]'hk).op ≠ GateOp.not; rw [← gateAt_eq hk]; exact hkBin,
            by change ∃ i ∈ (C.gates[k]'hk).inputs, _; rw [← gateAt_eq hk]; exact hkIn⟩
        · rcases Finset.mem_insert.mp h1 with rfl | h2
          · exact ⟨by change (C.gates[g]'hg).op ≠ GateOp.not; rw [← gateAt_eq hg]; exact hgBin,
              w0, by change w0 ∈ (C.gates[g]'hg).inputs; rw [← gateAt_eq hg]; exact hw0In, hw0c⟩
          · rw [Finset.mem_singleton.mp h2]
            exact ⟨by change (C.gates[h']'hh'lt).op ≠ GateOp.not; rw [← gateAt_eq hh'lt]; exact hh'Bin,
              w', by change w' ∈ (C.gates[h']'hh'lt).inputs; rw [← gateAt_eq hh'lt]; exact hw'in, hw'c⟩)
      omega
    · let fk : Fin C.size := ⟨k, hk⟩
      let fh : Fin C.size := ⟨h, hhlt⟩
      let fg : Fin C.size := ⟨g, hg⟩
      let S3 : Finset (Fin C.size) := {fk, fh, fg}
      have hcard3 : S3.card = 3 := by
        have h1 : fk ≠ fh := fun e => by have := congrArg Fin.val e; dsimp only [fk, fh] at this; omega
        have h2 : fk ≠ fg := fun e => hgk (congrArg Fin.val e).symm
        have h3 : fh ≠ fg := fun e => hgh (congrArg Fin.val e).symm
        rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1, h2⟩),
          Finset.card_pair h3]
      have hle := rRun_elim_card v C S3 hrb hshape (fun idx hidx => by
        rcases Finset.mem_insert.mp hidx with rfl | h1
        · exact ⟨by change (C.gates[k]'hk).op ≠ GateOp.not; rw [← gateAt_eq hk]; exact hkBin,
            by change ∃ i ∈ (C.gates[k]'hk).inputs, _; rw [← gateAt_eq hk]; exact hkIn⟩
        · rcases Finset.mem_insert.mp h1 with rfl | h2
          · exact ⟨by change (C.gates[h]'hhlt).op ≠ GateOp.not; rw [← gateAt_eq hhlt]; exact hhBin,
              w, by change w ∈ (C.gates[h]'hhlt).inputs; rw [← gateAt_eq hhlt]; exact hwin, hwc⟩
          · rw [Finset.mem_singleton.mp h2]
            exact ⟨by change (C.gates[g]'hg).op ≠ GateOp.not; rw [← gateAt_eq hg]; exact hgBin,
              w0, by change w0 ∈ (C.gates[g]'hg).inputs; rw [← gateAt_eq hg]; exact hw0In, hw0c⟩)
      omega
  -- Sanitize any FanInTwo circuit into ReadsBack 10 + NOT arity 1 while preserving size, eval, and OR ops
  have hSanitizeRB : ∀ (C : Circuit), FanInTwo C →
      ∃ C' : Circuit, FanInTwo C' ∧ ReadsBack 10 C' ∧ C'.size = C.size ∧ C'.output = C.output ∧
        notCount C' ≤ notCount C ∧
        (∀ g ∈ C'.gates, g.op = GateOp.not → g.inputs.length = 1) ∧
        (∀ m < C.size, (gateAt C m).op = GateOp.or → (gateAt C' m).op = GateOp.or) ∧
        (∀ x : Fin 10 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) := by
    intro C hfan
    let sanGate : ℕ → Gate → Gate := fun idx g =>
      if g.op = GateOp.not then
        if 1 ≤ g.inputs.length ∧ g.inputs.getD 0 0 < 10 + idx then ⟨GateOp.not, [g.inputs.getD 0 0]⟩
        else ⟨GateOp.and, []⟩
      else if g.op = GateOp.and then
        if g.inputs.all (fun w => decide (w < 10 + idx)) then g
        else ⟨GateOp.or, []⟩
      else
        ⟨GateOp.or, g.inputs.filter (fun w => decide (w < 10 + idx))⟩
    let sanStep : List Gate → Gate → List Gate := fun acc g => acc ++ [sanGate acc.length g]
    have hSanGate_ok : ∀ (idx : ℕ) (g : Gate),
        (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        let g' := sanGate idx g
        (g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
        (∀ i ∈ g'.inputs, i < 10 + idx) ∧
        (g'.op = GateOp.not → g.op = GateOp.not ∧ g'.inputs.length = 1) ∧
        (g.op = GateOp.or → g'.op = GateOp.or) ∧
        (∀ w : List Bool, w.length = 10 + idx →
          g'.op.eval (g'.inputs.map fun i => w.getD i false) =
            g.op.eval (g.inputs.map fun i => w.getD i false)) := by
      intro idx g hgf
      dsimp only [sanGate]
      by_cases hnot : g.op = GateOp.not
      · rw [ite_eq_left hnot]
        by_cases hok : 1 ≤ g.inputs.length ∧ g.inputs.getD 0 0 < 10 + idx
        · rw [ite_eq_left hok]
          refine ⟨⟨Or.inr (Or.inr rfl), by simp⟩, fun i hi => by rw [List.mem_singleton.mp hi]; exact hok.2,
            fun _ => ⟨hnot, rfl⟩, fun h => by rw [hnot] at h; exact False.elim (GateOp.noConfusion h), fun w hw => ?_⟩
          cases hl : g.inputs with
          | nil => rw [hl] at hok; simp only [List.length_nil] at hok; omega
          | cons a t => rw [hnot]; rfl
        · rw [ite_eq_right hok]
          refine ⟨⟨Or.inl rfl, by simp⟩, fun _ h => False.elim (List.not_mem_nil h),
            fun h => False.elim (GateOp.noConfusion h), fun h => by rw [hnot] at h; exact False.elim (GateOp.noConfusion h), fun w hw => ?_⟩
          cases hl : g.inputs with
          | nil => rw [hnot]; rfl
          | cons a t =>
            have hge : 10 + idx ≤ a := by
              rw [hl] at hok; simp only [List.length_cons, List.getD_cons_zero] at hok; omega
            rw [hnot]; simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.headD_cons, List.all_nil]
            rw [getD_ge w a (by omega)]; rfl
      · rw [ite_eq_right hnot]
        by_cases hand : g.op = GateOp.and
        · rw [ite_eq_left hand]
          by_cases hall : g.inputs.all (fun w => decide (w < 10 + idx)) = true
          · rw [ite_eq_left hall]
            refine ⟨hgf, fun i hi => of_decide_eq_true (List.all_eq_true.mp hall i hi),
              fun h => False.elim (hnot h), fun h => False.elim (GateOp.noConfusion (hand.symm.trans h)), fun _ _ => rfl⟩
          · rw [ite_eq_right hall]
            refine ⟨⟨Or.inr (Or.inl rfl), by simp⟩, fun _ h => False.elim (List.not_mem_nil h),
              fun h => False.elim (GateOp.noConfusion h), fun h => False.elim (GateOp.noConfusion (hand.symm.trans h)), fun w hw => ?_⟩
            have hex : ∃ i ∈ g.inputs, 10 + idx ≤ i := by
              by_contra hno
              apply hall
              exact List.all_eq_true.mpr (fun i hi => decide_eq_true (by by_contra hge; exact hno ⟨i, hi, by omega⟩))
            obtain ⟨i, hi, hge⟩ := hex
            rw [hand, hEvalAnd, hEvalOr]; change false = _
            symm; apply Bool.eq_false_iff.mpr; intro htrue
            have h1 := List.all_eq_true.mp htrue (w.getD i false) (List.mem_map.mpr ⟨i, hi, rfl⟩)
            rw [id_eq, getD_ge w i (by omega)] at h1; exact Bool.noConfusion h1
        · rw [ite_eq_right hand]
          have hor : g.op = GateOp.or := by
            rcases hgf.1 with h1 | h2 | h3
            · exact False.elim (hand h1)
            · exact h2
            · exact False.elim (hnot h3)
          refine ⟨⟨Or.inr (Or.inl rfl), le_trans (List.length_filter_le _ _) hgf.2⟩,
            fun i hi => of_decide_eq_true (List.mem_filter.mp hi).2,
            fun h => False.elim (GateOp.noConfusion h), fun _ => rfl, fun w hw => ?_⟩
          rw [hor, hEvalOr, hEvalOr]
          apply Bool.eq_iff_iff.mpr
          rw [List.any_eq_true, List.any_eq_true]
          constructor
          · rintro ⟨b, hb, hbt⟩
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
            exact ⟨w.getD i false, List.mem_map.mpr ⟨i, (List.mem_filter.mp hi).1, rfl⟩, hbt⟩
          · rintro ⟨b, hb, hbt⟩
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
            have hilt : i < 10 + idx := by
              by_contra hge
              rw [id_eq, getD_ge w i (by omega)] at hbt; exact Bool.noConfusion hbt
            exact ⟨w.getD i false, List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨hi, decide_eq_true hilt⟩, rfl⟩, hbt⟩
    have hSanFold : ∀ (gs acc orig : List Gate),
        acc.length = orig.length →
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        FanInTwo ⟨acc, 0⟩ →
        ReadsBack 10 ⟨acc, 0⟩ →
        (∀ g ∈ acc, g.op = GateOp.not → g.inputs.length = 1) →
        (∀ m < orig.length, (gateAt ⟨orig, 0⟩ m).op = GateOp.or → (gateAt ⟨acc, 0⟩ m).op = GateOp.or) →
        notCount ⟨acc, 0⟩ ≤ notCount ⟨orig, 0⟩ →
        (∀ x : Fin 10 → Bool, acc.foldl stepWire (List.ofFn x) = orig.foldl stepWire (List.ofFn x)) →
        let out := gs.foldl sanStep acc
        out.length = orig.length + gs.length ∧
        FanInTwo ⟨out, 0⟩ ∧
        ReadsBack 10 ⟨out, 0⟩ ∧
        (∀ g ∈ out, g.op = GateOp.not → g.inputs.length = 1) ∧
        (∀ m < orig.length + gs.length, (gateAt ⟨orig ++ gs, 0⟩ m).op = GateOp.or → (gateAt ⟨out, 0⟩ m).op = GateOp.or) ∧
        notCount ⟨out, 0⟩ ≤ notCount ⟨orig ++ gs, 0⟩ ∧
        (∀ x : Fin 10 → Bool, out.foldl stepWire (List.ofFn x) = (orig ++ gs).foldl stepWire (List.ofFn x)) := by
      intro gs
      induction gs with
      | nil =>
        intro acc orig hlen _ hfan' hrb' hnot1' hor' hnc' hw'
        exact ⟨by simp only [List.foldl_nil, List.length_nil, Nat.add_zero, hlen], hfan', hrb', hnot1',
          by simpa only [List.foldl_nil, List.length_nil, Nat.add_zero, List.append_nil] using hor',
          by simpa only [List.foldl_nil, List.append_nil] using hnc',
          by simpa only [List.foldl_nil, List.append_nil] using hw'⟩
      | cons g gs ih =>
        intro acc orig hlen hgs hfan' hrb' hnot1' hor' hnc' hw'
        obtain ⟨hgf', hgrb', hgn1', hgor', hgev'⟩ := hSanGate_ok acc.length g (hgs g List.mem_cons_self)
        let acc1 := sanStep acc g
        let orig1 := orig ++ [g]
        have hlen1 : acc1.length = orig1.length := by
          dsimp only [acc1, sanStep, orig1]; rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton, hlen]
        have hfan1 : FanInTwo ⟨acc1, 0⟩ := fun h hh =>
          (List.mem_append.mp hh).elim (hfan' h) (fun h2 => (List.mem_singleton.mp h2) ▸ hgf')
        have hrb1 : ReadsBack 10 ⟨acc1, 0⟩ := by
          intro k hk i hi
          dsimp only [acc1, sanStep] at hk hi
          rw [gateAt_eq (by dsimp only; exact hk)] at hi
          by_cases hlt : k < acc.length
          · rw [List.getElem_append_left hlt] at hi
            exact hrb' k hlt i (by rw [gateAt_eq hlt]; exact hi)
          · have hkeq : k = acc.length := by rw [List.length_append, List.length_singleton] at hk; omega
            subst hkeq
            rw [List.getElem_append_right (le_refl _)] at hi
            simp only [Nat.sub_self, List.getElem_cons_zero] at hi
            exact hgrb' i hi
        have hnot1_1 : ∀ h ∈ acc1, h.op = GateOp.not → h.inputs.length = 1 := fun h hh hhn =>
          (List.mem_append.mp hh).elim (fun h1 => hnot1' h h1 hhn) (fun h2 => (hgn1' ((List.mem_singleton.mp h2) ▸ hhn)).2 |> fun e => (List.mem_singleton.mp h2).symm ▸ e)
        have hor1 : ∀ m < orig1.length, (gateAt ⟨orig1, 0⟩ m).op = GateOp.or → (gateAt ⟨acc1, 0⟩ m).op = GateOp.or := by
          intro m hm hmo
          have hm' : m < orig.length + 1 := by dsimp only [orig1] at hm; rw [List.length_append, List.length_singleton] at hm; exact hm
          rw [gateAt_eq hm] at hmo; rw [gateAt_eq (by rw [hlen1]; exact hm)]
          by_cases hlt : m < orig.length
          · rw [List.getElem_append_left hlt] at hmo
            rw [List.getElem_append_left (by omega : m < acc.length)]
            have h := hor' m hlt (by rw [gateAt_eq hlt]; exact hmo)
            rw [gateAt_eq (by omega : m < acc.length)] at h; exact h
          · have hmeq : m = orig.length := by omega
            subst hmeq
            dsimp only [orig1] at hmo; rw [List.getElem_append_right (le_refl _)] at hmo; simp only [Nat.sub_self, List.getElem_cons_zero] at hmo
            dsimp only [acc1, sanStep]; rw [List.getElem_append_right (by omega : acc.length ≤ orig.length)]
            have hsub : orig.length - acc.length = 0 := by omega
            simp only [hsub, List.getElem_cons_zero]
            exact hgor' hmo
        have hnc1 : notCount ⟨acc1, 0⟩ ≤ notCount ⟨orig1, 0⟩ := by
          dsimp only [acc1, sanStep, orig1]
          rw [notCount_append _ _ 0 0 0, notCount_append _ _ 0 0 0, notCount_cons, notCount_cons]
          by_cases h1 : (sanGate acc.length g).op = GateOp.not
          · rw [ite_eq_left h1, ite_eq_left (hgn1' h1).1]; omega
          · rw [ite_eq_right h1]; omega
        have hw1 : ∀ x : Fin 10 → Bool, acc1.foldl stepWire (List.ofFn x) = orig1.foldl stepWire (List.ofFn x) := by
          intro x
          dsimp only [acc1, sanStep, orig1]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_append, List.foldl_cons, List.foldl_nil, hw' x]
          dsimp only [stepWire]
          congr 2
          exact hgev' (orig.foldl stepWire (List.ofFn x)) (by rw [foldl_len, List.length_ofFn, hlen])
        have hih := ih acc1 orig1 hlen1 (fun h hh => hgs h (List.mem_cons_of_mem g hh)) hfan1 hrb1 hnot1_1 hor1 hnc1 hw1
        have happ : orig ++ g :: gs = orig1 ++ gs := by dsimp only [orig1]; simp only [List.append_assoc, List.singleton_append]
        have hlenEq : orig1.length + gs.length = orig.length + (g :: gs).length := by
          dsimp only [orig1]; rw [List.length_append, List.length_singleton, List.length_cons]; omega
        rw [List.foldl_cons]
        exact ⟨by rw [hih.1, hlenEq], hih.2.1, hih.2.2.1, hih.2.2.2.1,
          fun m hm hmo => hih.2.2.2.2.1 m (by omega) (by rw [← happ]; exact hmo),
          by rw [happ]; exact hih.2.2.2.2.2.1,
          fun x => by rw [happ]; exact hih.2.2.2.2.2.2 x⟩
    have hAll := hSanFold C.gates [] [] rfl hfan
      (fun _ h => False.elim (List.not_mem_nil h))
      (fun k hk => False.elim (Nat.not_lt_zero k hk))
      (fun _ h => False.elim (List.not_mem_nil h))
      (fun m hm => False.elim (Nat.not_lt_zero m hm))
      (le_refl 0)
      (fun _ => rfl)
    let C' : Circuit := ⟨C.gates.foldl sanStep [], C.output⟩
    refine ⟨C', hAll.2.1, hAll.2.2.1,
      by change (C.gates.foldl sanStep []).length = C.gates.length; simpa only [List.length_nil, Nat.zero_add] using hAll.1, rfl,
      by change notCount ⟨C.gates.foldl sanStep [], 0⟩ ≤ notCount ⟨C.gates, 0⟩; simpa only [List.nil_append] using hAll.2.2.2.2.2.1,
      hAll.2.2.2.1,
      fun m hm hmo => hAll.2.2.2.2.1 m (by change m < 0 + C.gates.length; change m < C.gates.length at hm; omega) (by change (gateAt ⟨[] ++ C.gates, 0⟩ m).op = GateOp.or; rw [List.nil_append]; exact hmo),
      fun x => ?_⟩
    change (C'.gates.foldl stepWire (List.ofFn x)).getD C.output false = (C.gates.foldl stepWire (List.ofFn x)).getD C.output false
    have hw := hAll.2.2.2.2.2.2 x
    rw [List.nil_append] at hw; rw [hw]
  -- Delete gate k given an alias wire p (or out-of-range wire for const false)
  have hEraseWire : ∀ (C : Circuit) (k p : ℕ), k < C.size → FanInTwo C → ReadsBack 10 C →
      (p < 10 + k ∨ 10 + C.size ≤ p) →
      (∀ x : Fin 10 → Bool, (C.wires (List.ofFn x)).getD (10 + k) false = (C.wires (List.ofFn x)).getD p false) →
      ∃ C' : Circuit, FanInTwo C' ∧ C'.size + 1 = C.size ∧ notCount C' ≤ notCount C ∧
        ∀ x : Fin 10 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro C k p hk hfan hrb hp hEq
    change k < C.gates.length at hk
    let repW : ℕ → ℕ := fun w => if w = 10 + k then p else if w < 10 + k then w else w - 1
    let repG : Gate → Gate := fun g => ⟨g.op, g.inputs.map repW⟩
    let C' : Circuit := ⟨(C.gates.eraseIdx k).map repG, repW C.output⟩
    have hC'len : C'.gates.length = C.gates.length - 1 := by
      dsimp only [C']; rw [List.length_map, List.length_eraseIdx_of_lt hk]
    have hWireAgree : ∀ (x : Fin 10 → Bool) (m : ℕ), m ≤ C.gates.length →
        ∀ i < 10 + m, i ≠ 10 + k →
          (C'.wires (List.ofFn x)).getD (repW i) false = (C.wires (List.ofFn x)).getD i false := by
      intro x m
      induction m with
      | zero =>
        intro _ i hi _
        have h10 : i < 10 := hi
        have hr : repW i = i := by dsimp only [repW]; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        rw [hr, wire_ofFn C' x ⟨i, h10⟩, wire_ofFn C x ⟨i, h10⟩]
      | succ m ih =>
        intro hm i hi hine
        by_cases hilt : i < 10 + m
        · exact ih (by omega) i hilt hine
        · have hieq : i = 10 + m := by omega
          subst i
          have hmk : m ≠ k := fun e => hine (by rw [e])
          have hmLt : m < C.gates.length := by omega
          have hStepArg : ∀ w ∈ (gateAt C m).inputs,
              (if repW w < repW (10 + m) then (C'.wires (List.ofFn x)).getD (repW w) false else false) =
              (if w < 10 + m then (C.wires (List.ofFn x)).getD w false else false) := by
            intro w hwin
            have hw : w < 10 + m := hrb m hmLt w hwin
            by_cases hwk : w = 10 + k
            · subst hwk
              have hrw : repW (10 + k) = p := by dsimp only [repW]; rw [ite_eq_left rfl]
              rw [ite_eq_left hw, hrw, hEq x]
              rcases hp with hplt | hpge
              · have hltm : p < repW (10 + m) := by
                  dsimp only [repW]; rw [ite_eq_right (by omega : 10 + m ≠ 10 + k)]
                  by_cases hmk' : 10 + m < 10 + k
                  · omega
                  · rw [ite_eq_right hmk']; omega
                rw [ite_eq_left hltm]
                have hrp : repW p = p := by dsimp only [repW]; rw [ite_eq_right (by omega), ite_eq_left hplt]
                conv_lhs => rw [← hrp]
                exact ih (by omega) p (by omega) (by omega)
              · have hge2 : (C'.wires (List.ofFn x)).length ≤ p := by rw [wires_len]; change 10 + C'.gates.length ≤ p; change 10 + C.gates.length ≤ p at hpge; omega
                have hge3 : (C.wires (List.ofFn x)).length ≤ p := by rw [wires_len]; exact hpge
                rw [getD_ge _ p hge3]
                by_cases hlt : p < repW (10 + m)
                · rw [ite_eq_left hlt, getD_ge _ p hge2]
                · rw [ite_eq_right hlt]
            · have hltm : repW w < repW (10 + m) := by
                dsimp only [repW]; rw [ite_eq_right hwk, ite_eq_right (by omega : 10 + m ≠ 10 + k)]
                by_cases hw1 : w < 10 + k <;> by_cases hm1 : 10 + m < 10 + k
                · rw [ite_eq_left hw1, ite_eq_left hm1]; exact hw
                · rw [ite_eq_left hw1, ite_eq_right hm1]; omega
                · omega
                · rw [ite_eq_right hw1, ite_eq_right hm1]; omega
              rw [ite_eq_left hw, ite_eq_left hltm]
              exact ih (by omega) w hw hwk
          by_cases hmk' : m < k
          · have hrm : repW (10 + m) = 10 + m := by dsimp only [repW]; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
            have hm' : m < C'.size := by change m < C'.gates.length; rw [hC'len]; omega
            rw [hrm, wire_gate C' x m hm', wire_gate C x m hmLt]
            have hgate : gateAt C' m = repG (gateAt C m) := by
              rw [gateAt_eq hm', gateAt_eq hmLt]
              change ((C.gates.eraseIdx k).map repG)[m]'(by rw [List.length_map, List.length_eraseIdx_of_lt hk]; omega) = repG (C.gates[m]'hmLt)
              rw [List.getElem_map]; congr 1; exact List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx_of_lt hk]; omega) hmk'
            rw [hgate]; dsimp only [repG]; rw [List.map_map]
            congr 1; apply List.map_congr_left; intro w hw; change _ = _; conv_lhs => rw [← hrm]; exact hStepArg w hw
          · have hgt : k < m := by omega
            have hrm : repW (10 + m) = 10 + (m - 1) := by dsimp only [repW]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
            have hm' : m - 1 < C'.size := by change m - 1 < C'.gates.length; rw [hC'len]; omega
            rw [hrm, wire_gate C' x (m - 1) hm', wire_gate C x m hmLt]
            have hgate : gateAt C' (m - 1) = repG (gateAt C m) := by
              rw [gateAt_eq hm', gateAt_eq hmLt]
              change ((C.gates.eraseIdx k).map repG)[m - 1]'(by rw [List.length_map, List.length_eraseIdx_of_lt hk]; omega) = repG (C.gates[m]'hmLt)
              rw [List.getElem_map]; congr 1; rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx_of_lt hk]; omega) (by omega : k ≤ m - 1)]
              have : m - 1 + 1 = m := by omega
              simp only [this]
            rw [hgate]; dsimp only [repG]; rw [List.map_map]
            congr 1; apply List.map_congr_left; intro w hw; change _ = _; conv_lhs => rw [← hrm]; exact hStepArg w hw
    refine ⟨C', fun g hg => ?_, by change C'.gates.length + 1 = C.gates.length; rw [hC'len]; omega, ?_, fun x => ?_⟩
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
      have hf := hfan h (List.mem_of_mem_eraseIdx hh)
      exact ⟨hf.1, by dsimp only [repG]; rw [List.length_map]; exact hf.2⟩
    · have h1 : notCount C' = notCount ⟨C.gates.eraseIdx k, 0⟩ := notCount_map_same_op _ repG (fun _ _ => rfl)
      rw [h1]; exact notCount_eraseIdx_le C.gates k
    · change (C'.wires (List.ofFn x)).getD (repW C.output) false = (C.wires (List.ofFn x)).getD C.output false
      by_cases ho : C.output < 10 + C.gates.length
      · by_cases hok : C.output = 10 + k
        · rw [hok, hEq x]
          have hr : repW (10 + k) = p := by dsimp only [repW]; rw [ite_eq_left rfl]
          rw [hr]
          rcases hp with hplt | hpge
          · have hrp : repW p = p := by dsimp only [repW]; rw [ite_eq_right (by omega), ite_eq_left hplt]
            conv_lhs => rw [← hrp]
            exact hWireAgree x C.gates.length (le_refl _) p (by omega) (by omega)
          · rw [getD_ge _ p (by rw [wires_len]; change 10 + C'.gates.length ≤ p; change 10 + C.gates.length ≤ p at hpge; omega),
                getD_ge _ p (by rw [wires_len]; exact hpge)]
        · exact hWireAgree x C.gates.length (le_refl _) C.output ho hok
      · have hro : 10 + C'.gates.length ≤ repW C.output := by
          dsimp only [repW]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
        rw [getD_ge _ _ (by rw [wires_len]; exact hro),
            getD_ge _ _ (by rw [wires_len]; change 10 + C.gates.length ≤ C.output; omega)]
  -- Delete a constant-true gate k (under ReadsBack 10 C + NOT arity 1)
  have hEraseTrue : ∀ (C : Circuit) (k : ℕ), k < C.size → FanInTwo C → ReadsBack 10 C →
      (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length = 1) →
      C.output ≠ 10 + k →
      (∀ x : Fin 10 → Bool, (C.wires (List.ofFn x)).getD (10 + k) false = true) →
      ∃ C' : Circuit, FanInTwo C' ∧ C'.size + 1 = C.size ∧ notCount C' ≤ notCount C ∧
        ∀ x : Fin 10 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro C k hk hfan hrb hnot1 houtNe hTrue
    change k < C.gates.length at hk
    let shiftDown : ℕ → ℕ := fun w => if w < 10 + k then w else w - 1
    let foldTrue : Gate → Gate := fun g =>
      if g.op = GateOp.not then
        if (10 + k) ∈ g.inputs then ⟨GateOp.or, []⟩
        else ⟨GateOp.not, g.inputs.map shiftDown⟩
      else if g.op = GateOp.or then
        if (10 + k) ∈ g.inputs then ⟨GateOp.and, []⟩
        else ⟨GateOp.or, g.inputs.map shiftDown⟩
      else
        ⟨GateOp.and, (g.inputs.filter (fun w => decide (w ≠ 10 + k))).map shiftDown⟩
    let C' : Circuit := ⟨(C.gates.eraseIdx k).map foldTrue, shiftDown C.output⟩
    have hC'len : C'.gates.length = C.gates.length - 1 := by
      dsimp only [C']; rw [List.length_map, List.length_eraseIdx_of_lt hk]
    have hWireAgree : ∀ (x : Fin 10 → Bool) (m : ℕ), m ≤ C.gates.length →
        ∀ i < 10 + m, i ≠ 10 + k →
          (C'.wires (List.ofFn x)).getD (shiftDown i) false = (C.wires (List.ofFn x)).getD i false := by
      intro x m
      induction m with
      | zero =>
        intro _ i hi _
        have hr : shiftDown i = i := by dsimp only [shiftDown]; rw [ite_eq_left (by omega)]
        rw [hr, wire_ofFn C' x ⟨i, hi⟩, wire_ofFn C x ⟨i, hi⟩]
      | succ m ih =>
        intro hm i hi hine
        by_cases hilt : i < 10 + m
        · exact ih (by omega) i hilt hine
        · have hieq : i = 10 + m := by omega
          subst i
          have hmk : m ≠ k := fun e => hine (by rw [e])
          have hmLt : m < C.gates.length := by omega
          let g := gateAt C m
          have hgMem : g ∈ C.gates := by dsimp only [g]; rw [gateAt_eq hmLt]; exact List.getElem_mem hmLt
          have hgf := hfan g hgMem
          have hArg : ∀ w : ℕ, w ≠ 10 + k →
              (if shiftDown w < shiftDown (10 + m) then (C'.wires (List.ofFn x)).getD (shiftDown w) false else false) =
              (if w < 10 + m then (C.wires (List.ofFn x)).getD w false else false) := by
            intro w hwk
            by_cases hw : w < 10 + m
            · have hlt : shiftDown w < shiftDown (10 + m) := by
                dsimp only [shiftDown]
                by_cases h1 : w < 10 + k <;> by_cases h2 : 10 + m < 10 + k
                · rw [ite_eq_left h1, ite_eq_left h2]; exact hw
                · rw [ite_eq_left h1, ite_eq_right h2]; omega
                · omega
                · rw [ite_eq_right h1, ite_eq_right h2]; omega
              rw [ite_eq_left hw, ite_eq_left hlt]; exact ih (by omega) w hw hwk
            · have hge : ¬ shiftDown w < shiftDown (10 + m) := by
                dsimp only [shiftDown]
                by_cases h1 : w < 10 + k <;> by_cases h2 : 10 + m < 10 + k
                · rw [ite_eq_left h1, ite_eq_left h2]; omega
                · omega
                · rw [ite_eq_right h1, ite_eq_left h2]; omega
                · rw [ite_eq_right h1, ite_eq_right h2]; omega
              rw [ite_eq_right hw, ite_eq_right hge]
          have hEvalEq :
              (foldTrue g).op.eval ((foldTrue g).inputs.map fun w =>
                if w < shiftDown (10 + m) then (C'.wires (List.ofFn x)).getD w false else false) =
              g.op.eval (g.inputs.map fun w =>
                if w < 10 + m then (C.wires (List.ofFn x)).getD w false else false) := by
            dsimp only [foldTrue]
            by_cases hnot : g.op = GateOp.not
            · rw [ite_eq_left hnot]
              by_cases hmem : (10 + k) ∈ g.inputs
              · rw [ite_eq_left hmem]
                have hgl1 := hnot1 g hgMem hnot
                have hgins : g.inputs = [10 + k] := by
                  cases hl : g.inputs with
                  | nil => rw [hl] at hmem; exact False.elim (List.not_mem_nil hmem)
                  | cons a t =>
                    cases t with
                    | nil => rw [hl] at hmem; rw [List.mem_singleton.mp hmem]
                    | cons _ _ => rw [hl] at hgl1; simp only [List.length_cons] at hgl1; omega
                have hkm : 10 + k < 10 + m := hrb m hmLt (10 + k) hmem
                rw [hnot, hgins]; simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.headD_cons, ite_eq_left hkm, hTrue x]; rfl
              · rw [ite_eq_right hmem, hnot, List.map_map]
                congr 1; apply List.map_congr_left; intro w hw; exact hArg w (fun e => hmem (e ▸ hw))
            · rw [ite_eq_right hnot]
              by_cases hor : g.op = GateOp.or
              · rw [ite_eq_left hor]
                by_cases hmem : (10 + k) ∈ g.inputs
                · rw [ite_eq_left hmem]
                  have hkm : 10 + k < 10 + m := hrb m hmLt (10 + k) hmem
                  rw [hor]; change true = (g.inputs.map fun w => if w < 10 + m then (C.wires (List.ofFn x)).getD w false else false).any id
                  symm; rw [List.any_eq_true]
                  exact ⟨true, List.mem_map.mpr ⟨10 + k, hmem, by rw [ite_eq_left hkm, hTrue x]⟩, rfl⟩
                · rw [ite_eq_right hmem, hor, List.map_map]
                  congr 1; apply List.map_congr_left; intro w hw; exact hArg w (fun e => hmem (e ▸ hw))
              · rw [ite_eq_right hor]
                have hand : g.op = GateOp.and := by
                  rcases hgf.1 with h1 | h2 | h3
                  · exact h1
                  · exact False.elim (hor h2)
                  · exact False.elim (hnot h3)
                rw [hand, List.map_map, hEvalAnd, hEvalAnd]
                apply Bool.eq_iff_iff.mpr
                rw [List.all_eq_true, List.all_eq_true]
                constructor
                · intro hAll b hb
                  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hb
                  by_cases hwk : w = 10 + k
                  · subst hwk; rw [id_eq, ite_eq_left (hrb m hmLt _ hw), hTrue x]
                  · have hmemF : w ∈ g.inputs.filter (fun u => decide (u ≠ 10 + k)) :=
                      List.mem_filter.mpr ⟨hw, decide_eq_true hwk⟩
                    have h1 := hAll _ (List.mem_map.mpr ⟨w, hmemF, rfl⟩)
                    change (if shiftDown w < shiftDown (10 + m) then (C'.wires (List.ofFn x)).getD (shiftDown w) false else false) = true at h1
                    rw [hArg w hwk] at h1; exact h1
                · intro hAll b hb
                  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hb
                  obtain ⟨hwIn, hwkD⟩ := List.mem_filter.mp hw
                  have hwk : w ≠ 10 + k := of_decide_eq_true hwkD
                  have h1 := hAll _ (List.mem_map.mpr ⟨w, hwIn, rfl⟩)
                  change (if shiftDown w < shiftDown (10 + m) then (C'.wires (List.ofFn x)).getD (shiftDown w) false else false) = true
                  rw [hArg w hwk]; exact h1
          by_cases hmk' : m < k
          · have hrm : shiftDown (10 + m) = 10 + m := by dsimp only [shiftDown]; rw [ite_eq_left (by omega)]
            have hm' : m < C'.size := by change m < C'.gates.length; rw [hC'len]; omega
            rw [hrm, wire_gate C' x m hm', wire_gate C x m hmLt]
            have hgate : gateAt C' m = foldTrue g := by
              rw [gateAt_eq hm']; dsimp only [g]; rw [gateAt_eq hmLt]
              change ((C.gates.eraseIdx k).map foldTrue)[m]'(by rw [List.length_map, List.length_eraseIdx_of_lt hk]; omega) = foldTrue (C.gates[m]'hmLt)
              rw [List.getElem_map]; congr 1; exact List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx_of_lt hk]; omega) hmk'
            rw [hgate]; conv_lhs => rw [← hrm]; exact hEvalEq
          · have hgt : k < m := by omega
            have hrm : shiftDown (10 + m) = 10 + (m - 1) := by dsimp only [shiftDown]; rw [ite_eq_right (by omega)]; omega
            have hm' : m - 1 < C'.size := by change m - 1 < C'.gates.length; rw [hC'len]; omega
            rw [hrm, wire_gate C' x (m - 1) hm', wire_gate C x m hmLt]
            have hgate : gateAt C' (m - 1) = foldTrue g := by
              rw [gateAt_eq hm']; dsimp only [g]; rw [gateAt_eq hmLt]
              change ((C.gates.eraseIdx k).map foldTrue)[m - 1]'(by rw [List.length_map, List.length_eraseIdx_of_lt hk]; omega) = foldTrue (C.gates[m]'hmLt)
              rw [List.getElem_map]; congr 1; rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx_of_lt hk]; omega) (by omega : k ≤ m - 1)]
              have : m - 1 + 1 = m := by omega
              simp only [this]
            rw [hgate]; conv_lhs => rw [← hrm]; exact hEvalEq
    refine ⟨C', fun g hg => ?_, by change C'.gates.length + 1 = C.gates.length; rw [hC'len]; omega, ?_, fun x => ?_⟩
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
      have hf := hfan h (List.mem_of_mem_eraseIdx hh)
      dsimp only [foldTrue]
      by_cases h1 : h.op = GateOp.not
      · rw [ite_eq_left h1]
        by_cases h2 : (10 + k) ∈ h.inputs
        · rw [ite_eq_left h2]; exact ⟨Or.inr (Or.inl rfl), by simp⟩
        · rw [ite_eq_right h2]; exact ⟨Or.inr (Or.inr rfl), by rw [List.length_map]; exact hf.2⟩
      · rw [ite_eq_right h1]
        by_cases h2 : h.op = GateOp.or
        · rw [ite_eq_left h2]
          by_cases h3 : (10 + k) ∈ h.inputs
          · rw [ite_eq_left h3]; exact ⟨Or.inl rfl, by simp⟩
          · rw [ite_eq_right h3]; exact ⟨Or.inr (Or.inl rfl), by rw [List.length_map]; exact hf.2⟩
        · rw [ite_eq_right h2]; exact ⟨Or.inl rfl, by rw [List.length_map]; exact le_trans (List.length_filter_le _ _) hf.2⟩
    · have h1 : notCount C' ≤ notCount ⟨C.gates.eraseIdx k, 0⟩ :=
        notCount_map_le _ foldTrue (fun h _ hfn => by
          dsimp only [foldTrue] at hfn
          by_cases h1 : h.op = GateOp.not
          · exact h1
          · rw [ite_eq_right h1] at hfn
            by_cases h2 : h.op = GateOp.or
            · rw [ite_eq_left h2] at hfn
              by_cases h3 : (10 + k) ∈ h.inputs
              · rw [ite_eq_left h3] at hfn; exact False.elim (GateOp.noConfusion hfn)
              · rw [ite_eq_right h3] at hfn; exact False.elim (GateOp.noConfusion hfn)
            · rw [ite_eq_right h2] at hfn; exact False.elim (GateOp.noConfusion hfn))
      exact le_trans h1 (notCount_eraseIdx_le C.gates k)
    · change (C'.wires (List.ofFn x)).getD (shiftDown C.output) false = (C.wires (List.ofFn x)).getD C.output false
      by_cases ho : C.output < 10 + C.gates.length
      · exact hWireAgree x C.gates.length (le_refl _) C.output ho houtNe
      · have hro : 10 + C'.gates.length ≤ shiftDown C.output := by
          dsimp only [shiftDown]; rw [ite_eq_right (by omega)]; omega
        rw [getD_ge _ _ (by rw [wires_len]; exact hro),
            getD_ge _ _ (by rw [wires_len]; change 10 + C.gates.length ≤ C.output; omega)]
  -- Delete a dead gate k (not in InOutCone of C.output)
  have hEraseDead : ∀ (C : Circuit) (k : ℕ), k < C.size → FanInTwo C → ReadsBack 10 C →
      ¬ InOutCone 10 C (10 + k) C.output →
      ∃ C' : Circuit, FanInTwo C' ∧ C'.size + 1 = C.size ∧ notCount C' ≤ notCount C ∧
        ∀ x : Fin 10 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro C k hk hfan hrb hDead
    change k < C.gates.length at hk
    let dropW : ℕ → ℕ := fun w => if w = 10 + k then 0 else if w < 10 + k then w else w - 1
    let dropG : Gate → Gate := fun g => ⟨g.op, g.inputs.map dropW⟩
    let C' : Circuit := ⟨(C.gates.eraseIdx k).map dropG, dropW C.output⟩
    have hC'len : C'.gates.length = C.gates.length - 1 := by
      dsimp only [C']; rw [List.length_map, List.length_eraseIdx_of_lt hk]
    have hWireAgree : ∀ (x : Fin 10 → Bool) (m : ℕ), m ≤ C.gates.length →
        ∀ i < 10 + m, ¬ InOutCone 10 C (10 + k) i →
          (C'.wires (List.ofFn x)).getD (dropW i) false = (C.wires (List.ofFn x)).getD i false := by
      intro x m
      induction m with
      | zero =>
        intro _ i hi _
        have hr : dropW i = i := by dsimp only [dropW]; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        rw [hr, wire_ofFn C' x ⟨i, hi⟩, wire_ofFn C x ⟨i, hi⟩]
      | succ m ih =>
        intro hm i hi hnotC
        by_cases hilt : i < 10 + m
        · exact ih (by omega) i hilt hnotC
        · have hieq : i = 10 + m := by omega
          subst i
          have hmk : m ≠ k := fun e => hnotC (Or.inl (by rw [e]))
          have hmLt : m < C.gates.length := by omega
          have hArg : ∀ w ∈ (gateAt C m).inputs,
              (if dropW w < dropW (10 + m) then (C'.wires (List.ofFn x)).getD (dropW w) false else false) =
              (if w < 10 + m then (C.wires (List.ofFn x)).getD w false else false) := by
            intro w hw
            have hwlt : w < 10 + m := hrb m hmLt w hw
            have hwNotC : ¬ InOutCone 10 C (10 + k) w := by
              intro hwc
              apply hnotC
              right; refine ⟨by omega, by omega, ?_⟩
              have hsub1 : 10 + k - 10 = k := by omega
              have hsub2 : 10 + m - 10 = m := by omega
              rw [hsub1, hsub2]
              rcases hwc with rfl | ⟨_, hw10, hcone⟩
              · exact (inCone_iff C k m).mpr ⟨hmLt, k, by omega, hw, Or.inl rfl⟩
              · have hwEq : 10 + (w - 10) = w := by omega
                exact (inCone_iff C k m).mpr ⟨hmLt, w - 10, by omega, hwEq.symm ▸ hw, Or.inr (by rw [hsub1] at hcone; exact hcone)⟩
            have hwk : w ≠ 10 + k := fun e => hwNotC (Or.inl e.symm)
            have hlt : dropW w < dropW (10 + m) := by
              dsimp only [dropW]; rw [ite_eq_right hwk, ite_eq_right (by omega : 10 + m ≠ 10 + k)]
              by_cases h1 : w < 10 + k <;> by_cases h2 : 10 + m < 10 + k
              · rw [ite_eq_left h1, ite_eq_left h2]; exact hwlt
              · rw [ite_eq_left h1, ite_eq_right h2]; omega
              · omega
              · rw [ite_eq_right h1, ite_eq_right h2]; omega
            rw [ite_eq_left hwlt, ite_eq_left hlt]
            exact ih (by omega) w hwlt hwNotC
          by_cases hmk' : m < k
          · have hrm : dropW (10 + m) = 10 + m := by dsimp only [dropW]; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
            have hm' : m < C'.size := by change m < C'.gates.length; rw [hC'len]; omega
            rw [hrm, wire_gate C' x m hm', wire_gate C x m hmLt]
            have hgate : gateAt C' m = dropG (gateAt C m) := by
              rw [gateAt_eq hm', gateAt_eq hmLt]
              change ((C.gates.eraseIdx k).map dropG)[m]'(by rw [List.length_map, List.length_eraseIdx_of_lt hk]; omega) = dropG (C.gates[m]'hmLt)
              rw [List.getElem_map]; congr 1; exact List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx_of_lt hk]; omega) hmk'
            rw [hgate]; dsimp only [dropG]; rw [List.map_map]
            congr 1; apply List.map_congr_left; intro w hw; change _ = _; conv_lhs => rw [← hrm]; exact hArg w hw
          · have hgt : k < m := by omega
            have hrm : dropW (10 + m) = 10 + (m - 1) := by dsimp only [dropW]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
            have hm' : m - 1 < C'.size := by change m - 1 < C'.gates.length; rw [hC'len]; omega
            rw [hrm, wire_gate C' x (m - 1) hm', wire_gate C x m hmLt]
            have hgate : gateAt C' (m - 1) = dropG (gateAt C m) := by
              rw [gateAt_eq hm', gateAt_eq hmLt]
              change ((C.gates.eraseIdx k).map dropG)[m - 1]'(by rw [List.length_map, List.length_eraseIdx_of_lt hk]; omega) = dropG (C.gates[m]'hmLt)
              rw [List.getElem_map]; congr 1; rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx_of_lt hk]; omega) (by omega : k ≤ m - 1)]
              have : m - 1 + 1 = m := by omega
              simp only [this]
            rw [hgate]; dsimp only [dropG]; rw [List.map_map]
            congr 1; apply List.map_congr_left; intro w hw; change _ = _; conv_lhs => rw [← hrm]; exact hArg w hw
    refine ⟨C', fun g hg => ?_, by change C'.gates.length + 1 = C.gates.length; rw [hC'len]; omega, ?_, fun x => ?_⟩
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
      have hf := hfan h (List.mem_of_mem_eraseIdx hh)
      exact ⟨hf.1, by dsimp only [dropG]; rw [List.length_map]; exact hf.2⟩
    · have h1 : notCount C' = notCount ⟨C.gates.eraseIdx k, 0⟩ := notCount_map_same_op _ dropG (fun _ _ => rfl)
      rw [h1]; exact notCount_eraseIdx_le C.gates k
    · change (C'.wires (List.ofFn x)).getD (dropW C.output) false = (C.wires (List.ofFn x)).getD C.output false
      by_cases ho : C.output < 10 + C.gates.length
      · exact hWireAgree x C.gates.length (le_refl _) C.output ho hDead
      · have hro : 10 + C'.gates.length ≤ dropW C.output := by
          dsimp only [dropW]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
        rw [getD_ge _ _ (by rw [wires_len]; exact hro),
            getD_ge _ _ (by rw [wires_len]; change 10 + C.gates.length ≤ C.output; omega)]
  -- Swap the two inputs of a binary gate at index k (in-place, preserving every semantic & structural invariant)
  have hSwapBinAt : ∀ (C : Circuit) (k a b : ℕ) (op : GateOp),
      k < C.size → (op = GateOp.and ∨ op = GateOp.or) → C.gates[k]? = some ⟨op, [a, b]⟩ →
      let C' : Circuit := ⟨C.gates.set k ⟨op, [b, a]⟩, C.output⟩
      C'.size = C.size ∧ notCount C' = notCount C ∧
      C'.gates[k]? = some ⟨op, [b, a]⟩ ∧
      (∀ m, m ≠ k → C'.gates[m]? = C.gates[m]?) ∧
      (∀ x : Fin 10 → Bool, ∀ i < 10 + C.size,
        (C'.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD i false) ∧
      (∀ i j : ℕ, InCone 10 C' i j ↔ InCone 10 C i j) := by
    intro C k a b op hk hop hgk
    let C' : Circuit := ⟨C.gates.set k ⟨op, [b, a]⟩, C.output⟩
    have hLen : C'.gates.length = C.gates.length := List.length_set
    have hAtK : C'.gates[k]? = some ⟨op, [b, a]⟩ := by dsimp only [C']; rw [List.getElem?_set_self hk]
    have hAtNe : ∀ m, m ≠ k → C'.gates[m]? = C.gates[m]? := fun m hm => by dsimp only [C']; rw [List.getElem?_set_ne hm.symm]
    have hGateAtK : gateAt C k = ⟨op, [a, b]⟩ := by
      rw [gateAt_eq hk]; have := List.getElem?_eq_getElem hk; rw [this] at hgk; exact Option.some.inj hgk
    have hGateAtK' : gateAt C' k = ⟨op, [b, a]⟩ := by
      rw [gateAt_eq (by rw [hLen]; exact hk)]; have := List.getElem?_eq_getElem (by rw [hLen]; exact hk : k < C'.gates.length); rw [this] at hAtK; exact Option.some.inj hAtK
    have hGateAtNe : ∀ m < C.size, m ≠ k → gateAt C' m = gateAt C m := fun m hm hne => by
      rw [gateAt_eq (by rw [hLen]; exact hm), gateAt_eq hm]
      have h1 := hAtNe m hne
      rw [List.getElem?_eq_getElem (by rw [hLen]; exact hm), List.getElem?_eq_getElem hm] at h1
      exact Option.some.inj h1
    have hNotEq : ∀ (gs : List Gate) (idx : ℕ) (gnew : Gate) (hidx : idx < gs.length),
        (gs[idx]'hidx).op = gnew.op →
        notCount ⟨gs.set idx gnew, 0⟩ = notCount ⟨gs, 0⟩ := by
      intro gs
      induction gs with
      | nil => intro idx _ h; exact False.elim (Nat.not_lt_zero idx h)
      | cons g gs ih =>
        intro idx gnew hidx hopEq
        cases idx with
        | zero =>
          simp only [List.set_cons_zero, notCount_cons]
          simp only [List.getElem_cons_zero] at hopEq; rw [hopEq]
        | succ idx' =>
          simp only [List.set_cons_succ, notCount_cons]
          simp only [List.getElem_cons_succ] at hopEq
          rw [ih idx' gnew (by simp only [List.length_cons] at hidx; omega) hopEq]
    have hNc : notCount C' = notCount C := by
      have hopEq : (C.gates[k]).op = op := by rw [← gateAt_eq hk, hGateAtK]
      exact hNotEq C.gates k ⟨op, [b, a]⟩ hk hopEq
    have hWires : ∀ (x : Fin 10 → Bool) (m : ℕ), m ≤ C.gates.length →
        ∀ i < 10 + m, (C'.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD i false := by
      intro x m
      induction m with
      | zero => intro _ i hi; rw [wire_ofFn C' x ⟨i, hi⟩, wire_ofFn C x ⟨i, hi⟩]
      | succ m ih =>
        intro hm i hi
        by_cases hilt : i < 10 + m
        · exact ih (by omega) i hilt
        · have hieq : i = 10 + m := by omega
          subst i
          have hmLt : m < C.gates.length := by omega
          rw [wire_gate C' x m (by change m < C'.gates.length; rw [hLen]; exact hmLt), wire_gate C x m hmLt]
          by_cases hmk : m = k
          · subst hmk; rw [hGateAtK', hGateAtK]
            have hA : (if a < 10 + m then (C'.wires (List.ofFn x)).getD a false else false) =
                (if a < 10 + m then (C.wires (List.ofFn x)).getD a false else false) := by
              by_cases ha : a < 10 + m
              · rw [ite_eq_left ha, ite_eq_left ha, ih (by omega) a ha]
              · rw [ite_eq_right ha, ite_eq_right ha]
            have hB : (if b < 10 + m then (C'.wires (List.ofFn x)).getD b false else false) =
                (if b < 10 + m then (C.wires (List.ofFn x)).getD b false else false) := by
              by_cases hb : b < 10 + m
              · rw [ite_eq_left hb, ite_eq_left hb, ih (by omega) b hb]
              · rw [ite_eq_right hb, ite_eq_right hb]
            rcases hop with rfl | rfl
            · simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hA, hB]; exact Bool.and_comm _ _
            · simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, hA, hB]; exact Bool.or_comm _ _
          · rw [hGateAtNe m hmLt hmk]
            congr 1; apply List.map_congr_left; intro w _
            by_cases hw : w < 10 + m
            · rw [ite_eq_left hw, ite_eq_left hw, ih (by omega) w hw]
            · rw [ite_eq_right hw, ite_eq_right hw]
    have hCone : ∀ i j : ℕ, InCone 10 C' i j ↔ InCone 10 C i j := by
      intro i j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        rw [inCone_iff, inCone_iff, hLen]
        constructor
        · rintro ⟨hj, t, ht, htin, hc⟩
          refine ⟨hj, t, ht, ?_, hc.imp id (ih t ht).mp⟩
          by_cases hjk : j = k
          · subst hjk; rw [hGateAtK'] at htin; rw [hGateAtK]
            rcases List.mem_cons.mp htin with h1 | h2
            · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr h1)
            · exact List.mem_cons_self |> fun e => (List.mem_singleton.mp h2).symm ▸ e
          · rw [hGateAtNe j hj hjk] at htin; exact htin
        · rintro ⟨hj, t, ht, htin, hc⟩
          refine ⟨hj, t, ht, ?_, hc.imp id (ih t ht).mpr⟩
          by_cases hjk : j = k
          · subst hjk; rw [hGateAtK] at htin; rw [hGateAtK']
            rcases List.mem_cons.mp htin with h1 | h2
            · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr h1)
            · exact List.mem_cons_self |> fun e => (List.mem_singleton.mp h2).symm ▸ e
          · rw [hGateAtNe j hj hjk]; exact htin
    exact ⟨hLen, hNc, hAtK, hAtNe, fun x i hi => hWires x C.gates.length (le_refl _) i hi, hCone⟩
  -- Helper: given a normalized circuit computing Plist, prove the degree bound for all v and S
  have hDegBound : ∀ (C : Circuit),
      FanInTwo C → ReadsBack 10 C → C.output < 10 + C.size →
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Plist x) →
      (∀ k < C.size, ((gateAt C k).op ≠ GateOp.not ∧ (gateAt C k).inputs.length = 2 ∧ (gateAt C k).inputs.Nodup) ∨
        ((gateAt C k).op = GateOp.not ∧ (gateAt C k).inputs.length = 1)) →
      ∀ (v : Fin 10) (S : Finset (Fin C.size)),
        (∀ k ∈ S, (gateAt C k.val).op ≠ GateOp.not ∧
          (v.val ∈ (gateAt C k.val).inputs ∨
           ∃ j < C.size, ((gateAt C j).op = GateOp.not ∧ (gateAt C j).inputs = [v.val]) ∧ 10 + j ∈ (gateAt C k.val).inputs)) →
        S.card + 15 + notCount C ≤ C.size := by
    intro C hfan hrb hout hcomp hArity v S hS
    have hShape : ∀ g ∈ C.gates, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
        ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) := by
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
      have ha := hArity k hk; rw [gateAt_eq hk] at ha
      rcases ha with ⟨hnot, hl, _⟩ | ⟨hnot, hl⟩
      · right; refine ⟨?_, hl⟩
        rcases (hfan _ (List.getElem_mem hk)).1 with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · exact False.elim (hnot h3)
      · exact Or.inl ⟨hnot, hl⟩
    have hMain := rRun_main v C hrb hShape hout hcomp
    have hCard := rRun_elim_card v C S hrb hShape (fun k hk => by
      obtain ⟨hNot, hRd⟩ := hS k hk
      have hgk : C.gates.get k = gateAt C k.val := (gateAt_eq k.isLt).symm
      rw [hgk]
      refine ⟨hNot, ?_⟩
      rcases hRd with hDir | ⟨j, hjLt, ⟨hjOp, hjIns⟩, hjIn⟩
      · refine ⟨v.val, hDir, ?_⟩
        rw [rRun_init_at v C v, ite_eq_left rfl]
      · refine ⟨10 + j, hjIn, ?_⟩
        have hAt := rRun_at_step v C j hjLt
        rw [hAt.2.2]
        have hgj : gateAt C j = ⟨GateOp.not, [v.val]⟩ := by
          cases hg : gateAt C j with
          | mk op ins => rw [hg] at hjOp hjIns; dsimp only at hjOp hjIns; rw [hjOp, hjIns]
        rw [hgj]; dsimp only [rStep]; rw [ite_eq_left rfl, List.getD_cons_zero]
        have hvc : ((rRun v (C.gates.take j)).1.getD v.val (true, false, 0)).1 = true := by
          rw [← hAt.2.1 v.val (by have := v.isLt; omega), rRun_init_at v C v, ite_eq_left rfl]
        rw [ite_eq_left hvc]
        rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some])
    omega
  -- Helper: convert our hNormAll into the compact hNonMono per-gate hypothesis
  have hNormCompact : ∀ (C : Circuit),
      (∀ k < C.size,
        (((gateAt C k).op ≠ GateOp.not ∧ (gateAt C k).inputs.length = 2 ∧ (gateAt C k).inputs.Nodup) ∨
         ((gateAt C k).op = GateOp.not ∧ (gateAt C k).inputs.length = 1)) ∧
        InOutCone 10 C (10 + k) C.output ∧
        (∀ p < 10 + k, ∃ x : Fin 10 → Bool, (C.wires (List.ofFn x)).getD (10 + k) false ≠ (C.wires (List.ofFn x)).getD p false) ∧
        ∀ b : Bool, ∃ x : Fin 10 → Bool, (C.wires (List.ofFn x)).getD (10 + k) false = b) →
      ∀ k < C.size,
        ((gateAt C k).inputs.length = 1 ↔ (gateAt C k).op = GateOp.not) ∧ (gateAt C k).inputs.Nodup ∧
        InOutCone 10 C (10 + k) C.output ∧
        (∀ p < 10 + k, (fun x : Fin 10 → Bool => (C.wires (List.ofFn x)).getD (10 + k) false) ≠
          (fun x : Fin 10 → Bool => (C.wires (List.ofFn x)).getD p false)) ∧
        ∀ b : Bool, (fun x : Fin 10 → Bool => (C.wires (List.ofFn x)).getD (10 + k) false) ≠ fun _ => b := by
    intro C hN k hk
    obtain ⟨hAr, hLv, hNA, hNC⟩ := hN k hk
    refine ⟨?_, ?_, hLv, fun p hp hEq => ?_, fun b hEq => ?_⟩
    · rcases hAr with ⟨hnot, hl, _⟩ | ⟨hnot, hl⟩
      · exact ⟨fun h1 => False.elim (by omega), fun h2 => False.elim (hnot h2)⟩
      · exact ⟨fun _ => hnot, fun _ => hl⟩
    · rcases hAr with ⟨_, _, hnd⟩ | ⟨_, hl⟩
      · exact hnd
      · cases hi : (gateAt C k).inputs with
        | nil => rw [hi] at hl; exact False.elim (Nat.noConfusion hl)
        | cons a t =>
          cases t with
          | nil => exact List.nodup_singleton a
          | cons _ _ => rw [hi] at hl; simp only [List.length_cons] at hl; omega
    · obtain ⟨x, hx⟩ := hNA p hp
      exact hx (congrFun hEq x)
    · obtain ⟨x, hx⟩ := hNC (!b)
      have h1 := congrFun hEq x
      rw [hx] at h1
      cases b <;> exact Bool.noConfusion h1
  -- Helper: apply an S_5 permutation to a normalized circuit and preserve all normalization invariants
  have hRelabelNorm : ∀ (π πi : Fin 5 → Fin 5), (∀ i : Fin 5, πi (π i) = i ∧ π (πi i) = i) →
      ∀ (C : Circuit),
        FanInTwo C → ReadsBack 10 C → 1 ≤ notCount C → notCount C ≤ 2 →
        17 + notCount C ≤ C.size → C.size ≤ 19 → C.output + 1 = 10 + C.size →
        (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Plist x) →
        (∀ k < C.size,
          (((gateAt C k).op ≠ GateOp.not ∧ (gateAt C k).inputs.length = 2 ∧ (gateAt C k).inputs.Nodup) ∨
           ((gateAt C k).op = GateOp.not ∧ (gateAt C k).inputs.length = 1)) ∧
          InOutCone 10 C (10 + k) C.output ∧
          (∀ p < 10 + k, ∃ x : Fin 10 → Bool, (C.wires (List.ofFn x)).getD (10 + k) false ≠ (C.wires (List.ofFn x)).getD p false) ∧
          ∀ b : Bool, ∃ x : Fin 10 → Bool, (C.wires (List.ofFn x)).getD (10 + k) false = b) →
        let C' := relabelC (liftS5 π) C
        FanInTwo C' ∧ ReadsBack 10 C' ∧ C'.size = C.size ∧ notCount C' = notCount C ∧
        C'.output + 1 = 10 + C'.size ∧
        (∀ x : Fin 10 → Bool, C'.eval (List.ofFn x) = Plist x) ∧
        (∀ k < C'.size,
          (((gateAt C' k).op ≠ GateOp.not ∧ (gateAt C' k).inputs.length = 2 ∧ (gateAt C' k).inputs.Nodup) ∨
           ((gateAt C' k).op = GateOp.not ∧ (gateAt C' k).inputs.length = 1)) ∧
          InOutCone 10 C' (10 + k) C'.output ∧
          (∀ p < 10 + k, ∃ x : Fin 10 → Bool, (C'.wires (List.ofFn x)).getD (10 + k) false ≠ (C'.wires (List.ofFn x)).getD p false) ∧
          ∀ b : Bool, ∃ x : Fin 10 → Bool, (C'.wires (List.ofFn x)).getD (10 + k) false = b) := by
    intro π πi hbi C hfan hrb hnc1 hnc2 hsz17 hsz19 hout hcomp hNorm
    let σ := liftS5 π
    let σi := liftS5 πi
    have hLift := hLift_props π πi hbi
    let C' := relabelC σ C
    have hSz' : C'.size = C.size := List.length_map _
    have hNc' : notCount C' = notCount C := notCount_map_same_op C.gates (relabelG σ) (fun _ _ => rfl)
    have hOutGe10 : 10 ≤ C.output := by omega
    have hOutEq : C'.output = C.output := by dsimp only [C', relabelC, relabelW]; rw [dite_eq_right (by omega : ¬ C.output < 10)]
    have hRelW_inv : ∀ w : ℕ, relabelW σ (relabelW σi w) = w ∧ relabelW σi (relabelW σ w) = w := by
      intro w
      by_cases h10 : w < 10
      · dsimp only [relabelW]
        rw [dite_eq_left h10, dite_eq_left (σi ⟨w, h10⟩).isLt, dite_eq_left h10, dite_eq_left (σ ⟨w, h10⟩).isLt]
        exact ⟨congrArg Fin.val (hLift.1 ⟨w, h10⟩).2, congrArg Fin.val (hLift.1 ⟨w, h10⟩).1⟩
      · simp only [relabelW, dite_eq_right h10, and_self]
    have hRelW_inj : Function.Injective (relabelW σ) := fun a b hab => by
      have := congrArg (relabelW σi) hab; rw [(hRelW_inv a).2, (hRelW_inv b).2] at this; exact this
    have hFan' : FanInTwo C' := fun g hg => by
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
      have hf := hfan h hh
      exact ⟨hf.1, by dsimp only [relabelG]; rw [List.length_map]; exact hf.2⟩
    have hRb' : ReadsBack 10 C' := by
      intro k hk w hw
      have hkC : k < C.gates.length := by change k < C.size; rw [← hSz']; exact hk
      rw [gateAt_eq hk] at hw; dsimp only [C', relabelC] at hw; simp only [List.getElem_map] at hw; dsimp only [relabelG] at hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      have huLt : u < 10 + k := hrb k hkC u (by rw [gateAt_eq hkC]; exact hu)
      dsimp only [relabelW]
      by_cases h10 : u < 10
      · rw [dite_eq_left h10]; have := (σ ⟨u, h10⟩).isLt; omega
      · rw [dite_eq_right h10]; exact huLt
    have hComp' : ∀ x : Fin 10 → Bool, C'.eval (List.ofFn x) = Plist x := fun x => by
      change ((relabelC σ C).wires (List.ofFn x)).getD (relabelW σ C.output) false = Plist x
      rw [relabel_eval σ C x]; change C.eval (List.ofFn (x ∘ σ)) = Plist x; rw [hcomp (x ∘ σ), hLift.2.2 x]
    refine ⟨hFan', hRb', hSz', hNc', by rw [hOutEq, hSz']; exact hout, hComp', fun k hk => ?_⟩
    have hkC : k < C.size := by rw [← hSz']; exact hk
    obtain ⟨hAr, hLive, hNoAl, hNoCo⟩ := hNorm k hkC
    have hgEq : gateAt C' k = relabelG σ (gateAt C k) := by
      rw [gateAt_eq hk, gateAt_eq hkC]
      change (C.gates.map (relabelG σ))[k]'(by rw [List.length_map]; exact hkC) = relabelG σ (C.gates[k]'hkC)
      exact List.getElem_map _
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hgEq]; dsimp only [relabelG]
      rcases hAr with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, by rw [List.length_map]; exact h2, h3.map hRelW_inj⟩
      · exact Or.inr ⟨h1, by rw [List.length_map]; exact h2⟩
    · rw [hOutEq]
      rcases hLive with heq | ⟨h1, h2, hcone⟩
      · exact Or.inl heq
      · exact Or.inr ⟨h1, h2, (relabel_inCone σ C _ _).mpr hcone⟩
    · intro p hp
      let q := relabelW σi p
      have hqLt : q < 10 + k := by
        dsimp only [q, relabelW]
        by_cases h10 : p < 10
        · rw [dite_eq_left h10]; have := (σi ⟨p, h10⟩).isLt; omega
        · rw [dite_eq_right h10]; exact hp
      obtain ⟨x, hxne⟩ := hNoAl q hqLt
      refine ⟨x ∘ σi, ?_⟩
      have hCompId : (x ∘ σi) ∘ σ = x := funext (fun v => by change x (liftS5 πi (liftS5 π v)) = x v; rw [(hLift.1 v).1])
      have h1 := relabel_wire_any σ C (x ∘ σi) (10 + k) (by omega)
      have hrk : relabelW σ (10 + k) = 10 + k := by dsimp only [relabelW]; rw [dite_eq_right (by omega : ¬ 10 + k < 10)]
      rw [hrk, hCompId] at h1
      have h2 := relabel_wire_any σ C (x ∘ σi) q (by omega)
      rw [(hRelW_inv p).1, hCompId] at h2
      rw [h1, h2]; exact hxne
    · intro b
      obtain ⟨x, hxb⟩ := hNoCo b
      refine ⟨x ∘ σi, ?_⟩
      have hCompId : (x ∘ σi) ∘ σ = x := funext (fun v => by change x (liftS5 πi (liftS5 π v)) = x v; rw [(hLift.1 v).1])
      have h1 := relabel_wire_any σ C (x ∘ σi) (10 + k) (by omega)
      have hrk : relabelW σ (10 + k) = 10 + k := by dsimp only [relabelW]; rw [dite_eq_right (by omega : ¬ 10 + k < 10)]
      rw [hrk, hCompId] at h1
      rw [h1]; exact hxb
  -- Strong induction normalizing any circuit C of size s ≤ 19 computing Plist (with top OR if s = 19)
  have hNormalize : ∀ (s : ℕ), s ≤ 19 → ∀ (C : Circuit), C.size = s → FanInTwo C →
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Plist x) →
      (s = 19 → (gateAt C 18).op = GateOp.or) → False := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro hs19 C hSz hFan hComp hTop19
      obtain ⟨C1, hFan1, hRb1, hSz1, hOut1, _, hNot1, hOr1, hEv1⟩ := hSanitizeRB C hFan
      have hSz1s : C1.size = s := hSz1.trans hSz
      have hComp1 : ∀ x : Fin 10 → Bool, C1.eval (List.ofFn x) = Plist x := fun x => (hEv1 x).trans (hComp x)
      have hTop1 : s = 19 → (gateAt C1 18).op = GateOp.or := fun h19 =>
        hOr1 18 (by omega) (hTop19 h19)
      -- Case 0: notCount C1 = 0 -> contradicted by hMono (L-meta-18083)
      by_cases hNc0 : notCount C1 = 0
      · have hMono2 : Monotone2 C1 := by
          intro g hg
          have hneNot : g.op ≠ GateOp.not := by
            intro hgn
            have hmem : g ∈ C1.gates.filter (fun h => decide (h.op = GateOp.not)) :=
              List.mem_filter.mpr ⟨hg, decide_eq_true hgn⟩
            have hnil : C1.gates.filter (fun h => decide (h.op = GateOp.not)) = [] :=
              List.length_eq_zero_iff.mp hNc0
            rw [hnil] at hmem; exact List.not_mem_nil hmem
          have hgf := hFan1 g hg
          refine ⟨?_, hgf.2⟩
          rcases hgf.1 with h1 | h2 | h3
          · exact Or.inl h1
          · exact Or.inr h2
          · exact False.elim (hneNot h3)
        obtain ⟨x, hx⟩ := hMono C1 hMono2 (by omega)
        exact hx (hComp1 x)
      -- 1 ≤ notCount C1; apply hBound17 -> 17 + notCount C1 ≤ s ≤ 19 -> notCount C1 ≤ 2
      have hNc1 : 1 ≤ notCount C1 := by omega
      have hB17 := hBound17 C1 hFan1 (fun x => (hComp1 x).trans (hF_eq_P x).symm)
      have hNc2 : notCount C1 ≤ 2 := by omega
      -- Output must be a valid gate index (10 ≤ C1.output < 10 + s)
      have hP0 : Plist (fun _ => false) = false := by
        apply Bool.eq_false_iff.mpr; intro ht
        obtain ⟨a, b, _, ha, _⟩ := (hP_iff_adj (fun _ => false)).mp ht; exact Bool.noConfusion ha
      have hOutLt : C1.output < 10 + s := by
        by_contra hge
        obtain ⟨a, b, _, _, hab⟩ := hAvoidEdge 0
        let x1 : Fin 10 → Bool := fun v => decide (v = a ∨ v = b)
        have h1 : Plist x1 = true := (hP_iff_adj x1).mpr ⟨a, b, hab, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
        have h2 : C1.eval (List.ofFn x1) = false := getD_ge _ _ (by rw [wires_len]; omega)
        rw [hComp1 x1, h1] at h2; exact Bool.noConfusion h2
      have hOutGe10 : 10 ≤ C1.output := by
        by_contra hlt
        let v : Fin 10 := ⟨C1.output, by omega⟩
        let xv : Fin 10 → Bool := fun u => decide (u = v)
        have h1 : C1.eval (List.ofFn xv) = true := by
          change (C1.wires (List.ofFn xv)).getD v.val false = true
          rw [wire_ofFn C1 xv v]; exact decide_eq_true rfl
        have h2 : Plist xv = false := by
          apply Bool.eq_false_iff.mpr; intro ht
          obtain ⟨a, b, hab, ha, hb⟩ := (hP_iff_adj xv).mp ht
          have hav : a = v := of_decide_eq_true ha
          have hbv : b = v := of_decide_eq_true hb
          rw [hav, hbv, hAdj_irrefl v] at hab; exact Bool.noConfusion hab
        rw [hComp1 xv, h2] at h1; exact Bool.noConfusion h1
      -- Reduction 1: dead gate -> shrink size
      by_cases hHasDead : ∃ k < s, ¬ InOutCone 10 C1 (10 + k) C1.output
      · obtain ⟨k, hk, hDead⟩ := hHasDead
        obtain ⟨C2, hFan2, hSz2, _, hEv2⟩ := hEraseDead C1 k (by omega) hFan1 hRb1 hDead
        exact ih C2.size (by omega) (by omega) C2 rfl hFan2 (fun x => (hEv2 x).trans (hComp1 x)) (fun h19 => by omega)
      -- Reduction 2: constant gate -> shrink size
      by_cases hHasConst : ∃ k < s, ∃ b : Bool, ∀ x : Fin 10 → Bool, (C1.wires (List.ofFn x)).getD (10 + k) false = b
      · obtain ⟨k, hk, b, hConst⟩ := hHasConst
        cases b with
        | false =>
          have hEq : ∀ x : Fin 10 → Bool, (C1.wires (List.ofFn x)).getD (10 + k) false = (C1.wires (List.ofFn x)).getD (10 + C1.size) false := by
            intro x; rw [hConst x, getD_ge _ _ (by rw [wires_len])]
          obtain ⟨C2, hFan2, hSz2, _, hEv2⟩ := hEraseWire C1 k (10 + C1.size) (by omega) hFan1 hRb1 (Or.inr (le_refl _)) hEq
          exact ih C2.size (by omega) (by omega) C2 rfl hFan2 (fun x => (hEv2 x).trans (hComp1 x)) (fun h19 => by omega)
        | true =>
          have houtNe : C1.output ≠ 10 + k := by
            intro heq
            have h0 := hConst (fun _ => false)
            rw [← heq] at h0
            change C1.eval (List.ofFn (fun _ => false)) = true at h0
            rw [hComp1, hP0] at h0; exact Bool.noConfusion h0
          obtain ⟨C2, hFan2, hSz2, _, hEv2⟩ := hEraseTrue C1 k (by omega) hFan1 hRb1 hNot1 houtNe hConst
          exact ih C2.size (by omega) (by omega) C2 rfl hFan2 (fun x => (hEv2 x).trans (hComp1 x)) (fun h19 => by omega)
      -- Reduction 3: alias gate -> shrink size
      by_cases hHasAlias : ∃ k < s, ∃ p < 10 + k, ∀ x : Fin 10 → Bool,
          (C1.wires (List.ofFn x)).getD (10 + k) false = (C1.wires (List.ofFn x)).getD p false
      · obtain ⟨k, hk, p, hp, hAl⟩ := hHasAlias
        obtain ⟨C2, hFan2, hSz2, _, hEv2⟩ := hEraseWire C1 k p (by omega) hFan1 hRb1 (Or.inl hp) hAl
        exact ih C2.size (by omega) (by omega) C2 rfl hFan2 (fun x => (hEv2 x).trans (hComp1 x)) (fun h19 => by omega)
      -- Now C1 is FULLY NORMALIZED!
      have hLive : ∀ k < C1.size, InOutCone 10 C1 (10 + k) C1.output := fun k hk => by
        by_contra hnc; exact hHasDead ⟨k, by omega, hnc⟩
      have hNoConst : ∀ k < C1.size, ∀ b : Bool, ∃ x : Fin 10 → Bool, (C1.wires (List.ofFn x)).getD (10 + k) false = b := by
        intro k hk b; by_contra hno
        exact hHasConst ⟨k, by omega, !b, fun x => by
          cases hv : (C1.wires (List.ofFn x)).getD (10 + k) false with
          | true => cases b with | true => exact False.elim (hno ⟨x, hv⟩) | false => rfl
          | false => cases b with | false => exact False.elim (hno ⟨x, hv⟩) | true => rfl⟩
      have hNoAlias : ∀ k < C1.size, ∀ p < 10 + k, ∃ x : Fin 10 → Bool,
          (C1.wires (List.ofFn x)).getD (10 + k) false ≠ (C1.wires (List.ofFn x)).getD p false := by
        intro k hk p hp; by_contra hno
        exact hHasAlias ⟨k, by omega, p, hp, fun x => by by_contra hne; exact hno ⟨x, hne⟩⟩
      have hOutLast : C1.output + 1 = 10 + C1.size := by
        have hLast := hLive (C1.size - 1) (by omega)
        rcases hLast with heq | ⟨_, _, hcone⟩
        · omega
        · have hlt := (inCone_lt C1 hcone).1; omega
      have hArity : ∀ k < C1.size,
          (((gateAt C1 k).op ≠ GateOp.not ∧ (gateAt C1 k).inputs.length = 2 ∧ (gateAt C1 k).inputs.Nodup) ∨
           ((gateAt C1 k).op = GateOp.not ∧ (gateAt C1 k).inputs.length = 1)) := by
        intro k hk
        have hgMem : gateAt C1 k ∈ C1.gates := by rw [gateAt_eq hk]; exact List.getElem_mem hk
        have hgf := hFan1 _ hgMem
        by_cases hnot : (gateAt C1 k).op = GateOp.not
        · exact Or.inr ⟨hnot, hNot1 _ hgMem hnot⟩
        · left
          have hbo : (gateAt C1 k).op = GateOp.and ∨ (gateAt C1 k).op = GateOp.or := by
            rcases hgf.1 with h1 | h2 | h3; exact Or.inl h1; exact Or.inr h2; exact False.elim (hnot h3)
          cases hl : (gateAt C1 k).inputs with
          | nil =>
            exfalso
            rcases hbo with hand | hor
            · obtain ⟨x, hx⟩ := hNoConst k hk false
              rw [wire_gate C1 x k hk, hand, hl] at hx; exact Bool.noConfusion hx
            · obtain ⟨x, hx⟩ := hNoConst k hk true
              rw [wire_gate C1 x k hk, hor, hl] at hx; exact Bool.noConfusion hx
          | cons a t =>
            cases t with
            | nil =>
              exfalso
              have haLt : a < 10 + k := hRb1 k hk a (by rw [hl]; exact List.mem_cons_self)
              obtain ⟨x, hx⟩ := hNoAlias k hk a haLt
              rw [wire_gate C1 x k hk, hl] at hx
              rcases hbo with hand | hor
              · rw [hand] at hx; simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, ite_eq_left haLt] at hx; exact hx rfl
              · rw [hor] at hx; simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, ite_eq_left haLt] at hx; exact hx rfl
            | cons b t' =>
              cases t' with
              | nil =>
                refine ⟨hnot, rfl, ?_⟩
                have hab : a ≠ b := by
                  intro hEq; subst hEq
                  have haLt : a < 10 + k := hRb1 k hk a (by rw [hl]; exact List.mem_cons_self)
                  obtain ⟨x, hx⟩ := hNoAlias k hk a haLt
                  rw [wire_gate C1 x k hk, hl] at hx
                  rcases hbo with hand | hor
                  · rw [hand] at hx; simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_self, ite_eq_left haLt] at hx; exact hx rfl
                  · rw [hor] at hx; simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_self, ite_eq_left haLt] at hx; exact hx rfl
                exact List.nodup_cons.mpr ⟨fun h => hab (List.mem_singleton.mp h), List.nodup_singleton b⟩
              | cons _ _ =>
                have := hgf.2; rw [hl] at this; simp only [List.length_cons] at this; omega
      have hNormAll : ∀ k < C1.size,
          (((gateAt C1 k).op ≠ GateOp.not ∧ (gateAt C1 k).inputs.length = 2 ∧ (gateAt C1 k).inputs.Nodup) ∨
           ((gateAt C1 k).op = GateOp.not ∧ (gateAt C1 k).inputs.length = 1)) ∧
          InOutCone 10 C1 (10 + k) C1.output ∧
          (∀ p < 10 + k, ∃ x : Fin 10 → Bool, (C1.wires (List.ofFn x)).getD (10 + k) false ≠ (C1.wires (List.ofFn x)).getD p false) ∧
          ∀ b : Bool, ∃ x : Fin 10 → Bool, (C1.wires (List.ofFn x)).getD (10 + k) false = b :=
        fun k hk => ⟨hArity k hk, hLive k hk, hNoAlias k hk, hNoConst k hk⟩
      -- Branch split: either (s = 19 ∧ notCount C1 = 1) or (s = 17 + notCount C1)
      by_cases hCase19 : C1.size = 19 ∧ notCount C1 = 1
      · -- Case A: s = 19, notCount C1 = 1, top gate 18 is OR; normalize unique NOT gate's input to 0 if < 10
        have hOr18 : (gateAt C1 18).op = GateOp.or := hTop1 (by omega)
        have hexNot : ∃ j < C1.size, (gateAt C1 j).op = GateOp.not := by
          have hne : (C1.gates.filter fun g => decide (g.op = GateOp.not)) ≠ [] := by
            intro hnil
            have : notCount C1 = 0 := by change (C1.gates.filter _).length = 0; rw [hnil]; rfl
            omega
          cases hf : C1.gates.filter (fun g => decide (g.op = GateOp.not)) with
          | nil => exact False.elim (hne hf)
          | cons g _ =>
            have hmem : g ∈ C1.gates.filter (fun h => decide (h.op = GateOp.not)) := by rw [hf]; exact List.mem_cons_self
            obtain ⟨hgIn, hgNotD⟩ := List.mem_filter.mp hmem
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hgIn
            exact ⟨j, hj, by rw [gateAt_eq hj]; exact of_decide_eq_true hgNotD⟩
        obtain ⟨j, hj, hjNot⟩ := hexNot
        have hjLen : (gateAt C1 j).inputs.length = 1 := hNot1 _ (by rw [gateAt_eq hj]; exact List.getElem_mem hj) hjNot
        obtain ⟨u, hju⟩ : ∃ u, (gateAt C1 j).inputs = [u] := by
          cases hl : (gateAt C1 j).inputs with
          | nil => rw [hl] at hjLen; exact False.elim (Nat.noConfusion hjLen)
          | cons a t =>
            cases t with
            | nil => exact ⟨a, rfl⟩
            | cons _ _ => rw [hl] at hjLen; simp only [List.length_cons] at hjLen; omega
        have hjSome : C1.gates[j]? = some ⟨GateOp.not, [u]⟩ := by
          rw [List.getElem?_eq_getElem hj]; congr 1
          rw [← gateAt_eq hj]; cases hg : gateAt C1 j with
          | mk op ins => rw [hg] at hjNot hju; dsimp only at hjNot hju; rw [hjNot, hju]
        by_cases hu10 : 10 ≤ u
        · have hOnly0 : ∀ j' u', j' < 19 → u' < 10 → (gateAt C1 j').op = GateOp.not ∧ (gateAt C1 j').inputs = [u'] → u' = 0 := by
            rintro j' u' hj' hu' ⟨hj'Op, hj'Ins⟩
            have hC1len19 : C1.gates.length = 19 := hCase19.1
            have hj'Lt : j' < C1.gates.length := by omega
            have hjeq : j' = j := notCount_unique C1.gates (by change notCount C1 ≤ 1; omega) j' j hj'Lt hj
              (by rw [← gateAt_eq hj'Lt]; exact hj'Op) (by rw [← gateAt_eq hj]; exact hjNot)
            subst hjeq
            rw [hju] at hj'Ins
            have : u = u' := (List.cons.inj hj'Ins).1
            omega
          exact hNonMono C1 hFan1 hRb1 (by omega) hComp1 (hNormCompact C1 hNormAll)
            (hDegBound C1 hFan1 hRb1 (by omega) hComp1 hArity)
            (Or.inl ⟨hCase19.1, hCase19.2, hOr18, fun j' u' hj' => hOnly0 j' u' (by omega)⟩)
        · let uF : Fin 10 := ⟨u, by omega⟩
          let wF : Fin 10 := if uF = 0 then 1 else 0
          have huw : uF ≠ wF := by
            dsimp only [wF]; by_cases h0 : uF = 0
            · rw [ite_eq_left h0, h0]; decide
            · rw [ite_eq_right h0]; exact h0
          have hPP := hPairPerm_ok uF wF huw
          let C2 := relabelC (liftS5 (pairPerm5 uF wF).1) C1
          obtain ⟨hFan2, hRb2, hSz2, hNc2', hOut2, hComp2, hNorm2⟩ :=
            hRelabelNorm (pairPerm5 uF wF).1 (pairPerm5 uF wF).2 hPP.1 C1 hFan1 hRb1 hNc1 hNc2 hB17 (by omega) hOutLast hComp1 hNormAll
          change C2.size = C1.size at hSz2
          change notCount C2 = notCount C1 at hNc2'
          change C2.output + 1 = 10 + C2.size at hOut2
          have hC1len19 : C1.gates.length = 19 := hCase19.1
          have hC2len19 : C2.gates.length = 19 := by change C2.size = 19; omega
          have hOr18' : (gateAt C2 18).op = GateOp.or := by
            rw [gateAt_eq (by omega : 18 < C2.gates.length)]
            change ((C1.gates.map (relabelG (liftS5 (pairPerm5 uF wF).1)))[18]'(by rw [List.length_map]; omega)).op = GateOp.or
            rw [List.getElem_map]
            dsimp only [relabelG]; rw [← gateAt_eq (by omega : 18 < C1.gates.length)]; exact hOr18
          have hjSome' : C2.gates[j]? = some ⟨GateOp.not, [0]⟩ := by
            change (C1.gates.map (relabelG (liftS5 (pairPerm5 uF wF).1)))[j]? = some ⟨GateOp.not, [0]⟩
            rw [List.getElem?_map, hjSome]
            simp only [Option.map_some, relabelG, List.map_cons, List.map_nil, relabelW, dite_eq_left (by omega : u < 10)]
            have hu0 : (liftS5 (pairPerm5 uF wF).1 uF).val = 0 := congrArg Fin.val hPP.2.1
            exact congrArg Option.some (by rw [hu0])
          have hOnly0' : ∀ j' u', j' < 19 → u' < 10 → (gateAt C2 j').op = GateOp.not ∧ (gateAt C2 j').inputs = [u'] → u' = 0 := by
            rintro j' u' hj' _ ⟨hj'Op, hj'Ins⟩
            have hj2 : j < C2.gates.length := by omega
            have hj'2 : j' < C2.gates.length := by omega
            have hjGate : gateAt C2 j = ⟨GateOp.not, [0]⟩ := by
              rw [gateAt_eq hj2]; have := List.getElem?_eq_getElem hj2; rw [this] at hjSome'; exact Option.some.inj hjSome'
            have hjeq : j' = j := notCount_unique C2.gates (by change notCount C2 ≤ 1; omega) j' j hj'2 hj2
              (by rw [← gateAt_eq hj'2]; exact hj'Op) (by rw [← gateAt_eq hj2, hjGate])
            subst hjeq
            rw [hjGate] at hj'Ins
            exact (List.cons.inj hj'Ins).1.symm
          exact hNonMono C2 hFan2 hRb2 (by omega) hComp2 (hNormCompact C2 hNorm2)
            (hDegBound C2 hFan2 hRb2 (by omega) hComp2 (fun k hk => (hNorm2 k hk).1))
            (Or.inl ⟨by omega, by omega, hOr18', fun j' u' hj' => hOnly0' j' u' (by omega)⟩)
      · -- Case B: C1.size = 17 + notCount C1! Classify the first binary gate k0!
        have hBin17 : C1.size = 17 + notCount C1 := by omega
        have hShape1 : ∀ g ∈ C1.gates, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
            ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) := by
          intro g hg
          obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
          have ha := hArity k hk; rw [gateAt_eq hk] at ha
          rcases ha with ⟨hnot, hl, _⟩ | ⟨hnot, hl⟩
          · right; refine ⟨?_, hl⟩
            rcases (hFan1 _ (List.getElem_mem hk)).1 with h1 | h2 | h3; exact Or.inl h1; exact Or.inr h2; exact False.elim (hnot h3)
          · exact Or.inl ⟨hnot, hl⟩
        -- Find the FIRST binary gate k0 < C1.size (exists since C1.size ≥ 18 > 2 ≥ notCount C1)
        have hFindK0 : ∃ k0 < C1.size, (gateAt C1 k0).op ≠ GateOp.not ∧ ∀ j < k0, (gateAt C1 j).op = GateOp.not := by
          have hexBin : ∃ k < C1.size, (gateAt C1 k).op ≠ GateOp.not := by
            by_contra hAllNot
            have hAll : ∀ g ∈ C1.gates, g.op = GateOp.not := by
              intro g hg; obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
              by_contra hne; exact hAllNot ⟨k, hk, by rw [gateAt_eq hk]; exact hne⟩
            have hFilt : C1.gates.filter (fun g => decide (g.op = GateOp.not)) = C1.gates :=
              List.filter_eq_self.mpr (fun g hg => decide_eq_true (hAll g hg))
            have hEq : notCount C1 = C1.size := by change (C1.gates.filter _).length = C1.gates.length; rw [hFilt]
            omega
          let k0 := Nat.find hexBin
          have hk0Spec := Nat.find_spec hexBin
          refine ⟨k0, hk0Spec.1, hk0Spec.2, fun j hj => ?_⟩
          by_contra hne
          exact Nat.find_min hexBin hj ⟨by omega, hne⟩
        obtain ⟨k0, hk0Lt, hk0Bin, hPrefNot⟩ := hFindK0
        -- Every gate j < k0 is NOT [u] for a UNIQUE input u < 10 (no double-NOT, no duplicate NOT)
        have hPrefNotInput : ∀ j < k0, ∃ u : Fin 10, (gateAt C1 j) = ⟨GateOp.not, [u.val]⟩ ∧
            ∀ x : Fin 10 → Bool, (C1.wires (List.ofFn x)).getD (10 + j) false = !(x u) := by
          intro j
          induction j using Nat.strong_induction_on with
          | ind j ihj =>
            intro hjk0
            have hjLt : j < C1.size := by omega
            have hjOp := hPrefNot j hjk0
            have hjLen := hNot1 _ (by rw [gateAt_eq hjLt]; exact List.getElem_mem hjLt) hjOp
            obtain ⟨w, hgw⟩ : ∃ w, (gateAt C1 j).inputs = [w] := by
              cases hl : (gateAt C1 j).inputs with
              | nil => rw [hl] at hjLen; exact False.elim (Nat.noConfusion hjLen)
              | cons a t =>
                cases t with
                | nil => exact ⟨a, rfl⟩
                | cons _ _ => rw [hl] at hjLen; simp only [List.length_cons] at hjLen; omega
            have hwLt : w < 10 + j := hRb1 j hjLt w (by rw [hgw]; exact List.mem_cons_self)
            have hw10 : w < 10 := by
              by_contra hge
              have hj' : w - 10 < j := by omega
              obtain ⟨u, _, huEv⟩ := ihj (w - 10) hj' (by omega)
              have hEqW : 10 + (w - 10) = w := by omega
              obtain ⟨x, hxne⟩ := hNoAlias j hjLt u.val (by have := u.isLt; omega)
              rw [wire_gate C1 x j hjLt, hjOp, hgw] at hxne
              simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.headD_cons, ite_eq_left hwLt] at hxne
              rw [← hEqW, huEv x, Bool.not_not, wire_ofFn C1 x u] at hxne
              exact hxne rfl
            let u : Fin 10 := ⟨w, hw10⟩
            have hGateEq : gateAt C1 j = ⟨GateOp.not, [u.val]⟩ := by
              cases hg : gateAt C1 j with
              | mk op ins => rw [hg] at hjOp hgw; dsimp only at hjOp hgw; rw [hjOp, hgw]
            refine ⟨u, hGateEq, fun x => ?_⟩
            rw [wire_gate C1 x j hjLt, hGateEq]
            have huLt : u.val < 10 + j := hwLt
            simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.headD_cons, ite_eq_left huLt, wire_ofFn C1 x u]
        -- Helper: k0 ≤ notCount C1 ≤ 2
        have hk0LeNc : k0 ≤ notCount C1 := by
          have hSub : (List.range k0).length ≤ (C1.gates.filter fun g => decide (g.op = GateOp.not)).length := by
            have hTake : C1.gates.take k0 = (C1.gates.take k0).filter (fun g => decide (g.op = GateOp.not)) :=
              (List.filter_eq_self.mpr (fun g hg => by
                obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
                have hk0Len' : k0 < C1.gates.length := hk0Lt
                rw [List.length_take_of_le (le_of_lt hk0Len')] at hj
                simp only [List.getElem_take]
                rw [← gateAt_eq (by omega)]
                exact decide_eq_true (hPrefNot j hj))).symm
            have hSplit : C1.gates = C1.gates.take k0 ++ C1.gates.drop k0 := (List.take_append_drop k0 C1.gates).symm
            have hF : (C1.gates.filter fun g => decide (g.op = GateOp.not)).length =
                ((C1.gates.take k0).filter fun g => decide (g.op = GateOp.not)).length +
                ((C1.gates.drop k0).filter fun g => decide (g.op = GateOp.not)).length := by
              conv_lhs => rw [hSplit]
              rw [List.filter_append, List.length_append]
            rw [List.length_range, hF, ← hTake, List.length_take_of_le (le_of_lt hk0Lt)]; omega
          rw [List.length_range] at hSub; exact hSub
        -- Extract g0 = gateAt C1 k0 = ⟨op0, [a0, b0]⟩ with distinct inputs < 10 + k0
        have hk0Ar := hArity k0 hk0Lt
        have hk0Len : (gateAt C1 k0).inputs.length = 2 ∧ (gateAt C1 k0).inputs.Nodup := by
          rcases hk0Ar with ⟨_, h1, h2⟩ | ⟨h1, _⟩; exact ⟨h1, h2⟩; exact False.elim (hk0Bin h1)
        have hk0Op : (gateAt C1 k0).op = GateOp.and ∨ (gateAt C1 k0).op = GateOp.or := by
          rcases (hFan1 (gateAt C1 k0) (by rw [gateAt_eq hk0Lt]; exact List.getElem_mem hk0Lt)).1 with h1 | h2 | h3
          · exact Or.inl h1
          · exact Or.inr h2
          · exact False.elim (hk0Bin h3)
        obtain ⟨a0, b0, hab0Eq⟩ : ∃ a0 b0, (gateAt C1 k0).inputs = [a0, b0] := by
          cases hl : (gateAt C1 k0).inputs with
          | nil => rw [hl] at hk0Len; exact False.elim (Nat.noConfusion hk0Len.1)
          | cons a t =>
            cases t with
            | nil => rw [hl] at hk0Len; simp only [List.length_cons, List.length_nil] at hk0Len; omega
            | cons b t' =>
              cases t' with
              | nil => exact ⟨a, b, rfl⟩
              | cons _ _ => rw [hl] at hk0Len; simp only [List.length_cons] at hk0Len; omega
        have hab0Ne : a0 ≠ b0 := by
          have hn := hk0Len.2; rw [hab0Eq] at hn
          exact fun e => (List.nodup_cons.mp hn).1 (e ▸ List.mem_singleton.mpr rfl)
        have ha0Lt : a0 < 10 + k0 := hRb1 k0 hk0Lt a0 (by rw [hab0Eq]; exact List.mem_cons_self)
        have hb0Lt : b0 < 10 + k0 := hRb1 k0 hk0Lt b0 (by rw [hab0Eq]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        -- Extract underlying (u1, neg1) for a0 and (u2, neg2) for b0
        have hLitParse : ∀ w < 10 + k0, ∃ (u : Fin 10) (neg : Bool),
            (if neg then ∃ j < k0, w = 10 + j ∧ gateAt C1 j = ⟨GateOp.not, [u.val]⟩ else w = u.val) ∧
            (∀ x : Fin 10 → Bool, (C1.wires (List.ofFn x)).getD w false = if neg then !(x u) else x u) ∧
            ((rRun u C1.gates).1.getD w (true, false, 0) = (true, neg, 0)) := by
          intro w hw
          by_cases h10 : w < 10
          · refine ⟨⟨w, h10⟩, false, rfl, fun x => wire_ofFn C1 x ⟨w, h10⟩, ?_⟩
            rw [rRun_init_at ⟨w, h10⟩ C1 ⟨w, h10⟩, ite_eq_left rfl]
          · obtain ⟨u, hgu, huev⟩ := hPrefNotInput (w - 10) (by omega)
            have heq : 10 + (w - 10) = w := by omega
            refine ⟨u, true, ⟨w - 10, by omega, heq.symm, hgu⟩, fun x => by rw [← heq, huev x]; rfl, ?_⟩
            have hAt := rRun_at_step u C1 (w - 10) (by omega)
            rw [← heq, hAt.2.2, hgu]
            dsimp only [rStep]; rw [ite_eq_left rfl, List.getD_cons_zero]
            have hu0 : (rRun u (C1.gates.take (w - 10))).1.getD u.val (true, false, 0) = (true, false, 0) := by
              rw [← hAt.2.1 u.val (by have := u.isLt; omega), rRun_init_at u C1 u, ite_eq_left rfl]
            rw [hu0, ite_eq_left rfl]
            rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, Bool.not_false]
        obtain ⟨u1, n1, hSpec1, hEvA0, hRunA0⟩ := hLitParse a0 ha0Lt
        obtain ⟨u2, n2, hSpec2, hEvB0, hRunB0⟩ := hLitParse b0 hb0Lt
        -- u1 ≠ u2 (otherwise g0 is constant false/true or aliases a0/b0)
        have hu12Ne : u1 ≠ u2 := by
          intro hEq; subst hEq
          cases hn1 : n1 with
          | false =>
            cases hn2 : n2 with
            | false => rw [hn1] at hSpec1; rw [hn2] at hSpec2; exact hab0Ne (hSpec1.trans hSpec2.symm)
            | true =>
              rcases hk0Op with hand | hor
              · obtain ⟨x, hx⟩ := hNoConst k0 hk0Lt true
                rw [wire_gate C1 x k0 hk0Lt, hand, hab0Eq] at hx
                simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                  ite_eq_left ha0Lt, ite_eq_left hb0Lt, hEvA0 x, hEvB0 x, hn1, hn2, Bool.false_eq_true, ite_false, ite_true, Bool.and_true, Bool.and_not_self] at hx
              · obtain ⟨x, hx⟩ := hNoConst k0 hk0Lt false
                rw [wire_gate C1 x k0 hk0Lt, hor, hab0Eq] at hx
                simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                  ite_eq_left ha0Lt, ite_eq_left hb0Lt, hEvA0 x, hEvB0 x, hn1, hn2, Bool.false_eq_true, ite_false, ite_true, Bool.or_false, Bool.or_not_self] at hx
                exact Bool.noConfusion hx
          | true =>
            cases hn2 : n2 with
            | false =>
              rcases hk0Op with hand | hor
              · obtain ⟨x, hx⟩ := hNoConst k0 hk0Lt true
                rw [wire_gate C1 x k0 hk0Lt, hand, hab0Eq] at hx
                simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                  ite_eq_left ha0Lt, ite_eq_left hb0Lt, hEvA0 x, hEvB0 x, hn1, hn2, Bool.false_eq_true, ite_false, ite_true, Bool.and_true, Bool.not_and_self] at hx
              · obtain ⟨x, hx⟩ := hNoConst k0 hk0Lt false
                rw [wire_gate C1 x k0 hk0Lt, hor, hab0Eq] at hx
                simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                  ite_eq_left ha0Lt, ite_eq_left hb0Lt, hEvA0 x, hEvB0 x, hn1, hn2, Bool.false_eq_true, ite_false, ite_true, Bool.or_false, Bool.not_or_self] at hx
                exact Bool.noConfusion hx
            | true =>
              rw [hn1] at hSpec1; rw [hn2] at hSpec2
              obtain ⟨j1, hj1, ha0j1, _⟩ := hSpec1
              obtain ⟨j2, hj2, hb0j2, _⟩ := hSpec2
              have hj12Ne : j1 ≠ j2 := fun e => hab0Ne (by rw [ha0j1, hb0j2, e])
              by_cases hlt : j1 < j2
              · obtain ⟨x, hx⟩ := hNoAlias j2 (by omega) (10 + j1) (by omega)
                rw [← ha0j1, ← hb0j2, hEvA0 x, hEvB0 x, hn1, hn2] at hx; exact hx rfl
              · obtain ⟨x, hx⟩ := hNoAlias j1 (by omega) (10 + j2) (by omega)
                rw [← ha0j1, ← hb0j2, hEvA0 x, hEvB0 x, hn1, hn2] at hx; exact hx rfl
        -- Unified killer: if g0 becomes const under `u := false` AND `g0(x0) = g0(x1)` for separating pair (u, w, b2), False!
        have hKillBadG0 : ∀ (u w : Fin 10) (b2 : Bool), u ≠ w →
            (∃ i ∈ (gateAt C1 k0).inputs, ((rRun u C1.gates).1.getD i (true, false, 0)).1 = true) →
            ((rRun u C1.gates).1.getD (10 + k0) (true, false, 0)).1 = true →
            (∀ x0 x1 : Fin 10 → Bool, x0 u = false → x1 u = true → x0 w = b2 → x1 w = b2 →
              (∀ v : Fin 10, v ≠ u → x0 v = x1 v) →
              (C1.wires (List.ofFn x0)).getD (10 + k0) false = (C1.wires (List.ofFn x1)).getD (10 + k0) false) →
            False := by
          intro u w b2 huw hk0In hk0C hSameK0
          obtain ⟨z, hzu, hzw, huz, hwz⟩ := hSepWitness u w huw
          let x0 : Fin 10 → Bool := fun v => decide (v = z ∨ (b2 = true ∧ v = w))
          let x1 : Fin 10 → Bool := fun v => decide (v = u ∨ v = z ∨ (b2 = true ∧ v = w))
          have hx0u : x0 u = false := decide_eq_false (by rintro (rfl | ⟨_, rfl⟩); exact hzu rfl; exact huw rfl)
          have hx1u : x1 u = true := decide_eq_true (Or.inl rfl)
          have hx0w : x0 w = b2 := by
            cases b2 with
            | false => exact decide_eq_false (by rintro (rfl | ⟨h, _⟩); exact hzw rfl; exact Bool.noConfusion h)
            | true => exact decide_eq_true (Or.inr ⟨rfl, rfl⟩)
          have hx1w : x1 w = b2 := by
            cases b2 with
            | false => exact decide_eq_false (by rintro (rfl | rfl | ⟨h, _⟩); exact huw rfl; exact hzw rfl; exact Bool.noConfusion h)
            | true => exact decide_eq_true (Or.inr (Or.inr ⟨rfl, rfl⟩))
          have hAgree : ∀ v : Fin 10, v ≠ u → x0 v = x1 v := fun v hvu => by
            dsimp only [x0, x1]; apply Bool.eq_iff_iff.mpr; rw [decide_eq_true_eq, decide_eq_true_eq]
            constructor
            · intro h; exact Or.inr h
            · rintro (rfl | h)
              · exact False.elim (hvu rfl)
              · exact h
          have hP0' : Plist x0 = false := by
            apply Bool.eq_false_iff.mpr; intro ht
            obtain ⟨p, q, hpq, hxp, hxq⟩ := (hP_iff_adj x0).mp ht
            have hp := of_decide_eq_true hxp
            have hq := of_decide_eq_true hxq
            rcases hp with rfl | ⟨_, rfl⟩ <;> rcases hq with rfl | ⟨_, rfl⟩
            · rw [hAdj_irrefl] at hpq; exact Bool.noConfusion hpq
            · rw [hAdj_symm, hwz] at hpq; exact Bool.noConfusion hpq
            · rw [hwz] at hpq; exact Bool.noConfusion hpq
            · rw [hAdj_irrefl] at hpq; exact Bool.noConfusion hpq
          have hP1' : Plist x1 = true :=
            (hP_iff_adj x1).mpr ⟨u, z, huz, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr (Or.inl rfl))⟩
          have hRunM := rRun_main u C1 hRb1 hShape1 (by omega) hComp1
          have hElim2 : (rRun u C1.gates).2.2 ≤ 2 := by omega
          let Diff : ℕ → Prop := fun wire =>
            (C1.wires (List.ofFn x0)).getD wire false ≠ (C1.wires (List.ofFn x1)).getD wire false
          have hDiffOut : Diff C1.output := by
            dsimp only [Diff]; change C1.eval (List.ofFn x0) ≠ C1.eval (List.ofFn x1)
            rw [hComp1, hComp1, hP0', hP1']; exact Bool.false_ne_true
          -- Helper: if NO binary gate < m has Diff, then every wire < 10 + m with Diff is const in rRun u & outside k0's cone
          have hPrefixDiff : ∀ m ≤ C1.size, (∀ g < m, (gateAt C1 g).op ≠ GateOp.not → ¬ Diff (10 + g)) →
              ∀ wire < 10 + m, Diff wire →
                ((rRun u C1.gates).1.getD wire (true, false, 0)).1 = true ∧ ¬ InOutCone 10 C1 (10 + k0) wire := by
            intro m
            induction m with
            | zero =>
              intro _ _ wire hw hD
              have hwu : wire = u.val := by
                by_contra hne
                dsimp only [Diff] at hD
                rw [wire_ofFn C1 x0 ⟨wire, hw⟩, wire_ofFn C1 x1 ⟨wire, hw⟩, hAgree ⟨wire, hw⟩ (fun e => hne (congrArg Fin.val e))] at hD
                exact hD rfl
              subst hwu
              refine ⟨by rw [rRun_init_at u C1 u, ite_eq_left rfl], ?_⟩
              rintro (heq | ⟨_, hge, _⟩)
              · have := u.isLt; omega
              · have := u.isLt; omega
            | succ m ihm =>
              intro hm hNoBin wire hw hD
              by_cases hilt : wire < 10 + m
              · exact ihm (by omega) (fun g hg => hNoBin g (by omega)) wire hilt hD
              · have hweq : wire = 10 + m := by omega
                subst wire
                have hmLt : m < C1.size := by omega
                have hmNot : (gateAt C1 m).op = GateOp.not := by
                  by_contra hbin; exact hNoBin m (by omega) hbin hD
                have hmLen : (gateAt C1 m).inputs.length = 1 := hNot1 _ (by rw [gateAt_eq hmLt]; exact List.getElem_mem hmLt) hmNot
                obtain ⟨w', hgm⟩ : ∃ w', (gateAt C1 m).inputs = [w'] := by
                  cases hl : (gateAt C1 m).inputs with
                  | nil => rw [hl] at hmLen; exact False.elim (Nat.noConfusion hmLen)
                  | cons a t =>
                    cases t with
                    | nil => exact ⟨a, rfl⟩
                    | cons _ _ => rw [hl] at hmLen; simp only [List.length_cons] at hmLen; omega
                have hw'Lt : w' < 10 + m := hRb1 m hmLt w' (by rw [hgm]; exact List.mem_cons_self)
                have hDw' : Diff w' := by
                  intro hEq
                  dsimp only [Diff] at hD
                  rw [wire_gate C1 x0 m hmLt, wire_gate C1 x1 m hmLt, hmNot, hgm] at hD
                  simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.headD_cons, ite_eq_left hw'Lt, hEq] at hD
                  exact hD rfl
                obtain ⟨hw'C, hw'NC⟩ := ihm (by omega) (fun g hg => hNoBin g (by omega)) w' hw'Lt hDw'
                refine ⟨?_, ?_⟩
                · have hAt := rRun_at_step u C1 m hmLt
                  rw [hAt.2.2]; dsimp only [rStep]; rw [ite_eq_left hmNot, hgm, List.getD_cons_zero]
                  have hw'C' : ((rRun u (C1.gates.take m)).1.getD w' (true, false, 0)).1 = true := by
                    rw [← hAt.2.1 w' hw'Lt]; exact hw'C
                  rw [ite_eq_left hw'C']
                  rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
                    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
                · rintro (heq | ⟨_, _, hcone⟩)
                  · have hmk : m = k0 := by omega
                    subst hmk; exact hk0Bin hmNot
                  · have hsub1 : 10 + k0 - 10 = k0 := by omega
                    have hsub2 : 10 + m - 10 = m := by omega
                    rw [hsub1, hsub2] at hcone
                    obtain ⟨_, t, _, htin, htc⟩ := (inCone_iff C1 k0 m).mp hcone
                    rw [hgm] at htin
                    have htw' : 10 + t = w' := List.mem_singleton.mp htin
                    apply hw'NC
                    rcases htc with rfl | htk
                    · exact Or.inl htw'
                    · exact Or.inr ⟨by omega, by omega, by rw [hsub1, ← htw', Nat.add_sub_cancel_left]; exact htk⟩
          -- There MUST exist a binary gate with Diff (otherwise output itself is const in rRun u, contradicting hRunM.2)
          have hexDiffBin : ∃ g < C1.size, (gateAt C1 g).op ≠ GateOp.not ∧ Diff (10 + g) := by
            by_contra hNo
            have hOutC := (hPrefixDiff C1.size (le_refl _) (fun g hg hbin hD => hNo ⟨g, hg, hbin, hD⟩) C1.output (by omega) hDiffOut).1
            rw [hRunM.2] at hOutC; exact Bool.noConfusion hOutC
          let g := Nat.find hexDiffBin
          have hgSpec := Nat.find_spec hexDiffBin
          have hgLt : g < C1.size := hgSpec.1
          have hgBin : (gateAt C1 g).op ≠ GateOp.not := hgSpec.2.1
          have hgDiff : Diff (10 + g) := hgSpec.2.2
          have hgk0Ne : g ≠ k0 := by
            intro hEq; subst hEq
            exact hgDiff (hSameK0 x0 x1 hx0u hx1u hx0w hx1w hAgree)
          have hexW0 : ∃ w0 ∈ (gateAt C1 g).inputs, Diff w0 := by
            by_contra hAllSame
            apply hgDiff
            rw [wire_gate C1 x0 g hgLt, wire_gate C1 x1 g hgLt]
            congr 1; apply List.map_congr_left; intro w0 hw0
            have hw0Lt : w0 < 10 + g := hRb1 g hgLt w0 hw0
            rw [ite_eq_left hw0Lt, ite_eq_left hw0Lt]
            by_contra hne; exact hAllSame ⟨w0, hw0, hne⟩
          obtain ⟨w0, hw0In, hw0Diff⟩ := hexW0
          have hw0Lt : w0 < 10 + g := hRb1 g hgLt w0 hw0In
          obtain ⟨hw0C, hw0NC⟩ := hPrefixDiff g (le_of_lt hgLt)
            (fun g' hg' hbin hD => Nat.find_min hexDiffBin hg' ⟨by omega, hbin, hD⟩) w0 hw0Lt hw0Diff
          exact hNoConstWithOther u C1 hRb1 hShape1 hOutLast hRunM.2 hLive hElim2 k0 hk0Lt hk0Bin hk0In hk0C
            g hgLt hgk0Ne hgBin w0 hw0In hw0C hw0NC
        -- Helper: compute rRun at k0 when one input is constant under u
        have hK0Const : ∀ (u : Fin 10) (op : GateOp), (gateAt C1 k0).op = op →
            ((op = GateOp.and ∧ ((rRun u C1.gates).1.getD a0 (true, false, 0) = (true, false, 0) ∨
                                  (rRun u C1.gates).1.getD b0 (true, false, 0) = (true, false, 0))) ∨
             (op = GateOp.or ∧ ((rRun u C1.gates).1.getD a0 (true, false, 0) = (true, true, 0) ∨
                                 (rRun u C1.gates).1.getD b0 (true, false, 0) = (true, true, 0)))) →
            (∃ i ∈ (gateAt C1 k0).inputs, ((rRun u C1.gates).1.getD i (true, false, 0)).1 = true) ∧
            ((rRun u C1.gates).1.getD (10 + k0) (true, false, 0)).1 = true := by
          intro u op hop hCase
          have hAt := rRun_at_step u C1 k0 hk0Lt
          rcases hCase with ⟨rfl, hAB⟩ | ⟨rfl, hAB⟩
          · refine ⟨hAB.elim (fun h => ⟨a0, by rw [hab0Eq]; exact List.mem_cons_self, by rw [h]⟩)
              (fun h => ⟨b0, by rw [hab0Eq]; exact List.mem_cons_of_mem _ List.mem_cons_self, by rw [h]⟩), ?_⟩
            rw [hAt.2.2]; dsimp only [rStep]; rw [ite_eq_right hk0Bin, ite_eq_left hop, hab0Eq]
            simp only [List.getD_cons_zero, List.getD_cons_succ]
            rw [← hAt.2.1 a0 ha0Lt, ← hAt.2.1 b0 hb0Lt]
            rcases hAB with ha | hb
            · rw [ha, ite_eq_left rfl, ite_eq_right Bool.false_ne_true]
              rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            · by_cases hs1 : ((rRun u C1.gates).1.getD a0 (true, false, 0)).1 = true
              · rw [ite_eq_left hs1]
                by_cases hv1 : ((rRun u C1.gates).1.getD a0 (true, false, 0)).2.1 = true
                · rw [ite_eq_left hv1, hb]
                  rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
                · rw [ite_eq_right hv1]
                  rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              · rw [ite_eq_right hs1, hb, ite_eq_left rfl, ite_eq_right Bool.false_ne_true]
                rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          · refine ⟨hAB.elim (fun h => ⟨a0, by rw [hab0Eq]; exact List.mem_cons_self, by rw [h]⟩)
              (fun h => ⟨b0, by rw [hab0Eq]; exact List.mem_cons_of_mem _ List.mem_cons_self, by rw [h]⟩), ?_⟩
            have hNotAnd : (gateAt C1 k0).op ≠ GateOp.and := by rw [hop]; exact GateOp.noConfusion
            rw [hAt.2.2]; dsimp only [rStep]; rw [ite_eq_right hk0Bin, ite_eq_right hNotAnd, hab0Eq]
            simp only [List.getD_cons_zero, List.getD_cons_succ]
            rw [← hAt.2.1 a0 ha0Lt, ← hAt.2.1 b0 hb0Lt]
            rcases hAB with ha | hb
            · rw [ha, ite_eq_left rfl, ite_eq_left rfl]
              rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            · by_cases hs1 : ((rRun u C1.gates).1.getD a0 (true, false, 0)).1 = true
              · rw [ite_eq_left hs1]
                by_cases hv1 : ((rRun u C1.gates).1.getD a0 (true, false, 0)).2.1 = true
                · rw [ite_eq_left hv1]
                  rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
                · rw [ite_eq_right hv1, hb]
                  rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              · rw [ite_eq_right hs1, hb, ite_eq_left rfl, ite_eq_left rfl]
                rw [← hAt.1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        -- Now classify (hk0Op, n1, n2): 6 of 8 combinations die immediately via hKillBadG0!
        rcases hk0Op with hand0 | hor0
        · -- g0.op = AND
          cases hn1 : n1 with
          | false =>
            have hKC := hK0Const u1 GateOp.and hand0 (Or.inl ⟨rfl, Or.inl (hn1 ▸ hRunA0)⟩)
            exact hKillBadG0 u1 u2 n2 hu12Ne hKC.1 hKC.2 (fun x0 x1 _ _ hx0w hx1w _ => by
              rw [wire_gate C1 x0 k0 hk0Lt, wire_gate C1 x1 k0 hk0Lt, hand0, hab0Eq]
              simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                ite_eq_left ha0Lt, ite_eq_left hb0Lt, hEvA0, hEvB0, hx0w, hx1w]
              cases n2 <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true])
          | true =>
            cases hn2 : n2 with
            | false =>
              have hKC := hK0Const u2 GateOp.and hand0 (Or.inl ⟨rfl, Or.inr (hn2 ▸ hRunB0)⟩)
              exact hKillBadG0 u2 u1 true hu12Ne.symm hKC.1 hKC.2 (fun x0 x1 _ _ hx0w hx1w _ => by
                rw [wire_gate C1 x0 k0 hk0Lt, wire_gate C1 x1 k0 hk0Lt, hand0, hab0Eq]
                simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                  ite_eq_left ha0Lt, ite_eq_left hb0Lt, hEvA0, hEvB0, hn1, hx0w, hx1w, ite_true, Bool.not_true, Bool.false_and])
            | true =>
              -- Surviving AND case: BOTH inputs are NOT gates (j1, j2 < k0), forcing k0 = 2 and {j1, j2} = {0, 1}!
              rw [hn1] at hSpec1; rw [hn2] at hSpec2
              obtain ⟨j1, hj1, ha0j1, hgj1⟩ := hSpec1
              obtain ⟨j2, hj2, hb0j2, hgj2⟩ := hSpec2
              have hj12Ne : j1 ≠ j2 := fun e => hab0Ne (by rw [ha0j1, hb0j2, e])
              have hk0Eq2 : k0 = 2 := by omega
              subst hk0Eq2
              have hGate2Eq : C1.gates[2]? = some ⟨GateOp.and, [10 + j1, 10 + j2]⟩ := by
                rw [List.getElem?_eq_getElem hk0Lt]; congr 1
                rw [← gateAt_eq hk0Lt]; cases hg : gateAt C1 2 with
                | mk op ins => rw [hg] at hand0 hab0Eq; dsimp only at hand0 hab0Eq; rw [hand0, hab0Eq, ha0j1, hb0j2]
              -- Ensure gate 2 is AND [10, 11] (swap if j1 = 1, j2 = 0), then relabel (u0, u1) -> (0, 1/2)!
              have hApplyAnd : ∀ (D : Circuit) (v0 v1 : Fin 10), v0 ≠ v1 →
                  FanInTwo D → ReadsBack 10 D → D.size = C1.size → notCount D = notCount C1 →
                  D.output + 1 = 10 + D.size → (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = Plist x) →
                  (∀ k < D.size,
                    (((gateAt D k).op ≠ GateOp.not ∧ (gateAt D k).inputs.length = 2 ∧ (gateAt D k).inputs.Nodup) ∨
                     ((gateAt D k).op = GateOp.not ∧ (gateAt D k).inputs.length = 1)) ∧
                    InOutCone 10 D (10 + k) D.output ∧
                    (∀ p < 10 + k, ∃ x : Fin 10 → Bool, (D.wires (List.ofFn x)).getD (10 + k) false ≠ (D.wires (List.ofFn x)).getD p false) ∧
                    ∀ b : Bool, ∃ x : Fin 10 → Bool, (D.wires (List.ofFn x)).getD (10 + k) false = b) →
                  D.gates[0]? = some ⟨GateOp.not, [v0.val]⟩ →
                  D.gates[1]? = some ⟨GateOp.not, [v1.val]⟩ →
                  D.gates[2]? = some ⟨GateOp.and, [10, 11]⟩ → False := by
                intro D v0 v1 hv01 hFanD hRbD hSzD hNcD hOutD hCompD hNormD hD0 hD1 hD2
                have hPP := hPairPerm_ok v0 v1 hv01
                let D' := relabelC (liftS5 (pairPerm5 v0 v1).1) D
                obtain ⟨hFan', hRb', hSz', hNc', hOut', hComp', hNorm'⟩ :=
                  hRelabelNorm (pairPerm5 v0 v1).1 (pairPerm5 v0 v1).2 hPP.1 D hFanD hRbD (by omega) (by omega)
                    (by omega) (by omega) hOutD hCompD hNormD
                change D'.size = D.size at hSz'
                change notCount D' = notCount D at hNc'
                change D'.output + 1 = 10 + D'.size at hOut'
                have hDlen : D.gates.length = C1.size := hSzD
                have hD'len : D'.gates.length = C1.size := by change D'.size = C1.size; omega
                have hD'0 : D'.gates[0]? = some ⟨GateOp.not, [0]⟩ := by
                  rw [List.getElem?_eq_getElem (by omega : 0 < D'.gates.length)]
                  change some ((D.gates.map (relabelG (liftS5 (pairPerm5 v0 v1).1)))[0]'(by rw [List.length_map]; omega)) = _
                  rw [List.getElem_map]
                  have hg0 : D.gates[0]'(by omega) = ⟨GateOp.not, [v0.val]⟩ := by have := List.getElem?_eq_getElem (by omega : 0 < D.gates.length); rw [this] at hD0; exact Option.some.inj hD0
                  simp only [hg0, relabelG, List.map_cons, List.map_nil, relabelW, dite_eq_left v0.isLt]
                  exact congrArg Option.some (by congr 1; congr 1; exact congrArg Fin.val hPP.2.1)
                have hD'1 : D'.gates[1]? = some ⟨GateOp.not, [1]⟩ ∨ D'.gates[1]? = some ⟨GateOp.not, [2]⟩ := by
                  have hmap : D'.gates[1]? = some ⟨GateOp.not, [(liftS5 (pairPerm5 v0 v1).1 v1).val]⟩ := by
                    rw [List.getElem?_eq_getElem (by omega : 1 < D'.gates.length)]
                    change some ((D.gates.map (relabelG (liftS5 (pairPerm5 v0 v1).1)))[1]'(by rw [List.length_map]; omega)) = _
                    rw [List.getElem_map]
                    have hg1 : D.gates[1]'(by omega) = ⟨GateOp.not, [v1.val]⟩ := by have := List.getElem?_eq_getElem (by omega : 1 < D.gates.length); rw [this] at hD1; exact Option.some.inj hD1
                    simp only [hg1, relabelG, List.map_cons, List.map_nil, relabelW]; rw [dite_eq_left v1.isLt]
                  rw [hmap]
                  rcases hPP.2.2 with h1 | h2
                  · exact Or.inl (by rw [congrArg Fin.val h1]; rfl)
                  · exact Or.inr (by rw [congrArg Fin.val h2]; rfl)
                have hD'2 : D'.gates[2]? = some ⟨GateOp.and, [10, 11]⟩ := by
                  rw [List.getElem?_eq_getElem (by omega : 2 < D'.gates.length)]
                  change some ((D.gates.map (relabelG (liftS5 (pairPerm5 v0 v1).1)))[2]'(by rw [List.length_map]; omega)) = _
                  rw [List.getElem_map]
                  have hg2 : D.gates[2]'(by omega) = ⟨GateOp.and, [10, 11]⟩ := by have := List.getElem?_eq_getElem (by omega : 2 < D.gates.length); rw [this] at hD2; exact Option.some.inj hD2
                  rw [hg2]; rfl
                have hPref' : ∀ j < 2, (gateAt D' j).op = GateOp.not := fun j hj => by
                  rw [gateAt_eq (by omega : j < D'.gates.length)]
                  have h1 : j = 0 ∨ j = 1 := by omega
                  rcases h1 with rfl | rfl
                  · have := List.getElem?_eq_getElem (by omega : 0 < D'.gates.length); rw [this] at hD'0; rw [Option.some.inj hD'0]
                  · have := List.getElem?_eq_getElem (by omega : 1 < D'.gates.length); rw [this] at hD'1
                    rcases hD'1 with h | h <;> rw [Option.some.inj h]
                have hG0' : (gateAt D' 0).op = GateOp.not ∧ (gateAt D' 0).inputs = [0] := by
                  rw [gateAt_eq (by omega : 0 < D'.gates.length)]
                  have := List.getElem?_eq_getElem (by omega : 0 < D'.gates.length); rw [this] at hD'0; rw [Option.some.inj hD'0]; exact ⟨rfl, rfl⟩
                have hG1' : ((gateAt D' 1).op = GateOp.not ∧ (gateAt D' 1).inputs = [1]) ∨
                    ((gateAt D' 1).op = GateOp.not ∧ (gateAt D' 1).inputs = [2]) := by
                  rw [gateAt_eq (by omega : 1 < D'.gates.length)]
                  have := List.getElem?_eq_getElem (by omega : 1 < D'.gates.length); rw [this] at hD'1
                  rcases hD'1 with h | h
                  · exact Or.inl (by rw [Option.some.inj h]; exact ⟨rfl, rfl⟩)
                  · exact Or.inr (by rw [Option.some.inj h]; exact ⟨rfl, rfl⟩)
                have hG2' : (gateAt D' 2).op = GateOp.and ∧ (gateAt D' 2).inputs = [10, 11] := by
                  rw [gateAt_eq (by omega : 2 < D'.gates.length)]
                  have := List.getElem?_eq_getElem (by omega : 2 < D'.gates.length); rw [this] at hD'2; rw [Option.some.inj hD'2]; exact ⟨rfl, rfl⟩
                exact hNonMono D' hFan' hRb' (by omega) hComp' (hNormCompact D' hNorm')
                  (hDegBound D' hFan' hRb' (by omega) hComp' (fun k hk => (hNorm' k hk).1))
                  (Or.inr ⟨by omega, by omega, by omega, 2, by omega, hPref', Or.inr ⟨rfl, hG0', hG1', hG2'.1, hG2'.2⟩⟩)
              have hC1len : C1.gates.length = C1.size := rfl
              have hjCases : (j1 = 0 ∧ j2 = 1) ∨ (j1 = 1 ∧ j2 = 0) := by omega
              rcases hjCases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · have hG0 : C1.gates[0]? = some ⟨GateOp.not, [u1.val]⟩ := by rw [List.getElem?_eq_getElem (by omega : 0 < C1.gates.length), ← gateAt_eq (by omega), hgj1]
                have hG1 : C1.gates[1]? = some ⟨GateOp.not, [u2.val]⟩ := by rw [List.getElem?_eq_getElem (by omega : 1 < C1.gates.length), ← gateAt_eq (by omega), hgj2]
                exact hApplyAnd C1 u1 u2 hu12Ne hFan1 hRb1 rfl rfl hOutLast hComp1 hNormAll hG0 hG1 hGate2Eq
              · have hSw := hSwapBinAt C1 2 11 10 GateOp.and hk0Lt (Or.inl rfl) hGate2Eq
                let D : Circuit := ⟨C1.gates.set 2 ⟨GateOp.and, [10, 11]⟩, C1.output⟩
                have hDsz : D.size = C1.size := hSw.1
                have hDlen : D.gates.length = C1.gates.length := hSw.1
                have hDout : D.output = C1.output := rfl
                have hG0 : D.gates[0]? = some ⟨GateOp.not, [u2.val]⟩ := by
                  rw [hSw.2.2.2.1 0 (by omega), List.getElem?_eq_getElem (by omega : 0 < C1.gates.length), ← gateAt_eq (by omega), hgj2]
                have hG1 : D.gates[1]? = some ⟨GateOp.not, [u1.val]⟩ := by
                  rw [hSw.2.2.2.1 1 (by omega), List.getElem?_eq_getElem (by omega : 1 < C1.gates.length), ← gateAt_eq (by omega), hgj1]
                have hGateAtD : ∀ k < D.size, k ≠ 2 → gateAt D k = gateAt C1 k := fun k hk hne => by
                  have hk' : k < C1.gates.length := by change k < D.gates.length at hk; omega
                  rw [gateAt_eq hk, gateAt_eq hk']
                  have h1 := hSw.2.2.2.1 k hne
                  rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk'] at h1; exact Option.some.inj h1
                have hGateAtD2 : gateAt D 2 = ⟨GateOp.and, [10, 11]⟩ := by
                  rw [gateAt_eq (by omega : 2 < D.gates.length)]
                  have h1 := hSw.2.2.1; rw [List.getElem?_eq_getElem (by omega : 2 < D.gates.length)] at h1; exact Option.some.inj h1
                have hFanD : FanInTwo D := fun g hg => by
                  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
                  by_cases hk2 : k = 2
                  · subst hk2; rw [← gateAt_eq hk, hGateAtD2]; exact ⟨Or.inl rfl, by simp⟩
                  · have hk' : k < C1.gates.length := by omega
                    rw [← gateAt_eq hk, hGateAtD k hk hk2]; exact hFan1 (gateAt C1 k) (by rw [gateAt_eq hk']; exact List.getElem_mem hk')
                have hRbD : ReadsBack 10 D := fun k hk w hw => by
                  by_cases hk2 : k = 2
                  · subst hk2; rw [hGateAtD2] at hw
                    rcases List.mem_cons.mp hw with rfl | hw'
                    · omega
                    · rw [List.mem_singleton.mp hw']; omega
                  · rw [hGateAtD k hk hk2] at hw; exact hRb1 k (by change k < D.gates.length at hk; omega) w hw
                have hCompD : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = Plist x := fun x =>
                  (hSw.2.2.2.2.1 x C1.output (by omega)).trans (hComp1 x)
                have hNormD : ∀ k < D.size,
                    (((gateAt D k).op ≠ GateOp.not ∧ (gateAt D k).inputs.length = 2 ∧ (gateAt D k).inputs.Nodup) ∨
                     ((gateAt D k).op = GateOp.not ∧ (gateAt D k).inputs.length = 1)) ∧
                    InOutCone 10 D (10 + k) D.output ∧
                    (∀ p < 10 + k, ∃ x : Fin 10 → Bool, (D.wires (List.ofFn x)).getD (10 + k) false ≠ (D.wires (List.ofFn x)).getD p false) ∧
                    ∀ b : Bool, ∃ x : Fin 10 → Bool, (D.wires (List.ofFn x)).getD (10 + k) false = b := by
                  intro k hk
                  have hkC : k < C1.size := by omega
                  obtain ⟨hAr, hLv, hNA, hNC⟩ := hNormAll k hkC
                  refine ⟨?_, ?_, fun p hp => ?_, fun b => ?_⟩
                  · by_cases hk2 : k = 2
                    · subst hk2; rw [hGateAtD2]; exact Or.inl ⟨GateOp.noConfusion, rfl, by decide⟩
                    · rw [hGateAtD k hk hk2]; exact hAr
                  · rcases hLv with heq | ⟨h1, h2, hc⟩
                    · exact Or.inl heq
                    · exact Or.inr ⟨h1, h2, (hSw.2.2.2.2.2 _ _).mpr hc⟩
                  · obtain ⟨x, hx⟩ := hNA p hp
                    exact ⟨x, by rw [hSw.2.2.2.2.1 x (10 + k) (by omega), hSw.2.2.2.2.1 x p (by omega)]; exact hx⟩
                  · obtain ⟨x, hx⟩ := hNC b
                    exact ⟨x, by rw [hSw.2.2.2.2.1 x (10 + k) (by omega)]; exact hx⟩
                exact hApplyAnd D u2 u1 hu12Ne.symm hFanD hRbD hDsz hSw.2.1 (by omega) hCompD hNormD hG0 hG1 hSw.2.2.1
        · -- g0.op = OR
          cases hn1 : n1 with
          | true =>
            have hKC := hK0Const u1 GateOp.or hor0 (Or.inr ⟨rfl, Or.inl (hn1 ▸ hRunA0)⟩)
            exact hKillBadG0 u1 u2 (!n2) hu12Ne hKC.1 hKC.2 (fun x0 x1 _ _ hx0w hx1w _ => by
              rw [wire_gate C1 x0 k0 hk0Lt, wire_gate C1 x1 k0 hk0Lt, hor0, hab0Eq]
              simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                ite_eq_left ha0Lt, ite_eq_left hb0Lt, hEvA0, hEvB0, hx0w, hx1w]
              cases n2 <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false, Bool.not_true, Bool.or_true, Bool.or_false])
          | false =>
            cases hn2 : n2 with
            | true =>
              have hKC := hK0Const u2 GateOp.or hor0 (Or.inr ⟨rfl, Or.inr (hn2 ▸ hRunB0)⟩)
              exact hKillBadG0 u2 u1 true hu12Ne.symm hKC.1 hKC.2 (fun x0 x1 _ _ hx0w hx1w _ => by
                rw [wire_gate C1 x0 k0 hk0Lt, wire_gate C1 x1 k0 hk0Lt, hor0, hab0Eq]
                simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                  ite_eq_left ha0Lt, ite_eq_left hb0Lt, hEvA0, hEvB0, hn1, hx0w, hx1w, Bool.false_eq_true, ite_false, Bool.true_or])
            | false =>
              -- Surviving OR case: BOTH inputs are direct inputs u1, u2 < 10! Relabel (u1, u2) -> (0, 1/2)!
              rw [hn1] at hSpec1; rw [hn2] at hSpec2
              have hPP := hPairPerm_ok u1 u2 hu12Ne
              let C2 := relabelC (liftS5 (pairPerm5 u1 u2).1) C1
              obtain ⟨hFan2, hRb2, hSz2, hNc2', hOut2, hComp2, hNorm2⟩ :=
                hRelabelNorm (pairPerm5 u1 u2).1 (pairPerm5 u1 u2).2 hPP.1 C1 hFan1 hRb1 hNc1 hNc2 hB17 (by omega) hOutLast hComp1 hNormAll
              change C2.size = C1.size at hSz2
              change notCount C2 = notCount C1 at hNc2'
              change C2.output + 1 = 10 + C2.size at hOut2
              have hC1len : C1.gates.length = C1.size := rfl
              have hC2len : C2.gates.length = C1.size := hSz2
              have hPref2 : ∀ j < k0, (gateAt C2 j).op = GateOp.not := fun j hj => by
                rw [gateAt_eq (by omega : j < C2.gates.length)]
                change ((C1.gates.map (relabelG (liftS5 (pairPerm5 u1 u2).1)))[j]'(by rw [List.length_map]; omega)).op = GateOp.not
                rw [List.getElem_map]
                dsimp only [relabelG]; rw [← gateAt_eq (by omega : j < C1.gates.length)]; exact hPrefNot j hj
              have hK0Some : C2.gates[k0]? = some ⟨GateOp.or, [0, 1]⟩ ∨ C2.gates[k0]? = some ⟨GateOp.or, [0, 2]⟩ := by
                have hg1 : C1.gates[k0]? = some ⟨GateOp.or, [u1.val, u2.val]⟩ := by
                  rw [List.getElem?_eq_getElem hk0Lt]; congr 1
                  rw [← gateAt_eq hk0Lt]; cases hg : gateAt C1 k0 with
                  | mk op ins => rw [hg] at hor0 hab0Eq; dsimp only at hor0 hab0Eq; rw [hor0, hab0Eq, hSpec1, hSpec2]
                have hmap : C2.gates[k0]? = some ⟨GateOp.or, [(liftS5 (pairPerm5 u1 u2).1 u1).val, (liftS5 (pairPerm5 u1 u2).1 u2).val]⟩ := by
                  change (C1.gates.map (relabelG (liftS5 (pairPerm5 u1 u2).1)))[k0]? = _
                  rw [List.getElem?_map, hg1]
                  simp only [Option.map_some, relabelG, List.map_cons, List.map_nil, relabelW, dite_eq_left u1.isLt, dite_eq_left u2.isLt]
                rw [hmap, congrArg Fin.val hPP.2.1]
                rcases hPP.2.2 with h1 | h2
                · exact Or.inl (by rw [congrArg Fin.val h1]; rfl)
                · exact Or.inr (by rw [congrArg Fin.val h2]; rfl)
              have hK0Or : (gateAt C2 k0).op = GateOp.or ∧ (gateAt C2 k0).inputs ∈ [[0, 1], [0, 2]] := by
                rw [gateAt_eq (by omega : k0 < C2.gates.length)]
                have := List.getElem?_eq_getElem (by omega : k0 < C2.gates.length); rw [this] at hK0Some
                rcases hK0Some with h | h
                · rw [Option.some.inj h]; exact ⟨rfl, List.mem_cons_self⟩
                · rw [Option.some.inj h]; exact ⟨rfl, List.mem_cons_of_mem _ List.mem_cons_self⟩
              exact hNonMono C2 hFan2 hRb2 (by omega) hComp2 (hNormCompact C2 hNorm2)
                (hDegBound C2 hFan2 hRb2 (by omega) hComp2 (fun k hk => (hNorm2 k hk).1))
                (Or.inr ⟨by omega, by omega, by omega, k0, by omega, hPref2, Or.inl hK0Or⟩)
  -- Wire the top-level target statement of L-meta-4940 into hNormalize
  intro x1 x2 x3 x4 hFan1 hFan2 hSz2
  dsimp only
  intro _ _ hSafe
  by_contra hNoUncov
  let D : Circuit := ⟨x1 :: (x2.gates ++ [⟨GateOp.or, [x3, x4]⟩]), 28⟩
  have hSzD : D.size = 19 := by
    change (x1 :: (x2.gates ++ [⟨GateOp.or, [x3, x4]⟩])).length = 19
    rw [List.length_cons, List.length_append, List.length_singleton]
    change x2.size + 1 + 1 = 19; omega
  have hFanD : FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | h1
    · exact hFan1 g List.mem_cons_self
    · rcases List.mem_append.mp h1 with h2 | h3
      · exact hFan2 g h2
      · rw [List.mem_singleton.mp h3]; exact ⟨Or.inr (Or.inl rfl), le_refl 2⟩
  have hTopD : (gateAt D 18).op = GateOp.or := by
    have hDlen19 : D.gates.length = 19 := hSzD
    rw [gateAt_eq (by omega : 18 < D.gates.length)]
    change ((x1 :: (x2.gates ++ [⟨GateOp.or, [x3, x4]⟩]))[18]'(by rw [List.length_cons, List.length_append, List.length_singleton]; change 18 < x2.size + 1 + 1; omega)).op = GateOp.or
    simp only [List.getElem_cons_succ]
    have h17 : 17 = x2.gates.length := hSz2.symm
    have hget : (x2.gates ++ [⟨GateOp.or, [x3, x4]⟩])[17]'(by rw [List.length_append, List.length_singleton]; omega) = ⟨GateOp.or, [x3, x4]⟩ := by
      rw [List.getElem_append_right (by omega : x2.gates.length ≤ 17)]
      have hsub : 17 - x2.gates.length = 0 := by omega
      simp only [hsub, List.getElem_cons_zero]
    rw [hget]
  have hEvalD : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = Plist x := by
    intro x
    have hW : D.eval (List.ofFn x) =
        ((x2.wires ({ gates := [x1], output := 0 : Circuit }.wires (List.ofFn x))).getD x3 false ||
         (x2.wires ({ gates := [x1], output := 0 : Circuit }.wires (List.ofFn x))).getD x4 false) := by
      change ((x1 :: (x2.gates ++ [⟨GateOp.or, [x3, x4]⟩])).foldl stepWire (List.ofFn x)).getD 28 false = _
      rw [List.foldl_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hLen28 : (x2.gates.foldl stepWire (stepWire (List.ofFn x) x1)).length = 28 := by
        rw [foldl_len]; simp only [stepWire, List.length_append, List.length_ofFn, List.length_singleton]
        change 10 + 1 + x2.size = 28; omega
      conv_lhs => rw [← hLen28]
      rw [getD_step_at]
      simp only [hEvalAnd, hEvalOr, hEvalNot, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rfl
    rw [hW, ← hF_eq_P x]
    cases hfx : F x with
    | false =>
      have hs := hSafe x hfx
      rw [hs.1, hs.2]; rfl
    | true =>
      cases h3 : (x2.wires ({ gates := [x1], output := 0 : Circuit }.wires (List.ofFn x))).getD x3 false with
      | true => rfl
      | false =>
        cases h4 : (x2.wires ({ gates := [x1], output := 0 : Circuit }.wires (List.ofFn x))).getD x4 false with
        | true => rfl
        | false => exact False.elim (hNoUncov ⟨x, hfx, h3, h4⟩)
  exact hNormalize 19 (le_refl 19) D hSzD hFanD hEvalD (fun _ => hTopD)
