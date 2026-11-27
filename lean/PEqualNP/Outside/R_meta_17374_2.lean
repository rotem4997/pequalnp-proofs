import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_17374_2
    (core :
      ∃ R : Circuit, Monotone2 R ∧ ReadsBack 18 R ∧ R.output < 18 + R.size ∧ R.size ≤ 17 ∧
        ∀ r : Fin 14 → Bool,
          circuitFun 18 R (fun i : Fin 18 => if hi : i.val < 14 then r ⟨i.val,hi⟩ else if i.val = 14 then (r 0 || r 1) else if i.val = 15 then (r 1 || r 5) else if i.val = 16 then (r 3 || r 4) else (r 0 || r 2)) =
            ((r 0 && r 10) || (r 1 && r 10) || (r 3 && r 10) || (r 7 && r 10) || (r 1 && r 11) || (r 2 && r 11) || (r 4 && r 11) || (r 8 && r 11) || (r 2 && r 12) || (r 3 && r 12) || (r 5 && r 12) || (r 9 && r 12) || (r 4 && r 13) || (r 5 && r 13) || (r 6 && r 13) || (r 0 && r 13)))
    (splice :
      ∀ (n m : ℕ) (A R : Circuit) (src : Fin m → ℕ),
        Monotone2 A → Monotone2 R → ReadsBack n A → ReadsBack m R →
        A.output < n + A.size → R.output < m + R.size → (∀ i, src i < n + A.size) →
        ∃ C : Circuit, Monotone2 C ∧ C.size ≤ A.size + R.size + 1 ∧
          ∀ z : Fin n → Bool,
            circuitFun n C z =
              (circuitFun n A z ||
                circuitFun m R (fun i => (A.wires (List.ofFn z)).getD (src i) false))) :
    have x1 : (Fin (26 : ℕ) → Bool) → Bool := fun (x1 : Fin (26 : ℕ) → Bool) => Decidable.decide (∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true); ∃ x2 ∈ [(1 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ))], ∃ (x3 : Bool) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (62 : ℕ) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), (∀ (x6 : Fin (26 : ℕ)), x5 x6 = x1 x5 → x1 (Function.update x5 x6 !x5 x6) ≠ x1 x5) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (Fin.snoc x5 (if x3 = Bool.true then x5 (0 : Fin (26 : ℕ)) || x5 x2 else x5 (0 : Fin (26 : ℕ)) && x5 x2)) = x1 x5 := by
  classical
  dsimp only
  obtain ⟨R,hR,hbackR,houtR,hsizeR,hevalR⟩ := core
  let A : Circuit := ⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.or, [27, 6]⟩,
    ⟨.or, [28, 12]⟩,
    ⟨.and, [16, 29]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [31, 6]⟩,
    ⟨.or, [32, 8]⟩,
    ⟨.and, [18, 33]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [35, 9]⟩,
    ⟨.or, [36, 2]⟩,
    ⟨.and, [19, 37]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [39, 10]⟩,
    ⟨.or, [40, 3]⟩,
    ⟨.and, [20, 41]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [43, 11]⟩,
    ⟨.or, [44, 4]⟩,
    ⟨.and, [21, 45]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [47, 12]⟩,
    ⟨.or, [48, 5]⟩,
    ⟨.and, [22, 49]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [51, 0]⟩,
    ⟨.or, [52, 6]⟩,
    ⟨.and, [23, 53]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [55, 1]⟩,
    ⟨.or, [56, 7]⟩,
    ⟨.and, [24, 57]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [59, 12]⟩,
    ⟨.or, [60, 8]⟩,
    ⟨.and, [25, 61]⟩,
    ⟨.or, [30, 34]⟩,
    ⟨.or, [63, 38]⟩,
    ⟨.or, [64, 42]⟩,
    ⟨.or, [65, 46]⟩,
    ⟨.or, [66, 50]⟩,
    ⟨.or, [67, 54]⟩,
    ⟨.or, [68, 58]⟩,
    ⟨.or, [69, 62]⟩
    ], 70⟩
  let src (i : Fin 18) : ℕ := ([0, 1, 2, 3, 4, 5, 7, 9, 10, 11, 13, 14, 15, 17, 26, 31, 27, 59] : List ℕ).getD i.val 0
  have hmonoA : Monotone2 A := by
    delta Monotone2
    simp [A]
  have hsizeA : A.size = 44 := rfl
  have hbackA : ReadsBack 27 A := by
    have hh : ∀ j : Fin A.gates.length, ∀ i ∈ (gateAt A j.val).inputs, i < 27+j.val := by
      decide +kernel
    exact fun j hj => hh ⟨j,hj⟩
  have houtA : A.output < 27 + A.size := by decide
  have hsrc : ∀ i : Fin 18, src i < 27 + A.size := by decide +kernel
  obtain ⟨C,hC,hsize,hval⟩ :=
    splice 27 18 A R src hmonoA hR hbackA hbackR houtA houtR hsrc
  refine ⟨1,by simp,true,C,hC,by omega,?_⟩
  intro x _
  let z : Fin 27 → Bool := Fin.snoc x (x 0 || x 1)
  let r (i : Fin 14) : Bool := x (([0, 1, 2, 3, 4, 5, 7, 9, 10, 11, 13, 14, 15, 17] : List (Fin 26)).getD i.val 0)
  change circuitFun 27 C z = _
  rw [hval]
  have hzs : List.ofFn z = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 0 || x 1] := rfl
  have eAnd (w : List Bool) : GateOp.eval .and w = w.all id := rfl
  have eOr (w : List Bool) : GateOp.eval .or w = w.any id := rfl
  have hAr : circuitFun 27 A z = ((x 3 && x 16) || (x 4 && x 16) || (x 6 && x 16) || (x 12 && x 16) || (x 5 && x 18) || (x 6 && x 18) || (x 8 && x 18) || (x 1 && x 18) || (x 6 && x 19) || (x 7 && x 19) || (x 9 && x 19) || (x 2 && x 19) || (x 7 && x 20) || (x 8 && x 20) || (x 10 && x 20) || (x 3 && x 20) || (x 8 && x 21) || (x 9 && x 21) || (x 11 && x 21) || (x 4 && x 21) || (x 9 && x 22) || (x 10 && x 22) || (x 12 && x 22) || (x 5 && x 22) || (x 10 && x 23) || (x 11 && x 23) || (x 0 && x 23) || (x 6 && x 23) || (x 11 && x 24) || (x 12 && x 24) || (x 1 && x 24) || (x 7 && x 24) || (x 12 && x 25) || (x 0 && x 25) || (x 2 && x 25) || (x 8 && x 25)) := by
    change A.eval (List.ofFn z) = _
    delta Circuit.eval Circuit.wires
    rw [hzs]
    simp [A,eAnd,eOr,Bool.and_or_distrib_left]
    ac_rfl
  have hread : (fun i : Fin 18 => (A.wires (List.ofFn z)).getD (src i) false) =
      (fun i : Fin 18 => if hi : i.val < 14 then r ⟨i.val,hi⟩ else if i.val = 14 then (r 0 || r 1) else if i.val = 15 then (r 1 || r 5) else if i.val = 16 then (r 3 || r 4) else (r 0 || r 2)) := by
    funext i
    delta Circuit.wires
    rw [hzs]
    fin_cases i <;> simp [A,src,r,eAnd,eOr]
  rw [hAr,hread,hevalR r]
  have hfull : ((x 0 && x 13) || (x 1 && x 13) || (x 3 && x 13) || (x 9 && x 13) || (x 1 && x 14) || (x 2 && x 14) || (x 4 && x 14) || (x 10 && x 14) || (x 2 && x 15) || (x 3 && x 15) || (x 5 && x 15) || (x 11 && x 15) || (x 3 && x 16) || (x 4 && x 16) || (x 6 && x 16) || (x 12 && x 16) || (x 4 && x 17) || (x 5 && x 17) || (x 7 && x 17) || (x 0 && x 17) || (x 5 && x 18) || (x 6 && x 18) || (x 8 && x 18) || (x 1 && x 18) || (x 6 && x 19) || (x 7 && x 19) || (x 9 && x 19) || (x 2 && x 19) || (x 7 && x 20) || (x 8 && x 20) || (x 10 && x 20) || (x 3 && x 20) || (x 8 && x 21) || (x 9 && x 21) || (x 11 && x 21) || (x 4 && x 21) || (x 9 && x 22) || (x 10 && x 22) || (x 12 && x 22) || (x 5 && x 22) || (x 10 && x 23) || (x 11 && x 23) || (x 0 && x 23) || (x 6 && x 23) || (x 11 && x 24) || (x 12 && x 24) || (x 1 && x 24) || (x 7 && x 24) || (x 12 && x 25) || (x 0 && x 25) || (x 2 && x 25) || (x 8 && x 25)) =
      decide (∃ p l : Fin 13, (∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
    let E : List (Fin 13 × Fin 13) := [(0,0), (1,0), (3,0), (9,0), (1,1), (2,1), (4,1), (10,1), (2,2), (3,2), (5,2), (11,2), (3,3), (4,3), (6,3), (12,3), (4,4), (5,4), (7,4), (0,4), (5,5), (6,5), (8,5), (1,5), (6,6), (7,6), (9,6), (2,6), (7,7), (8,7), (10,7), (3,7), (8,8), (9,8), (11,8), (4,8), (9,9), (10,9), (12,9), (5,9), (10,10), (11,10), (0,10), (6,10), (11,11), (12,11), (1,11), (7,11), (12,12), (0,12), (2,12), (8,12)]
    have hlist : ((x 0 && x 13) || (x 1 && x 13) || (x 3 && x 13) || (x 9 && x 13) || (x 1 && x 14) || (x 2 && x 14) || (x 4 && x 14) || (x 10 && x 14) || (x 2 && x 15) || (x 3 && x 15) || (x 5 && x 15) || (x 11 && x 15) || (x 3 && x 16) || (x 4 && x 16) || (x 6 && x 16) || (x 12 && x 16) || (x 4 && x 17) || (x 5 && x 17) || (x 7 && x 17) || (x 0 && x 17) || (x 5 && x 18) || (x 6 && x 18) || (x 8 && x 18) || (x 1 && x 18) || (x 6 && x 19) || (x 7 && x 19) || (x 9 && x 19) || (x 2 && x 19) || (x 7 && x 20) || (x 8 && x 20) || (x 10 && x 20) || (x 3 && x 20) || (x 8 && x 21) || (x 9 && x 21) || (x 11 && x 21) || (x 4 && x 21) || (x 9 && x 22) || (x 10 && x 22) || (x 12 && x 22) || (x 5 && x 22) || (x 10 && x 23) || (x 11 && x 23) || (x 0 && x 23) || (x 6 && x 23) || (x 11 && x 24) || (x 12 && x 24) || (x 1 && x 24) || (x 7 && x 24) || (x 12 && x 25) || (x 0 && x 25) || (x 2 && x 25) || (x 8 && x 25)) = E.any
        (fun e => x (Fin.castAdd 13 e.1) && x (Fin.natAdd 13 e.2)) := by
      simp [E] <;> ac_rfl
    rw [hlist]
    have hmem : ∀ p l : Fin 13, (p,l) ∈ E ↔
        ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d := by decide +kernel
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Prod.exists, hmem]
  rw [← hfull]
  simp only [r]
  norm_num
  ac_rfl
