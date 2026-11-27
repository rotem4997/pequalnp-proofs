import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Bit positions 0 through 20 are the graph edges. The other positions are maximal independent sets.
-- The last input column is the disjunction of the first two vertex columns.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2278_58
    (packed : ∀ (n : ℕ) (inputs : List (BitVec n)) (C : Circuit), Monotone2 C →
    ∃ S : List (BitVec n), S.length ≤ C.size ∧
    (∀ j : Fin S.length, ∃ a ∈ (0 :: BitVec.allOnes n :: (inputs ++ S.take j)), ∃ b ∈ (0 :: BitVec.allOnes n :: (inputs ++ S.take j)),
      S.get j = a &&& b ∨ S.get j = a ||| b) ∧
    ∃ t ∈ (0 :: BitVec.allOnes n :: (inputs ++ S)), ∀ k : Fin n,
      t.getLsbD k = C.eval (inputs.map fun v => v.getLsbD k))
    (obstruction : let base : List (BitVec 58) :=
      0 :: BitVec.allOnes 58 :: [95229015649943559, 63038587666488, 256462815680, 4292497062759936,
      8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
      155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984,
      270286071508633728, 288160007407550752, 95274182876594239]
    ∀ S : List (BitVec 58), S.length ≤ 25 →
      (∀ j : Fin S.length, let pool := base ++ S.take j
        ∃ a ∈ pool, ∃ b ∈ pool, S.get j = a &&& b ∨ S.get j = a ||| b) →
      (2097151 : BitVec 58) ∉ base ++ S) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → (x4.eval (List.ofFn x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 (0 : Fin (14 : ℕ)), x6 (1 : Fin (14 : ℕ))]]) = Bool.true ↔ x2 x6)) → (26 : ℕ) ≤ x4.size := by
  let cols : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936,
      8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
      155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984,
      270286071508633728, 288160007407550752]
  let edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
      (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
      (6, 8), (6, 9), (6, 11)]
  let hit := fun x : Fin 14 → Bool =>
    ∃ a b : Fin 14, (a.val, b.val) ∈ edges ∧ x a = true ∧ x b = true
  let ext := fun x : Fin 14 → Bool =>
    (hit x ∧ ∀ i : Fin 14, x i = true → ¬ hit (Function.update x i false)) ∨
    (¬ hit x ∧ ∀ i : Fin 14, x i = false → hit (Function.update x i true))
  let row := fun (k : Fin 58) (i : Fin 14) => (cols.getD i 0).getLsbD k
  let test := fun x : Fin 14 → Bool => edges.any fun e =>
    x (Fin.ofNat 14 e.1) && x (Fin.ofNat 14 e.2)
  have bounds : ∀ e ∈ edges, e.1 < 14 ∧ e.2 < 14 := by
    unfold edges
    decide
  have reflect (x : Fin 14 → Bool) : hit x ↔ test x = true := by
    simp only [hit, test, List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      exact ⟨(a.val,b.val), hab, by simpa using ha, by simpa using hb⟩
    · rintro ⟨⟨a,b⟩, hab, ha,hb⟩
      obtain ⟨hal,hbl⟩ := bounds (a,b) hab
      exact ⟨⟨a,hal⟩, ⟨b,hbl⟩, hab, by simpa [Fin.ofNat, Nat.mod_eq_of_lt hal] using ha,
        by simpa [Fin.ofNat, Nat.mod_eq_of_lt hbl] using hb⟩
  let target : BitVec 58 := 2097151
  let verify := fun (k : Fin 58) =>
    let x := row k
    let p := target.getLsbD k
    (test x == p) && (List.finRange 14).all fun i =>
      if x i = p then test (Function.update x i (!p)) == !p else true
  have allRows : (List.finRange 58).all verify = true := by
    dsimp only [verify, test, target, row, cols, edges]
    decide +kernel
  have cert : ∀ k : Fin 58, ext (row k) ∧ (hit (row k) ↔ (2097151 : BitVec 58).getLsbD k = true) := by
    intro k
    have hk := List.all_eq_true.mp allRows k (by simp)
    change (_ && _) = true at hk
    obtain ⟨hp, hflip⟩ := Bool.and_eq_true_iff.mp hk
    have heq : test (row k) = target.getLsbD k := beq_iff_eq.mp hp
    change _ ∧ (hit (row k) ↔ target.getLsbD k = true)
    refine ⟨?_, by rw [reflect, heq]⟩
    have flips (i : Fin 14) (hi : row k i = target.getLsbD k) :
        test (Function.update (row k) i (!(target.getLsbD k))) = !(target.getLsbD k) := by
      have h := List.all_eq_true.mp hflip i (by simp)
      change (if row k i = target.getLsbD k then _ else true) = true at h
      simpa [hi] using h
    cases hp : target.getLsbD k with
    | false =>
      right
      refine ⟨by rw [reflect, heq, hp]; decide, ?_⟩
      intro i hi
      have hf := flips i (hi.trans hp.symm)
      rw [hp] at hf
      exact (reflect _).2 hf
    | true =>
      left
      refine ⟨(reflect _).2 (heq.trans hp), ?_⟩
      intro i hi
      have hf := flips i (hi.trans hp.symm)
      rw [hp] at hf
      change test (Function.update (row k) i false) = false at hf
      rw [reflect, hf]
      decide
  let inputs := cols ++ [(cols.getD 0 0) ||| (cols.getD 1 0)]
  have inputRows (k : Fin 58) :
      inputs.map (fun v => v.getLsbD k) =
        List.ofFn (row k) ++ [GateOp.or.eval [row k 0, row k 1]] := by
    have h : cols.map (fun v => v.getLsbD k) = List.ofFn (row k) := by
      apply List.ext_getElem
      · simp [cols]
      · intro i hi hi'
        have hi14 : i < 14 := by simpa using hi'
        have hic : i < cols.length := by simpa using hi
        simp only [List.getElem_map, List.getElem_ofFn, row, List.getD_eq_getElem _ _ hic]
    simp only [inputs, List.map_append, List.map_cons, List.map_nil, h, BitVec.getLsbD_or]
    change _ ++ [row k 0 || row k 1] = _ ++ [row k 0 || (row k 1 || false)]
    simp only [Bool.or_false]
  let base : List (BitVec 58) :=
      0 :: BitVec.allOnes 58 :: [95229015649943559, 63038587666488, 256462815680, 4292497062759936,
      8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
      155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984,
      270286071508633728, 288160007407550752, 95274182876594239]
  have hbase : base = 0 :: BitVec.allOnes 58 :: inputs := by
    dsimp only [base, inputs, cols]
    decide +kernel
  change ∀ S : List (BitVec 58), S.length ≤ 25 →
      (∀ j : Fin S.length, let pool := base ++ S.take j
        ∃ a ∈ pool, ∃ b ∈ pool, S.get j = a &&& b ∨ S.get j = a ||| b) →
      (2097151 : BitVec 58) ∉ base ++ S at obstruction
  rw [hbase] at obstruction
  change ∀ C : Circuit, Monotone2 C →
    (∀ x : Fin 14 → Bool, ext x → (C.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x 1]]) = true ↔ hit x)) →
    26 ≤ C.size
  intro C hm hc
  obtain ⟨S, hsize, hsteps, t, ht, htBits⟩ := packed 58 inputs C hm
  have eqTarget : t = 2097151 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    let r : Fin 58 := ⟨k,hk⟩
    change t.getLsbD r = (2097151 : BitVec 58).getLsbD r
    rw [htBits, inputRows]
    exact Bool.eq_iff_iff.2 ((hc (row r) (cert r).1).trans (cert r).2)
  by_contra hsmall
  have hlen : S.length ≤ 25 := by omega
  exact obstruction S hlen hsteps (eqTarget ▸ ht)
