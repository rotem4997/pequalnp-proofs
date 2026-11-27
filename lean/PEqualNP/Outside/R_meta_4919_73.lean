import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The rotations by three preserve all supplied features. So does the involution
-- taking point t to 8t and line s to 8s+7 modulo 21. These fourteen permutations
-- have six wire orbits, with least elements 0, 1, 21, 23, 42 and 49.
-- Group unordered operand pairs when their Boolean functions are translates.
-- Keep the least pair for each operation after giving copies their own diagonal.
-- Bit b of row r selects wire b as the partner of the r-th wire above. An AND of nested supports is a copy.
-- An OR whose union is already supplied is also a copy. Keep a single OR
-- diagonal per wire orbit for copies, and bit zero of the last row for each constant.
-- This gives 132 proper ANDs, 120 proper ORs, six copies and both constants.
theorem PEqualNP.Outside.R_meta_4919_73
    (materialize : ∀ (C : Circuit), Monotone2 C → ∀ (p : Bool) (a b : ℕ),
      ∃ E : Circuit, Monotone2 E ∧ E.size ≤ C.size + 1 ∧ ∀ w : List Bool,
        E.eval w = C.eval (w ++ [if a = 56 then p else
          if p then w.getD a false && w.getD b false else w.getD a false || w.getD b false]))
    (search : ∃ (p : Bool) (r : Fin 7) (b : Fin 56) (C : Circuit),
      ((if p then
        ([72055719014180606,72057594035963316,72055848129527808,32347636988116992,70993266782240768,7881299347898368,1] : List ℕ)
       else [72055719014180607,72057594035963318,72055848131624960,32198099120160768,19144696462835712,5066549580791808,1]).getD r.val 0).testBit b.val = true ∧
      Monotone2 C ∧ C.size ≤ 109 ∧ ∀ x : Fin 42 → Bool,
        let L (j : Fin 7) (d : ℕ) := x (Fin.ofNat 42 (21 + (3*j.val+d)%21))
        let w := (List.ofFn x ++ List.ofFn (fun j : Fin 7 => L j 5 || L j 17)) ++
          List.ofFn (fun j : Fin 7 => L j 5 || L j 17 || L j 20)
        let a := ([0,1,21,23,42,49] : List ℕ).getD r.val 56
        C.eval (w ++ [if a = 56 then p else
          if p then w.getD a false && w.getD b false else w.getD a false || w.getD b false]) = true ↔
        ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧
          x u = true ∧ x v = true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (110 : ℕ) ∧       ∀ (x2 : Fin (42 : ℕ) → Bool),         x1.eval               (have x3 : Fin (7 : ℕ) → ℕ → Bool := fun (x3 : Fin (7 : ℕ)) (x4 : ℕ) => x2 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x3 + x4) % (21 : ℕ)));               (List.ofFn x2 ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ)) ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ) || x3 x4 (20 : ℕ)) =             Bool.true ↔           ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true := by
  obtain ⟨p, r, b, C, _, hC, hsize, heval⟩ := search
  obtain ⟨E, hE, hbudget, hprefix⟩ := materialize C hC p
    (([0,1,21,23,42,49] : List ℕ).getD r.val 56) b.val
  refine ⟨E, hE, by omega, ?_⟩
  intro x
  rw [hprefix]
  exact heval x
