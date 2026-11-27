import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The rows 3j meet the seven residue-2 lines in triples. The first seven wires
-- cache pairs of these line variables; the next seven complete the triples.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1475_73
    (hBank : ∃ P : Circuit, Monotone2 P ∧ P.size ≤ 14 ∧ ∀ x : Fin 42 → Bool,
      P.wires (List.ofFn x) = (let L := fun (j : Fin 7) (d : Nat) => x (Fin.ofNat 42 (21 + (3*j.val + d) % 21))
      List.ofFn x ++ List.ofFn (fun j : Fin 7 => L j 5 || L j 17) ++
        List.ofFn (fun j : Fin 7 => (L j 5 || L j 17) || L j 20)))
    (hRest : ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 110 ∧ ∀ x : Fin 42 → Bool,
      D.eval (let L := fun (j : Fin 7) (d : Nat) => x (Fin.ofNat 42 (21 + (3*j.val + d) % 21))
      List.ofFn x ++ List.ofFn (fun j : Fin 7 => L j 5 || L j 17) ++
        List.ofFn (fun j : Fin 7 => (L j 5 || L j 17) || L j 20)) = true ↔
        ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)) ∧ x u = true ∧ x v = true) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧ (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  obtain ⟨P, hp, ps, pw⟩ := hBank
  obtain ⟨D, hd, ds, de⟩ := hRest
  let C : Circuit := ⟨P.gates ++ D.gates, D.output⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    exact (List.mem_append.mp hg).elim (hp g) (hd g)
  · change (P.gates ++ D.gates).length ≤ 124
    change P.gates.length ≤ 14 at ps
    change D.gates.length ≤ 110 at ds
    rw [List.length_append]; omega
  · have incidence : ∀ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ↔ (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)) := by decide +kernel
    intro x
    have wireEval : C.eval (List.ofFn x) = D.eval (P.wires (List.ofFn x)) := by
      let step (w : List Bool) (g : Gate) :=
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      change ((P.gates ++ D.gates).foldl step (List.ofFn x)).getD D.output false =
        (D.gates.foldl step (P.gates.foldl step (List.ofFn x))).getD D.output false
      rw [List.foldl_append]
    rw [wireEval,pw,de]
    simp only [incidence]
