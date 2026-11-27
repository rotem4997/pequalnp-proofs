import PEqualNP.Defs

-- A cut of the 13 + 13 circulant lattice step along the two kinds of step it needs.
-- The 22 masks hold one 26-bit row pattern each, split into two 13-bit blocks, and the
-- 285 indices are the 22 by 13 grid with the cell (0, 0) dropped. Generator 13 * q + s
-- holds the cell (r, c) exactly when block q of mask r carries the bit (s - c) mod 13,
-- so the 26 sets are two families of 13 cyclic shifts. Rows 0 to 3 carry the offsets
-- 0, 1, 3, 9 in block 0 and 0 in block 1, and 0, 1, 3, 9 is a perfect difference set
-- mod 13: the point-line incidence of the projective plane of order 3. The target, the
-- first 51 indices, is rows 0 to 3 in full, and it is exactly the union of the 52
-- pairwise terms S(0, a) cap S(1, b) with a - b in 0, 1, 3, 9, each a single cell and
-- one of them empty at the dropped cell. No other pair of generators meets inside the
-- target, and since the incidence has no four-cycle, a pair of generator families whose
-- product stays inside the target is always a star: batching is impossible.
-- hAssembly is the half the star normal form controls: the unions. Each star needs the
-- union of a whole line of the plane, two lines share one point, so no union of two or
-- more line members is reusable; covering the 51 cells with t stars costs 51 - t leaf
-- unions and t - 1 more to assemble them, which is 50 whatever t is. So 50 steps sit
-- beside any roster of steps that are not unions.
-- hHeads is the half it does not control: the intersections. A single intersection
-- harvests at most one star, hence at most 4 of the 51 cells, so 13 star heads are
-- needed; the pair the step forbids supplies one of them for free as its own final
-- intersection, leaving 12 inside the list.
-- Together they force 50 + 12 = 62 steps against a budget of 61.

theorem PEqualNP.Outside.R_meta_4955_2
    (hAssembly : have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))) (x4 : ℕ) (x9 : Fin x4 → ℕ), (∀ (x5 : Fin x3.length), have x6 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x5) x3; ∃ x7 ∈ x6, ∃ x8 ∈ x6, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x3.get x5 ∉ x6 ∧ (x3.get x5 = x7 ∩ x8 ∨ x3.get x5 = x7 ∪ x8)) → (∃ x6 ∈ x2 ++ x3, ∃ x8 ∈ x2 ++ x3, ¬x6 ⊆ x8 ∧ ¬x8 ⊆ x6 ∧ x6 ∩ x8 = (List.filter (fun (x12 : Fin (285 : ℕ)) => Decidable.decide (↑x12 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset) → Function.Injective x9 → (∀ (x10 : Fin x4), x9 x10 < x3.length ∧ ¬(∃ x7 ∈ x2 ++ List.take (x9 x10) x3, ∃ x8 ∈ x2 ++ List.take (x9 x10) x3, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x3.getD (x9 x10) ∅ = x7 ∪ x8)) → (50 : ℕ) + x4 ≤ x3.length)
    (hHeads : have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))), (∀ (x5 : Fin x3.length), have x6 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x5) x3; ∃ x7 ∈ x6, ∃ x8 ∈ x6, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x3.get x5 ∉ x6 ∧ (x3.get x5 = x7 ∩ x8 ∨ x3.get x5 = x7 ∪ x8)) → (∃ x6 ∈ x2 ++ x3, ∃ x8 ∈ x2 ++ x3, ¬x6 ⊆ x8 ∧ ¬x8 ⊆ x6 ∧ x6 ∩ x8 = (List.filter (fun (x12 : Fin (285 : ℕ)) => Decidable.decide (↑x12 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset) → ∃ (x9 : Fin (12 : ℕ) → ℕ), Function.Injective x9 ∧ ∀ (x10 : Fin (12 : ℕ)), x9 x10 < x3.length ∧ ¬(∃ x7 ∈ x2 ++ List.take (x9 x10) x3, ∃ x8 ∈ x2 ++ List.take (x9 x10) x3, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x3.getD (x9 x10) ∅ = x7 ∪ x8)) :
    have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))),   x3.length ≤ (61 : ℕ) →     (∀ (x5 : Fin x3.length),         have x6 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x5) x3;         ∃ x7 ∈ x6, ∃ x8 ∈ x6, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x3.get x5 ∉ x6 ∧ (x3.get x5 = x7 ∩ x8 ∨ x3.get x5 = x7 ∪ x8)) →       ∀ x6 ∈ x2 ++ x3, ∀ x8 ∈ x2 ++ x3, ¬x6 ⊆ x8 → ¬x8 ⊆ x6 → x6 ∩ x8 ≠ (List.filter (fun (x12 : Fin (285 : ℕ)) => Decidable.decide (↑x12 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset := by
  intro g1 g2 L hlen hderiv X hX Y hY hXY hYX heq
  obtain ⟨f, hinj, hros⟩ := hHeads L hderiv ⟨X, hX, Y, hY, hXY, hYX, heq⟩
  have hb : (62 : ℕ) ≤ L.length :=
    hAssembly L (12 : ℕ) f hderiv ⟨X, hX, Y, hY, hXY, hYX, heq⟩ hinj hros
  exact Nat.not_succ_le_self (61 : ℕ) (Nat.le_trans hb hlen)
