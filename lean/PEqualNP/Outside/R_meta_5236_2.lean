import PEqualNP.Defs

-- Counting cut of L-meta-5236 (Petersen edge function, 18 gates after the extra input
-- x0 or x2, three or four NOT gates).
-- Put the extra input back as a first OR gate reading wires 0 and 2: the wire numbers of
-- the remaining gates do not move, and the result is a 19 gate circuit on the ten inputs that
-- computes the edge function of the Petersen graph, with the same NOT gates.
-- Child count (verbatim the desk step L-meta-4725): every fan-in-two circuit on ten inputs computing the Petersen edge function has
-- at least 15 AND or OR gates. This is the first-boundary branch count of L-meta-2165 run on
-- the full Petersen graph: removing twin groups needs 6 rounds there (5 on Petersen minus a
-- vertex, which gave 13 in L-meta-2165), so at least 6 wires are read twice and the AND or OR
-- gates number at least 10 - 1 + 6. Girth 5 gives the alternate-neighbor witnesses.
-- With 4 NOT gates this forces exactly 18 gates, with 3 NOT gates 17 or 18 gates: the
-- children four and three are these tight cases, where every extra read is a forced branch.
theorem PEqualNP.Outside.R_meta_5236_2
    (count : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (10 : ℕ) → Bool), x2.eval (List.ofFn x4) = x1 x4) → (15 : ℕ) + PEqualNP.NotBracket.notCount x2 ≤ x2.size)
    (four : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 11 C → 11 ≤ C.output → C.output < 11 + C.size →
      PEqualNP.NotBracket.notCount C = 4 → C.size = 18 →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) ≠ (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))))
    (three : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 11 C → 11 ≤ C.output → C.output < 11 + C.size →
      PEqualNP.NotBracket.notCount C = 3 → 17 ≤ C.size → C.size ≤ 18 →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) ≠ (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (11 : ℕ) ≤ x1.output → x1.output < (11 : ℕ) + x1.size → (3 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (4 : ℕ) → ∃ (x9 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x9 ++ [x9 (0 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ))]) ≠ (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))) := by
  intro C hfan hrb hsize hlo hhi hk3 hk4
  by_contra hcon
  push Not at hcon
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ :: C.gates, C.output⟩
  have hDfan : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp
    · exact hfan g hg
  have hDeval : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))) := by
    intro x
    have key : ((List.ofFn x).getD 0 false || ((List.ofFn x).getD 2 false || false)) = (x 0 || x 2) := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Bool.or_false]
      rfl
    have he : D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [x 0 || x 2]) := by
      show (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn x ++ [(List.ofFn x).getD 0 false || ((List.ofFn x).getD 2 false || false)])).getD
          C.output false = _
      rw [key]
      rfl
    rw [he]
    exact hcon x
  have count' : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)))) →
      15 + PEqualNP.NotBracket.notCount C ≤ C.size := count
  have hc := count' D hDfan hDeval
  have hn : PEqualNP.NotBracket.notCount D = PEqualNP.NotBracket.notCount C := rfl
  have hs : D.size = C.size + 1 := rfl
  rw [hn, hs] at hc
  by_cases h4 : PEqualNP.NotBracket.notCount C = 4
  · obtain ⟨x, hx⟩ := four C hfan hrb hlo hhi h4 (by omega)
    exact hx (hcon x)
  · obtain ⟨x, hx⟩ := three C hfan hrb hlo hhi (by omega) (by omega) hsize
    exact hx (hcon x)
