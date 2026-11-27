import PEqualNP.Defs

-- A cut of the Petersen-graph OR-substitution step along the two things the
-- argument does: building the substituted circuit, and counting the gates any
-- circuit of the model needs for the function the point sets pin down.
--
-- The point sets decode. Each of the fifteen numbers of the positive list has
-- exactly two bits, so it is a pair of inputs: (0,1) (1,2) (2,3) (0,4) (3,4)
-- (0,5) (1,6) (2,7) (5,7) (3,8) (5,8) (6,8) (4,9) (6,9) (7,9). That graph is
-- 3-regular on ten vertices with no triangle and no two vertices sharing two
-- neighbours, so it has girth five: the Petersen graph. The fifteen numbers of
-- the negative list are exactly its fifteen maximal independent sets, the ten
-- of size three and the five of size four. A monotone function true on every
-- edge and false on every maximal independent set is forced to be the graph
-- function of the Petersen graph with no further inputs, since every input set
-- either contains an edge or sits inside a maximal independent set.
--
-- substOneGate is the surgery. The clause on the gates says every gate whose
-- output wire is at most w reads no input 0, so the cone of wire w avoids
-- input 0, wire w has the same value before and after input 0 is forced false,
-- and every gate that does read input 0 comes after wire w. Insert one OR gate
-- directly above wire w reading input 0 and wire w, and send every later read
-- of input 0 to it: one extra gate buys the whole substitution, the model is
-- kept, and the new circuit computes the substituted function on the nose.
-- This is the half that carries the twelve positive points where bit 0 is
-- clear and the wire value is unknown: the new circuit computes the
-- substituted function at every assignment, so no case split on the wire is
-- left to make.
--
-- orAssemblyCost and coverSixAnds are the count. In a graph with no four-cycle
-- two vertices share at most one neighbour, so an AND gate of the model that
-- stays below the graph function spans a star. Fifteen edges have to be merged
-- into one output wire, which takes fourteen OR gates however the stars are
-- chosen, so a circuit with t AND gates has at least 14 + t gates in all; and
-- the star centres cover every edge, so there are at least as many AND gates
-- as the least vertex cover, which on the Petersen graph is six. Together they
-- put twenty gates under any circuit of the model meeting both point lists,
-- against the nineteen the surgery leaves, so the two halves meet with slack
-- two and neither says anything on its own: the first produces a circuit and
-- no bound, the second bounds a circuit and produces none.
theorem PEqualNP.Outside.R_meta_7893_1
    (substOneGate : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ), PEqualNP.TopForm.IsAO2 (10 : ℕ) C → w ≠ (0 : ℕ) → w < (10 : ℕ) + C.size → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), (10 : ℕ) + j ≤ w → C.gates[j]? = Option.some g → (0 : ℕ) ∉ g.inputs) → ∃ (E : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) E ∧ E.size ≤ C.size + (1 : ℕ) ∧ ∀ (y : Fin (10 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (10 : ℕ) E y = PEqualNP.MetaComplexity.circuitFun (10 : ℕ) C (Function.update y (0 : Fin (10 : ℕ)) (y (0 : Fin (10 : ℕ)) || (C.wires (List.ofFn (Function.update y (0 : Fin (10 : ℕ)) Bool.false))).getD w Bool.false)))
    (orAssemblyCost : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (t : ℕ) (f : Fin t → ℕ), PEqualNP.TopForm.IsAO2 (10 : ℕ) C → (∀ x10 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], PEqualNP.MetaComplexity.circuitFun (10 : ℕ) C (fun (x11 : Fin (10 : ℕ)) => x10.testBit ↑x11) = Bool.true) → (∀ x10 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], PEqualNP.MetaComplexity.circuitFun (10 : ℕ) C (fun (x11 : Fin (10 : ℕ)) => x10.testBit ↑x11) = Bool.false) → Function.Injective f → (∀ (i : Fin t), f i < C.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (f i)).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (14 : ℕ) + t ≤ C.size)
    (coverSixAnds : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) C → (∀ x10 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], PEqualNP.MetaComplexity.circuitFun (10 : ℕ) C (fun (x11 : Fin (10 : ℕ)) => x10.testBit ↑x11) = Bool.true) → (∀ x10 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], PEqualNP.MetaComplexity.circuitFun (10 : ℕ) C (fun (x11 : Fin (10 : ℕ)) => x10.testBit ↑x11) = Bool.false) → ∃ (f : Fin (6 : ℕ) → ℕ), Function.Injective f ∧ ∀ (i : Fin (6 : ℕ)), f i < C.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (f i)).op = PEqualNP.CircuitLowerBounds.GateOp.and) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 →     (16 : ℕ) ≤ x1.size ∧ x1.size ≤ (18 : ℕ) →       (x2 ≠ (0 : ℕ) ∧ x2 < (10 : ℕ) + x1.size ∧ ∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), (10 : ℕ) + x5 ≤ x2 → x1.gates[x5]? = Option.some x6 → (0 : ℕ) ∉ x6.inputs) →         have x6 : ℕ → Fin (10 : ℕ) → Bool := fun (x6 : ℕ) (x7 : Fin (10 : ℕ)) => x6.testBit ↑x7;         have x7 : ℕ → Bool := fun (x7 : ℕ) => (x1.wires (List.ofFn (Function.update (x6 x7) (0 : Fin (10 : ℕ)) Bool.false))).getD x2 Bool.false;         have x8 : ℕ → Bool := fun (x8 : ℕ) => PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 (Function.update (x6 x8) (0 : Fin (10 : ℕ)) (x6 x8 (0 : Fin (10 : ℕ)) || x7 x8));         (∀ x9 ∈ [(50 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ)], x7 x9 = Bool.false) → ¬((∀ x10 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x8 x10 = Bool.true) ∧ ∀ x10 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x8 x10 = Bool.false) :=
    fun C w hao hsz hw hX hspec => by
  obtain ⟨E, hEao, hEsize, hEfun⟩ := substOneGate C w hao hw.1 hw.2.1 hw.2.2
  have hpos : ∀ x10 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], PEqualNP.MetaComplexity.circuitFun (10 : ℕ) E (fun (x11 : Fin (10 : ℕ)) => x10.testBit ↑x11) = Bool.true := by
    intro n hn
    exact (hEfun _).trans (hspec.1 n hn)
  have hneg : ∀ x10 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], PEqualNP.MetaComplexity.circuitFun (10 : ℕ) E (fun (x11 : Fin (10 : ℕ)) => x10.testBit ↑x11) = Bool.false := by
    intro n hn
    exact (hEfun _).trans (hspec.2 n hn)
  obtain ⟨f, hinj, hroster⟩ := coverSixAnds E hEao hpos hneg
  have h20 : (20 : ℕ) ≤ E.size :=
    orAssemblyCost E (6 : ℕ) f hEao hpos hneg hinj hroster
  exact Nat.not_succ_le_self (19 : ℕ)
    (Nat.le_trans h20 (Nat.le_trans hEsize (Nat.succ_le_succ hsz.2)))
