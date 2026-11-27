import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Extract a shared cover using the singleton supports of the two operands
-- of each AND gate. A mixed OR gate can carry an earlier block upward.
-- For a graph without four-cycles, every block is a star. Merge stars with
-- the same center and count their OR gates together before removing sharing.

theorem PEqualNP.Outside.R_meta_2656_481
    (extract : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit), Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
        ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = true →
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      PEqualNP.SharedBlockCost.HasSharedBlockCost G C.size)
    (removeSharing : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : ℕ),
      PEqualNP.TopForm.NoFourCycle G → PEqualNP.SharedBlockCost.HasSharedBlockCost G s →
      PEqualNP.BicliqueBlockCost.HasBlockCost G s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → (∀ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x8]? = Option.some x9 → x9.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x12 : Fin x1 → Bool), (x3.wires (List.ofFn x12)).getD (x1 + x8) Bool.false = Bool.true → ∃ (x14 : Fin x1) (x15 : Fin x1), x2.Adj x14 x15 ∧ x12 x14 = Bool.true ∧ x12 x15 = Bool.true) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x3.size := by
  classical
  intro n G C _ noCycle mono computes soundAnd
  have commonNeighbor : PEqualNP.TopForm.NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro c hc d hd
    have hcAdj : G.Adj a c ∧ G.Adj b c := (Finset.mem_filter.mp hc).2
    have hdAdj : G.Adj a d ∧ G.Adj b d := (Finset.mem_filter.mp hd).2
    by_contra hcd
    exact noCycle a c b d
      (G.ne_of_adj hcAdj.1) hab (G.ne_of_adj hdAdj.1)
      (G.ne_of_adj hcAdj.2).symm hcd (G.ne_of_adj hdAdj.2)
      hcAdj.1 hcAdj.2.symm hdAdj.2 hdAdj.1.symm
  exact removeSharing n G C.size commonNeighbor (extract n G C mono computes soundAnd)
