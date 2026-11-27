import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104

namespace PEqualNP.Outside.L_meta_760

abbrev G : SimpleGraph (Fin 6) where
  Adj i j := i.val / 2 = j.val / 2 ∧ i ≠ j
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

def circ : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩], output := 10 }

theorem tuple (x : Fin 6 → Bool) : (![x 0, x 1, x 2, x 3, x 4, x 5] : Fin 6 → Bool) = x := by
  funext i
  fin_cases i <;> rfl

theorem evalKey : ∀ a0 a1 a2 a3 a4 a5 : Bool,
    circ.eval [a0, a1, a2, a3, a4, a5] = ((a0 && a1) || (a2 && a3) || (a4 && a5)) := by
  decide +kernel

theorem evalOk (x : Fin 6 → Bool) :
    circ.eval (List.ofFn x) = ((x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) := by
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hx]
  exact evalKey _ _ _ _ _ _

theorem fanin : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
theorem adjKey : ∀ a0 a1 a2 a3 a4 a5 : Bool,
    ((∃ i j : Fin 6, G.Adj i j ∧ (![a0, a1, a2, a3, a4, a5] : Fin 6 → Bool) i = true ∧
      (![a0, a1, a2, a3, a4, a5] : Fin 6 → Bool) j = true) ↔
      ((a0 && a1) || (a2 && a3) || (a4 && a5)) = true) := by
  decide +kernel

theorem funEq : (fun x : Fin 6 → Bool =>
      decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) =
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) := by
  funext x
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  have h := adjKey (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
  rw [tuple] at h
  exact h

theorem unique_nbr : ∀ v u w : Fin 6, G.Adj v u → G.Adj v w → u = w := by decide

theorem acyclic : G.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro v w hvw
  rw [SimpleGraph.isBridge_iff]
  rintro ⟨p⟩
  cases p with
  | nil => exact hvw.2 rfl
  | cons h q =>
    rw [SimpleGraph.deleteEdges_adj] at h
    have hu := unique_nbr _ _ _ h.1 hvw
    subst hu
    exact h.2 rfl

theorem cover3 : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) →
    3 ≤ T.card := by
  intro T hT
  have h1 := hT 0 1 (by decide)
  have h2 := hT 2 3 (by decide)
  have h3 := hT 4 5 (by decide)
  have hsub : ∃ a b c : Fin 6, a ∈ T ∧ b ∈ T ∧ c ∈ T ∧
      ({a, b, c} : Finset (Fin 6)).card = 3 := by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      exact ⟨_, _, _, h1, h2, h3, by decide⟩
  obtain ⟨a, b, c, ha, hb, hc, hcard⟩ := hsub
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

theorem edges3 : 3 ≤ G.edgeFinset.card := by
  have hsub : ({s(0, 1), s(2, 3), s(4, 5)} : Finset (Sym2 (Fin 6))) ⊆ G.edgeFinset := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rw [SimpleGraph.mem_edgeFinset]
    rcases he with rfl | rfl | rfl <;> rw [SimpleGraph.mem_edgeSet] <;> decide
  have h1 := Finset.card_le_card hsub
  have h2 : ({s(0, 1), s(2, 3), s(4, 5)} : Finset (Sym2 (Fin 6))).card = 3 := by decide
  omega

theorem main (s : ℕ) : PEqualNP.MetaComplexity.HasCircuitSize 6
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  constructor
  · intro h
    rw [← funEq] at h
    have h1 := PEqualNP.MetaComplexity.L104 6 3 s G acyclic ⟨0, 1, by decide⟩ cover3 h
    have h2 := edges3
    omega
  · intro hs
    exact ⟨circ, fanin, le_trans (by decide) hs, evalOk⟩

end PEqualNP.Outside.L_meta_760

theorem PEqualNP.Outside.L_meta_760 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s :=
  fun s => PEqualNP.Outside.L_meta_760.main s
