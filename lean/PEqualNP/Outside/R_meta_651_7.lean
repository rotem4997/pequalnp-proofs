import Mathlib
import PEqualNP.Defs

-- Cut by the number of NOT gates. With none, the circuit is made of AND and OR gates only.
-- With at least one, it is the case NOT gates can open. Every circuit is in one of the two.
theorem PEqualNP.Outside.R_meta_651_7 :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 19 → ¬ (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 19 → (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ¬ (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)) →
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) 19 := by
  intro hmono hnot hex
  obtain ⟨C, hfan, hsize, hcomp⟩ := hex
  by_cases hn : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact hnot C hfan hsize hn hcomp
  · apply hmono C _ hsize hcomp
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨g, hg, h⟩ hn
