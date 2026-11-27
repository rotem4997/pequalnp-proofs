import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta135

def edgeBlocks : Fin 8 → Finset (Sym2 (Fin 5)) :=
  ![{s(0,1), s(0,4)}, {s(0,1)}, {s(0,4)},
    {s(1,2), s(2,3)}, {s(1,2)}, {s(2,3)}, {s(3,4)}, {s(3,4)}]

def independentBlocks : Fin 8 → Finset (Finset (Fin 5)) :=
  ![Finset.univ.filter (fun I => 0 ∉ I),
    Finset.univ.filter (fun I => 0 ∈ I ∧ 1 ∉ I),
    Finset.univ.filter (fun I => 0 ∈ I ∧ 4 ∉ I),
    Finset.univ.filter (fun I => 2 ∉ I),
    Finset.univ.filter (fun I => 2 ∈ I ∧ 1 ∉ I),
    Finset.univ.filter (fun I => 2 ∈ I ∧ 3 ∉ I),
    Finset.univ.filter (fun I => 3 ∉ I),
    Finset.univ.filter (fun I => 3 ∈ I ∧ 4 ∉ I)]

def labels : Fin 8 → Fin 5 := ![0,1,4,2,1,3,3,4]

end PEqualNP.Outside.Meta135

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_135 : ∃ (A : Fin 8 → Finset (Sym2 (Fin 5))) (B : Fin 8 → Finset (Finset (Fin 5))) (t : Fin 8 → Fin 5), (∀ i, ∀ e ∈ A i, e ∈ (SimpleGraph.cycleGraph 5).edgeFinset ∧ t i ∈ e) ∧ (∀ i, ∀ I ∈ B i, t i ∉ I) ∧ (∀ e ∈ (SimpleGraph.cycleGraph 5).edgeFinset, ∀ I : Finset (Fin 5), (∀ u ∈ I, ∀ w ∈ I, ¬ (SimpleGraph.cycleGraph 5).Adj u w) → ∃! i : Fin 8, e ∈ A i ∧ I ∈ B i) := by
  refine ⟨PEqualNP.Outside.Meta135.edgeBlocks, PEqualNP.Outside.Meta135.independentBlocks,
    PEqualNP.Outside.Meta135.labels, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · simp only [ExistsUnique]
    decide +kernel
