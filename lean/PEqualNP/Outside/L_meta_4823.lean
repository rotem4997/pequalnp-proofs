import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4823
open PEqualNP.CircuitLowerBounds



theorem fm_len : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length = 2) →
    (gs.flatMap Gate.inputs).length = 2 * gs.length := by
  intro gs
  induction gs with
  | nil => intro _; rfl
  | cons g gs ih =>
    intro h
    rw [List.flatMap_cons, List.length_append, ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')),
      h g List.mem_cons_self, List.length_cons]
    omega

end PEqualNP.Outside.L_meta_4823

open PEqualNP.Outside.L_meta_4823 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4823 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → (0 : ℕ) < x1 + x2.size → (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset = Finset.range (x1 + x2.size - (1 : ℕ)) → x1 + ((List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).length - (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset.card) = x2.size + (1 : ℕ) := by
  intro n C hAO hpos hset
  have hlen := fm_len C.gates hAO.2.2
  have hcard : (List.flatMap Gate.inputs C.gates).toFinset.card = n + C.gates.length - 1 := by
    have := congrArg Finset.card hset
    rw [Finset.card_range] at this
    exact this
  have hle := List.toFinset_card_le (List.flatMap Gate.inputs C.gates)
  have hpos' : 0 < n + C.gates.length := hpos
  show n + ((List.flatMap Gate.inputs C.gates).length - (List.flatMap Gate.inputs C.gates).toFinset.card)
    = C.gates.length + 1
  omega
