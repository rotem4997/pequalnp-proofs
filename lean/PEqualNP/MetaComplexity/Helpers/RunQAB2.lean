import PEqualNP.MetaComplexity.Helpers.RunQAB1

/-!
# Theorem QA, cases B1 and B2: bricks on the removed circuit and on the chain

* `qa_L_len`, `qa_L_get`: the length of `qaL` and its gate at the new position of a kept gate.
* `qa_next`: in a circuit with an OR chain whose gates are the sole readers of the previous
  chain wire (the clauses of the free-input chain statement), a gate reading an earlier wire
  that is `x_n` or a chain wire is the next chain gate; nothing reads the last chain wire.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunFour2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Loc.Removal

theorem qa_L_len (N : ℕ) (C : Circuit) (g1 g2 o2 jM u1 u2 z : ℕ) :
    (qaL N C g1 g2 o2 jM u1 u2 z).gates.length = cnt (qaS g1 g2 o2 jM) C.gates.length := by
  unfold qaL
  exact len_build _ _ _ _

theorem qa_L_get (N : ℕ) (C : Circuit) (g1 g2 o2 jM u1 u2 z : ℕ) (q : ℕ)
    (hq : q < C.gates.length) (hqS : q ∉ qaS g1 g2 o2 jM) :
    (qaL N C g1 g2 o2 jM u1 u2 z).gates[cnt (qaS g1 g2 o2 jM) q]? =
      some ⟨(C.gates.getD q g0).op, (C.gates.getD q g0).inputs.map fun i =>
        qaRho N (qaS g1 g2 o2 jM) (qaTgt g1 g2 jM u1 u2 z)
          (N + cnt (qaS g1 g2 o2 jM) C.gates.length)
          (if i < N + q then i else N + C.gates.length)⟩ := by
  unfold qaL
  simp only
  rw [get_build _ _ _ hqS hq, qaNorm_getD _ _ q hq]
  simp [rg, List.map_map, Function.comp_def]

theorem qa_next (n : ℕ) (D : Circuit) (k : ℕ) (c : Fin (k + 1) → Fin D.gates.length)
    (hlast : (c (Fin.last k)).val + 1 = D.gates.length)
    (h0 : ∀ j : Fin D.gates.length, qaReads (D.gates.get j) n → j = c 0)
    (hs : ∀ (i : Fin k) (j : Fin D.gates.length),
      qaReads (D.gates.get j) (n + 1 + (c i.castSucc).val) → j = c i.succ)
    (j : Fin D.gates.length) (τ : ℕ) (hr : qaReads (D.gates.get j) τ)
    (hlt : τ < n + 1 + j.val)
    (hτ : τ = n ∨ ∃ i : Fin (k + 1), τ = n + 1 + (c i).val) :
    (τ = n ∧ j = c 0) ∨ ∃ i : Fin k, τ = n + 1 + (c i.castSucc).val ∧ j = c i.succ := by
  rcases hτ with rfl | ⟨i, rfl⟩
  · exact Or.inl ⟨rfl, h0 j hr⟩
  · right
    by_cases hi : i.val < k
    · refine ⟨⟨i.val, hi⟩, ?_, ?_⟩
      · rfl
      · exact hs ⟨i.val, hi⟩ j hr
    · have hil : i = Fin.last k := Fin.ext (by have := i.isLt; simp; omega)
      subst hil
      have := j.isLt
      omega

end PEqualNP.MetaComplexity.Helpers.RunFour2
