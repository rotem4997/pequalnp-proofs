import PEqualNP.MetaComplexity.Helpers.RunQACases

/-!
# Theorem QA, cases B1 and B2: the freedom tool

* `qa_free`: a wire that is neither the input `v` nor above `v` (in the read relation of the
  recorded statement) takes the same value at two points that differ only at `v`. This is the
  root form of the paper's FREEDOM step (case B2: `W2`, `Omega`, `B` free of `x_q3`). No
  leastness is used.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunFour2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

theorem qa_free (N : ℕ) (C : Circuit) (v : ℕ) (x x' : Fin N → Bool)
    (hx : ∀ i : Fin N, i.val ≠ v → x i = x' i) :
    ∀ t, t ≠ v → ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length,
        b = N + j.val ∧ qaReads (C.gates.get j) a) v t →
      (wiresFrom C.gates (List.ofFn x)).getD t false =
        (wiresFrom C.gates (List.ofFn x')).getD t false := by
  set R := fun a b : ℕ => ∃ j : Fin C.gates.length, b = N + j.val ∧ qaReads (C.gates.get j) a
    with hR
  have hlen : (List.ofFn x).length = N := List.length_ofFn
  have key := qa_agree C.gates (List.ofFn x) (List.ofFn x') (by simp)
    (fun i => i = v ∨ Relation.TransGen R v i)
    (by
      intro i hi hB
      rw [hlen] at hi
      rw [qa_ofFn_getD _ _ hi, qa_ofFn_getD _ _ hi]
      exact hx ⟨i, hi⟩ (fun h => hB (Or.inl h)))
    (by
      intro j g hj hB ih
      rw [hlen] at hB ih ⊢
      have hjl : j < C.gates.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hj; exact absurd hj (by simp)
      have hg : C.gates.get ⟨j, hjl⟩ = g := by
        rw [List.getElem?_eq_getElem hjl] at hj; exact Option.some.inj hj
      apply qa_eval_congr
      intro a ha
      by_cases hlt : a < N + j
      · rw [if_pos hlt, if_pos hlt]
        apply ih a hlt
        have hRa : R a (N + j) := ⟨⟨j, hjl⟩, rfl, by rw [hg]; exact ha⟩
        rintro (rfl | hta)
        · exact hB (Or.inr (Relation.TransGen.single hRa))
        · exact hB (Or.inr (Relation.TransGen.tail hta hRa))
      · rw [if_neg hlt, if_neg hlt])
  intro t ht hnt
  exact key t (by rintro (h | h) <;> contradiction)

end PEqualNP.MetaComplexity.Helpers.RunFour2
