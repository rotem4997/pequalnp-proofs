import PEqualNP.Defs
import Mathlib.Tactic

/-!
# Helpers: soundness of Res(lin) over the integers

Used by `L-lib-081`.
-/

namespace PEqualNP.Search.Helpers

open PEqualNP.Search

theorem litQEq_holds {V : Type} [Fintype V] [DecidableEq V] (a : V → Bool) (l : V × Bool)
    (h : a l.1 = l.2) : QEq.Holds a (litQEq l) := by
  simp only [QEq.Holds, litQEq, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ l.1 (fun u => if a u = true then (1 : ℤ) else 0)]
  simp [h]

theorem combo_holds {V : Type} [Fintype V] (a : V → Bool) (e e' : QEq V) (α β : ℤ)
    (h : QEq.Holds a e) (h' : QEq.Holds a e') :
    QEq.Holds a (α • e.1 + β • e'.1, α * e.2 + β * e'.2) := by
  simp only [QEq.Holds] at *
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
  rw [← h, ← h', Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun v _ => by ring

theorem resLinQ_lines_hold {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) (a : V → Bool)
    (ha : PEqualNP.ProofComplexity.Satisfies a F) :
    ∀ π : List (QLine V), IsResLinQDerivation F π → ∀ L ∈ π, QLine.Holds a L := by
  intro π h
  induction h with
  | nil => intro L hL; simp at hL
  | ax C _ hC hL ih =>
    intro L' hL'
    rcases List.mem_cons.mp hL' with rfl | hL'
    · obtain ⟨l, hl, hal⟩ := ha C hC
      exact ⟨litQEq l, (hL _).mpr ⟨l, hl, rfl⟩, litQEq_holds a l hal⟩
    · exact ih L' hL'
  | @res π e e' C D α β _ h1 h2 ih =>
    intro L' hL'
    rcases List.mem_cons.mp hL' with rfl | hL'
    · obtain ⟨f, hf, hfa⟩ := ih _ h1
      obtain ⟨g, hg, hga⟩ := ih _ h2
      rcases List.mem_cons.mp hf with rfl | hf
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨_, List.mem_cons_self, combo_holds a f g α β hfa hga⟩
        · exact ⟨g, List.mem_cons_of_mem _ (List.mem_append_right _ hg), hga⟩
      · exact ⟨f, List.mem_cons_of_mem _ (List.mem_append_left _ hf), hfa⟩
    · exact ih L' hL'
  | weaken _ hC himp ih =>
    intro L' hL'
    rcases List.mem_cons.mp hL' with rfl | hL'
    · exact himp a (ih _ hC)
    · exact ih L' hL'

end PEqualNP.Search.Helpers
