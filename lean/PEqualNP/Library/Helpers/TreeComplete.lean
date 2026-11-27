import PEqualNP.Defs
import Mathlib.Tactic

/-!
# Completeness of tree-like Res(lin) over the integers

Every unsatisfiable set of clauses over a finite variable type has a tree-like Res(lin)
refutation: branch on the variables one by one, refute each total assignment by the axiom of a
clause it falsifies, and merge two branches on `v` by subtracting `v = 0` from `v = 1`.
-/

namespace PEqualNP.Library.Helpers.TreeComplete

open PEqualNP.Search PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V]

theorem holds_litQEq (a : V → Bool) (v : V) (b : Bool) :
    QEq.Holds a (litQEq (v, b)) ↔ a v = b := by
  unfold QEq.Holds litQEq
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  cases a v <;> cases b <;> simp

/-- The line saying that `a` differs from `ρ` on some variable of `ds`. -/
def nline (ds : List V) (ρ : V → Bool) : QLine V :=
  ds.map fun v => litQEq (v, !ρ v)

theorem holds_nline (a : V → Bool) (ds : List V) (ρ : V → Bool) :
    QLine.Holds a (nline ds ρ) ↔ ∃ v ∈ ds, a v ≠ ρ v := by
  unfold QLine.Holds nline
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, ⟨v, hv, rfl⟩, h⟩
    exact ⟨v, hv, by rw [(holds_litQEq a v _).1 h]; cases ρ v <;> simp⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨_, ⟨v, hv, rfl⟩, by rw [holds_litQEq]; revert h; cases a v <;> cases ρ v <;> simp⟩

theorem step (F : Set (Clause V)) (hF : ¬ Satisfiable F) :
    ∀ (us ds : List V), (∀ v, v ∈ ds ∨ v ∈ us) → ∀ ρ : V → Bool,
      Nonempty (ResLinQTree F (nline ds ρ)) := by
  intro us
  induction us with
  | nil =>
    intro ds hcov ρ
    have hρ : ¬ Satisfies ρ F := fun h => hF ⟨ρ, h⟩
    unfold Satisfies at hρ
    simp only [not_forall, exists_prop] at hρ
    obtain ⟨C, hC, hCf⟩ := hρ
    refine ⟨ResLinQTree.weaken (C := C.toList.map litQEq)
      (ResLinQTree.ax C hC (fun e => by simp [eq_comm])) ?_⟩
    intro a ha
    rw [holds_nline]
    obtain ⟨e, he, hae⟩ := ha
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 he
    have hl' : l ∈ C := Finset.mem_toList.1 hl
    obtain ⟨v, b⟩ := l
    have h1 : a v = b := (holds_litQEq a v b).1 hae
    have h2 : ρ v ≠ b := fun h => hCf ⟨(v, b), hl', h⟩
    refine ⟨v, ?_, by rw [h1]; exact fun h => h2 h.symm⟩
    rcases hcov v with h | h
    · exact h
    · simp at h
  | cons u us ih =>
    intro ds hcov ρ
    by_cases hu : u ∈ ds
    · refine ih ds (fun v => ?_) ρ
      rcases hcov v with h | h
      · exact Or.inl h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl hu
        · exact Or.inr h
    · have hcov' : ∀ v, v ∈ u :: ds ∨ v ∈ us := by
        intro v
        rcases hcov v with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl List.mem_cons_self
          · exact Or.inr h
      obtain ⟨T1⟩ := ih (u :: ds) hcov' (Function.update ρ u true)
      obtain ⟨T0⟩ := ih (u :: ds) hcov' (Function.update ρ u false)
      have R := ResLinQTree.res 1 (-1) T1 T0
      refine ⟨ResLinQTree.weaken R ?_⟩
      intro a ha
      obtain ⟨e, he, hae⟩ := ha
      rcases List.mem_cons.1 he with rfl | he
      · exfalso
        unfold QEq.Holds at hae
        simp [litQEq] at hae
      · have key : ∀ b, QLine.Holds a (nline ds (Function.update ρ u b)) →
            QLine.Holds a (nline ds ρ) := by
          intro b hb
          rw [holds_nline] at hb ⊢
          obtain ⟨v, hv, hne⟩ := hb
          have : v ≠ u := fun h => hu (h ▸ hv)
          exact ⟨v, hv, by rwa [Function.update_of_ne this] at hne⟩
        rcases List.mem_append.1 he with he | he
        · exact key true ⟨e, he, hae⟩
        · exact key false ⟨e, he, hae⟩

/-- Completeness: an unsatisfiable set of clauses has a tree-like Res(lin) refutation. -/
theorem complete (F : Set (Clause V)) (hF : ¬ Satisfiable F) :
    Nonempty (ResLinQTree F []) :=
  step F hF Finset.univ.toList [] (fun v => Or.inr (Finset.mem_toList.2 (Finset.mem_univ v)))
    (fun _ => false)

end PEqualNP.Library.Helpers.TreeComplete
