import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_561 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.AndCount.AndCountCircuit n),
      C.Computes G →
        C.outVars = ∅ ∧ ∀ j ∈ C.outGates, ∀ v : Fin n, C.gateVal {v} j = false := by
  classical
  intro n G C hC
  constructor
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    have hEv : C.eval {v} = true := by
      simp [PEqualNP.AndCount.AndCountCircuit.eval, hv]
    rcases (hC {v}).mp hEv with ⟨a, ha, c, hc, hac⟩
    simp only [Finset.mem_singleton] at ha hc
    subst ha
    subst hc
    exact G.irrefl hac
  · intro j hj v
    have hNot : C.gateVal {v} j ≠ true := by
      intro hTrue
      have hEv : C.eval {v} = true := by
        rw [PEqualNP.AndCount.AndCountCircuit.eval, decide_eq_true_eq]
        exact Or.inr ⟨j, hj, hTrue⟩
      rcases (hC {v}).mp hEv with ⟨a, ha, c, hc, hac⟩
      simp only [Finset.mem_singleton] at ha hc
      subst ha
      subst hc
      exact G.irrefl hac
    cases h : C.gateVal {v} j with
    | false => rfl
    | true => exact (hNot h).elim
