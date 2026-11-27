import PEqualNP.Defs
import PEqualNP.Library.Helpers.OracleCanon

open PEqualNP.Library.Helpers.Enum Turing in
/-- Baker-Gill-Solovay, machine half: the oracle polynomial-time languages are covered by a
sequence of deciders, each depending on the oracle through polynomially many strings. -/
theorem PEqualNP.Library.L058 : ∃ (g : ℕ → Language Bool → Language Bool) (q : ℕ → Polynomial ℕ), (∀ (A L : Language Bool), L ∈ PEqualNP.Library.OracleP A → ∃ i : ℕ, g i A = L) ∧ ∀ (i : ℕ) (A : Language Bool) (x : List Bool), ∃ Q : Finset (List Bool), Q.card ≤ (q i).eval x.length ∧ ∀ A' : Language Bool, (∀ y ∈ Q, y ∈ A ↔ y ∈ A') → (x ∈ g i A ↔ x ∈ g i A') := by
  have hfs : Countable (ℕ →₀ ℕ) := inferInstance
  have hpoly : Countable (Polynomial ℕ) :=
    Function.Injective.countable (f := fun p : Polynomial ℕ => AddMonoidAlgebra.coeff p)
      (fun p q h => by cases p; cases q; cases h; rfl)
  have hne : Nonempty Code :=
    ⟨⟨(1, 1, 1, 1), ⟨0, 0, 0, 0, 0, 0, 0, 0, fun _ => TM2.Stmt.halt, fun _ => true, fun _ => 0, 0⟩⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (Code × Polynomial ℕ)
  refine ⟨fun i A => {x | (e i).1.Accepts A ((e i).2.eval x.length) x}, fun i => (e i).2, ?_, ?_⟩
  · rintro A L ⟨p, f, M, ein, eout, hf, hrun⟩
    obtain ⟨i, hi⟩ := he (canon M ein.symm (eout.symm true), p)
    refine ⟨i, ?_⟩
    ext x
    show (e i).1.Accepts A ((e i).2.eval x.length) x ↔ x ∈ L
    rw [hi]
    exact (accepts_canon M ein.symm (eout.symm true) A _ x).trans
      ((decides_iff_accepts M A f ein eout (fun n => p.eval n) hrun x).symm.trans (hf x).symm)
  · intro i A x
    exact accepts_local (e i).1.2.toM A _ _ _ x
