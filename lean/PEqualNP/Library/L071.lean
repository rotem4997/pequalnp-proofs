import PEqualNP.Defs
import PEqualNP.Library.Helpers.OracleCanonIn
import PEqualNP.Library.Helpers.OracleQueryLength

open PEqualNP.Library.Helpers.Enum PEqualNP.Library.Helpers.EnumIn Turing Polynomial in
/-- Baker-Gill-Solovay, verifier half: the oracle polynomial-time verifiers are covered by a
sequence, each answer on a pair depending on the oracle only through strings of polynomially
bounded length. -/
theorem PEqualNP.Library.L071 : ∃ (g : ℕ → Language Bool → Set (List Bool × List Bool)) (r : ℕ → Polynomial ℕ), (∀ (A : Language Bool) (R : Set (List Bool × List Bool)), PEqualNP.Library.OracleDecidableInPolyTime A PEqualNP.Library.encodePair R → ∃ i : ℕ, g i A = R) ∧ ∀ (i : ℕ) (A A' : Language Bool) (x w : List Bool), (∀ y : List Bool, y.length ≤ (r i).eval (x.length + w.length) → (y ∈ A ↔ y ∈ A')) → ((x, w) ∈ g i A ↔ (x, w) ∈ g i A') := by
  have hpoly : Countable (Polynomial ℕ) :=
    Function.Injective.countable (f := fun p : Polynomial ℕ => AddMonoidAlgebra.coeff p)
      (fun p q h => by cases p; cases q; cases h; rfl)
  have hcode : Countable (PEqualNP.Library.Helpers.EnumIn.Code (Bool ⊕ Bool)) := code_countable
  have hne : Nonempty (PEqualNP.Library.Helpers.EnumIn.Code (Bool ⊕ Bool)) :=
    ⟨⟨(1, 1, 1, 1), ⟨0, 0, 0, 0, 0, 0, 0, 0, fun _ => TM2.Stmt.halt, fun _ => true,
      fun _ => 0, 0⟩⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (PEqualNP.Library.Helpers.EnumIn.Code (Bool ⊕ Bool) × Polynomial ℕ)
  refine ⟨fun i A => {q | (e i).1.Accepts A ((e i).2.eval (encodePair q).length) (encodePair q)},
    fun i => X + C (PEqualNP.Library.Machines.maxPush (e i).1.2.toM.tm) * (e i).2, ?_, ?_⟩
  · rintro A R ⟨p, f, M, ein, eout, hf, hrun⟩
    obtain ⟨i, hi⟩ := he (canon M ein.symm (eout.symm true), p)
    refine ⟨i, ?_⟩
    ext q
    show (e i).1.Accepts A ((e i).2.eval (encodePair q).length) (encodePair q) ↔ q ∈ R
    rw [hi]
    refine (accepts_canon M ein.symm (eout.symm true) A _ _).trans ?_
    rw [hf q]
    obtain ⟨⟨⟨n, hn⟩, hle⟩⟩ := hrun q
    have hn' : runFrom M A (initList M.tm ((encodePair q).map ein.symm)) n =
        some (haltC M [eout.symm (f q)]) := hn
    constructor
    · rintro ⟨s, _, hs⟩
      have := runFrom_halt_unique M A _ _ _ _ _ hn' hs
      simp only [List.cons.injEq, and_true] at this
      exact eout.symm.injective this
    · intro hfq
      rw [hfq] at hn'
      exact ⟨n, hle, hn'⟩
  · intro i A A' x w h
    have hlen : (encodePair (x, w)).length = x.length + w.length := by
      simp [encodePair]
    show PEqualNP.Library.Helpers.Enum.Accepts (e i).1.2.toM A (e i).1.2.ιin (e i).1.2.o _ _ ↔
      PEqualNP.Library.Helpers.Enum.Accepts (e i).1.2.toM A' (e i).1.2.ιin (e i).1.2.o _ _
    refine accepts_congr_short _ A _ _ _ _ A' (fun y hy => h y ?_)
    rw [hlen] at hy
    simpa [hlen] using hy
