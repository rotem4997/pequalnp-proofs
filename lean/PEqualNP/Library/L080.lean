import PEqualNP.Library.L071
import Mathlib.Tactic

/-- For every oracle some language is outside `NP^A`. -/
theorem PEqualNP.Library.L080 : ∀ A : Language Bool, ∃ L : Language Bool, L ∉ PEqualNP.Library.OracleNP A := by
  intro A
  obtain ⟨g, r, hcover, -⟩ := PEqualNP.Library.L071
  have : Countable (Polynomial ℕ) := by
    refine Function.Injective.countable
      (f := fun p : Polynomial ℕ => (List.range (p.natDegree + 1)).map p.coeff) ?_
    intro p q h
    have hl := congrArg List.length h
    simp only [List.length_map, List.length_range] at hl
    have hd : p.natDegree = q.natDegree := by omega
    ext n
    by_cases hn : n ≤ p.natDegree
    · have := congrArg (fun l : List ℕ => l.getD n 0) h
      simpa [List.getD_eq_getElem?_getD, hn, hd ▸ hn, Nat.lt_succ_of_le hn,
        Nat.lt_succ_of_le (hd ▸ hn)] using this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  obtain ⟨e, he⟩ := exists_surjective_nat (ℕ × Polynomial ℕ)
  -- the language decided by index `i` and witness bound `p`
  let lang : ℕ × Polynomial ℕ → Set (List Bool) := fun ip =>
    {x | ∃ w : List Bool, w.length ≤ ip.2.eval x.length ∧ (x, w) ∈ g ip.1 A}
  refine ⟨{x : List Bool | x ∉ lang (e x.length)}, fun hL => ?_⟩
  obtain ⟨R, p, hR, hx⟩ := hL
  obtain ⟨i, hi⟩ := hcover A R hR
  obtain ⟨k, hk⟩ := he (i, p)
  have h1 := hx (List.replicate k true)
  have h2 : (List.replicate k true ∈ ({x : List Bool | x ∉ lang (e x.length)} : Language Bool)) ↔
      List.replicate k true ∉ lang (i, p) := by
    show (List.replicate k true ∉ lang (e (List.replicate k true).length)) ↔ _
    rw [List.length_replicate, hk]
  have h3 : List.replicate k true ∈ lang (i, p) ↔
      ∃ w : List Bool, w.length ≤ p.eval (List.replicate k true).length ∧ (List.replicate k true, w) ∈ R := by
    show (∃ w : List Bool, w.length ≤ p.eval (List.replicate k true).length ∧ (List.replicate k true, w) ∈ g i A) ↔ _
    rw [hi]
  exact iff_not_self (h3.trans (Iff.trans h1.symm h2))
