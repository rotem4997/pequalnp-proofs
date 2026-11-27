import PEqualNP.Library.SearchHelpers.Weight

/-- A k-CNF formula whose clauses each have exactly `k` literals on `k` distinct variables, and
which has fewer than `2^k` clauses, is satisfiable. -/
theorem PEqualNP.Library.L028 : ∀ (k : ℕ) (φ : PEqualNP.Search.CNF),
    (∀ c ∈ φ, c.length = k ∧ (c.map Prod.fst).Nodup) → φ.length < 2 ^ k →
    PEqualNP.Search.Satisfiable φ := by
  intro k φ hc hlen
  open PEqualNP.Library.SearchHelpers in
  have hwt : ∀ ψ : PEqualNP.Search.CNF, (∀ c ∈ ψ, c.length = k) →
      wt ψ = ψ.length * (2 : ℚ)⁻¹ ^ k := by
    intro ψ hψ
    induction ψ with
    | nil => simp [wt]
    | cons c ψ ih =>
      rw [wt_cons, hψ c List.mem_cons_self, ih (fun c' h' => hψ c' (List.mem_cons_of_mem _ h'))]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
  apply PEqualNP.Library.SearchHelpers.satisfiable_of_wt_lt_one
    (((φ.flatten).map Prod.fst).sum + 1) φ
  · intro c hc' l hl
    have : l.1 ≤ ((φ.flatten).map Prod.fst).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem (List.mem_flatten.mpr ⟨c, hc', hl⟩))
    omega
  · exact fun c h => (hc c h).2
  · rw [hwt φ (fun c h => (hc c h).1), inv_pow]
    have hpos : (0 : ℚ) < 2 ^ k := by positivity
    rw [← div_eq_mul_inv, div_lt_one hpos]
    exact_mod_cast hlen
