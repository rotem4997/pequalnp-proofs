import PEqualNP.Library.L058

/-- For every oracle some language is outside `P^A`. -/
theorem PEqualNP.Library.L078 : ∀ A : Language Bool, ∃ L : Language Bool, L ∉ PEqualNP.Library.OracleP A := by
  intro A
  obtain ⟨g, q, hcover, -⟩ := PEqualNP.Library.L058
  refine ⟨{x : List Bool | x ∉ g x.length A}, fun hL => ?_⟩
  obtain ⟨i, hi⟩ := hcover A _ hL
  have key : List.replicate i true ∈ g i A ↔ List.replicate i true ∈ ({x : List Bool | x ∉ g x.length A} : Language Bool) := by rw [hi]; exact Iff.rfl
  have e : (List.replicate i true ∈ ({x : List Bool | x ∉ g x.length A} : Language Bool)) ↔ List.replicate i true ∉ g i A := by
    show (List.replicate i true ∉ g (List.replicate i true).length A) ↔ _
    rw [List.length_replicate]
  rw [e] at key
  exact (iff_not_self key)
