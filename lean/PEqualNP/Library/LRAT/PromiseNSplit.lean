import PEqualNP.Library.LRAT.PromiseN

/-!
# Splitting the NOT-gate refusal formula into pieces

A refutation of `LinkN.enc2` can be too long for one file. Every satisfying assignment of the
formula picks an operation for the last gate (one of 4) and a first source for it (one of `n + s`),
since both at-least-one clauses are clauses of the formula. So the formula is unsatisfiable as
soon as each of the `4 * (n + s)` pieces, the formula with those two choices added as unit
clauses, is: `repN_lower_mask_pieces` turns one certificate per piece into the floor.
-/

namespace PEqualNP.Library.LRAT.PromiseN

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Library.LRAT
  PEqualNP.Library.LRAT.LinkN PEqualNP.Represents

/-- Branching on a clause of the formula: if each of its literals, added as a unit clause, makes
the formula unsatisfiable, the formula is unsatisfiable. -/
theorem unsat_of_branch (F : List (List ℕ)) (c : List ℕ) (hc : c ∈ F)
    (h : ∀ l ∈ c, ¬ FormulaSat (F ++ [[l]])) : ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  obtain ⟨l, hl, hv⟩ := ha c hc
  refine h l hl ⟨a, fun d hd => ?_⟩
  rcases List.mem_append.1 hd with hd | hd
  · exact ha d hd
  · rw [List.mem_singleton.1 hd]
    exact ⟨l, by simp, hv⟩

/-- The piece with operation `o` and first source `k` for the last gate. -/
def piece (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (o k : ℕ) : List (List ℕ) :=
  (enc2 n s g rows ++ [[LinkN.P (ix n s 0 (s - 1) o)]]) ++ [[LinkN.P (ix n s 1 (s - 1) k)]]

theorem opCl_mem (n s : ℕ) (hs : 0 < s) (g : ℕ → Bool) (rows : List ℕ) :
    [LinkN.P (ix n s 0 (s - 1) 0), LinkN.P (ix n s 0 (s - 1) 1), LinkN.P (ix n s 0 (s - 1) 2),
      LinkN.P (ix n s 0 (s - 1) 3)] ∈ enc2 n s g rows := by
  have h : [LinkN.P (ix n s 0 (s - 1) 0), LinkN.P (ix n s 0 (s - 1) 1), LinkN.P (ix n s 0 (s - 1) 2),
      LinkN.P (ix n s 0 (s - 1) 3)] ∈ fOp n s :=
    List.mem_map.2 ⟨s - 1, List.mem_range.2 (by omega), rfl⟩
  simp only [enc2, enc, List.mem_append, h, true_or]

theorem s1Cl_mem (n s : ℕ) (hs : 0 < s) (g : ℕ → Bool) (rows : List ℕ) :
    ((List.range (n + (s - 1) + 1)).map fun k => LinkN.P (ix n s 1 (s - 1) k)) ∈ enc2 n s g rows := by
  have h : ((List.range (n + (s - 1) + 1)).map fun k => LinkN.P (ix n s 1 (s - 1) k)) ∈
      fSrcAlo n s :=
    List.mem_flatMap.2 ⟨1, by simp, List.mem_map.2 ⟨s - 1, List.mem_range.2 (by omega), rfl⟩⟩
  simp only [enc2, enc, List.mem_append, h, true_or, or_true]

/-- The formula is unsatisfiable when every piece is. -/
theorem unsat_of_pieces (n s : ℕ) (hs : 0 < s) (g : ℕ → Bool) (rows : List ℕ)
    (h : ∀ o < 4, ∀ k < n + s, ¬ FormulaSat (piece n s g rows o k)) :
    ¬ FormulaSat (enc2 n s g rows) := by
  refine unsat_of_branch _ _ (opCl_mem n s hs g rows) fun l hl => ?_
  have ho : ∃ o < 4, l = LinkN.P (ix n s 0 (s - 1) o) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    exacts [⟨0, by omega, rfl⟩, ⟨1, by omega, rfl⟩, ⟨2, by omega, rfl⟩, ⟨3, by omega, rfl⟩]
  obtain ⟨o, ho, rfl⟩ := ho
  refine unsat_of_branch _ _ (List.mem_append_left _ (s1Cl_mem n s hs g rows)) fun l' hl' => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl'
  exact h o ho k (by have := List.mem_range.1 hk; omega)

/-- The floor from one certificate per piece: if every piece `piece (n + m) s (gMask n m M)
(repRows n m) o k`, `o < 4`, `k < n + m + s`, is unsatisfiable, no circuit with NOT gates of at
most `s` gates represents the graph with mask `M`. -/
theorem repN_lower_mask_pieces (n m M s : ℕ) (hs : 0 < s)
    (h : ∀ o < 4, ∀ k < n + m + s,
      ¬ FormulaSat (piece (n + m) s (Promise.gMask n m M) (Promise.repRows n m) o k)) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧
      Represents (fun (u : Fin n) (v : Fin m) => M.testBit (m * u + v)) C :=
  repN_lower_mask n m M s (unsat_of_pieces (n + m) s hs _ _ h)

end PEqualNP.Library.LRAT.PromiseN
