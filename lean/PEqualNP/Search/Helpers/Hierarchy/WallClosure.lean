import PEqualNP.Search.Helpers.Hierarchy.Draft

/-!
# The sum-of-squares wall for parity systems, step P1: Gaussian closure and the value of a set

Pure combinatorics on `XorDerivable`. For a parity system `F` with no Gaussian refutation of
width `d`, the value `val F d S` of a finite set `S` is `1` when `(S, false)` is derivable in
width `d`, `-1` when `(S, true)` is, and `0` otherwise. The facts proved here: the value is
well defined (not both are derivable), it is `1` at the empty set, and adding a derivable line
multiplies the value by the sign of that line (`val_symmDiff`, `val_symmDiff_mul`).

Known mathematics (Grigoriev 2001; Schoenebeck 2008). Nothing here is a result of the fleet
until the checker accepts it.
-/

namespace PEqualNP.Search.Helpers.HierarchyDraft.Wall

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- Every derived line has at most `d` variables. -/
theorem XorDerivable.card_le {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ} {e : PEqualNP.ProofComplexity.LinEq V}
    (h : XorDerivable F d e) : e.1.card ≤ d := by
  induction h with
  | ax _ hw => exact hw
  | zero => simp
  | add _ _ hw _ _ => exact hw

/-- Without a refutation, no set is derivable with both right-hand sides. -/
theorem not_both {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ} (hF : ¬ XorRefutable F d) {S : Finset V}
    (h0 : XorDerivable F d (S, false)) (h1 : XorDerivable F d (S, true)) : False := by
  apply hF
  have h := XorDerivable.add h0 h1 (by simp)
  simpa [XorRefutable] using h

/-- Adding a derived line `(T, b)` to a derived line `(S, c)`, when the sum is narrow. -/
theorem derivable_symmDiff {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ} {S T : Finset V} {b c : Bool}
    (hS : XorDerivable F d (S, c)) (hT : XorDerivable F d (T, b))
    (hw : (symmDiff S T).card ≤ d) : XorDerivable F d (symmDiff S T, xor c b) :=
  XorDerivable.add hS hT hw

/-- The closure property: with `(T, b)` derived and `S`, `S Δ T` narrow, the line `(S, c)` is
derivable exactly when `(S Δ T, c + b)` is. -/
theorem derivable_symmDiff_iff {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ} {S T : Finset V} {b : Bool}
    (hT : XorDerivable F d (T, b)) (hS : S.card ≤ d) (hw : (symmDiff S T).card ≤ d) (c : Bool) :
    XorDerivable F d (S, c) ↔ XorDerivable F d (symmDiff S T, xor c b) := by
  constructor
  · intro h
    exact derivable_symmDiff h hT hw
  · intro h
    have h' := XorDerivable.add h hT (by simpa using hS)
    have e1 : symmDiff (symmDiff S T) T = S := by simp
    have e2 : xor (xor c b) b = c := by cases c <;> cases b <;> rfl
    simpa only [e1, e2] using h'

/-- The sign of a right-hand side: `true` is `-1`, `false` is `1`. -/
noncomputable def sgn (b : Bool) : ℝ := if b = true then -1 else 1

@[simp] theorem sgn_false : sgn false = 1 := by simp [sgn]

@[simp] theorem sgn_true : sgn true = -1 := by simp [sgn]

theorem sgn_xor (b c : Bool) : sgn (xor b c) = sgn b * sgn c := by
  cases b <;> cases c <;> simp

theorem sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by
  cases b <;> simp

open Classical in
/-- The value of a set: `1` if `(S, false)` is derivable in width `d`, `-1` if `(S, true)` is,
`0` otherwise. -/
noncomputable def val (F : Set (PEqualNP.ProofComplexity.LinEq V)) (d : ℕ) (S : Finset V) : ℝ :=
  if XorDerivable F d (S, false) then 1 else if XorDerivable F d (S, true) then -1 else 0

/-- The value is `0`, `1` or `-1`. -/
theorem val_trichotomy (F : Set (PEqualNP.ProofComplexity.LinEq V)) (d : ℕ) (S : Finset V) :
    val F d S = 0 ∨ val F d S = 1 ∨ val F d S = -1 := by
  unfold val
  split_ifs <;> simp

/-- Without a refutation, a derivable line has the value of its sign. -/
theorem val_of_derivable {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ} (hF : ¬ XorRefutable F d) {S : Finset V}
    {c : Bool} (h : XorDerivable F d (S, c)) : val F d S = sgn c := by
  unfold val
  cases c with
  | false => simp [h]
  | true =>
    have h0 : ¬ XorDerivable F d (S, false) := fun h0 => not_both hF h0 h
    simp [h0, h]

/-- A set with no derivable line has value `0`. -/
theorem val_of_not_derivable {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ} {S : Finset V}
    (h : ∀ c, ¬ XorDerivable F d (S, c)) : val F d S = 0 := by
  unfold val
  simp [h false, h true]

/-- A nonzero value comes from a derivable line. -/
theorem exists_derivable_of_val_ne_zero {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ} {S : Finset V}
    (h : val F d S ≠ 0) : ∃ c, XorDerivable F d (S, c) := by
  by_contra hc
  exact h (val_of_not_derivable (fun c hd => hc ⟨c, hd⟩))

/-- The value of the empty set is `1`. -/
theorem val_empty {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ} (hF : ¬ XorRefutable F d) :
    val F d (∅ : Finset V) = 1 := by
  simpa using val_of_derivable hF (XorDerivable.zero (F := F) (d := d))

/-- Adding a derived line `(T, b)` multiplies the value by its sign. -/
theorem val_symmDiff {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ} (hF : ¬ XorRefutable F d) {S T : Finset V}
    {b : Bool} (hT : XorDerivable F d (T, b)) (hS : S.card ≤ d)
    (hw : (symmDiff S T).card ≤ d) : val F d (symmDiff S T) = sgn b * val F d S := by
  by_cases h : ∃ c, XorDerivable F d (S, c)
  · obtain ⟨c, hc⟩ := h
    rw [val_of_derivable hF hc, val_of_derivable hF (derivable_symmDiff hc hT hw), sgn_xor,
      mul_comm]
  · have hS0 : val F d S = 0 := val_of_not_derivable (fun c hc => h ⟨c, hc⟩)
    have hST : val F d (symmDiff S T) = 0 := by
      apply val_of_not_derivable
      intro c hc
      apply h
      refine ⟨xor c b, ?_⟩
      rw [derivable_symmDiff_iff hT hS hw]
      have e2 : xor (xor c b) b = c := by cases c <;> cases b <;> rfl
      rwa [e2]
    rw [hS0, hST, mul_zero]

/-- Multiplicativity along derivable sums: if `A Δ B` and `B Δ C` have nonzero value and
`A Δ C` is narrow, the value of `A Δ C` is the product. -/
theorem val_symmDiff_mul {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ} (hF : ¬ XorRefutable F d)
    {A B C : Finset V} (hAB : val F d (symmDiff A B) ≠ 0) (hBC : val F d (symmDiff B C) ≠ 0)
    (hw : (symmDiff A C).card ≤ d) :
    val F d (symmDiff A C) = val F d (symmDiff A B) * val F d (symmDiff B C) := by
  obtain ⟨c1, h1⟩ := exists_derivable_of_val_ne_zero hAB
  obtain ⟨c2, h2⟩ := exists_derivable_of_val_ne_zero hBC
  have e : symmDiff (symmDiff A B) (symmDiff B C) = symmDiff A C := by
    rw [symmDiff_assoc, symmDiff_symmDiff_cancel_left]
  have h := XorDerivable.add h1 h2 (by simpa only [e] using hw)
  simp only [e] at h
  rw [val_of_derivable hF h, val_of_derivable hF h1, val_of_derivable hF h2, sgn_xor]

end PEqualNP.Search.Helpers.HierarchyDraft.Wall
