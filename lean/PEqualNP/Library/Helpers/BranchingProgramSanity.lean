import PEqualNP.Library.Helpers.ReplayBP

/-! Sanity statements for `PEqualNP.Defs.BranchingProgram` (local attempts, conjecture until checked). -/

namespace PEqualNP.Library.Helpers.BranchingProgramSanity

open PEqualNP.BranchingProgram PEqualNP.Library.Helpers.ReplayBP

theorem bp_s1 : HasBPSize 1 (fun x : Fin 1 → Bool => x 0) 1 :=
  hasBPSize_of_replay [⟨0, Next.out false, Next.out true⟩] (by decide +kernel)

theorem bp_s2 : ¬ HasBPSize 1 (fun x : Fin 1 → Bool => x 0) 0 := by
  rintro ⟨P, -, -, hs, h⟩
  have hP : P = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hs)
  subst hP
  have := h (fun _ => true)
  simp [Program.eval, Program.run] at this

theorem bp_s3 : ¬ Program.Forward [⟨0, Next.state 0, Next.out true⟩] := by
  intro h
  exact absurd (h 0 _ rfl 0 (Or.inl rfl)).1 (lt_irrefl 0)

theorem bp_s4 : HasBPSize 2 (fun x : Fin 2 → Bool => xor (x 0) (x 1)) 3 :=
  hasBPSize_of_replay
    [⟨0, Next.state 1, Next.state 2⟩, ⟨1, Next.out false, Next.out true⟩,
      ⟨1, Next.out true, Next.out false⟩] (by decide +kernel)

theorem bp_s5 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s t : ℕ),
    HasBPSize n f s → s ≤ t → HasBPSize n f t := by
  rintro n f s t ⟨P, h1, h2, h3, h4⟩ hst
  exact ⟨P, h1, h2, le_trans h3 hst, h4⟩

theorem bp_s6 : ∀ n : ℕ, HasBPSize n (fun _ => false) 0 := by
  intro n
  refine ⟨[], ?_, ?_, le_refl _, fun x => ?_⟩
  · intro i s hs; simp at hs
  · intro s hs; simp at hs
  · simp [Program.eval, Program.run]

end PEqualNP.Library.Helpers.BranchingProgramSanity
