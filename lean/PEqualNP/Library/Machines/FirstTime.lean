import PEqualNP.Library.Machines.ComposeTime
import PEqualNP.Library.Machines.Pairing

/-!
# Pairing an input with the output of a clock, with a general time bound

Helper module (proofs only, no statement may use it). If the clock `x ↦ 1 ^ t |x|` is computed
within `c * t n + c` steps, then `x ↦ (1 ^ t |x|, x)` is computed, into the pair encoding, within
`c * t n + c + 2 * t n + p n` steps for a fixed polynomial `p` that does not depend on `t`. The
machine duplicates the input and then runs the clock on the first component; the run is assembled
on the specific pair `(x, x)`, so no monotonicity of `t` is needed.
-/

namespace PEqualNP.Library.Machines

open Turing PEqualNP.Library

/-- The clock paired with the input, in general time. The polynomial overhead `p` is fixed. -/
theorem clockPair_time : ∃ p : Polynomial ℕ, ∀ (t : ℕ → ℕ) (c : ℕ),
    PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (t x.length) true) (fun n => c * t n + c) →
    PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair
      (fun x : List Bool => (List.replicate (t x.length) true, x))
      (fun n => c * t n + c + 2 * t n + p.eval n) := by
  classical
  obtain ⟨pd, c1, hc1⟩ := time_of_polyTime cpt_dup
  refine ⟨pd + Polynomial.C 8 * Polynomial.X + Polynomial.C 7, ?_⟩
  rintro t c ⟨c2, hc2⟩
  let e₀ : Bool → c2.tm.Γ c2.tm.k₀ := c2.inputAlphabet.invFun
  let e₁ : c2.tm.Γ c2.tm.k₁ → Bool := c2.outputAlphabet
  let M2 : FinTM2 := firstM c2.tm e₀ e₁
  let φ : c1.tm.Γ c1.tm.k₁ → M2.Γ M2.k₀ := fun y => c1.outputAlphabet y
  let d : Option (M2.Γ M2.k₀) := some (Sum.inl true)
  have hd : d = none → IsEmpty (M2.Γ M2.k₀) := fun h => absurd h (Option.some_ne_none _)
  let T : ℕ → ℕ := fun n => c * t n + c + 2 * t n +
    (pd + Polynomial.C 8 * Polynomial.X + Polynomial.C 7).eval n
  have key : ∀ x : List Bool, ∃ n, n ≤ T x.length ∧
      (flip bind (TM2.step (prog c1.tm M2 φ d)))^[n]
          (some (initList (comp c1.tm M2 φ d) (List.map c1.inputAlphabet.invFun x))) =
        some (haltList (comp c1.tm M2 φ d)
          (encodePair (List.replicate (t x.length) true, x))) := by
    intro x
    have r1 := c1.outputsFun x
    have r2 := c2.outputsFun x
    obtain ⟨n2, hn2, hrun2⟩ := first_run e₀ e₁ x x _ r2.steps r2.evals_in_steps
    have hm : (List.map c2.outputAlphabet.invFun (List.replicate (t x.length) true)).map e₁ =
        List.replicate (t x.length) true := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (List.replicate (t x.length) true)]
      exact List.map_congr_left fun y _ => c2.outputAlphabet.right_inv y
    rw [hm] at hrun2
    have hφ : (List.map c1.outputAlphabet.invFun (encodePair (x, x))).map φ =
        encodePair (x, x) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (encodePair (x, x))]
      exact List.map_congr_left fun y _ => c1.outputAlphabet.right_inv y
    have h2 : (flip bind (TM2.step M2.m))^[n2]
        (some (initList M2 ((List.map c1.outputAlphabet.invFun (encodePair (x, x))).map φ))) =
        some (haltList M2 (encodePair (List.replicate (t x.length) true, x))) := by
      rw [hφ]; exact hrun2
    obtain ⟨n, hn, -, hrun⟩ := comp_run φ d hd _ _ _ r1.steps n2 r1.evals_in_steps h2
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 : r1.steps ≤ pd.eval x.length := r1.steps_le_m.trans (hc1 _)
    have b2 : r2.steps ≤ c * t x.length + c := r2.steps_le_m.trans (hc2 _)
    simp only [List.length_map, List.length_replicate, encodePair_length] at hn2 ⊢
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    omega
  exact ⟨{
    tm := comp c1.tm M2 φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun x =>
      { steps := Classical.choose (key x)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (Classical.choose_spec (key x)).2.trans
            (congrArg (fun l => some (haltList (comp c1.tm M2 φ d) l))
              (hm _ (encodePair (List.replicate (t x.length) true, x))).symm)
        steps_le_m := (Classical.choose_spec (key x)).1 } }, fun _ => le_rfl⟩

end PEqualNP.Library.Machines
