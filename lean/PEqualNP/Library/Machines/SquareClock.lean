import PEqualNP.Library.Machines.TwoPass
import PEqualNP.Library.Machines.Mul
import PEqualNP.Library.Machines.ComposeTime

/-!
# The quadratic clock

Helper module (proofs only, no statement may use it). The duplication machine and the unary
multiplication machine are repackaged with explicit time functions and composed, so that
`x ↦ replicate (x.length ^ 2) true` is computed within an explicit quadratic time.
-/

namespace PEqualNP.Library.Machines

open Turing

/-- Duplicating a string takes `4 * n + 4` steps. -/
theorem dup_time :
    PEqualNP.Library.ComputableInTime (fun x : List Bool => x) PEqualNP.Library.encodePair
      (fun x : List Bool => (x, x)) (fun n : ℕ => 4 * n + 4) := by
  let φ₁ : Bool → Option (Bool ⊕ Bool) := fun b => some (Sum.inl b)
  let φ₂ : Bool → Option (Bool ⊕ Bool) := fun b => some (Sum.inr b)
  let d : Option (Bool ⊕ Bool) := some (Sum.inl true)
  have hd : ∀ φ : Bool → Option (Bool ⊕ Bool), d = none → ∀ x, φ x = none :=
    fun φ h => by simp [d] at h
  have hid : ∀ x : List Bool, PEqualNP.Library.encodePair (x, x) =
      x.filterMap φ₁ ++ x.filterMap φ₂ := by
    intro x
    have h1 : x.filterMap φ₁ = x.map Sum.inl := by
      simp [φ₁]
    have h2 : x.filterMap φ₂ = x.map Sum.inr := by
      simp [φ₂]
    rw [h1, h2]; rfl
  exact ⟨{
    tm := tp φ₁ φ₂ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun n => 4 * n + 4
    outputsFun := fun a =>
      { steps := a.length + 1 + (a.length + 1) + (a.length + 1) + (a.length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) a
          exact (congrArg (fun l => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[a.length + 1 +
            (a.length + 1) + (a.length + 1) + (a.length + 1)]
            (some (initList (tp φ₁ φ₂ d) l))) (hm Bool a)).trans
            (this.trans (congrArg (fun l => some (haltList (tp φ₁ φ₂ d) l))
              ((hid a).symm.trans (hm _ (PEqualNP.Library.encodePair (a, a))).symm)))
        steps_le_m := by
          show _ ≤ 4 * a.length + 4
          omega } }, fun _ => le_rfl⟩

/-- Unary multiplication of the lengths of a pair takes at most `2 * m ^ 2 + 5 * m + 3` steps
on a pair of total length `m`. -/
theorem mul_time :
    PEqualNP.Library.ComputableInTime PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)
      (fun m : ℕ => 2 * m ^ 2 + 5 * m + 3) := by
  exact ⟨{
    tm := mulTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun m => 2 * m ^ 2 + 5 * m + 3
    outputsFun := fun p =>
      { steps := mulSteps p.1.length p.2.length
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := mul_run p.1 p.2
          exact (congrArg (fun l => (flip bind (TM2.step mulProg))^[mulSteps p.1.length
            p.2.length] (some (initList mulTM l))) (hm _ (PEqualNP.Library.encodePair p))).trans
            (this.trans (congrArg (fun l => some (haltList mulTM l)) (hm Bool _).symm))
        steps_le_m := by
          simp only [PEqualNP.Library.encodePair, List.length_append, List.length_map, mulSteps]
          nlinarith [Nat.zero_le (p.1.length * p.1.length),
            Nat.zero_le (p.2.length * p.2.length), Nat.zero_le (p.1.length * p.2.length)] } },
    fun _ => le_rfl⟩

/-- The quadratic clock with an explicit constant. -/
theorem square_time :
    PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (x.length ^ 2) true)
      (fun n : ℕ => 27 * n ^ 2 + 27) := by
  have h := comp_time (fun x : List Bool => x) PEqualNP.Library.encodePair
    (fun x : List Bool => x) (fun x : List Bool => (x, x))
    (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)
    (fun n : ℕ => 4 * n + 4) (fun m : ℕ => 2 * m ^ 2 + 5 * m + 3) (fun n : ℕ => 2 * n)
    dup_time mul_time
    (fun a b hab => by
      have := Nat.pow_le_pow_left hab 2
      show 2 * a ^ 2 + 5 * a + 3 ≤ 2 * b ^ 2 + 5 * b + 3
      omega)
    (fun a => by simp [PEqualNP.Library.encodePair]; omega)
  have h' : PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (x.length ^ 2) true)
      (fun n : ℕ => 4 * n + 4 + (2 * (2 * n) + 2) + (2 * (2 * n) ^ 2 + 5 * (2 * n) + 3)) := by
    simpa only [sq] using h
  refine time_mono h' fun n => ?_
  nlinarith [Nat.zero_le (n * n), Nat.le_mul_self n]

end PEqualNP.Library.Machines
