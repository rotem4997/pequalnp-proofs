import PEqualNP.Library.Machines.FirstPoly
import PEqualNP.Library.Machines.ComposeTime

/-!
# Running a function on the first component of a pair, with a general time bound

Helper module (proofs only, no statement may use it). If `f` is computed within a monotone time
`t` and its output length is at most a monotone `len` of the input length, then
`(x, w) ↦ (f x, w)` is computed, on the pair encoding, within `t n + 2 n + 2 len n + 5` steps.
This is `first_polyTime` with the time bound kept explicit.
-/

namespace PEqualNP.Library.Helpers

open Turing PEqualNP.Library PEqualNP.Library.Machines

theorem first_time (f : List Bool → List Bool) (t len : ℕ → ℕ) (ht : Monotone t)
    (hl : Monotone len) (hlen : ∀ x, (f x).length ≤ len x.length)
    (h : PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) f t) :
    PEqualNP.Library.ComputableInTime PEqualNP.Library.encodePair PEqualNP.Library.encodePair
      (fun p : List Bool × List Bool => (f p.1, p.2)) (fun n => t n + 2 * n + 2 * len n + 5) := by
  obtain ⟨c, hc⟩ := h
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let T : ℕ → ℕ := fun n => t n + 2 * n + 2 * len n + 5
  have key : ∀ p : List Bool × List Bool, ∃ n, n ≤ T (encodePair p).length ∧
      (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[n]
          (some (initList (firstM c.tm e₀ e₁) (encodePair p))) =
        some (haltList (firstM c.tm e₀ e₁) (encodePair (f p.1, p.2))) := by
    rintro ⟨x, w⟩
    have hs : ∃ s, s ≤ c.time x.length ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
      ⟨(c.outputsFun x).steps, (c.outputsFun x).steps_le_m, (c.outputsFun x).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run e₀ e₁ x w _ s h
    have hm : (List.map c.outputAlphabet.invFun (f x)).map e₁ = f x := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (f x)]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have b2 : c.time x.length ≤ t (x.length + w.length) :=
      (hc _).trans (ht (by omega))
    have b3 : (f x).length ≤ len (x.length + w.length) :=
      (hlen x).trans (hl (by omega))
    simp only [T, encodePair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm e₀ e₁) l)))
            (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm e₀ e₁) l))
              (hm _ (encodePair (f p.1, p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }, fun _ => le_rfl⟩

end PEqualNP.Library.Helpers
