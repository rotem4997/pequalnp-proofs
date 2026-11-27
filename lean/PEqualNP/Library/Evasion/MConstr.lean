import PEqualNP.Library.Evasion.RungPlan
import PEqualNP.Library.Evasion.Clock
import PEqualNP.Library.Machines.FirstTime
import PEqualNP.Library.Helpers.PadMap

/-!
# Evasion chain: affine and composed bounds are constructible, and the pad clock

* `constrAff : StmtConstrAff`: the writer is `t2a C C`.
* `constrComp : StmtConstrComp`: write `1^(f n)`, then run `g`'s writer on it.
* `dup_time`: `x ↦ (x, x)` in the pair encoding, in `4 n + 4` steps (two-pass machine).
* `clockPairLin`: `x ↦ (1^(t |x|), x)` with linear overhead: the machine of `clockPair_time`
  with the linear duplication in place of the polynomial one.
* `padClock : StmtPadClock`: `clockPairLin`, then `sepPair_time`.
-/

namespace PEqualNP.Library.Evasion

open Turing PEqualNP.Library PEqualNP.Library.Machines

/-- Affine bounds are constructible. -/
theorem constrAff : StmtConstrAff := by
  intro C hC
  refine ⟨fun a b hab => ?_, fun n => ?_, ?_⟩
  · show C * a + C ≤ C * b + C
    exact Nat.add_le_add_right (Nat.mul_le_mul_left C hab) C
  · show n ≤ C * n + C
    nlinarith
  · obtain ⟨C', hC'⟩ := t2a C C
    refine ⟨C', time_mono hC' fun n => ?_⟩
    show C' * n + C' ≤ C' * (C * n + C) + C'
    nlinarith [Nat.zero_le (C' * n)]

/-- Constructible bounds compose. -/
theorem constrComp : StmtConstrComp := by
  intro f g ⟨hfm, hfn, cf, hf⟩ ⟨hgm, hgn, cg, hg⟩
  refine ⟨hgm.comp hfm, fun n => (hfn n).trans (hgn (f n)), ?_⟩
  have h := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => x) (fun x : List Bool => List.replicate (f x.length) true)
    (fun x : List Bool => List.replicate (g x.length) true) _ _ f hf hg
    (fun a b hab => by
      show cg * g a + cg ≤ cg * g b + cg
      exact Nat.add_le_add_right (Nat.mul_le_mul_left cg (hgm hab)) cg)
    (fun x => by simp)
  simp only [List.length_replicate] at h
  refine ⟨cf + 2 + cg, time_mono h fun n => ?_⟩
  have e := hgn (f n)
  show cf * f n + cf + (2 * f n + 2) + (cg * g (f n) + cg) ≤
    (cf + 2 + cg) * g (f n) + (cf + 2 + cg)
  nlinarith [Nat.mul_le_mul_left cf e]

/-- Duplication into the pair encoding in linear time. -/
theorem dup_time : PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
    PEqualNP.Library.encodePair (fun x : List Bool => (x, x)) (fun n => 4 * n + 4) :=
  tp_time _ _ _ (fun b => some (Sum.inl b)) (fun b => some (Sum.inr b)) (Sum.inl true)
    (fun x => by simp [PEqualNP.Library.encodePair])

/-- The clock paired with the input, with a linear overhead. -/
theorem clockPairLin (t : ℕ → ℕ) (c : ℕ)
    (h : PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (t x.length) true) (fun n => c * t n + c)) :
    PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair
      (fun x : List Bool => (List.replicate (t x.length) true, x))
      (fun n => c * t n + c + 2 * t n + 12 * n + 11) := by
  classical
  obtain ⟨c1, hc1⟩ := dup_time
  obtain ⟨c2, hc2⟩ := h
  let e₀ : Bool → c2.tm.Γ c2.tm.k₀ := c2.inputAlphabet.invFun
  let e₁ : c2.tm.Γ c2.tm.k₁ → Bool := c2.outputAlphabet
  let M2 : FinTM2 := firstM c2.tm e₀ e₁
  let φ : c1.tm.Γ c1.tm.k₁ → M2.Γ M2.k₀ := fun y => c1.outputAlphabet y
  let d : Option (M2.Γ M2.k₀) := some (Sum.inl true)
  have hd : d = none → IsEmpty (M2.Γ M2.k₀) := fun h => absurd h (Option.some_ne_none _)
  let T : ℕ → ℕ := fun n => c * t n + c + 2 * t n + 12 * n + 11
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
    have b1 : r1.steps ≤ 4 * x.length + 4 := r1.steps_le_m.trans (hc1 _)
    have b2 : r2.steps ≤ c * t x.length + c := r2.steps_le_m.trans (hc2 _)
    simp only [List.length_map, List.length_replicate, encodePair_length] at hn2 ⊢
    simp only [T]
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

/-- The pad clock: `1^(N |x|) 0 x` in time `O(N)`. -/
theorem padClock : StmtPadClock := by
  intro N ⟨hNm, hNn, c, hc⟩
  have hA := clockPairLin N c hc
  have hB := comp_time (fun x : List Bool => x)
    PEqualNP.Library.encodePair (fun x : List Bool => x)
    (fun x : List Bool => (List.replicate (N x.length) true, x))
    (fun p : List Bool × List Bool => p.1 ++ false :: p.2)
    _ (fun n => 2 * n + 3) (fun n => N n + n) hA
    PEqualNP.Library.Helpers.sepPair_time (fun a b h => by dsimp; omega)
    (fun x => by simp [PEqualNP.Library.encodePair])
  refine ⟨c + 30, time_mono hB fun n => ?_⟩
  have e := hNn n
  show c * N n + c + 2 * N n + 12 * n + 11 + (2 * (N n + n) + 2) + (2 * (N n + n) + 3) ≤
    (c + 30) * N n + (c + 30)
  nlinarith

end PEqualNP.Library.Evasion
