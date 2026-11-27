import PEqualNP.Library.Machines.ComposeRun

/-!
# Composition with general time bounds

Helper module (proofs only, no statement may use it). The composite machine `comp M1 M2 φ d`
runs the first machine, moves its output across, then runs the second machine. Here the run
length is packaged with arbitrary time functions instead of polynomials: the first function runs
in time `t₁`, its encoded output has length at most `len n`, and the second runs in a monotone
time `t₂`.
-/

namespace PEqualNP.Library.Machines

open Turing

/-- Composition with general time bounds: the first function runs in time `t₁`, its encoded
output has length at most `len n` on inputs of encoded length `n`, the second runs in a monotone
time `t₂`. -/
theorem comp_time {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (ec : γ → List γΓ) (f : α → β) (g : β → γ) (t₁ t₂ len : ℕ → ℕ)
    (h₁ : PEqualNP.Library.ComputableInTime ea eb f t₁)
    (h₂ : PEqualNP.Library.ComputableInTime eb ec g t₂)
    (hmono : Monotone t₂)
    (hlen : ∀ a, (eb (f a)).length ≤ len (ea a).length) :
    PEqualNP.Library.ComputableInTime ea ec (fun a => g (f a))
      (fun n => t₁ n + (2 * len n + 2) + t₂ (len n)) := by
  classical
  obtain ⟨c1, hc1⟩ := h₁
  obtain ⟨c2, hc2⟩ := h₂
  let φ : c1.tm.Γ c1.tm.k₁ → c2.tm.Γ c2.tm.k₀ :=
    fun x => c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d : Option (c2.tm.Γ c2.tm.k₀) :=
    if h : Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd : d = none → IsEmpty (c2.tm.Γ c2.tm.k₀) := by
    intro h
    by_cases hn : Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d, hn] at h
    · exact not_nonempty_iff.mp hn
  let T : ℕ → ℕ := fun n => t₁ n + (2 * len n + 2) + t₂ (len n)
  have key : ∀ a, ∃ n, n ≤ T (ea a).length ∧
      (flip bind (TM2.step (prog c1.tm c2.tm φ d)))^[n]
          (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
        some (haltList (comp c1.tm c2.tm φ d)
          (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
    intro a
    have r1 := c1.outputsFun a
    have r2 := c2.outputsFun (f a)
    have hφ : (List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
        List.map c2.inputAlphabet.invFun (eb (f a)) := by
      rw [List.map_map]
      refine List.map_congr_left fun y _ => ?_
      show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y)) = _
      exact congrArg _ (c1.outputAlphabet.right_inv y)
    have h2 : (flip bind (TM2.step c2.tm.m))^[r2.steps]
        (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
        some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
      rw [hφ]; exact r2.evals_in_steps
    obtain ⟨n, hn, -, hrun⟩ := comp_run φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 : r1.steps ≤ t₁ (ea a).length := r1.steps_le_m.trans (hc1 _)
    have b2 : r2.steps ≤ t₂ (len (ea a).length) :=
      (r2.steps_le_m.trans (hc2 _)).trans (hmono (hlen a))
    have b3 := hlen a
    simp only [T, List.length_map]
    omega
  exact ⟨{
    tm := comp c1.tm c2.tm φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := c2.outputAlphabet
    time := T
    outputsFun := fun a =>
      ⟨⟨Classical.choose (key a), (Classical.choose_spec (key a)).2⟩,
        (Classical.choose_spec (key a)).1⟩ }, fun _ => le_rfl⟩

/-- A polynomial-time function is computable within its polynomial, as a time function. -/
theorem time_of_polyTime {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : PEqualNP.Library.ComputableInPolyTime ea eb f) :
    ∃ p : Polynomial ℕ, PEqualNP.Library.ComputableInTime ea eb f (fun n => p.eval n) := by
  obtain ⟨c⟩ := h
  exact ⟨c.time, ⟨{
    tm := c.tm
    inputAlphabet := c.inputAlphabet
    outputAlphabet := c.outputAlphabet
    time := fun n => c.time.eval n
    outputsFun := c.outputsFun }, fun _ => le_rfl⟩⟩

/-- The time bound can be weakened. -/
theorem time_mono {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    {t t' : ℕ → ℕ} (h : PEqualNP.Library.ComputableInTime ea eb f t) (ht : ∀ n, t n ≤ t' n) :
    PEqualNP.Library.ComputableInTime ea eb f t' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun n => (hc n).trans (ht n)⟩

end PEqualNP.Library.Machines
