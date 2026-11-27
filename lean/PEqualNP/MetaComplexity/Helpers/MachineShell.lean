import PEqualNP.Library.SearchHelpers.KSatHard
import PEqualNP.Library.SearchHelpers.Encoding
import PEqualNP.MetaComplexity.Helpers.MachinePair
import PEqualNP.Defs.MetaComplexityLgp

/-!
# The outer shell of a polynomial-time map on CNF codes

Helper module (proofs only, no statement may use it).

A polynomial-time map `R` on CNF formulas (input written by `encodeCNF`) extends to every bit
string: on a code of `φ` it is `R φ`, on any other string it is the instance `(0, empty
circuit with output 0)`. The machine first tests whether the string is a code (the checked
well-formedness test `wfB` of the SAT verifier, machine `cpt_wfF`), normalizes the input to the
code of a formula (the string itself, or the empty string, which codes the empty formula), runs
the machine of `R` on it, and selects between that output and the constant code.
-/

namespace PEqualNP.MetaComplexity.Helpers.MachineShell

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The formula a string codes, or the empty formula when it codes none. -/
noncomputable def shellDec (x : List Bool) : CNF := by
  classical
  exact if h : ∃ φ : CNF, encodeCNF φ = x then Classical.choose h else []

/-- The instance written on strings that code no formula. -/
def shellConst : ℕ × Circuit := (0, Circuit.mk [] 0)

/-- The outer shell of `R`. -/
noncomputable def shellMap (R : CNF → ℕ × Circuit) (x : List Bool) : ℕ × Circuit :=
  if wfB x = true then R (shellDec x) else shellConst

theorem shellDec_enc (φ : CNF) : shellDec (encodeCNF φ) = φ := by
  have h : ∃ ψ : CNF, encodeCNF ψ = encodeCNF φ := ⟨φ, rfl⟩
  unfold shellDec
  rw [dif_pos h]
  exact encodeCNF_injective (Classical.choose_spec h)

theorem enc_shellDec (x : List Bool) :
    encodeCNF (shellDec x) = sel (bflag (wfB x)) [] x := by
  cases hw : wfB x with
  | true =>
    obtain ⟨φ, rfl⟩ := (wfB_iff _).1 hw
    rw [shellDec_enc]
    rfl
  | false =>
    have hn : ¬ ∃ φ : CNF, encodeCNF φ = x := fun h => by
      rw [(wfB_iff x).2 h] at hw
      exact Bool.noConfusion hw
    unfold shellDec
    rw [dif_neg hn]
    rfl

theorem cpt_shellDec :
    ComputableInPolyTime (fun x : List Bool => x) encodeCNF shellDec := by
  obtain ⟨c⟩ := cpt_sel KSat.Hard.cpt_wfF (cpt_const []) cpt_id
  exact MachinePair.cpt_transport c id shellDec (fun _ => rfl) enc_shellDec

theorem shellMap_enc (R : CNF → ℕ × Circuit) (φ : CNF) :
    shellMap R (encodeCNF φ) = R φ := by
  have hw : wfB (encodeCNF φ) = true := (wfB_iff _).2 ⟨φ, rfl⟩
  unfold shellMap
  rw [if_pos hw, shellDec_enc]

theorem shellMap_non (R : CNF → ℕ × Circuit) (x : List Bool)
    (hx : ∀ φ : CNF, encodeCNF φ ≠ x) : shellMap R x = (0, Circuit.mk [] 0) := by
  have hw : wfB x ≠ true := fun h => by
    obtain ⟨φ, hφ⟩ := (wfB_iff x).1 h
    exact hx φ hφ
  unfold shellMap
  rw [if_neg hw]
  rfl

theorem cpt_shellMap (R : CNF → ℕ × Circuit)
    (hR : ComputableInPolyTime encodeCNF encodeLgp R) :
    ComputableInPolyTime (fun x : List Bool => x) encodeLgp (shellMap R) := by
  obtain ⟨c1⟩ := cpt_comp cpt_shellDec hR
  have h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => encodeLgp (R (shellDec x))) :=
    MachinePair.cpt_transport c1 id _ (fun _ => rfl) (fun _ => rfl)
  obtain ⟨c3⟩ := cpt_sel KSat.Hard.cpt_wfF (cpt_const (encodeLgp shellConst)) h2
  refine MachinePair.cpt_transport c3 id (shellMap R) (fun _ => rfl) ?_
  intro x
  unfold shellMap
  show _ = sel (bflag (wfB x)) _ _
  cases h : wfB x <;> simp [sel, bflag]

theorem shell :
    ∀ R : CNF → ℕ × Circuit, ComputableInPolyTime encodeCNF encodeLgp R →
      ∃ r : List Bool → ℕ × Circuit,
        ComputableInPolyTime (fun x : List Bool => x) encodeLgp r ∧
          (∀ φ : CNF, r (encodeCNF φ) = R φ) ∧
          ∀ x : List Bool, (∀ φ : CNF, encodeCNF φ ≠ x) → r x = (0, Circuit.mk [] 0) :=
  fun R hR => ⟨shellMap R, cpt_shellMap R hR, shellMap_enc R, shellMap_non R⟩

end PEqualNP.MetaComplexity.Helpers.MachineShell
