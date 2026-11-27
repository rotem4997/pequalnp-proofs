import PEqualNP.MetaComplexity.Helpers.Expand
import PEqualNP.MetaComplexity.Helpers.Machines.VerifierPoly
import PEqualNP.Library.Machines.IterMeasure

/-!
# The short-witness verifier of partial MCSP runs in polynomial time

Helper for "partial MCSP has short witnesses". The witness is the bit code of the last row
alone; `expand` rebuilds the full witness from it and from the table of the instance, and the
verifier of `Verifier` is run on the result.

* `expand`, `expand_polyTime`: the rebuilding is polynomial-time computable. The step `gS` is
  two transducer runs and one concatenation; it is iterated with the measure "length of the
  first row", which the step never increases.
* `verify_polyTime_of`: the verifier is polynomial time on any polynomial-time computable
  witness string.
* `shortWitness`: the statement.
-/

namespace PEqualNP.MetaComplexity.Helpers.Machines

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.MetaComplexity.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The full witness rebuilt from the instance `y` and the bit code `c` of the last row. -/
def expand (y c : List Bool) : List Sym := expandS y (dec4 c)

/-- The step on bit codes. -/
def gB (w : List Bool) : List Bool := enc4 (gS (dec4 w))

/-- The measure: four times the length of the first row, plus four. -/
def mB (w : List Bool) : ℕ := 4 * ((rowOf (dec4 w)).length + 1)

theorem cpt_gB :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) gB := by
  have h1 := lift_sym_sym δprev finPrev (PrevQ.lead none)
  have h2 := lift_sym_sym δdrop finDrop false
  refine cpt_congr (cpt_comp (cpt_pair h1 h2) cpt_append) (fun w => ?_)
  show enc4 (prevStr (dec4 w)) ++ enc4 (dropStr (dec4 w)) = enc4 (gS (dec4 w))
  rw [← enc4_append]
  rfl

theorem mB_gB (y : List Bool) : mB (gB y) ≤ mB y := by
  show 4 * ((rowOf (dec4 (enc4 (gS (dec4 y))))).length + 1) ≤ 4 * ((rowOf (dec4 y)).length + 1)
  rw [dec4_enc4, gS_row]

theorem length_gB (y : List Bool) : (gB y).length ≤ y.length + mB y := by
  show (enc4 (gS (dec4 y))).length ≤ y.length + 4 * ((rowOf (dec4 y)).length + 1)
  rw [length_enc4]
  have h1 := gS_length (dec4 y)
  have h2 := length_dec4_le y
  omega

theorem mB_le (y : List Bool) : mB y ≤ 4 * y.length + 4 := by
  show 4 * ((rowOf (dec4 y)).length + 1) ≤ 4 * y.length + 4
  have h1 := rowOf_length_le (dec4 y)
  have h2 := length_dec4_le y
  omega

/-- Rebuilding the full witness is polynomial-time computable. -/
theorem expand_polyTime :
    ComputableInPolyTime encodePair (fun u : List Sym => u)
      (fun p : List Bool × List Bool => expand p.1 p.2) := by
  obtain ⟨c⟩ := cpt_gB
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => gB^[p.2.length] p.1) :=
    Iter.iter_polyTime_measure gB c mB 4 mB_gB length_gB mB_le
  have hinit : ComputableInPolyTime encodePair (fun u : List Sym => u)
      (fun p : List Bool × List Bool => entStr (instStr p.1) ++ dec4 p.2) :=
    sym_append
      (cpt_fstRun2_comp (cpt_fstRun2_comp cpt_fst δinst finInst false) δent finEnt (none, none))
      sym_dec4_snd
  have h := cpt_comp (cpt_comp (pair_prod (sym_enc hinit) cpt_fst) hI) cpt_dec4
  refine cpt_congr h (fun p => ?_)
  have e := dec4_iterate gS p.1.length (enc4 (entStr (instStr p.1) ++ dec4 p.2))
  rw [dec4_enc4] at e
  exact e

/-- The verifier on a polynomial-time computable witness string is polynomial time. -/
theorem verify_polyTime_of {F : List Bool × List Bool → List Sym}
    (hf : ComputableInPolyTime encodePair (fun u : List Sym => u) F) :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => verify p.1 (F p)) := by
  have h1 := pair_allTrue (cpt_fstRun2_comp hf δwf finWf (WfQ.start true true))
  have h2 := sym_eq (cpt_fstRun2_comp hf δsucc finSucc SuccQ.carry)
    (sym_append (cpt_fstRun2_comp hf δtail finTail false) (cpt_fstRun2_comp hf δhead finHead false))
  have h3 := pair_eq (cpt_fstRun2_comp hf δtab finTab ())
    (cpt_fstRun2_comp cpt_fst δinst finInst false)
  have h4 := pair_lenLE (cpt_fstRun2_comp cpt_fst δunary finUnary false)
    (cpt_fstRun2_comp hf δgates finGates (GQ.run false))
  have h5 := pair_allTrue (cpt_fstRun2_comp
    (sym_iter δstep finStep StepQ.start step_length_le hf cpt_fst) δout finOut OutQ.init)
  have h6 := pair_allTrue (cpt_fstRun2_comp cpt_fst δsep finSep false)
  exact cpt_congr (pair_and (pair_and (pair_and (pair_and (pair_and h1 h2) h3) h4) h5) h6)
    (fun p => rfl)

/-- Partial MCSP has a polynomial-time verifier, sound on every string, whose witness has
length quadratic in the number of inputs plus the size of a consistent circuit. -/
theorem shortWitness :
    ∃ (V : Set (List Bool × List Bool)) (a : ℕ), DecidableInPolyTime encodePair V ∧
      (∀ y c : List Bool, (y, c) ∈ V → y ∈ PartialMCSP) ∧
      ∀ (n s t : ℕ) (T : List (Option Bool)) (f : (Fin n → Bool) → Bool), T.length = 2 ^ n →
        Consistent n T f → HasCircuitSize n f t → t ≤ s →
        ∃ c : List Bool, c.length ≤ a * (n + t + 1) ^ 2 ∧
          (List.replicate s true ++ false :: encodePartial T, c) ∈ V := by
  refine ⟨{p | verify p.1 (expand p.1 p.2) = true}, 24,
    ⟨fun p => verify p.1 (expand p.1 p.2), fun _ => Iff.rfl, verify_polyTime_of expand_polyTime⟩,
    fun y c h => verify_sound y _ h, ?_⟩
  rintro n s t T f hT hcons ⟨C, hfan, hsize, hev⟩ hts
  have hC' := goodC_normCircuit (n + t) C hfan
  have hszt : (normCircuit (n + t) C).gates.length ≤ t := by
    rw [size_normCircuit]; exact hsize
  have hsz : (normCircuit (n + t) C).gates.length ≤ s := le_trans hszt hts
  have hval : ∀ j < 2 ^ n, T.getD j none = none
      ∨ T.getD j none = some ((normCircuit (n + t) C).eval (bitsL n j)) := by
    intro j hj
    have e : (normCircuit (n + t) C).eval (bitsL n j) = f (bitsOf n j) := by
      rw [eval_normCircuit _ _ hfan _ (by
        rw [length_bitsL]
        exact Nat.add_le_add_left hsize n), bitsL_eq_ofFn, hev]
    rw [e]
    rcases hT' : T.getD j none with _ | b
    · exact Or.inl rfl
    · right
      have := hcons (bitsOf n j) b (by rw [tableIndex_bitsOf hj]; exact hT')
      rw [this]
  obtain ⟨hv, _⟩ := verify_honest n s (n + t) T hT _ hC' hsz
    (inputs_normCircuit_le _ C) (output_normCircuit_le _ C) hval
  refine ⟨enc4 (encW (bitsL n (2 ^ n - 1), normCircuit (n + t) C, T.getD (2 ^ n - 1) none)),
    ?_, ?_⟩
  · rw [length_enc4]
    have h2 := length_encW_le (n + t)
      (bitsL n (2 ^ n - 1), normCircuit (n + t) C, T.getD (2 ^ n - 1) none) hC'
      (inputs_normCircuit_le _ C) (output_normCircuit_le _ C)
    dsimp only at h2
    have h3 : (bitsL n (2 ^ n - 1)).length = n := length_bitsL n _
    have h4 : (normCircuit (n + t) C).gates.length * (2 * (n + t) + 3)
        ≤ t * (2 * (n + t) + 3) := Nat.mul_le_mul_right _ hszt
    have h5 : t * (2 * (n + t) + 3) ≤ (n + t + 1) * (2 * (n + t + 1) + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h6 : (n + t + 1) * (2 * (n + t + 1) + 1) = 2 * (n + t + 1) ^ 2 + (n + t + 1) := by
      ring
    have h7 : n + t + 1 ≤ (n + t + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  · show verify (List.replicate s true ++ false :: encodePartial T)
      (expandS (List.replicate s true ++ false :: encodePartial T) (dec4 (enc4 _))) = true
    rw [dec4_enc4, expandS_honest n s T hT]
    exact hv

end PEqualNP.MetaComplexity.Helpers.Machines
