import PEqualNP.Library.Universal.PrimsCPT
import PEqualNP.Library.L045
import PEqualNP.MetaComplexity.Helpers.Machines.Glue

/-!
# Helpers: NP languages are the ranges of polynomially bounded proof systems

Cook and Reckhow, J. Symb. Logic 44(1), 1979. A nonempty language is in NP exactly when it is
the range of a polynomial-time function under which every member has a proof of polynomial
length.

* `cr_range_np`: the range of such a function is in NP; the verifier tests `f c = x`.
* `cr_decode_cpt`: reading a self-delimiting pair `(x, w)` and answering `x` when the verifier
  accepts, a fixed string otherwise, is polynomial time.
* `cr_code_length`: the length of the self-delimiting pair is polynomial in `|x|`.
* `cr_np_range`: every nonempty NP language is such a range.
-/

namespace PEqualNP.ProofComplexity.Helpers

/-- The range of a polynomial-time function with polynomially short proofs is in NP. -/
theorem cr_range_np (L : Language Bool) (f : List Bool → List Bool)
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f)
    (hr : Set.range f = L) (p : Polynomial ℕ)
    (hp : ∀ x ∈ L, ∃ w : List Bool, w.length ≤ p.eval x.length ∧ f w = x) :
    L ∈ PEqualNP.Library.NP := by
  have hdec := PEqualNP.MetaComplexity.Helpers.Machines.pair_eq
    (PEqualNP.Library.Machines.cpt_comp PEqualNP.Library.Machines.cpt_snd hf)
    PEqualNP.Library.Machines.cpt_fst
  refine ⟨{q | f q.2 = q.1}, p, ⟨_, fun q => by simp, hdec⟩, fun x => ?_⟩
  constructor
  · intro hx
    exact hp x hx
  · rintro ⟨w, -, hw⟩
    rw [← hr]
    exact ⟨w, hw⟩

/-- Decoding a self-delimiting pair and answering its first component when the verifier
accepts, a fixed string otherwise, is polynomial time. -/
theorem cr_decode_cpt (fR : List Bool × List Bool → Bool)
    (cR : PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      Computability.encodeBool fR) (x0 : List Bool) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => if fR (PEqualNP.Library.Universal.unpairB s) = true then
        (PEqualNP.Library.Universal.unpairB s).1 else x0) := by
  have hflag := PEqualNP.Library.Universal.cpt_bitFlag
    (PEqualNP.Library.Machines.cpt_comp PEqualNP.Library.Universal.cpt_unpairB cR)
  have h := PEqualNP.Library.Universal.cpt_sel hflag (PEqualNP.Library.Universal.cpt_const x0)
    PEqualNP.Library.Universal.cpt_unpairB1
  have e : (fun s : List Bool => PEqualNP.Library.Universal.sel
      (if fR (PEqualNP.Library.Universal.unpairB s) then [true] else []) x0
      (PEqualNP.Library.Universal.unpairB s).1) =
      (fun s : List Bool => if fR (PEqualNP.Library.Universal.unpairB s) = true then
        (PEqualNP.Library.Universal.unpairB s).1 else x0) := by
    funext s
    by_cases hb : fR (PEqualNP.Library.Universal.unpairB s) = true <;>
      simp [PEqualNP.Library.Universal.sel, hb]
  rw [← e]
  exact h

/-- The self-delimiting pair of `x` and a short `w` has length polynomial in `|x|`. -/
theorem cr_code_length (p : Polynomial ℕ) (x w : List Bool)
    (hw : w.length ≤ p.eval x.length) :
    (PEqualNP.Library.Universal.pairB x w).length ≤
      (Polynomial.C 2 * Polynomial.X + p + Polynomial.C 1).eval x.length := by
  rw [PEqualNP.Library.Universal.pairB_length]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

/-- Every nonempty NP language is the range of a polynomial-time function under which every
member has a proof of polynomial length. -/
theorem cr_np_range (L : Language Bool) (hne : Set.Nonempty L)
    (hL : L ∈ PEqualNP.Library.NP) :
    ∃ f : List Bool → List Bool,
      PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f ∧
        Set.range f = L ∧
          ∃ p : Polynomial ℕ, ∀ x ∈ L, ∃ w : List Bool, w.length ≤ p.eval x.length ∧ f w = x := by
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨R, p, ⟨fR, hfR, cR⟩, hbd, hLR⟩ := PEqualNP.Library.L045 L hL
  refine ⟨fun s => if fR (PEqualNP.Library.Universal.unpairB s) = true then
      (PEqualNP.Library.Universal.unpairB s).1 else x0, cr_decode_cpt fR cR x0, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨s, rfl⟩
      dsimp only
      split
      · next h => exact (hLR _).2 ⟨_, (hfR _).2 h⟩
      · exact hx0
    · intro hx
      obtain ⟨w, hw⟩ := (hLR x).1 hx
      refine ⟨PEqualNP.Library.Universal.pairB x w, ?_⟩
      simp [PEqualNP.Library.Universal.unpairB_pairB, (hfR _).1 hw]
  · refine ⟨Polynomial.C 2 * Polynomial.X + p + Polynomial.C 1, fun x hx => ?_⟩
    obtain ⟨w, hw⟩ := (hLR x).1 hx
    refine ⟨PEqualNP.Library.Universal.pairB x w, cr_code_length p x w (hbd x w hw), ?_⟩
    simp [PEqualNP.Library.Universal.unpairB_pairB, (hfR _).1 hw]

end PEqualNP.ProofComplexity.Helpers
