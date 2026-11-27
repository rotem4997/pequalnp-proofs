import PEqualNP.Library.Universal.Padding
import PEqualNP.Library.Machines.LenLE

/-!
# Unary padding of a witness bound keeps a verifier relation in NP

Helper module (proofs only, no statement may use it).

For a polynomial-time decidable relation `R`, the language of the strings `1 ^ t 0 x` such that
some `w` of length at most `t` has `(x, w) ∈ R` is in NP: the verifier reads the leading run and
the rest of the string, compares the witness length with the run, and runs the decider of `R`.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

local notation "CPT" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

private theorem cptU {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem neU_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

private theorem cpt_neU :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, neU_true, Computability.encodeBool])

private theorem combU (A : List Bool) (a b : Bool) :
    (!(sel A [] (sel (if a then [true] else []) []
      (sel (if b then [true] else []) [] [true]))).isEmpty) =
      (!A.isEmpty && (a && b)) := by
  cases A <;> cases a <;> cases b <;> simp [sel]

/-- The verifier of the unary-padded language, as a Boolean function of the pair. -/
def upV (fR : List Bool × List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  !(padA p.1).isEmpty && (decide (p.2.length ≤ (hd p.1).length) && fR (dropN p.1, p.2))

private theorem cpt_upVS {fR : List Bool × List Bool → Bool}
    (hfR : ComputableInPolyTime encodePair Computability.encodeBool fR) :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => upV fR ((unpairB s).1, (unpairB s).2)) := by
  have hy : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have hw : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have fA : CPT (fun s => padA (unpairB s).1) := cpt_comp hy cpt_padA
  have f1 := cpt_bitFlag (cpt_comp (cpt_pair (cpt_hd1 hy) hw) LenCmp.lenLE_polyTime)
  have f2 := cpt_bitFlag (cpt_comp (cpt_pair (cpt_dropN1 hy) hw) hfR)
  have all := cpt_sel fA (cpt_const []) (cpt_sel f1 (cpt_const [])
    (cpt_sel f2 (cpt_const []) (cpt_const [true])))
  exact cptU (cpt_comp all cpt_neU) (fun s => combU _ _ _)

/-- The verifier is polynomial-time computable on the pair encoding. -/
theorem cpt_upV {fR : List Bool × List Bool → Bool}
    (hfR : ComputableInPolyTime encodePair Computability.encodeBool fR) :
    ComputableInPolyTime encodePair Computability.encodeBool (upV fR) :=
  cptU (cpt_comp cpt_pairB (cpt_upVS hfR)) (fun p => by
    obtain ⟨z, w⟩ := p
    simp only [unpairB_pairB])

/-- The unary-padded language of a polynomial-time decidable relation is in NP. -/
theorem unaryPad_NP (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R) :
    ({y : List Bool | ∃ (t : ℕ) (x w : List Bool),
      y = List.replicate t true ++ false :: x ∧ w.length ≤ t ∧ (x, w) ∈ R} : Language Bool) ∈
      NP := by
  obtain ⟨fR, hfR, hc⟩ := hR
  refine ⟨{p | upV fR p = true}, Polynomial.X, ⟨upV fR, fun _ => Iff.rfl, cpt_upV hc⟩,
    fun y => ?_⟩
  rw [Polynomial.eval_X]
  constructor
  · rintro ⟨t, x, w, rfl, hwt, hxw⟩
    refine ⟨w, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons]
      omega
    · have h1 : hd (List.replicate t true ++ false :: x) = un t := hd_un t x
      have h2 : dropN (List.replicate t true ++ false :: x) = x := dropN_un t x
      have h3 : padA (List.replicate t true ++ false :: x) = x ++ [false] := by
        have e : (List.replicate t true ++ false :: x) ++ [false] =
            un t ++ false :: (x ++ [false]) := by simp [un]
        rw [padA, e, dropN_un]
      show upV fR (List.replicate t true ++ false :: x, w) = true
      simp only [upV, h1, h2, h3, un_length]
      simp [hwt, (hfR (x, w)).1 hxw]
  · rintro ⟨w, -, hV⟩
    have hV' : upV fR (y, w) = true := hV
    simp only [upV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hV'
    obtain ⟨hA, hlen, hf⟩ := hV'
    have hA' : padA y ≠ [] := by
      intro h
      rw [h] at hA
      simp at hA
    have hs := (hd_split y).resolve_left hA'
    refine ⟨(hd y).length, dropN y, w, ?_, hlen, (hfR _).2 hf⟩
    have hu : hd y = List.replicate (hd y).length true := hd_eq_un y
    rw [← hu]
    exact hs

end PEqualNP.Library.Universal
