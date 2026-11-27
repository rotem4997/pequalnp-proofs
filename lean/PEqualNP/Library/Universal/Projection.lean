import PEqualNP.Library.Universal.PrimsCPT
import PEqualNP.Library.Machines.LenLE
import PEqualNP.Library.Machines.ReduceNP
import PEqualNP.Library.L045
import PEqualNP.Library.L055

/-!
# Projection of an NP language along a polynomial-time map

Helper module (proofs only, no statement may use it).

Given `E` in NP, a polynomial-time map `π` on pairs and a polynomial `p`, the language of all
`x` having some `c` of length at most `p (length of x)` with `π (x, c)` in `E` is in NP. The new
witness is the self-delimiting pair of `c` and a witness for `π (x, c)`. The new verifier is
built by packing its input into one string and computing every subexpression as a
polynomial-time function of that string.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

local notation "CPT" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

private theorem cptp {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem proj_ne_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

/-- From a flag string to a decision bit. -/
private theorem proj_cpt_ne :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, proj_ne_true, Computability.encodeBool])

private theorem proj_comb (a b : Bool) :
    (!(sel (if a then [true] else []) [] (sel (if b then [true] else []) [] [true])).isEmpty) =
      (a && b) := by
  cases a <;> cases b <;> simp [sel]

/-- The verifier of the projected language. -/
def projV (π : List Bool × List Bool → List Bool) (p : Polynomial ℕ)
    (fR : List Bool × List Bool → Bool) (q : List Bool × List Bool) : Bool :=
  decide ((unpairB q.2).1.length ≤ p.eval q.1.length) &&
    fR (π (q.1, (unpairB q.2).1), (unpairB q.2).2)

/-- The verifier of the projected language is polynomial-time computable. -/
theorem cpt_projV (π : List Bool × List Bool → List Bool) (p : Polynomial ℕ)
    (fR : List Bool × List Bool → Bool)
    (hπ : ComputableInPolyTime encodePair (fun x : List Bool => x) π)
    (cR : ComputableInPolyTime encodePair Computability.encodeBool fR) :
    ComputableInPolyTime encodePair Computability.encodeBool (projV π p fR) := by
  have hX : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have hW : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hC : CPT (fun s => (unpairB (unpairB s).2).1) :=
    cptp (cpt_comp hW cpt_unpairB1) (fun _ => rfl)
  have hW' : CPT (fun s => (unpairB (unpairB s).2).2) :=
    cptp (cpt_comp hW cpt_unpairB2) (fun _ => rfl)
  have hclk := cpt_comp hX (PEqualNP.Library.L055 p)
  have f1 := cpt_bitFlag (cpt_comp (cpt_pair hclk hC) LenCmp.lenLE_polyTime)
  have hπs := cpt_comp (cpt_pair hX hC) hπ
  have f2 := cpt_bitFlag (cpt_comp (cpt_pair hπs hW') cR)
  have all := cpt_sel f1 (cpt_const []) (cpt_sel f2 (cpt_const []) (cpt_const [true]))
  have hS : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => projV π p fR ((unpairB s).1, (unpairB s).2)) :=
    cptp (cpt_comp all proj_cpt_ne) (fun s => by
      rw [proj_comb]
      simp [projV])
  exact cptp (cpt_comp cpt_pairB hS) (fun q => by
    obtain ⟨x, w⟩ := q
    simp only [unpairB_pairB])

/-- Projection of an NP language along a polynomial-time map, with a polynomially bounded
second argument, is in NP. -/
theorem projection_np (E : Language Bool) (π : List Bool × List Bool → List Bool)
    (p : Polynomial ℕ) (hE : E ∈ NP)
    (hπ : ComputableInPolyTime encodePair (fun x : List Bool => x) π) :
    ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ π (x, c) ∈ E} :
      Language Bool) ∈ NP := by
  obtain ⟨R, q, ⟨fR, hfR, cR⟩, hbd, hE'⟩ := PEqualNP.Library.L045 E hE
  obtain ⟨r, hr⟩ := output_length_poly (fun s => π (unpairB s)) (cpt_comp cpt_unpairB hπ)
  refine ⟨{qq | projV π p fR qq = true},
    Polynomial.C 2 * p + Polynomial.C 1 +
      q.comp (r.comp (Polynomial.C 2 * Polynomial.X + p + Polynomial.C 1)),
    ⟨projV π p fR, fun _ => Iff.rfl, cpt_projV π p fR hπ cR⟩, fun x => ?_⟩
  constructor
  · rintro ⟨c, hc, hmem⟩
    obtain ⟨w', hw'⟩ := (hE' _).1 hmem
    refine ⟨pairB c w', ?_, ?_⟩
    · have h1 := hbd _ _ hw'
      have h2 := hr (pairB x c)
      simp only [unpairB_pairB, pairB_length] at h2
      have h3 : r.eval (2 * x.length + c.length + 1) ≤
          r.eval (2 * x.length + p.eval x.length + 1) := eval_mono r (by omega)
      have h4 := eval_mono q (h2.trans h3)
      rw [pairB_length]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_comp, Polynomial.eval_X]
      omega
    · show projV π p fR (x, pairB c w') = true
      simp only [projV, unpairB_pairB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hc, (hfR _).1 hw'⟩
  · rintro ⟨w, -, hw⟩
    have hw' : projV π p fR (x, w) = true := hw
    simp only [projV, Bool.and_eq_true, decide_eq_true_eq] at hw'
    exact ⟨_, hw'.1, (hE' _).2 ⟨_, (hfR _).2 hw'.2⟩⟩

end PEqualNP.Library.Universal
