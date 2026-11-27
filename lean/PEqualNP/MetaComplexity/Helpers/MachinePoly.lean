import PEqualNP.Defs
import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Helper module (proofs only): polynomials on unary tuples, and a context loop

* `l507`: a fixed list of polynomials with natural coefficients, evaluated on a tuple of unary
  numbers (missing entries read 0), is polynomial time. Constants, sums (append of unary strings)
  and products by a variable (unary multiplication by a projection), by induction on the
  polynomial; then the outputs are concatenated by a fixed list of appends.
-/

namespace PEqualNP.MetaComplexity.Helpers.MachinePoly

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
  PEqualNP.CircuitLowerBounds

/-- Polynomial-time computability of a function on plain bit strings. -/
local notation "CPTs" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

theorem mp_cptE {f f' : List Bool → List Bool} (h : CPTs f) (e : ∀ a, f a = f' a) :
    CPTs f' := by
  obtain rfl : f = f' := funext e
  exact h

/-- A string machine re-read on encoded inputs and outputs. -/
theorem mp_lift {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {F : List Bool → List Bool} {f : α → β} (hF : CPTs F) (h : ∀ a, F (ea a) = eb (f a)) :
    ComputableInPolyTime ea eb f := by
  obtain ⟨c⟩ := hF
  have h1 : ComputableInPolyTime ea (fun x : List Bool => x) (fun a => F (ea a)) :=
    ⟨⟨c.toTM2ComputableAux, c.time, fun a => c.outputsFun (ea a)⟩⟩
  have e : (fun a => F (ea a)) = (fun a => eb (f a)) := funext h
  rw [e] at h1
  obtain ⟨c1⟩ := h1
  exact ⟨⟨c1.toTM2ComputableAux, c1.time, fun a => c1.outputsFun a⟩⟩

/-- A typed machine with bit-string output, seen as a machine onto its output code. -/
theorem mp_out {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (h : ComputableInPolyTime ea eb f) :
    ComputableInPolyTime ea (fun x : List Bool => x) (fun a => eb (f a)) := by
  obtain ⟨c⟩ := h
  exact ⟨⟨c.toTM2ComputableAux, c.time, fun a => c.outputsFun a⟩⟩

/-- The unary tuple code is `encL`. -/
theorem mp_encList (t : List ℕ) :
    encodeList (fun a : ℕ => List.replicate a true ++ [false]) t = encL t := rfl

theorem mp_encL_cons (a : ℕ) (l : List ℕ) : encL (a :: l) = un (a + 1) ++ false :: encL l := by
  simp [encL, encNs, encN]

/-! ## Projections -/

/-- The `i`-th entry of a tuple code, in unary, missing entries read 0. -/
def proj (i : ℕ) (s : List Bool) : List Bool := (hd (dropN^[i] s)).tail

theorem mp_hd_iter_false (i : ℕ) : hd (dropN^[i] [false]) = [] := by
  cases i with
  | zero => rfl
  | succ i =>
    rw [Function.iterate_succ_apply]
    have : dropN [false] = [] := rfl
    rw [this, Function.iterate_fixed (f := dropN) (x := []) rfl]
    rfl

theorem proj_spec (i : ℕ) (t : List ℕ) : proj i (encL t) = un (t.getD i 0) := by
  induction i generalizing t with
  | zero =>
    cases t with
    | nil => rfl
    | cons a l =>
      show (hd (encL (a :: l))).tail = _
      rw [mp_encL_cons, hd_un]
      rfl
  | succ i ih =>
    cases t with
    | nil =>
      simp only [proj]
      have : encL [] = [false] := rfl
      rw [this, mp_hd_iter_false]
      rfl
    | cons a l =>
      have h := ih l
      simp only [proj] at h ⊢
      rw [Function.iterate_succ_apply, mp_encL_cons, dropN_un, h]
      simp

theorem cpt_dropN_iter (i : ℕ) : CPTs (dropN^[i]) := by
  induction i with
  | zero => exact cpt_id
  | succ i ih =>
    exact mp_cptE (cpt_comp ih cpt_dropN) (fun s => by
      rw [Function.iterate_succ_apply'])

theorem cpt_proj (i : ℕ) : CPTs (proj i) :=
  mp_cptE (cpt_comp (cpt_comp (cpt_dropN_iter i) cpt_hd) cpt_tail) (fun _ => rfl)

/-! ## Polynomials -/

theorem poly_good (s : ℕ) (q : MvPolynomial (Fin s) ℕ) :
    ∃ G : List Bool → List Bool, CPTs G ∧
      ∀ t : List ℕ, G (encL t) = un (MvPolynomial.eval (fun i : Fin s => t.getD i.val 0) q) := by
  induction q using MvPolynomial.induction_on with
  | C a => exact ⟨fun _ => un a, cpt_const _, fun t => by simp⟩
  | add p q hp hq =>
    obtain ⟨Gp, hGp, ep⟩ := hp
    obtain ⟨Gq, hGq, eq⟩ := hq
    refine ⟨fun x => Gp x ++ Gq x, cpt_app2 hGp hGq, fun t => ?_⟩
    simp only [ep, eq, MvPolynomial.eval_add, un, List.replicate_add]
  | mul_X p i hp =>
    obtain ⟨Gp, hGp, ep⟩ := hp
    refine ⟨fun x => mulU (Gp x) (proj i.val x), cpt_mulU2 hGp (cpt_proj i.val), fun t => ?_⟩
    simp only [ep, proj_spec, mulU, un_length, MvPolynomial.eval_mul, MvPolynomial.eval_X]

theorem list_good (s : ℕ) (P : List (MvPolynomial (Fin s) ℕ)) :
    ∃ H : List Bool → List Bool, CPTs H ∧
      ∀ t : List ℕ, H (encL t) =
        encNs (P.map (fun q => MvPolynomial.eval (fun i : Fin s => t.getD i.val 0) q)) := by
  induction P with
  | nil => exact ⟨fun _ => [], cpt_const _, fun t => rfl⟩
  | cons q P ih =>
    obtain ⟨H, hH, eH⟩ := ih
    obtain ⟨G, hG, eG⟩ := poly_good s q
    refine ⟨fun x => (true :: (G x ++ [false])) ++ H x,
      cpt_app2 (cpt_app2 (cpt_const [true]) (cpt_app2 hG (cpt_const [false]))) hH, fun t => ?_⟩
    simp only [eH, eG, List.map_cons, encNs_cons, encN, un_succ, List.cons_append]

theorem l507 (s : ℕ) (P : List (MvPolynomial (Fin s) ℕ)) :
    ComputableInPolyTime (encodeList (fun a : ℕ => List.replicate a true ++ [false]))
      (encodeList (fun a : ℕ => List.replicate a true ++ [false]))
      (fun t : List ℕ => P.map (fun q : MvPolynomial (Fin s) ℕ =>
        MvPolynomial.eval (fun i : Fin s => t.getD i.val 0) q)) := by
  obtain ⟨H, hH, eH⟩ := list_good s P
  refine mp_lift (cpt_app2 hH (cpt_const [false])) (fun t => ?_)
  simp only [mp_encList, eH]
  rfl

end PEqualNP.MetaComplexity.Helpers.MachinePoly
