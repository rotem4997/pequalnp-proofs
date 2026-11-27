import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.Machines.AllTrue
import PEqualNP.Library.Machines.LenLE
import PEqualNP.Library.Machines.FirstGRun
import PEqualNP.Library.L055

/-!
# Helper module (proofs only): the witness length bound inside the verifier

This is a helper module: it holds proofs only, no new notions. Given a polynomial-time decider
`fR` for a set of pairs and a polynomial `p`, the function
`q ↦ decide (q.2.length ≤ p.eval q.1.length) && fR q` is polynomial-time computable.

A machine is only specified on well-formed inputs, so the construction works on raw lists over
`Bool ⊕ Bool`: decode the raw list into a pair, compute each of the two bits from a copy of the
raw list, and answer whether both bits are true. Restricting to well-formed inputs at the end
costs nothing.
-/

namespace PEqualNP.Library.Machines

open PEqualNP.Library

/-- Decoding a raw list over `Bool ⊕ Bool` into a pair of strings. -/
def nfDec (l : List (Bool ⊕ Bool)) : List Bool × List Bool :=
  (l.filterMap Sum.getLeft?, l.filterMap Sum.getRight?)

theorem nfDec_encodePair (q : List Bool × List Bool) : nfDec (encodePair q) = q := by
  obtain ⟨x, w⟩ := q
  have h1 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getLeft? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  have h2 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getLeft? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h3 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getRight? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h4 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getRight? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  simp only [nfDec, encodePair, List.filterMap_append, h1, h2, h3, h4, List.append_nil,
    List.nil_append]

/-- Decoding is polynomial-time computable. -/
theorem nfDec_polyTime :
    ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) encodePair nfDec := by
  refine twoPass_polyTime _ _ _
    (fun s : Bool ⊕ Bool => (Sum.getLeft? s).map Sum.inl)
    (fun s : Bool ⊕ Bool => (Sum.getRight? s).map Sum.inr) ?_
  intro l
  simp only [nfDec, encodePair, List.map_filterMap]

/-- Restricting a machine on raw lists to the well-formed inputs. -/
theorem nf_restrict {β βΓ : Type} {eb : β → List βΓ} {F : List (Bool ⊕ Bool) → β}
    (h : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) eb F) :
    ComputableInPolyTime encodePair eb (fun q => F (encodePair q)) := by
  obtain ⟨c⟩ := h
  exact ⟨⟨c.toTM2ComputableAux, c.time, fun q => c.outputsFun (encodePair q)⟩⟩

/-- Two bits computed from the same raw list can be combined by conjunction. -/
theorem nf_and {A B : List (Bool ⊕ Bool) → Bool}
    (hA : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool A)
    (hB : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool B) :
    ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool
      (fun l => B l && A l) := by
  obtain ⟨cA⟩ := hA
  obtain ⟨cB⟩ := hB
  have dup : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l)
      (fun p : List (Bool ⊕ Bool) × List (Bool ⊕ Bool) => Gen.gpair (p.1, p.2))
      (fun l => (l, l)) := by
    refine twoPass_polyTime _ _ _ (fun s => some (Sum.inl s)) (fun s => some (Sum.inr s)) ?_
    intro l
    have e1 : ∀ l : List (Bool ⊕ Bool), l.filterMap
        (fun s => some (Sum.inl (β := Bool ⊕ Bool) s)) = l.map Sum.inl := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp
    have e2 : ∀ l : List (Bool ⊕ Bool), l.filterMap
        (fun s => some (Sum.inr (α := Bool ⊕ Bool) s)) = l.map Sum.inr := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp
    simp only [Gen.gpair, e1, e2]
  have s1 : ComputableInPolyTime
      (fun p : List (Bool ⊕ Bool) × List (Bool ⊕ Bool) => Gen.gpair (p.1, p.2))
      (fun p : Bool × List (Bool ⊕ Bool) => Gen.gpair (Computability.encodeBool p.1, p.2))
      (fun p => (A p.1, p.2)) :=
    Gen.first_polyTime (C := Bool ⊕ Bool) (fun l : List (Bool ⊕ Bool) => l)
      Computability.encodeBool A cA
  have sw : ComputableInPolyTime
      (fun p : Bool × List (Bool ⊕ Bool) => Gen.gpair (Computability.encodeBool p.1, p.2))
      (fun p : List (Bool ⊕ Bool) × List Bool => Gen.gpair (p.1, p.2))
      (fun p => (p.2, [p.1])) := by
    refine twoPass_polyTime _ _ _
      (fun s : Bool ⊕ (Bool ⊕ Bool) => Sum.elim (fun _ => none) (fun b => some (Sum.inl b)) s)
      (fun s : Bool ⊕ (Bool ⊕ Bool) => Sum.elim (fun b => some (Sum.inr b)) (fun _ => none) s) ?_
    rintro ⟨b, l⟩
    have h1 : ∀ l : List (Bool ⊕ Bool), (l.map (Sum.inr (α := Bool))).filterMap
        (fun s : Bool ⊕ (Bool ⊕ Bool) =>
          Sum.elim (fun _ => none) (fun b => some (Sum.inl (β := Bool) b)) s) =
        l.map Sum.inl := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp
    have h2 : ∀ l : List (Bool ⊕ Bool), (l.map (Sum.inr (α := Bool))).filterMap
        (fun s : Bool ⊕ (Bool ⊕ Bool) =>
          Sum.elim (fun b => some (Sum.inr (α := Bool ⊕ Bool) b)) (fun _ => none) s) = [] := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp
    simp [Gen.gpair, Computability.encodeBool, h2]
    exact (h1 l).symm
  have s2 : ComputableInPolyTime
      (fun p : List (Bool ⊕ Bool) × List Bool => Gen.gpair (p.1, p.2))
      (fun p : Bool × List Bool => Gen.gpair (Computability.encodeBool p.1, p.2))
      (fun p => (B p.1, p.2)) :=
    Gen.first_polyTime (C := Bool) (fun l : List (Bool ⊕ Bool) => l)
      Computability.encodeBool B cB
  have cv : ComputableInPolyTime
      (fun p : Bool × List Bool => Gen.gpair (Computability.encodeBool p.1, p.2))
      encodePair (fun p => (([p.1], p.2) : List Bool × List Bool)) := by
    refine filterMap_polyTime _ _ _ (fun s => some s) ?_
    intro p
    simp only [List.filterMap_some]
    rfl
  have h := cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp dup s1) sw) s2) cv)
    allTrue_polyTime
  have e : (fun l : List (Bool ⊕ Bool) => B l && A l) =
      (fun l : List (Bool ⊕ Bool) => ([B l] ++ [A l]).all id) := by
    funext l; simp
  rw [e]; exact h

/-- The verifier with the witness length bound built in: polynomial-time decidable whenever the
original verifier is. -/
theorem nf_decider (fR : List Bool × List Bool → Bool) (p : Polynomial ℕ)
    (cR : ComputableInPolyTime encodePair Computability.encodeBool fR) :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun q : List Bool × List Bool => decide (q.2.length ≤ p.eval q.1.length) && fR q) := by
  have hA : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool
      (fun l => fR (nfDec l)) := cpt_comp nfDec_polyTime cR
  have hB0 := cpt_comp (cpt_comp nfDec_polyTime (cpt_first (PEqualNP.Library.L055 p)))
    LenCmp.lenLE_polyTime
  have hB : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool
      (fun l => decide ((nfDec l).2.length ≤ p.eval (nfDec l).1.length)) := by
    have e : (fun l : List (Bool ⊕ Bool) =>
        decide ((nfDec l).2.length ≤ p.eval (nfDec l).1.length)) =
        (fun l : List (Bool ⊕ Bool) => decide ((nfDec l).2.length ≤
          (List.replicate (p.eval (nfDec l).1.length) true).length)) := by
      funext l; simp
    rw [e]; exact hB0
  have h := nf_restrict (nf_and hA hB)
  have e : (fun q : List Bool × List Bool =>
      decide (q.2.length ≤ p.eval q.1.length) && fR q) =
      (fun q : List Bool × List Bool =>
        decide ((nfDec (encodePair q)).2.length ≤ p.eval (nfDec (encodePair q)).1.length) &&
          fR (nfDec (encodePair q))) := by
    funext q; rw [nfDec_encodePair]
  rw [e]; exact h

end PEqualNP.Library.Machines
