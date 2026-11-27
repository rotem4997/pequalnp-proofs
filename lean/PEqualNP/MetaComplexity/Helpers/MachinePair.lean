import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.Machines.FirstGRun
import PEqualNP.Library.Machines.Transducer
import PEqualNP.Defs.Search
import PEqualNP.Defs.CircuitLowerBounds

/-!
# Pairing two polynomial-time outputs, and the length of a code in unary

Helper module (proofs only, no statement may use it).

`ComputableInPolyTime ea eb f` mentions the input encoding only through `ea a` and the output
only through `eb (f a)`, so a machine for one function serves any other function whose encoded
input and output are the same strings (`cpt_transport`). With it, pairing is a chain of
machines on one and the same element `a`, re-encoded at each stage:

`ea a` to `(ea a, ea a)` (two passes), to `(eb (f a), ea a)` (run the machine of `f` on the
first component), to `(ea a, eb (f a))` (two passes), to `(ec (g a), eb (f a))` (run the
machine of `g`), to `eb (f a) ++ ec (g a)` (two passes).

The length of a code in unary is two finite-state transducers: every bit to `true` and a final
`false`, then a leading `true` and a second final `false`.
-/

namespace PEqualNP.MetaComplexity.Helpers.MachinePair

open PEqualNP.Library PEqualNP.Library.Machines

/-- A machine for `f` computes any `F` whose encoded inputs and outputs are those of `f` along
a map `h`. -/
theorem cpt_transport {α α' β β' Γ Δ : Type} {ea : α → List Γ} {eb : β → List Δ} {f : α → β}
    (c : Turing.TM2ComputableInPolyTime ea eb f) {ea' : α' → List Γ} {eb' : β' → List Δ}
    (h : α' → α) (F : α' → β') (hea : ∀ x, ea' x = ea (h x))
    (heb : ∀ x, eb' (F x) = eb (f (h x))) :
    PEqualNP.Library.ComputableInPolyTime ea' eb' F :=
  ⟨{ tm := c.tm
     inputAlphabet := c.inputAlphabet
     outputAlphabet := c.outputAlphabet
     time := c.time
     outputsFun := fun x => by
       rw [hea x, heb x]
       exact c.outputsFun (h x) }⟩

/-- The tagged pair of two binary strings. -/
abbrev tp (x w : List Bool) : List (Bool ⊕ Bool) := Gen.gpair (x, w)

theorem fm_tp {δ : Type} (x w : List Bool) (φ : Bool ⊕ Bool → Option δ) :
    (tp x w).filterMap φ = x.filterMap (fun b => φ (Sum.inl b)) ++
      w.filterMap (fun b => φ (Sum.inr b)) := by
  simp [tp, Gen.gpair, List.filterMap_append, List.filterMap_map]

theorem fm_some_map {γ δ : Type} (l : List γ) (k : γ → δ) :
    l.filterMap (fun b => some (k b)) = l.map k := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem fm_none {γ δ : Type} (l : List γ) :
    l.filterMap (fun _ => (none : Option δ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Pairing of two polynomial-time outputs, the output pair written as the concatenation of
the two codes. -/
theorem cpt_pairApp (α β γ : Type) (ea : α → List Bool) (eb : β → List Bool)
    (ec : γ → List Bool) (f : α → β) (g : α → γ)
    (hf : PEqualNP.Library.ComputableInPolyTime ea eb f)
    (hg : PEqualNP.Library.ComputableInPolyTime ea ec g) :
    PEqualNP.Library.ComputableInPolyTime ea (fun p : β × γ => eb p.1 ++ ec p.2)
      (fun a : α => (f a, g a)) := by
  obtain ⟨cf⟩ := hf
  obtain ⟨cg⟩ := hg
  -- stage 1: duplicate
  have s1 : PEqualNP.Library.ComputableInPolyTime ea (fun a : α => tp (ea a) (ea a))
      (fun a : α => a) := by
    refine twoPass_polyTime _ _ _ (fun b : Bool => some (Sum.inl b))
      (fun b : Bool => some (Sum.inr b)) ?_
    intro a
    rw [fm_some_map, fm_some_map]
    rfl
  -- stage 2: run `f` on the first component
  have s2 : PEqualNP.Library.ComputableInPolyTime (fun a : α => tp (ea a) (ea a))
      (fun a : α => tp (eb (f a)) (ea a)) (fun a : α => a) := by
    obtain ⟨c⟩ := Gen.first_polyTime (C := Bool) ea eb f cf
    exact cpt_transport c (fun a => (a, ea a)) (fun a => a) (fun _ => rfl) (fun _ => rfl)
  -- stage 3: swap
  have s3 : PEqualNP.Library.ComputableInPolyTime (fun a : α => tp (eb (f a)) (ea a))
      (fun a : α => tp (ea a) (eb (f a))) (fun a : α => a) := by
    refine twoPass_polyTime _ _ _
      (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some (Sum.inl b)) s)
      (fun s : Bool ⊕ Bool => Sum.elim (fun b => some (Sum.inr b)) (fun _ => none) s) ?_
    intro a
    simp only [fm_tp, Sum.elim_inl, Sum.elim_inr, fm_some_map, fm_none, List.nil_append,
      List.append_nil]
    rfl
  -- stage 4: run `g` on the first component
  have s4 : PEqualNP.Library.ComputableInPolyTime (fun a : α => tp (ea a) (eb (f a)))
      (fun a : α => tp (ec (g a)) (eb (f a))) (fun a : α => a) := by
    obtain ⟨c⟩ := Gen.first_polyTime (C := Bool) ea ec g cg
    exact cpt_transport c (fun a => (a, eb (f a))) (fun a => a) (fun _ => rfl) (fun _ => rfl)
  -- stage 5: concatenate in the other order
  have s5 : PEqualNP.Library.ComputableInPolyTime (fun a : α => tp (ec (g a)) (eb (f a)))
      (fun p : β × γ => eb p.1 ++ ec p.2) (fun a : α => (f a, g a)) := by
    refine twoPass_polyTime _ _ _
      (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some b) s)
      (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun _ => none) s) ?_
    intro a
    simp only [fm_tp, Sum.elim_inl, Sum.elim_inr, fm_none, List.nil_append, List.append_nil]
    rw [fm_some_map, fm_some_map]
    simp
  exact cpt_comp (cpt_comp (cpt_comp (cpt_comp s1 s2) s3) s4) s5

/-- Unary code of `n`, then `false`. -/
theorem fst_unary1 (x : List Bool) :
    fstRun (fun (_ : Unit) (_ : Bool) => ((), some true)) (fun _ => some false) () x =
      List.replicate x.length true ++ [false] := by
  induction x with
  | nil => rfl
  | cons a l ih => simp [fstRun, ih, List.replicate_succ]

/-- The second transducer: a leading `true`, a copy, and a final `false`. -/
def δ2 : Bool → Bool → Bool × Option Bool × Option Bool :=
  fun q a => if q then (true, some a, none) else (true, some true, some a)

theorem fst_unary2_rest (y : List Bool) :
    fstRun2 δ2 (fun _ => some false) true y = y ++ [false] := by
  induction y with
  | nil => rfl
  | cons a l ih => simp [fstRun2, δ2, ih]

theorem fst_unary2 (a : Bool) (y : List Bool) :
    fstRun2 δ2 (fun _ => some false) false (a :: y) = true :: a :: y ++ [false] := by
  simp [fstRun2, δ2, fst_unary2_rest]

/-- The length of the code of a formula, as a one-entry list of unary numbers. -/
theorem cpt_codeLength :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Search.encodeCNF
      (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]))
      (fun φ : PEqualNP.Search.CNF => [(PEqualNP.Search.encodeCNF φ).length]) := by
  have t1 : PEqualNP.Library.ComputableInPolyTime PEqualNP.Search.encodeCNF
      (fun φ : PEqualNP.Search.CNF =>
        List.replicate (PEqualNP.Search.encodeCNF φ).length true ++ [false])
      (fun φ => φ) :=
    fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some true)) (fun _ => some false) ()
      (fun φ => (fst_unary1 _).symm)
  have t2 : PEqualNP.Library.ComputableInPolyTime
      (fun φ : PEqualNP.Search.CNF =>
        List.replicate (PEqualNP.Search.encodeCNF φ).length true ++ [false])
      (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]))
      (fun φ : PEqualNP.Search.CNF => [(PEqualNP.Search.encodeCNF φ).length]) := by
    refine fst2_polyTime _ _ _ δ2 (fun _ => some false) false ?_
    intro φ
    cases hr : List.replicate (PEqualNP.Search.encodeCNF φ).length true with
    | nil =>
      simp [PEqualNP.CircuitLowerBounds.encodeList, hr, fstRun2, δ2]
    | cons b y =>
      rw [List.cons_append, fst_unary2]
      simp [PEqualNP.CircuitLowerBounds.encodeList, hr]
  exact cpt_comp t1 t2

end PEqualNP.MetaComplexity.Helpers.MachinePair
