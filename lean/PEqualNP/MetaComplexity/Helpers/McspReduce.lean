import PEqualNP.MetaComplexity.Helpers.Machines.VerifierPoly
import PEqualNP.Library.L017

/-!
# Helper module (proofs only): MCSP reduces to partial MCSP

A truth table is a partial truth table with every entry defined. The reduction copies the
instance up to and including the first `false` (the unary size bound and the separator) and
then writes every table bit `b` as the two bits `true, b`, the code of the defined entry
`some b`. This is one finite-state transducer with a Boolean state, so it is polynomial-time
computable. A string is in `MCSP` exactly when its image is in `PartialMCSP`, and since partial
MCSP is in NP, so is MCSP.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.MetaComplexity

/-! ## The transducer -/

/-- The state says whether the separator has been read. Before it, copy; after it, write
`true` and then the bit read. -/
def δred : Bool → Bool → Bool × Option Bool × Option Bool
  | false, true => (false, some true, none)
  | false, false => (true, some false, none)
  | true, b => (true, some true, some b)

/-- Nothing is written at the end of the input. -/
def finRed : Bool → Option Bool := fun _ => none

/-- The reduction from MCSP to partial MCSP. -/
def red : List Bool → List Bool := fstRun2 δred finRed false

theorem enc_none_cons (T : List (Option Bool)) :
    encodePartial (none :: T) = false :: false :: encodePartial T := by
  simp [encodePartial]

theorem enc_some_cons (b : Bool) (T : List (Option Bool)) :
    encodePartial (some b :: T) = true :: b :: encodePartial T := by
  simp [encodePartial]

theorem red_run_true (T : List Bool) :
    fstRun2 δred finRed true T = encodePartial (T.map some) := by
  induction T with
  | nil => simp [fstRun2, finRed, encodePartial]
  | cons b T ih =>
    rw [List.map_cons, enc_some_cons, ← ih]
    simp [fstRun2, δred]

theorem red_run_false (s : ℕ) (T : List Bool) :
    fstRun2 δred finRed false (List.replicate s true ++ false :: T) =
      List.replicate s true ++ false :: encodePartial (T.map some) := by
  induction s with
  | zero => simp [fstRun2, δred, red_run_true]
  | succ s ih =>
    rw [List.replicate_succ, List.cons_append, List.cons_append, ← ih]
    simp [fstRun2, δred]

/-- The image of an instance of MCSP is the instance of partial MCSP with the same bound and the
same table, every entry defined. -/
theorem red_instance (s : ℕ) (T : List Bool) :
    red (List.replicate s true ++ false :: T) =
      List.replicate s true ++ false :: encodePartial (T.map some) :=
  red_run_false s T

/-- A string with no `false` is left unchanged. -/
theorem red_all_true (x : List Bool) (h : ∀ b ∈ x, b = true) : red x = x := by
  show fstRun2 δred finRed false x = x
  induction x with
  | nil => simp [fstRun2, finRed]
  | cons b x ih =>
    have hb : b = true := h b (by simp)
    subst hb
    have hx : fstRun2 δred finRed false x = x := ih (fun c hc => h c (by simp [hc]))
    simp [fstRun2, δred, hx]

/-! ## Parsing -/

/-- A string is all `true`, or splits at its first `false`. -/
theorem split_cases (x : List Bool) :
    (∀ b ∈ x, b = true) ∨ ∃ (s : ℕ) (T : List Bool), x = List.replicate s true ++ false :: T := by
  induction x with
  | nil => left; simp
  | cons b x ih =>
    cases b with
    | false => right; exact ⟨0, x, by simp⟩
    | true =>
      rcases ih with h | ⟨s, T, h⟩
      · left
        intro c hc
        rcases List.mem_cons.mp hc with hc | hc
        · exact hc
        · exact h c hc
      · right
        exact ⟨s + 1, T, by rw [h, List.replicate_succ, List.cons_append]⟩

/-- The split at the first `false` is unique. -/
theorem split_unique : ∀ (s s' : ℕ) (A B : List Bool),
    List.replicate s true ++ false :: A = List.replicate s' true ++ false :: B →
      s = s' ∧ A = B
  | 0, 0, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.nil_append] at h
    exact ⟨rfl, (List.cons.inj h).2⟩
  | 0, s' + 1, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | s + 1, 0, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | s + 1, s' + 1, A, B, h => by
    rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append] at h
    obtain ⟨h1, h2⟩ := split_unique s s' A B (List.cons.inj h).2
    exact ⟨by rw [h1], h2⟩

/-- The code of a partial truth table determines it. -/
theorem encodePartial_injective : ∀ (T T' : List (Option Bool)),
    encodePartial T = encodePartial T' → T = T'
  | [], [], _ => rfl
  | [], o :: T', h => by
    have hl := congrArg List.length h
    rw [length_encodePartial, length_encodePartial] at hl
    simp at hl
  | o :: T, [], h => by
    have hl := congrArg List.length h
    rw [length_encodePartial, length_encodePartial] at hl
    simp at hl
  | o :: T, o' :: T', h => by
    have ih := encodePartial_injective T T'
    rcases o with _ | b <;> rcases o' with _ | b'
    · rw [enc_none_cons, enc_none_cons] at h
      rw [ih (List.cons.inj (List.cons.inj h).2).2]
    · rw [enc_none_cons, enc_some_cons] at h
      exact absurd (List.cons.inj h).1 (by decide)
    · rw [enc_some_cons, enc_none_cons] at h
      exact absurd (List.cons.inj h).1 (by decide)
    · rw [enc_some_cons, enc_some_cons] at h
      rw [(List.cons.inj (List.cons.inj h).2).1, ih (List.cons.inj (List.cons.inj h).2).2]

/-! ## Reading a table with every entry defined -/

theorem getD_map_some (T : List Bool) (j : ℕ) (b : Bool)
    (h : (T.map some).getD j none = some b) : T.getD j false = b := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at h ⊢
  cases hj : T[j]? with
  | none => rw [hj] at h; simp at h
  | some v => rw [hj] at h; simpa using h

theorem getD_map_some_lt (T : List Bool) (j : ℕ) (h : j < T.length) :
    (T.map some).getD j none = some (T.getD j false) := by
  have h' : j < (T.map some).length := by rw [List.length_map]; exact h
  rw [List.getD_eq_getElem _ _ h', List.getD_eq_getElem _ _ h, List.getElem_map]

/-! ## The reduction is correct -/

theorem mcsp_iff (x : List Bool) : x ∈ MCSP ↔ red x ∈ PartialMCSP := by
  constructor
  · rintro ⟨n, s, T, rfl, hT, hC⟩
    refine ⟨n, s, T.map some, red_instance s T, by rw [List.length_map]; exact hT,
      tableFun n T, ?_, hC⟩
    intro y b hb
    exact getD_map_some T (tableIndex y) b hb
  · rintro ⟨n, s, T', hx, hT', f, hf, hC⟩
    rcases split_cases x with hall | ⟨s0, T, rfl⟩
    · exfalso
      rw [red_all_true x hall] at hx
      have hmem : false ∈ x := by rw [hx]; simp
      exact Bool.false_ne_true (hall false hmem)
    · rw [red_instance] at hx
      obtain ⟨hs, he⟩ := split_unique _ _ _ _ hx
      have hTT : T.map some = T' := encodePartial_injective _ _ he
      subst hTT
      subst hs
      rw [List.length_map] at hT'
      refine ⟨n, s0, T, rfl, hT', ?_⟩
      have hfe : tableFun n T = f := by
        funext y
        have hlt : tableIndex y < T.length := by rw [hT']; exact tableIndex_lt y
        exact (hf y _ (getD_map_some_lt T _ hlt)).symm
      rw [hfe]
      exact hC

/-- MCSP reduces to partial MCSP in polynomial time. -/
theorem mcsp_reduces : PolyTimeReducible MCSP PartialMCSP :=
  ⟨red, PEqualNP.MetaComplexity.Helpers.Machines.cpt_fstRun2 δred finRed false, mcsp_iff⟩

/-- MCSP is in NP. -/
theorem mcsp_mem_NP : MCSP ∈ NP :=
  PEqualNP.Library.L017 MCSP PartialMCSP mcsp_reduces
    PEqualNP.MetaComplexity.Helpers.Machines.partialMCSP_mem_NP

end PEqualNP.MetaComplexity.Helpers
