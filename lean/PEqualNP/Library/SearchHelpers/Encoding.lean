import PEqualNP.Defs
import Mathlib.Data.Nat.Bitwise

/-!
# Helpers: the binary encoding of CNF formulas is uniquely decodable

Used by the proof of `L-lib-026`. Each lemma peels one encoded object off the front of a
string followed by an arbitrary rest.
-/

namespace PEqualNP.Library.SearchHelpers

open PEqualNP.Search

/-- `Nat.bits` is injective. -/
theorem bits_injective : Function.Injective Nat.bits := by
  intro n m h
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, h]

/-- A run of digits closed by a non-digit pair is read back uniquely. -/
theorem digits_append_inj : ∀ (ds ds' : List Bool) (b b' : Bool) (r r' : List Bool),
    (ds.flatMap fun d => [true, d]) ++ (false :: b :: r) =
      (ds'.flatMap fun d => [true, d]) ++ (false :: b' :: r') →
    ds = ds' ∧ b = b' ∧ r = r' := by
  intro ds
  induction ds with
  | nil =>
    intro ds' b b' r r' h
    cases ds' with
    | nil => simp_all
    | cons d ds' => simp at h
  | cons d ds ih =>
    intro ds' b b' r r' h
    cases ds' with
    | nil => simp at h
    | cons d' ds' =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at h
      obtain ⟨hd, h⟩ := h
      obtain ⟨h1, h2, h3⟩ := ih ds' b b' r r' h
      exact ⟨by rw [hd, h1], h2, h3⟩

theorem literal_append_inj (l l' : Literal) (r r' : List Bool)
    (h : encodeLiteral l ++ r = encodeLiteral l' ++ r') : l = l' ∧ r = r' := by
  obtain ⟨i, b⟩ := l
  obtain ⟨i', b'⟩ := l'
  simp only [encodeLiteral, List.cons_append, List.nil_append, List.append_assoc,
    List.cons.injEq, true_and] at h
  obtain ⟨hb, h⟩ := h
  obtain ⟨h1, -, h3⟩ := digits_append_inj _ _ true true r r' h
  exact ⟨by rw [bits_injective h1, hb], h3⟩

theorem encodeLiteral_head (l : Literal) (r : List Bool) :
    ∃ t, encodeLiteral l ++ r = true :: t := ⟨_, rfl⟩

theorem clause_append_inj : ∀ (c c' : Clause) (r r' : List Bool),
    encodeClause c ++ r = encodeClause c' ++ r' → c = c' ∧ r = r' := by
  intro c
  induction c with
  | nil =>
    intro c' r r' h
    cases c' with
    | nil => simpa [encodeClause] using h
    | cons l' c' =>
      exfalso
      obtain ⟨t, ht⟩ := encodeLiteral_head l' (c'.flatMap encodeLiteral ++ [false, false] ++ r')
      simp only [encodeClause, List.flatMap_cons, List.append_assoc] at h ht
      rw [ht] at h
      simp at h
  | cons l c ih =>
    intro c' r r' h
    cases c' with
    | nil =>
      exfalso
      obtain ⟨t, ht⟩ := encodeLiteral_head l (c.flatMap encodeLiteral ++ [false, false] ++ r)
      simp only [encodeClause, List.flatMap_cons, List.append_assoc] at h ht
      rw [ht] at h
      simp at h
    | cons l' c' =>
      simp only [encodeClause, List.flatMap_cons, List.append_assoc] at h
      obtain ⟨h1, h2⟩ := literal_append_inj l l' _ _ h
      have := ih c' r r' (by simpa [encodeClause, List.append_assoc] using h2)
      exact ⟨by rw [h1, this.1], this.2⟩

theorem encodeCNF_injective : Function.Injective encodeCNF := by
  intro φ
  induction φ with
  | nil =>
    intro φ' h
    cases φ' with
    | nil => rfl
    | cons c φ' => simp [encodeCNF, encodeClause] at h
  | cons c φ ih =>
    intro φ' h
    cases φ' with
    | nil => simp [encodeCNF, encodeClause] at h
    | cons c' φ' =>
      simp only [encodeCNF, List.flatMap_cons] at h
      obtain ⟨h1, h2⟩ := clause_append_inj c c' _ _ h
      rw [h1, ih h2]

end PEqualNP.Library.SearchHelpers
