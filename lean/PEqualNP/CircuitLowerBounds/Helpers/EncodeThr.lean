import Mathlib
import PEqualNP.Defs

/-!
Helpers for L-clb-017: every encoder used by `encodeThr` can be decoded uniquely from the
front of a string, so `encodeThr` is injective.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open PEqualNP.CircuitLowerBounds

/-- `e` is uniquely decodable from the front of a string. -/
def PF {α : Type} (e : α → List Bool) : Prop :=
  ∀ a b s t, e a ++ s = e b ++ t → a = b ∧ s = t

theorem bits_pf (l₁ l₂ : List Bool) (s t : List Bool)
    (h : (l₁.flatMap (fun b => [true, b]) ++ [false]) ++ s =
      (l₂.flatMap (fun b => [true, b]) ++ [false]) ++ t) : l₁ = l₂ ∧ s = t := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => simpa using h
    | cons b l => simp at h
  | cons a l ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l' =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at h
      obtain ⟨hab, h⟩ := h
      obtain ⟨hl, hst⟩ := ih l' (by simpa using h)
      exact ⟨by rw [hab, hl], hst⟩

theorem foldr_bits (n : ℕ) : (Nat.bits n).foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih => rw [Nat.bits_append_bit n b h, List.foldr_cons, ih]

theorem bits_injective : Function.Injective Nat.bits :=
  Function.LeftInverse.injective foldr_bits

theorem encodeNat_pf : PF encodeNat := by
  intro a b s t h
  obtain ⟨hb, hst⟩ := bits_pf _ _ s t h
  exact ⟨bits_injective hb, hst⟩

theorem encodeInt_pf : PF encodeInt := by
  intro a b s t h
  simp only [encodeInt, List.cons_append, List.cons.injEq] at h
  obtain ⟨hs, h⟩ := h
  obtain ⟨hn, hst⟩ := encodeNat_pf _ _ s t h
  refine ⟨?_, hst⟩
  have hs' : a < 0 ↔ b < 0 := by simpa using hs
  omega

theorem encodeList_pf {α : Type} (e : α → List Bool) (he : PF e) : PF (encodeList e) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ s t h
    cases l₂ with
    | nil => simpa [encodeList] using h
    | cons b l => simp [encodeList] at h
  | cons a l ih =>
    intro l₂ s t h
    cases l₂ with
    | nil => simp [encodeList] at h
    | cons b l' =>
      simp only [encodeList, List.flatMap_cons, List.cons_append, List.append_assoc,
        List.cons.injEq, true_and] at h
      obtain ⟨hab, h⟩ := he a b _ _ h
      obtain ⟨hl, hst⟩ := ih l' s t (by simpa [encodeList] using h)
      exact ⟨by rw [hab, hl], hst⟩

/-- The encoder of one bottom gate. -/
def encodeGate (g : List ℤ × ℤ × ℤ) : List Bool :=
  encodeList encodeInt g.1 ++ encodeInt g.2.1 ++ encodeInt g.2.2

theorem encodeGate_pf : PF encodeGate := by
  rintro ⟨w, t₁, a₁⟩ ⟨w', t₂, a₂⟩ s t h
  simp only [encodeGate, List.append_assoc] at h
  obtain ⟨hw, h⟩ := encodeList_pf encodeInt encodeInt_pf _ _ _ _ h
  obtain ⟨ht, h⟩ := encodeInt_pf _ _ _ _ h
  obtain ⟨ha, hst⟩ := encodeInt_pf _ _ _ _ h
  exact ⟨by rw [hw, ht, ha], hst⟩

theorem encodeThr_injective : Function.Injective encodeThr := by
  rintro ⟨g₁, t₁⟩ ⟨g₂, t₂⟩ h
  have h' : encodeList encodeGate g₁ ++ encodeInt t₁ = encodeList encodeGate g₂ ++ encodeInt t₂ :=
    h
  obtain ⟨hg, h'⟩ := encodeList_pf encodeGate encodeGate_pf _ _ _ _ h'
  have h'' : encodeInt t₁ ++ [] = encodeInt t₂ ++ [] := by simpa using h'
  obtain ⟨ht, _⟩ := encodeInt_pf _ _ _ _ h''
  rw [hg, ht]

end PEqualNP.CircuitLowerBounds.Helpers
