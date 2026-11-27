import PEqualNP.Defs.Algebraic

/-!
# The self-delimiting number encoding is prefix-free

`algEncodeNat` writes each bit of a number preceded by `true` and ends with `false`. We show
that an encoded number followed by any string determines both the number and the rest.
-/

namespace PEqualNP.Library.Helpers.AlgEncode

open PEqualNP.Library

/-- Reading a little-endian bit list back as a number. -/
def bitsValue (l : List Bool) : ℕ := l.foldr (fun b n => Nat.bit b n) 0

theorem bitsValue_bits (n : ℕ) : bitsValue (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n h ih =>
    rw [Nat.bits_append_bit _ _ h]
    simp only [bitsValue, List.foldr_cons] at ih ⊢
    rw [ih]

theorem bits_injective : Function.Injective Nat.bits := by
  intro a b h
  rw [← bitsValue_bits a, ← bitsValue_bits b, h]

theorem flatMap_prefix_unique : ∀ (l l' s t : List Bool),
    l.flatMap (fun b => [true, b]) ++ false :: s = l'.flatMap (fun b => [true, b]) ++ false :: t →
      l = l' ∧ s = t
  | [], [], s, t, h => by simpa using h
  | [], _ :: _, s, t, h => by simp at h
  | _ :: _, [], s, t, h => by simp at h
  | x :: l, y :: l', s, t, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append,
      List.cons.injEq, true_and] at h
    obtain ⟨hxy, h⟩ := h
    obtain ⟨hl, hst⟩ := flatMap_prefix_unique l l' s t (by simpa using h)
    exact ⟨by rw [hxy, hl], hst⟩

theorem prefix_unique : ∀ (a b : ℕ) (s t : List Bool),
    PEqualNP.Library.algEncodeNat a ++ s = PEqualNP.Library.algEncodeNat b ++ t →
      a = b ∧ s = t := by
  intro a b s t h
  simp only [algEncodeNat, List.append_assoc, List.singleton_append] at h
  obtain ⟨hb, hst⟩ := flatMap_prefix_unique _ _ s t h
  exact ⟨bits_injective hb, hst⟩

theorem flatten_unique : ∀ (l l' : List ℕ) (s t : List Bool), l.length = l'.length →
    (l.map PEqualNP.Library.algEncodeNat).flatten ++ s =
      (l'.map PEqualNP.Library.algEncodeNat).flatten ++ t → l = l' ∧ s = t
  | [], [], s, t, _, h => by simpa using h
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | a :: l, b :: l', s, t, hlen, h => by
    simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h
    obtain ⟨hab, h⟩ := prefix_unique a b _ _ h
    obtain ⟨hl, hst⟩ := flatten_unique l l' s t (by simpa using hlen) h
    exact ⟨by rw [hab, hl], hst⟩

end PEqualNP.Library.Helpers.AlgEncode
