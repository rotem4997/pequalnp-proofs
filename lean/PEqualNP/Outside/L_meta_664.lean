import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_664

variable {F : Type} [Field F] [CharP F 2]

def Q (b : F) (v : F × F) : F := v.1 ^ 2 + b * v.1 * v.2 + v.2 ^ 2

def cross (b : F) (p d : F × F) : F := b * (p.1 * d.2 + p.2 * d.1)

def poly (a c : F) : F →+ F where
  toFun x := a * x ^ 2 + c * x
  map_zero' := by simp
  map_add' x y := by rw [CharTwo.add_sq]; ring

lemma Q_ne (b : F) (hb : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0)
    (v : F × F) (hv : v ≠ 0) : Q b v ≠ 0 := by
  rcases v with ⟨x,y⟩
  change x ^ 2 + b * x * y + y ^ 2 ≠ 0
  intro he
  by_cases hy : y = 0
  · subst y
    simp at he
    exact hv (by simp [he])
  · apply hb (x / y)
    field_simp
    linear_combination he

lemma Q_line (b : F) (p d : F × F) (t : F) :
    Q b (p + t • d) = Q b p + poly (Q b d) (cross b p d) t := by
  change (p.1 + t * d.1) ^ 2 + b * (p.1 + t * d.1) * (p.2 + t * d.2) +
    (p.2 + t * d.2) ^ 2 = _ + ((d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2) * t ^ 2 +
    (b * (p.1 * d.2 + p.2 * d.1)) * t)
  rw [CharTwo.add_sq, CharTwo.add_sq]
  unfold Q
  ring

lemma poly_bijective [Fintype F] (a : F) (ha : a ≠ 0) :
    Function.Bijective (poly a 0) := by
  apply Finite.injective_iff_bijective.mp
  intro x y h
  change a * x ^ 2 + 0 * x = a * y ^ 2 + 0 * y at h
  simp only [zero_mul, add_zero] at h
  have hs : x ^ 2 = y ^ 2 := mul_left_cancel₀ ha h
  apply CharTwo.add_eq_zero.mp
  have h2 : (x + y) ^ 2 = 0 := by rw [CharTwo.add_sq, hs, CharTwo.add_self_eq_zero]
  simpa using h2

lemma poly_ker_card (a c : F) (ha : a ≠ 0) (hc : c ≠ 0) :
    Nat.card (poly a c).ker = 2 := by
  have hk : ((poly a c).ker : Set F) = {0,c/a} := by
    ext x
    change a * x ^ 2 + c * x = 0 ↔ x = 0 ∨ x = c / a
    rw [show a * x ^ 2 + c * x = x * (x * a + c) by ring, mul_eq_zero,
      CharTwo.add_eq_zero, eq_div_iff ha]
  change ((poly a c).ker : Set F).ncard = 2
  rw [hk]
  exact Set.ncard_pair (Ne.symm (div_ne_zero hc ha))

end PEqualNP.Outside.L_meta_664


namespace PEqualNP.Outside.L_meta_664

theorem offset_not_mem {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (b : F) (hb : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0) (p d : F × F)
    (h : cross b p d ≠ 0) : Q b p ∉ (poly (Q b d) (cross b p d)).range := by
  rintro ⟨t, ht⟩
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hz : Q b (p + t • d) = 0 := by
    rw [Q_line, ht]
    linear_combination Q b p * htwo
  have hv : p + t • d = 0 := by
    by_contra hn
    exact Q_ne b hb _ hn hz
  have hx : p.1 + t * d.1 = 0 := congrArg Prod.fst hv
  have hy : p.2 + t * d.2 = 0 := congrArg Prod.snd hv
  apply h
  unfold cross
  have he : p.1 * d.2 + p.2 * d.1 = 0 := by
    linear_combination d.2 * hx + d.1 * hy - (t * d.1 * d.2) * htwo
  rw [he, mul_zero]

end PEqualNP.Outside.L_meta_664


namespace PEqualNP.Outside.L_meta_664

lemma count_bij {F : Type} [Field F] [Fintype F] (f : F →+ F) (q : F)
    (A : AddSubgroup F) [DecidablePred (· ∈ A)] (hf : Function.Bijective f) :
    (Finset.univ.filter (fun t : F => q + f t ∈ A)).card = Nat.card A := by
  classical
  let e : F ≃ F := (Equiv.ofBijective f hf).trans (Equiv.addLeft q)
  calc
    _ = Nat.card {t : F // q + f t ∈ A} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card A := Nat.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))

lemma count_two {F : Type} [Field F] [Fintype F] (f : F →+ F) (q : F)
    (A : AddSubgroup F) [DecidablePred (· ∈ A)] (hk : Nat.card f.ker = 2)
    (hq : q ∉ f.range) :
    (Finset.univ.filter (fun t : F => q + f t ∈ A)).card = 0 ∨
    (Finset.univ.filter (fun t : F => q + f t ∈ A)).card = Nat.card A := by
  classical
  by_cases hex : ∃ s, q + f s ∈ A
  · right
    obtain ⟨s, hs⟩ := hex
    have hidx : f.range.index = 2 := by
      apply Nat.mul_right_cancel (Nat.card_pos (α := f.range))
      rw [f.range.index_mul_card, ← hk, AddSubgroup.card_ker_mul_card_range]
    have hne : ¬ (f.range ⊔ A : AddSubgroup F) ≤ f.range := by
      intro h
      have hmem : q + f s ∈ f.range := h ((show A ≤ f.range ⊔ A from le_sup_right) hs)
      exact hq (by simpa using f.range.sub_mem hmem (show f s ∈ f.range from ⟨s, rfl⟩))
    have ht : f.range ⊔ A = ⊤ := by
      have h1 := AddSubgroup.relIndex_mul_index (H := f.range) (K := f.range ⊔ A) le_sup_left
      rw [hidx] at h1
      apply AddSubgroup.index_eq_one.mp
      by_contra hn
      have hr : f.range.relIndex (f.range ⊔ A) ≠ 1 := fun h => hne (AddSubgroup.relIndex_eq_one.mp h)
      have hr0 : f.range.relIndex (f.range ⊔ A) ≠ 0 := by intro h; simp [h] at h1
      have hi0 : (f.range ⊔ A).index ≠ 0 := by intro h; simp [h] at h1
      have h4 := Nat.mul_le_mul
        (show 2 ≤ f.range.relIndex (f.range ⊔ A) by omega)
        (show 2 ≤ (f.range ⊔ A).index by omega)
      omega
    have hi : (A.comap f).index = A.index := by
      rw [A.index_comap, ← AddSubgroup.relIndex_sup_right f.range A, ht, AddSubgroup.relIndex_top_right]
    calc
      _ = Nat.card {t : F // q + f t ∈ A} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      _ = Nat.card (A.comap f) := by
        apply Nat.card_congr
        refine Equiv.subtypeEquiv (Equiv.addRight (-s)) (fun t => ?_)
        change q + f t ∈ A ↔ f (t + -s) ∈ A
        have he : f (t + -s) = (q + f t) - (q + f s) := by
          rw [map_add, map_neg]
          abel
        rw [he]
        exact ⟨fun h => A.sub_mem h hs, fun h => by simpa only [sub_add_cancel] using A.add_mem h hs⟩
      _ = Nat.card A := by
        apply Nat.mul_left_cancel (Nat.pos_of_ne_zero A.index_ne_zero_of_finite)
        rw [← hi, (A.comap f).index_mul_card, hi, A.index_mul_card]
  · left
    simpa [Finset.card_eq_zero, Finset.filter_eq_empty_iff] using (not_exists.mp hex)

end PEqualNP.Outside.L_meta_664




open PEqualNP.Outside.L_meta_664
theorem PEqualNP.Outside.L_meta_664 : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F instField instFin instDec instChar b hb A instMem p d hd
  change ((Finset.univ.filter (fun t : F => Q b (p + t • d) ∈ A)).card = 0 ∨
    (Finset.univ.filter (fun t : F => Q b (p + t • d) ∈ A)).card = Nat.card A) ∧
    (p = 0 → (Finset.univ.filter (fun t : F => Q b (p + t • d) ∈ A)).card = Nat.card A)
  simp only [Q_line]
  have ha := Q_ne b hb d hd
  by_cases h : cross b p d = 0
  · rw [h]
    have eqCard := count_bij (poly (Q b d) 0) (Q b p) A (poly_bijective (Q b d) ha)
    exact ⟨Or.inr eqCard, fun _ => eqCard⟩
  · constructor
    · exact count_two _ _ A (poly_ker_card _ _ ha h) (offset_not_mem b hb p d h)
    · intro hp
      subst p
      exact (h (by simp [cross])).elim
