import Mathlib
import PEqualNP.Defs

-- Each chosen line meets an outside line in at most one point.
theorem PEqualNP.Outside.L_meta_3495 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), x7.card ≤ x1 → ∀ (x9 x10 : Fin x2 → Prop), (∀ (x11 x12 : Fin x2), x3 x11 x12 → x9 x11 ∨ x10 x12) → (∀ (x12 : Fin x2), x9 x12 → ∃ x14 ∈ x7, x3 x12 x14) → (∀ x13 ∈ x7, ¬x10 x13) → (∀ (x14 : Fin x2), x9 x14 ↔ ∃ x15 ∈ x7, x3 x14 x15) ∧ ∀ (x14 : Fin x2), x10 x14 ↔ x14 ∉ x7 := by
  classical
  intro q n inc dec degree unique chosen bound points lines cover supported blocked
  constructor
  · intro p
    refine ⟨supported p, ?_⟩
    rintro ⟨l, hl, hp⟩
    exact (cover p l hp).resolve_right (blocked l hl)
  · intro l
    refine ⟨fun hl hin => blocked l hin hl, ?_⟩
    intro outside
    by_contra off
    have hit (p : {p : Fin n // inc p l}) :
        ∃ s : {s : Fin n // s ∈ chosen}, inc p.val s.val := by
      obtain ⟨s,hs,hp⟩ := supported p.val ((cover p.val l p.property).resolve_right off)
      exact ⟨⟨s,hs⟩,hp⟩
    let f (p : {p : Fin n // inc p l}) := Classical.choose (hit p)
    have on (p : {p : Fin n // inc p l}) : inc p.val (f p).val := Classical.choose_spec (hit p)
    have injective : Function.Injective f := by
      intro p r eqf
      by_contra different
      have ne : p.val ≠ r.val := fun h => different (Subtype.ext h)
      have hr : inc r.val (f p).val := by rw [eqf]; exact on r
      have eql : l = (f p).val := (unique p.val r.val ne).unique
        ⟨p.property,r.property⟩ ⟨on p,hr⟩
      exact outside (eql ▸ (f p).property)
    have small := Fintype.card_le_of_injective f injective
    rw [degree l,Fintype.card_coe] at small
    omega
