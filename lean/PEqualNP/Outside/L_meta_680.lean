import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_680

-- The common elements of two translates are the pairs of D with the difference of the shifts.
theorem inter_eq {n : ℕ} (D : Finset (ZMod n)) (s t : ZMod n) :
    D.image (fun a : ZMod n => a + s) ∩ D.image (fun a : ZMod n => a + t)
      = ((D ×ˢ D).filter (fun q : ZMod n × ZMod n => q.1 - q.2 = t - s)).image
          (fun q => q.1 + s) := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩
    refine ⟨(a, b), ⟨⟨ha, hb⟩, ?_⟩, hax⟩
    show a - b = t - s
    linear_combination hax - hbx
  · rintro ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hd⟩, hx⟩
    simp only at ha hb hd hx
    refine ⟨⟨a, ha, hx⟩, ⟨b, hb, ?_⟩⟩
    linear_combination hx - hd

theorem inj_on {n : ℕ} (D : Finset (ZMod n)) (s t : ZMod n) :
    Set.InjOn (fun q : ZMod n × ZMod n => q.1 + s)
      (((D ×ˢ D).filter (fun q : ZMod n × ZMod n => q.1 - q.2 = t - s) :
        Finset (ZMod n × ZMod n)) : Set (ZMod n × ZMod n)) := by
  rintro ⟨a, b⟩ hq ⟨a', b'⟩ hq' h
  rw [Finset.mem_coe, Finset.mem_filter] at hq hq'
  have h1 : a = a' := add_right_cancel h
  have hd : a - b = t - s := hq.2
  have hd' : a' - b' = t - s := hq'.2
  have h2 : b = b' := by linear_combination h1 - hd + hd'
  rw [h1, h2]

theorem count_eq {n : ℕ} [NeZero n] (D : Finset (ZMod n)) (x : ZMod n) :
    Finset.univ.filter (fun w : ZMod n => x ∈ D.image (fun a : ZMod n => a + w))
      = D.image (fun a : ZMod n => x - a) := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, by ring⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, by ring⟩

end PEqualNP.Outside.L_meta_680

theorem PEqualNP.Outside.L_meta_680 : ∀ (n : ℕ) [NeZero n] (D : Finset (ZMod n)),
    (∀ d : ZMod n, d ≠ 0 → ((D ×ˢ D).filter (fun q : ZMod n × ZMod n => q.1 - q.2 = d)).card = 1) →
    (∀ s t : ZMod n, s ≠ t →
        (D.image (fun a : ZMod n => a + s) ∩ D.image (fun a : ZMod n => a + t)).card = 1) ∧
    (∀ x : ZMod n,
        (Finset.univ.filter (fun w : ZMod n => x ∈ D.image (fun a : ZMod n => a + w))).card = D.card) := by
  intro n _ D hD
  constructor
  · intro s t hst
    rw [PEqualNP.Outside.L_meta_680.inter_eq,
      Finset.card_image_of_injOn (PEqualNP.Outside.L_meta_680.inj_on D s t)]
    exact hD (t - s) (sub_ne_zero.mpr (Ne.symm hst))
  · intro x
    rw [PEqualNP.Outside.L_meta_680.count_eq]
    exact Finset.card_image_of_injective _ (fun a b h => by simpa using h)
