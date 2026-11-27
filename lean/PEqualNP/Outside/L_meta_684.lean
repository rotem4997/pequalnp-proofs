import Mathlib
import PEqualNP.Defs


theorem PEqualNP.Outside.L_meta_684 : ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H]
    (L : G →+ H) (A : AddSubgroup H) (g : H),
    Nat.card {t : G // L t - g ∈ A} = 0 ∨
    Nat.card {t : G // L t - g ∈ A} = Nat.card L.ker * Nat.card (A ⊓ L.range : AddSubgroup H) := by
  intro G H _ _ _ _ L A g
  classical
  by_cases h : Nonempty {t : G // L t - g ∈ A}
  · right
    obtain ⟨t₀⟩ := h
    let translate : {t : G // L t - g ∈ A} ≃ A.comap L :=
      { toFun := fun t => ⟨t.val - t₀.val, by
          change L (t.val - t₀.val) ∈ A
          rw [map_sub, show L t.val - L t₀.val = (L t.val - g) - (L t₀.val - g) by abel]
          exact A.sub_mem t.property t₀.property⟩
        invFun := fun t => ⟨t.val + t₀.val, by
          rw [map_add, show L t.val + L t₀.val - g = L t.val + (L t₀.val - g) by abel]
          exact A.add_mem t.property t₀.property⟩
        left_inv := fun t => Subtype.ext (sub_add_cancel t.val t₀.val)
        right_inv := fun t => Subtype.ext (add_sub_cancel_right t.val t₀.val) }
    have hker : Nat.card (L.domRestrict (A.comap L)).ker = Nat.card L.ker := by
      rw [AddMonoidHom.ker_domRestrict]
      exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (L.ker_le_comap A)).toEquiv
    have hrange : (L.domRestrict (A.comap L)).range = A ⊓ L.range := by
      rw [AddMonoidHom.domRestrict_range, AddSubgroup.map_comap_eq, inf_comm]
    calc
      _ = Nat.card (A.comap L) := Nat.card_congr translate
      _ = Nat.card (L.domRestrict (A.comap L)).ker *
          Nat.card (L.domRestrict (A.comap L)).range :=
        (AddSubgroup.card_ker_mul_card_range _).symm
      _ = _ := by rw [hker, hrange]
  · left
    exact Finite.card_eq_zero_iff.mpr ⟨fun t => h ⟨t⟩⟩
