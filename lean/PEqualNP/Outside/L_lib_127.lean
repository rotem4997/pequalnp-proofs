import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_127_aux

theorem routing (n : ℕ) (π : Equiv.Perm (Fin n × Bool)) :
    ∃ b : Fin n → Bool, ∃ π₀ π₁ : Equiv.Perm (Fin n),
      ∀ (ρ : Fin n) (β : Bool),
        (π (ρ, β)).1 = (if (β != b ρ) = true then π₁ else π₀) ρ := by
  classical
  let t : Fin n → Finset (Fin n) := fun i =>
    {(π (i, false)).1, (π (i, true)).1}
  have hall : ∀ s : Finset (Fin n), s.card ≤ (s.biUnion t).card := by
    intro s
    have hs : (s ×ˢ (Finset.univ : Finset Bool)).image π ⊆
        (s.biUnion t) ×ˢ (Finset.univ : Finset Bool) := by
      intro q hq
      obtain ⟨⟨i,b⟩, hi, rfl⟩ := Finset.mem_image.mp hq
      have his : i ∈ s := (Finset.mem_product.mp hi).1
      simp only [Finset.mem_product, Finset.mem_univ, and_true]
      apply Finset.mem_biUnion.mpr
      refine ⟨i, his, ?_⟩
      cases b <;> simp [t]
    have hc := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _ π.injective] at hc
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hc
    omega
  obtain ⟨f, hf, hft⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  have hchoose : ∀ i, ∃ b : Bool, (π (i,b)).1 = f i := by
    intro i
    have h := hft i
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩
  choose b hb using hchoose
  let π₀ : Equiv.Perm (Fin n) := Equiv.ofBijective f
    ⟨hf, Finite.surjective_of_injective hf⟩
  let g : Fin n → Fin n := fun i => (π (i, !(b i))).1
  have hg : Function.Injective g := by
    intro i j hij
    obtain ⟨k, hk⟩ := Finite.surjective_of_injective hf (g i)
    have hki : (π (k,b k)).1 = (π (i, !(b i))).1 := (hb k).trans hk
    have hkj : (π (k,b k)).1 = (π (j, !(b j))).1 := hki.trans hij
    have neqki : π (k,b k) ≠ π (i, !(b i)) := by
      intro h
      have e := π.injective h
      have eki : k = i := congrArg Prod.fst e
      subst k
      have ebit := congrArg Prod.snd e
      cases b i <;> simp_all
    have neqkj : π (k,b k) ≠ π (j, !(b j)) := by
      intro h
      have e := π.injective h
      have ekj : k = j := congrArg Prod.fst e
      subst k
      have ebit := congrArg Prod.snd e
      cases b j <;> simp_all
    have sndeq : (π (i, !(b i))).2 = (π (j, !(b j))).2 := by
      have a : (π (k,b k)).2 ≠ (π (i, !(b i))).2 :=
        fun h => neqki (Prod.ext hki h)
      have c : (π (k,b k)).2 ≠ (π (j, !(b j))).2 :=
        fun h => neqkj (Prod.ext hkj h)
      have pigeon : ∀ a b c : Bool, a ≠ b → a ≠ c → b = c := by decide
      exact pigeon _ _ _ a c
    exact congrArg Prod.fst (π.injective (Prod.ext hij sndeq))
  let π₁ : Equiv.Perm (Fin n) := Equiv.ofBijective g
    ⟨hg, Finite.surjective_of_injective hg⟩
  refine ⟨b, π₀, π₁, ?_⟩
  intro i β
  have hi := hb i
  cases hbi : b i <;> cases β <;> simp_all [g, π₀, π₁, Equiv.ofBijective]

end PEqualNP.Outside.L_lib_127_aux

theorem PEqualNP.Outside.L_lib_127 :
    ∀ (n : ℕ) (π : Equiv.Perm (Fin n × Bool)), ∃ b : Fin n → Bool,
      ∃ π₀ π₁ : Equiv.Perm (Fin n), ∀ (ρ : Fin n) (β : Bool),
        (π (ρ, β)).1 = (if (β != b ρ) = true then π₁ else π₀) ρ :=
  PEqualNP.Outside.L_lib_127_aux.routing
