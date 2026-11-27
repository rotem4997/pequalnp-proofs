import PEqualNP.ProofComplexity.Helpers.LiftQuadDefs

/-!
# L-pcx-072, legs A1 and A2: the subspace chain lemma and the step relation

Conjecture until the checker accepts it. Proves `StmtChain` and `StmtStep` of
`Helpers.LiftQuadDefs`.

The chain lemma is proved on the reversed list, with the target space generalised: along
`z :: r` (each space inside the NEXT one plus a vector, some entry `⊥`), for every space `W`
and `1 ≤ k ≤ dim (E z ⊓ W)`, a nonzero vector of `E z ⊓ W` lies in `k` entries. The next
entry `z'` has `dim (E z' ⊓ (E z ⊓ W)) ≥ dim (E z ⊓ W) - 1`, so induction on `r` with
`W := E z ⊓ W` and `k - 1` gives the rest.
-/

namespace PEqualNP.ProofComplexity.LiftQuad

open PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers

/-! ### The chain lemma -/

section Chain

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

/-- Intersecting with a space inside `A ⊔ span {y}` loses at most one dimension. -/
theorem finrank_inf_ge {A X : Submodule (ZMod 2) M} {y : M}
    (h : X ≤ A ⊔ Submodule.span (ZMod 2) {y}) :
    Module.finrank (ZMod 2) X ≤ Module.finrank (ZMod 2) (A ⊓ X : Submodule (ZMod 2) M) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A X
  have h2 : A ⊔ X ≤ A ⊔ Submodule.span (ZMod 2) {y} := sup_le le_sup_left h
  have h3 := Submodule.finrank_mono h2
  have h4 := Submodule.finrank_add_le_finrank_add_finrank A (Submodule.span (ZMod 2) {y})
  have h5 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {y}) ≤ 1 := by
    have := finrank_span_le_card (R := ZMod 2) ({y} : Set M)
    simpa using this
  omega

theorem chain_rev {α : Type} (E : α → Submodule (ZMod 2) M) (r : List α) :
    ∀ z : α, (z :: r).IsChain (fun B A => ∃ y : M, E B ≤ E A ⊔ Submodule.span (ZMod 2) {y}) →
      (∃ A ∈ z :: r, E A = ⊥) → ∀ (W : Submodule (ZMod 2) M) (k : ℕ), 1 ≤ k →
      k ≤ Module.finrank (ZMod 2) (E z ⊓ W : Submodule (ZMod 2) M) →
      ∃ v ∈ E z ⊓ W, v ≠ 0 ∧ ∃ l' : List α, l'.Sublist (z :: r) ∧ k ≤ l'.length ∧
        ∀ A ∈ l', v ∈ E A := by
  induction r with
  | nil =>
    intro z _ hbot W k hk hkd
    obtain ⟨A, hA, hAb⟩ := hbot
    rw [List.mem_singleton] at hA
    subst hA
    rw [hAb, bot_inf_eq, finrank_bot] at hkd
    omega
  | cons z' r ih =>
    intro z hch hbot W k hk hkd
    have hne : E z ⊓ W ≠ ⊥ := by
      intro h0
      rw [h0, finrank_bot] at hkd
      omega
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      refine ⟨v, hv, hv0, [z], List.singleton_sublist.2 List.mem_cons_self, by simp; omega, ?_⟩
      intro A hA
      rw [List.mem_singleton] at hA
      subst hA
      exact (Submodule.mem_inf.1 hv).1
    · rw [List.isChain_cons_cons] at hch
      obtain ⟨⟨y, hy⟩, hch'⟩ := hch
      have hbot' : ∃ A ∈ z' :: r, E A = ⊥ := by
        obtain ⟨A, hA, hAb⟩ := hbot
        rcases List.mem_cons.1 hA with rfl | hA'
        · exact absurd (by rw [hAb, bot_inf_eq]) hne
        · exact ⟨A, hA', hAb⟩
      have hX : E z ⊓ W ≤ E z' ⊔ Submodule.span (ZMod 2) {y} := le_trans inf_le_left hy
      have hd := finrank_inf_ge hX
      obtain ⟨v, hv, hv0, l', hsub, hlen, hall⟩ :=
        ih z' hch' hbot' (E z ⊓ W) (k - 1) (by omega) (by omega)
      have hv' := Submodule.mem_inf.1 hv
      refine ⟨v, hv'.2, hv0, z :: l', hsub.cons_cons z, by simp; omega, ?_⟩
      intro A hA
      rcases List.mem_cons.1 hA with rfl | hA'
      · exact (Submodule.mem_inf.1 hv'.2).1
      · exact hall A hA'

end Chain

theorem chain : StmtChain := by
  intro M _ _ _ α E l x z k hx hE hz hch hk hkd
  obtain ⟨r, hr⟩ : ∃ r, l.reverse = z :: r := by
    rw [List.getLast?_eq_head?_reverse] at hz
    cases h : l.reverse with
    | nil => rw [h] at hz; simp at hz
    | cons a r => rw [h] at hz; simp at hz; exact ⟨r, by rw [hz]⟩
  have hch' : (z :: r).IsChain
      (fun B A => ∃ y : M, E B ≤ E A ⊔ Submodule.span (ZMod 2) {y}) := by
    rw [← hr, List.isChain_reverse]
    exact hch
  have hbot : ∃ A ∈ z :: r, E A = ⊥ := by
    refine ⟨x, ?_, hE⟩
    rw [← hr, List.mem_reverse]
    exact List.mem_of_mem_head? hx
  obtain ⟨v, hv, hv0, l', hsub, hlen, hall⟩ :=
    chain_rev E r z hch' hbot ⊤ k hk (by rw [inf_top_eq]; exact hkd)
  refine ⟨v, (Submodule.mem_inf.1 hv).1, hv0, l'.reverse, ?_, by simpa using hlen, ?_⟩
  · have := hsub.reverse
    rw [← hr, List.reverse_reverse] at this
    exact this
  · intro A hA
    exact hall A (List.mem_reverse.1 hA)

/-! ### The step relation -/

section Step

variable {V : Type} [Fintype V] [DecidableEq V]

theorem zmod2_eq_of_ne {a b c : ZMod 2} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  revert a b c; decide

/-- A form of `formSpan R` takes the same value at any two falsifiers of `R`. -/
theorem formSpan_const {R : LinClause V} {x x' : V → ZMod 2} (hx : Fals R x) (hx' : Fals R x')
    {h : V → ZMod 2} (hh : h ∈ formSpan R) : h ⬝ᵥ x = h ⬝ᵥ x' := by
  let φ : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun g => g ⬝ᵥ (x - x')
      map_add' := fun a b => add_dotProduct a b _
      map_smul' := fun c a => smul_dotProduct c a _ }
  have hle : formSpan R ≤ LinearMap.ker φ := by
    unfold formSpan
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk, φ,
      dotProduct_sub, sub_eq_zero]
    exact zmod2_eq_of_ne (hx q hq) (hx' q hq)
  have := hle hh
  simp only [LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk, φ, dotProduct_sub,
    sub_eq_zero] at this
  exact this

end Step

theorem step : StmtStep := by
  intro V _ _ R P hst
  rcases hst with h1 | ⟨f, b, ⟨a0, ha0R, ha0f⟩, h2⟩
  · refine ⟨0, le_trans ?_ le_sup_left⟩
    intro p hp a ha
    exact hp a (h1 a ha)
  · refine ⟨(ind f, toZ b), ?_⟩
    intro p hp
    obtain ⟨g, e⟩ := p
    rw [mem_impSpace] at hp
    have hx0 : Fals R (vec a0) := (fals_vec a0 R).2 ha0R
    have hf0 : ind f ⬝ᵥ vec a0 = toZ b := (linEqSat_iff a0 (f, b)).1 ha0f
    -- every falsifier of `R` with `f = b` satisfies `g = e`
    have hF : ∀ x : V → ZMod 2, Fals R x → ind f ⬝ᵥ x = toZ b → g ⬝ᵥ x = e := by
      intro x hx hfx
      obtain ⟨a, rfl⟩ := vec_surj x
      exact hp a (h2 a ((fals_vec a R).1 hx) ((linEqSat_iff a (f, b)).2 hfx))
    by_cases hg : g ∈ formSpan R ⊔ Submodule.span (ZMod 2) {ind f}
    · obtain ⟨h, hh, t, ht, rfl⟩ := Submodule.mem_sup.1 hg
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ht
      have he : e = h ⬝ᵥ vec a0 + c * toZ b := by
        rw [← hF _ hx0 hf0, add_dotProduct, smul_dotProduct, hf0, smul_eq_mul]
      subst he
      have hmem : ((h, h ⬝ᵥ vec a0) : (V → ZMod 2) × ZMod 2) ∈ impSpace R := by
        intro a ha
        exact formSpan_const ((fals_vec a R).2 ha) hx0 hh
      have hmem2 : ((c • ind f, c * toZ b) : (V → ZMod 2) × ZMod 2) ∈
          Submodule.span (ZMod 2) {((ind f, toZ b) : (V → ZMod 2) × ZMod 2)} :=
        Submodule.mem_span_singleton.2 ⟨c, by simp⟩
      exact Submodule.add_mem_sup hmem hmem2
    · exfalso
      obtain ⟨w, hw, hgw⟩ := exists_perp_of_notMem hg
      have hwR : ∀ u ∈ formSpan R, u ⬝ᵥ w = 0 := fun u hu => hw u (Submodule.mem_sup_left hu)
      have hwf : ind f ⬝ᵥ w = 0 :=
        hw _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      have hx1 := hF _ (fals_add hx0 hwR) (by rw [dotProduct_add, hwf, add_zero, hf0])
      rw [dotProduct_add, hF _ hx0 hf0] at hx1
      exact hgw (by simpa using hx1)

end PEqualNP.ProofComplexity.LiftQuad
