import PEqualNP.CircuitLowerBounds.Helpers.Switching.CoreCount
import PEqualNP.CircuitLowerBounds.Helpers.Switching.Plan

/-!
# Switching lemma: from ordered DNFs to the semantic statement of the plan

A function all of whose true points have a certificate of at most `w` variables is the value
of a DNF of width at most `w` on `Fin (card V)`; small canonical depth of that DNF under a
restriction gives certificates for both values of the restricted function. With the ratio form
of the counting lemma this is `Plan.SwitchingSem`.
-/

namespace PEqualNP.CircuitLowerBounds.Switching.Core

open Plan

section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The term of a point `x` and a set `S` of variables: `x` on `S`, carried to `Fin N`. -/
noncomputable def termOf (x : V → Bool) (S : Finset V) : Term (Fintype.card V) :=
  S.toList.map fun v => (Fintype.equivFin V v, x v)

theorem termOf_length (x : V → Bool) (S : Finset V) : (termOf x S).length = S.card := by
  simp [termOf]

theorem termOf_eval (x : V → Bool) (S : Finset V) (z : Fin (Fintype.card V) → Bool) :
    (termOf x S).eval z = true ↔ ∀ v ∈ S, z (Fintype.equivFin V v) = x v := by
  unfold termOf Term.eval
  rw [List.all_eq_true]
  constructor
  · intro h v hv
    have := h (Fintype.equivFin V v, x v) (List.mem_map.2 ⟨v, Finset.mem_toList.2 hv, rfl⟩)
    simpa using this
  · intro h p hp
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hp
    simpa using h v (Finset.mem_toList.1 hv)

/-- A function with 1-certificates of size `w` is a DNF of width at most `w`. -/
theorem exists_dnf {w : ℕ} {f : BF V} (hf : Cert1 w f) :
    ∃ F : DNF (Fintype.card V), (∀ T ∈ F, T.length ≤ w) ∧
      ∀ z : Fin (Fintype.card V) → Bool, F.eval z = f (fun v => z (Fintype.equivFin V v)) := by
  classical
  choose! S hS using hf
  refine ⟨(Finset.univ.filter fun x : V → Bool => f x = true).toList.map fun x => termOf x (S x),
    ?_, ?_⟩
  · intro T hT
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hT
    rw [Finset.mem_toList, Finset.mem_filter] at hx
    rw [termOf_length]; exact (hS x hx.2).1
  · intro z
    rw [Bool.eq_iff_iff]
    unfold DNF.eval
    rw [List.any_eq_true]
    constructor
    · rintro ⟨T, hT, hTz⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hT
      rw [Finset.mem_toList, Finset.mem_filter] at hx
      rw [termOf_eval] at hTz
      exact (hS x hx.2).2 _ hTz
    · intro h
      refine ⟨termOf (fun v => z (Fintype.equivFin V v)) (S fun v => z (Fintype.equivFin V v)),
        List.mem_map.2 ⟨_, ?_, rfl⟩, ?_⟩
      · rw [Finset.mem_toList, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
      · rw [termOf_eval]; intro v _; rfl

/-- The restriction carried to `Fin N`. -/
noncomputable def tr (ρ : Plan.Restr V) : Restr (Fintype.card V) :=
  fun i => ρ ((Fintype.equivFin V).symm i)

theorem tr_injective : Function.Injective (tr (V := V)) := by
  intro ρ ρ₂ h
  funext v
  have := congrFun h (Fintype.equivFin V v)
  simpa [tr] using this

theorem stars_tr (ρ : Plan.Restr V) [inst : Fintype (Stars ρ)] :
    @Fintype.card (Stars ρ) inst = stars (tr ρ) := by
  unfold stars
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr ((Fintype.equivFin V).subtypeEquiv ?_)
  intro v
  simp [tr]

/-- Small canonical depth of the DNF under the carried restriction gives certificates for both
values of the restricted function. -/
theorem low_of_cdt {f : BF V} {F : DNF (Fintype.card V)}
    (hF : ∀ z : Fin (Fintype.card V) → Bool, F.eval z = f (fun v => z (Fintype.equivFin V v)))
    (ρ : Plan.Restr V) (t : ℕ) (h : cdt F (tr ρ) ≤ t) : Low t (restr ρ f) := by
  classical
  have key : ∀ y : Stars ρ → Bool, ∃ S : Finset (Stars ρ), S.card ≤ t ∧
      ∀ y' : Stars ρ → Bool, (∀ s ∈ S, y' s = y s) → restr ρ f y' = restr ρ f y := by
    intro y
    have hc : ∀ y' : Stars ρ → Bool,
        Compat (tr ρ) (fun i => fill ρ y' ((Fintype.equivFin V).symm i)) := by
      intro y' i b hib
      have hne : ¬ ρ ((Fintype.equivFin V).symm i) = none := by
        intro h0; rw [tr] at hib; rw [h0] at hib; cases hib
      simp only [fill, dif_neg hne]
      rw [tr] at hib; rw [hib]; rfl
    have hval : ∀ y' : Stars ρ → Bool,
        restr ρ f y' = F.eval (fun i => fill ρ y' ((Fintype.equivFin V).symm i)) := by
      intro y'
      rw [hF]; unfold restr; congr 1; funext v; simp
    obtain ⟨S, hS, hstar, hcert⟩ := cert_of_cdt F (tr ρ) t h _ (hc y)
    refine ⟨Finset.univ.filter fun s : Stars ρ => Fintype.equivFin V s.1 ∈ S, ?_, ?_⟩
    · refine le_trans (Finset.card_le_card_of_injOn (fun s : Stars ρ => Fintype.equivFin V s.1)
        ?_ ?_) hS
      · intro s hs
        rw [Finset.mem_coe, Finset.mem_filter] at hs
        exact hs.2
      · intro s _ s₂ _ hss
        exact Subtype.ext ((Fintype.equivFin V).injective hss)
    · intro y' hy'
      rw [hval, hval]
      apply hcert _ (hc y')
      intro i hi
      have hi0 : ρ ((Fintype.equivFin V).symm i) = none := hstar i hi
      simp only [fill, dif_pos hi0]
      apply hy'
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa using hi⟩
  constructor
  · intro y hy
    obtain ⟨S, hS, hc⟩ := key y
    exact ⟨S, hS, fun y' hy' => by rw [hc y' hy', hy]⟩
  · intro y hy
    obtain ⟨S, hS, hc⟩ := key y
    exact ⟨S, hS, fun y' hy' => by rw [hc y' hy', hy]⟩

end

/-- **The switching lemma, semantic counting form** (the statement of the plan). -/
theorem switchingSem : Plan.SwitchingSem := by
  intro V _ _ w t l f hf
  classical
  obtain ⟨F, hw, hF⟩ := exists_dnf hf
  have hA : (Finset.univ.filter fun ρ : Plan.Restr V =>
      Fintype.card (Stars ρ) = l ∧ ¬ Low t (restr ρ f)).card ≤ (bad F l t).card := by
    refine Finset.card_le_card_of_injOn tr ?_ (tr_injective.injOn)
    intro ρ hρ
    rw [Finset.mem_coe, Finset.mem_filter] at hρ
    rw [Finset.mem_coe]
    unfold bad
    rw [Finset.mem_filter, mem_R]
    refine ⟨by rw [← hρ.2.1]; exact (stars_tr ρ).symm, ?_⟩
    by_contra hlt
    exact hρ.2.2 (low_of_cdt hF ρ t (by omega))
  have hB : (R (Fintype.card V) l).card ≤
      (Finset.univ.filter fun ρ : Plan.Restr V => Fintype.card (Stars ρ) = l).card := by
    refine Finset.card_le_card_of_injOn
      (fun θ : Restr (Fintype.card V) => fun v => θ (Fintype.equivFin V v)) ?_ ?_
    · intro θ hθ
      rw [Finset.mem_coe, mem_R] at hθ
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [stars_tr, ← hθ]
      congr 1
      funext i
      simp [tr]
    · intro θ _ θ₂ _ h
      funext i
      have := congrFun h ((Fintype.equivFin V).symm i)
      simpa using this
  calc _ ≤ (bad F l t).card * (Fintype.card V - l) ^ t := Nat.mul_le_mul_right _ hA
    _ ≤ (R (Fintype.card V) l).card * (8 * w * l) ^ t := card_bad_ratio F w hw l t
    _ ≤ _ := Nat.mul_le_mul_right _ hB

end PEqualNP.CircuitLowerBounds.Switching.Core
