import PEqualNP.ProofComplexity.Helpers.Resolution
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Basic

/-!
# Helpers: completeness of resolution with the exponential length bound

The induction is on the set `S` of variables still free. Given an assignment `a` such that
every assignment agreeing with `a` outside `S` falsifies a clause of `F`, there is a
derivation of at most `2 ^ (|S| + 1) - 1` lines holding a clause falsified by `a` that
mentions no variable of `S`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

/-- Derivations can be concatenated. -/
theorem derivation_append {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π₁ π₂ : List (Clause V)} (h₁ : IsDerivation F π₁) (h₂ : IsDerivation F π₂) :
    IsDerivation F (π₁ ++ π₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | ax _ hC ih => exact IsDerivation.ax ih hC
  | res _ hC hD hR ih =>
    exact IsDerivation.res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hR

theorem completeness_aux {V : Type} [DecidableEq V] (F : Set (Clause V)) (S : Finset V) :
    ∀ a : V → Bool,
      (∀ b : V → Bool, (∀ v, v ∉ S → b v = a v) → ∃ C ∈ F, ¬ ClauseSat b C) →
      ∃ π : List (Clause V), IsDerivation F π ∧ π.length + 1 ≤ 2 ^ (S.card + 1) ∧
        ∃ C ∈ π, (∀ l ∈ C, a l.1 ≠ l.2) ∧ ∀ l ∈ C, l.1 ∉ S := by
  induction S using Finset.induction_on with
  | empty =>
    intro a h
    obtain ⟨C, hCF, hC⟩ := h a (fun _ _ => rfl)
    refine ⟨[C], IsDerivation.ax IsDerivation.nil hCF, by simp, C, by simp, ?_, by simp⟩
    intro l hl hal
    exact hC ⟨l, hl, hal⟩
  | insert x S hx ih =>
    intro a h
    have hsub : ∀ t : Bool, ∀ b : V → Bool, (∀ v, v ∉ S → b v = Function.update a x t v) →
        ∃ C ∈ F, ¬ ClauseSat b C := by
      intro t b hb
      apply h b
      intro v hv
      have hvx : v ≠ x := fun e => hv (e ▸ Finset.mem_insert_self x S)
      have hvS : v ∉ S := fun e => hv (Finset.mem_insert_of_mem e)
      rw [hb v hvS, Function.update_of_ne hvx]
    obtain ⟨π₀, hπ₀, hlen₀, C₀, hC₀π, hC₀a, hC₀S⟩ := ih (Function.update a x false) (hsub false)
    obtain ⟨π₁, hπ₁, hlen₁, C₁, hC₁π, hC₁a, hC₁S⟩ := ih (Function.update a x true) (hsub true)
    have hpow : 2 ^ ((insert x S).card + 1) = 2 * 2 ^ (S.card + 1) := by
      rw [Finset.card_insert_of_notMem hx, pow_succ, mul_comm]
    -- a literal on a variable other than `x`, falsified by an update of `a`, is falsified by `a`
    have key : ∀ (t : Bool) (C : Clause V), (∀ l ∈ C, Function.update a x t l.1 ≠ l.2) →
        (∀ l ∈ C, l.1 ∉ S) → ∀ l ∈ C, l.1 ≠ x → a l.1 ≠ l.2 ∧ l.1 ∉ insert x S := by
      intro t C hCa hCS l hl hlx
      refine ⟨?_, ?_⟩
      · have := hCa l hl
        rwa [Function.update_of_ne hlx] at this
      · intro hmem
        rcases Finset.mem_insert.mp hmem with e | e
        · exact hlx e
        · exact hCS l hl e
    -- a literal on `x` in a clause falsified by the update to `t` is `(x, !t)`
    have onx : ∀ (t : Bool) (C : Clause V), (∀ l ∈ C, Function.update a x t l.1 ≠ l.2) →
        ∀ l ∈ C, l.1 = x → l = (x, !t) := by
      intro t C hCa l hl hlx
      have := hCa l hl
      rw [hlx, Function.update_self] at this
      obtain ⟨v, s⟩ := l
      simp only at hlx this
      subst hlx
      cases t <;> cases s <;> simp_all
    by_cases h₀ : (x, true) ∈ C₀
    · by_cases h₁ : (x, false) ∈ C₁
      · refine ⟨(C₀.erase (x, true) ∪ C₁.erase (x, false)) :: (π₀ ++ π₁), ?_, ?_, _,
          List.mem_cons_self, ?_, ?_⟩
        · exact IsDerivation.res (derivation_append hπ₀ hπ₁) (List.mem_append_left _ hC₀π)
            (List.mem_append_right _ hC₁π) ⟨x, h₀, h₁, rfl⟩
        · rw [hpow]; simp only [List.length_cons, List.length_append]; omega
        · intro l hl
          rcases Finset.mem_union.mp hl with hl | hl
          · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
            have hlx : l.1 ≠ x := fun e => hne (by simpa using onx false C₀ hC₀a l hl e)
            exact (key false C₀ hC₀a hC₀S l hl hlx).1
          · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
            have hlx : l.1 ≠ x := fun e => hne (by simpa using onx true C₁ hC₁a l hl e)
            exact (key true C₁ hC₁a hC₁S l hl hlx).1
        · intro l hl
          rcases Finset.mem_union.mp hl with hl | hl
          · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
            have hlx : l.1 ≠ x := fun e => hne (by simpa using onx false C₀ hC₀a l hl e)
            exact (key false C₀ hC₀a hC₀S l hl hlx).2
          · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
            have hlx : l.1 ≠ x := fun e => hne (by simpa using onx true C₁ hC₁a l hl e)
            exact (key true C₁ hC₁a hC₁S l hl hlx).2
      · have hnox : ∀ l ∈ C₁, l.1 ≠ x := by
          intro l hl e
          have := onx true C₁ hC₁a l hl e
          simp at this
          exact h₁ (this ▸ hl)
        refine ⟨π₁, hπ₁, by rw [hpow]; omega, C₁, hC₁π, ?_, ?_⟩
        · exact fun l hl => (key true C₁ hC₁a hC₁S l hl (hnox l hl)).1
        · exact fun l hl => (key true C₁ hC₁a hC₁S l hl (hnox l hl)).2
    · have hnox : ∀ l ∈ C₀, l.1 ≠ x := by
        intro l hl e
        have := onx false C₀ hC₀a l hl e
        simp at this
        exact h₀ (this ▸ hl)
      refine ⟨π₀, hπ₀, by rw [hpow]; omega, C₀, hC₀π, ?_, ?_⟩
      · exact fun l hl => (key false C₀ hC₀a hC₀S l hl (hnox l hl)).1
      · exact fun l hl => (key false C₀ hC₀a hC₀S l hl (hnox l hl)).2

/-- Completeness with the length bound. -/
theorem completeness {V : Type} [DecidableEq V] [Fintype V] (F : Set (Clause V))
    (h : ¬ Satisfiable F) :
    ∃ π : List (Clause V), IsRefutation F π ∧ π.length ≤ 2 ^ (Fintype.card V + 1) - 1 := by
  have hF : ∀ b : V → Bool, ∃ C ∈ F, ¬ ClauseSat b C := by
    intro b
    by_contra hb
    exact h ⟨b, fun C hC => by_contra fun hn => hb ⟨C, hC, hn⟩⟩
  obtain ⟨π, hπ, hlen, C, hCπ, -, hCS⟩ :=
    completeness_aux F Finset.univ (fun _ => false) (fun b _ => hF b)
  have hC : C = ∅ := Finset.eq_empty_of_forall_notMem fun l hl => hCS l hl (Finset.mem_univ _)
  refine ⟨π, ⟨hπ, hC ▸ hCπ⟩, ?_⟩
  rw [Finset.card_univ] at hlen
  omega

end PEqualNP.ProofComplexity.Helpers
