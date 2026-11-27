import PEqualNP.Search.Helpers.BWTri.Core
import PEqualNP.Search.Helpers.BW.Bridge
import PEqualNP.Defs.SearchCP

/-!
# Helpers: from triangle dags for bit pigeonhole to abstract triangle dags (L-lib-105)

A point of `BPHP (n + 1) l` with `l = 2 t` is the join of two halves (`BW/Bridge.lean`). A
set of points maps to the set of pairs of halves whose join lies in it; a triangle maps to an
abstract triangle. This turns a triangle dag into an abstract one of the same length, and the
core bound `tdag_lower'` gives a superpolynomial lower bound.
-/

namespace PEqualNP.Search.Helpers.BWTri

open Classical
open PEqualNP.Search.Helpers.BW

section Split

variable {n l t : ℕ}

/-- The image of a set of points: the pairs of halves whose join lies in it. -/
def tproj (hl : 2 * t = l) (R : Set (Fin (n + 1) × Fin l → Bool)) :
    Set (Half n t × Half n t) :=
  {p | joinPart hl p.1 p.2 ∈ R}

theorem join_eq_mix (hl : 2 * t = l) (x y : Half n t) :
    joinPart hl x y = PEqualNP.Search.mix (fun v : Fin (n + 1) × Fin l => decide (2 * v.2.val < l))
      (joinPart hl x x) (joinPart hl y y) := by
  rw [mix_eq_join hl, xPart_join, yPart_join]

theorem triRel_tproj (hl : 2 * t = l) {R : Set (Fin (n + 1) × Fin l → Bool)}
    (hR : PEqualNP.Search.IsTri (fun v : Fin (n + 1) × Fin l => decide (2 * v.2.val < l)) R) :
    TriRel (fun x y => (x, y) ∈ tproj hl R) := by
  obtain ⟨a, b, ha, hb, hab⟩ := hR
  refine ⟨fun x => a (joinPart hl x x), fun y => b (joinPart hl y y), fun x y => ?_⟩
  show joinPart hl x y ∈ R ↔ _
  rw [hab, join_eq_mix hl x y, ha, hb]

theorem xPart_coll (hl : 2 * t = l) {a : Fin (n + 1) × Fin l → Bool} {i i' : Fin (n + 1)}
    {α : Fin l → Bool} (h : ∀ b : Fin l, a (i, b) = α b ∧ a (i', b) = α b) :
    xPart hl a i = xPart hl a i' := by
  funext c
  simp only [xPart]
  rw [(h _).1, (h _).2]

theorem yPart_coll (hl : 2 * t = l) {a : Fin (n + 1) × Fin l → Bool} {i i' : Fin (n + 1)}
    {α : Fin l → Bool} (h : ∀ b : Fin l, a (i, b) = α b ∧ a (i', b) = α b) :
    yPart hl a i = yPart hl a i' := by
  funext c
  simp only [yPart]
  rw [(h _).1, (h _).2]

theorem tdag_map (hl : 2 * t = l) {ρ : List (Set (Fin (n + 1) × Fin l → Bool))}
    (h : PEqualNP.Search.IsTriDag (fun v : Fin (n + 1) × Fin l => decide (2 * v.2.val < l))
      (PEqualNP.ProofComplexity.BPHP (n + 1) l) ρ) :
    TDag n t (ρ.map (tproj hl)) := by
  induction h with
  | nil => exact TDag.nil
  | @sink ρ R _ hR hC ih =>
    obtain ⟨C, ⟨i, i', α, hii', rfl⟩, hfal⟩ := hC
    have key : ∀ a ∈ R, ∀ b : Fin l, a (i, b) = α b ∧ a (i', b) = α b := by
      intro a ha b
      have hna := hfal a ha
      simp only [PEqualNP.ProofComplexity.ClauseSat, Finset.mem_union, Finset.mem_image,
        Finset.mem_univ, true_and] at hna
      have hb : ∀ j, (∃ b', ((j, b'), !α b') = ((j, b), !α b)) → (j = i ∨ j = i') →
          a (j, b) = α b := by
        intro j hj hji
        by_contra hne
        refine hna ⟨((j, b), !α b), ?_, ?_⟩
        · rcases hji with rfl | rfl
          · exact Or.inl hj
          · exact Or.inr hj
        · show a (j, b) = !α b
          revert hne
          generalize a (j, b) = u
          generalize α b = w
          cases u <;> cases w <;> simp
      exact ⟨hb i ⟨b, rfl⟩ (Or.inl rfl), hb i' ⟨b, rfl⟩ (Or.inr rfl)⟩
    refine TDag.sink i i' ih (triRel_tproj hl hR) hii' ?_
    rintro ⟨x, y⟩ hp
    have hk := key _ hp
    have h1 := xPart_coll hl hk
    have h2 := yPart_coll hl hk
    rw [xPart_join] at h1
    rw [yPart_join] at h2
    exact ⟨h1, h2⟩
  | @split ρ R R₁ R₂ _ hR h₁ h₂ hsub ih =>
    refine TDag.split ih (triRel_tproj hl hR) (List.mem_map_of_mem h₁)
      (List.mem_map_of_mem h₂) ?_
    intro p hp
    rcases hsub hp with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem tproj_univ (hl : 2 * t = l) :
    tproj hl (Set.univ : Set (Fin (n + 1) × Fin l → Bool)) =
      (Set.univ : Set (Half n t × Half n t)) :=
  Set.eq_univ_of_forall fun _ => Set.mem_univ _

/-- The bridge for a general split `l = 2 t`. -/
theorem triDag_to_tdag_gen (hl : 2 * t = l) {ρ : List (Set (Fin (n + 1) × Fin l → Bool))}
    (h : PEqualNP.Search.IsTriDagFor
      (fun v : Fin (n + 1) × Fin l => decide (2 * v.2.val < l))
      (PEqualNP.ProofComplexity.BPHP (n + 1) l) ρ) :
    ∃ σ, TDagFor n t σ ∧ σ.length ≤ ρ.length := by
  refine ⟨ρ.map (tproj hl), ⟨tdag_map hl h.1, ?_⟩, by simp⟩
  rw [← tproj_univ hl]
  exact List.mem_map_of_mem h.2

end Split

/-- BRIDGE: a triangle dag for bit pigeonhole with `2 ^ l + 1` pigeons and `l = 4 s + 4`
bits, split down the middle, gives an abstract triangle dag of no greater length. -/
theorem triDag_to_tdag (s : ℕ)
    {ρ : List (Set (Fin (2 ^ (4 * s + 4) + 1) × Fin (4 * s + 4) → Bool))}
    (h : PEqualNP.Search.IsTriDagFor
      (fun v : Fin (2 ^ (4 * s + 4) + 1) × Fin (4 * s + 4) => decide (2 * v.2.val < 4 * s + 4))
      (PEqualNP.ProofComplexity.BPHP (2 ^ (4 * s + 4) + 1) (4 * s + 4)) ρ) :
    ∃ σ, TDagFor (16 ^ (s + 1)) (2 * s + 2) σ ∧ σ.length ≤ ρ.length := by
  have key : ∀ n, n = 16 ^ (s + 1) →
      ∀ ρ : List (Set (Fin (n + 1) × Fin (4 * s + 4) → Bool)),
      PEqualNP.Search.IsTriDagFor
        (fun v : Fin (n + 1) × Fin (4 * s + 4) => decide (2 * v.2.val < 4 * s + 4))
        (PEqualNP.ProofComplexity.BPHP (n + 1) (4 * s + 4)) ρ →
      ∃ σ, TDagFor (16 ^ (s + 1)) (2 * s + 2) σ ∧ σ.length ≤ ρ.length := by
    intro n hn ρ hρ
    subst hn
    exact triDag_to_tdag_gen (by ring) hρ
  exact key _ (two_pow_eq_sixteen_pow s) ρ h

/-- FINAL: triangle dags for bit pigeonhole, split down the middle, are superpolynomial in
the number of holes. -/
theorem bwtri_superpoly : ∀ p : Polynomial ℕ, ∃ l : ℕ,
    ∀ ρ : List (Set (Fin (2 ^ l + 1) × Fin l → Bool)),
      PEqualNP.Search.IsTriDagFor (fun v : Fin (2 ^ l + 1) × Fin l => decide (2 * v.2.val < l))
        (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) ρ → p.eval (2 ^ l) < ρ.length := by
  intro p
  obtain ⟨s, hs⟩ := exists_eval_lt p
  refine ⟨4 * s + 4, fun ρ hρ => ?_⟩
  obtain ⟨σ, hσ, hlen⟩ := triDag_to_tdag s hρ
  have := tdag_lower' s σ hσ
  have e : p.eval (2 ^ (4 * s + 4)) = p.eval (16 ^ (s + 1)) := by
    rw [two_pow_eq_sixteen_pow]
  omega

end PEqualNP.Search.Helpers.BWTri
