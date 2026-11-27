import PEqualNP.Search.Helpers.BW.Core
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Helpers: from rectangle dags for bit pigeonhole to abstract rectangle dags (L-lib-090)

A point of `BPHP (n + 1) l` with `l = 2 t` splits into two halves: the first player's `t`
columns and the second player's `t` columns. A rectangle maps to the pair of its projections.
This turns a rectangle dag into an abstract one of the same length, and the core bound
`adag_lower` then gives a superpolynomial lower bound.
-/

namespace PEqualNP.Search.Helpers.BW

open Classical

section Split

variable {n l t : ℕ}

/-- The first player's half of a point: the columns `c < t`. -/
def xPart (hl : 2 * t = l) (a : Fin (n + 1) × Fin l → Bool) : Half n t :=
  fun i c => a (i, ⟨c.val, by omega⟩)

/-- The second player's half of a point: the columns `t + c`. -/
def yPart (hl : 2 * t = l) (a : Fin (n + 1) × Fin l → Bool) : Half n t :=
  fun i c => a (i, ⟨t + c.val, by omega⟩)

/-- The point with halves `x` and `y`. -/
def joinPart (hl : 2 * t = l) (x y : Half n t) : Fin (n + 1) × Fin l → Bool :=
  fun v => if h : v.2.val < t then x v.1 ⟨v.2.val, h⟩ else y v.1 ⟨v.2.val - t, by omega⟩

theorem xPart_join (hl : 2 * t = l) (x y : Half n t) : xPart hl (joinPart hl x y) = x := by
  funext i c
  simp [xPart, joinPart, c.isLt]

theorem yPart_join (hl : 2 * t = l) (x y : Half n t) : yPart hl (joinPart hl x y) = y := by
  funext i c
  simp [yPart, joinPart]

theorem mix_eq_join (hl : 2 * t = l) (a b : Fin (n + 1) × Fin l → Bool) :
    PEqualNP.Search.mix (fun v : Fin (n + 1) × Fin l => decide (2 * v.2.val < l)) a b =
      joinPart hl (xPart hl a) (yPart hl b) := by
  funext v
  obtain ⟨i, c, hc⟩ := v
  simp only [PEqualNP.Search.mix, joinPart, xPart, yPart]
  by_cases h : c < t
  · have : 2 * c < l := by omega
    simp [h, this]
  · have : ¬ 2 * c < l := by omega
    simp only [this, decide_false, h, dite_false]
    simp only [Bool.false_eq_true, ite_false]
    congr 2
    apply Fin.ext
    simp only
    omega

/-- The image of a rectangle: its two projections. -/
def proj (hl : 2 * t = l) (R : Set (Fin (n + 1) × Fin l → Bool)) :
    Set (Half n t) × Set (Half n t) :=
  (xPart hl '' R, yPart hl '' R)

theorem join_mem_of_mem (hl : 2 * t = l) {R : Set (Fin (n + 1) × Fin l → Bool)}
    (hR : PEqualNP.Search.IsRect (fun v : Fin (n + 1) × Fin l => decide (2 * v.2.val < l)) R)
    {x y : Half n t} (hx : x ∈ xPart hl '' R) (hy : y ∈ yPart hl '' R) :
    joinPart hl x y ∈ R := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [← mix_eq_join hl]
  exact hR a ha b hb

theorem isRect_of_mem {V : Type} {side : V → Bool}
    {F : Set (PEqualNP.ProofComplexity.Clause V)} {ρ : List (Set (V → Bool))}
    (h : PEqualNP.Search.IsRectDag side F ρ) : ∀ R ∈ ρ, PEqualNP.Search.IsRect side R := by
  induction h with
  | nil => simp
  | sink _ hR _ ih =>
    intro R' hR'
    rcases List.mem_cons.1 hR' with rfl | h'
    · exact hR
    · exact ih R' h'
  | split _ hR _ _ _ ih =>
    intro R' hR'
    rcases List.mem_cons.1 hR' with rfl | h'
    · exact hR
    · exact ih R' h'

theorem adag_map (hl : 2 * t = l) {ρ : List (Set (Fin (n + 1) × Fin l → Bool))}
    (h : PEqualNP.Search.IsRectDag (fun v : Fin (n + 1) × Fin l => decide (2 * v.2.val < l))
      (PEqualNP.ProofComplexity.BPHP (n + 1) l) ρ) :
    ADag n t (ρ.map (proj hl)) := by
  induction h with
  | nil => exact ADag.nil
  | @sink ρ R _ _ hC ih =>
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
    refine ADag.sink i i' ih hii' ?_ ?_
    · rintro x ⟨a, ha, rfl⟩
      funext c
      simp only [xPart]
      rw [(key a ha _).1, (key a ha _).2]
    · rintro y ⟨a, ha, rfl⟩
      funext c
      simp only [yPart]
      rw [(key a ha _).1, (key a ha _).2]
  | @split ρ R R₁ R₂ _ hR h₁ h₂ hsub ih =>
    refine ADag.split (A₁ := (proj hl R₁).1) (B₁ := (proj hl R₁).2) (A₂ := (proj hl R₂).1)
      (B₂ := (proj hl R₂).2) ih (List.mem_map_of_mem h₁) (List.mem_map_of_mem h₂) ?_
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hj := hsub (join_mem_of_mem hl hR hx hy)
    rcases hj with hj | hj
    · left
      exact ⟨⟨_, hj, xPart_join hl x y⟩, ⟨_, hj, yPart_join hl x y⟩⟩
    · right
      exact ⟨⟨_, hj, xPart_join hl x y⟩, ⟨_, hj, yPart_join hl x y⟩⟩

theorem proj_univ (hl : 2 * t = l) :
    proj hl (Set.univ : Set (Fin (n + 1) × Fin l → Bool)) =
      ((Set.univ : Set (Half n t)), (Set.univ : Set (Half n t))) := by
  simp only [proj, Set.image_univ, Prod.mk.injEq]
  refine ⟨Set.eq_univ_of_forall fun x => ⟨joinPart hl x x, xPart_join hl x x⟩,
    Set.eq_univ_of_forall fun y => ⟨joinPart hl y y, yPart_join hl y y⟩⟩

/-- The bridge for a general split `l = 2 t`. -/
theorem rectDag_to_adag_gen (hl : 2 * t = l) {ρ : List (Set (Fin (n + 1) × Fin l → Bool))}
    (h : PEqualNP.Search.IsRectDagFor
      (fun v : Fin (n + 1) × Fin l => decide (2 * v.2.val < l))
      (PEqualNP.ProofComplexity.BPHP (n + 1) l) ρ) :
    ∃ σ, ADagFor n t σ ∧ σ.length ≤ ρ.length := by
  refine ⟨ρ.map (proj hl), ⟨adag_map hl h.1, ?_⟩, by simp⟩
  rw [← proj_univ hl]
  exact List.mem_map_of_mem h.2

end Split

theorem two_pow_eq_sixteen_pow (s : ℕ) : 2 ^ (4 * s + 4) = 16 ^ (s + 1) := by
  rw [show 4 * s + 4 = 4 * (s + 1) by ring, pow_mul]
  norm_num

/-- BRIDGE: a rectangle dag for bit pigeonhole with `2 ^ l + 1` pigeons and `l = 4 s + 4`
bits, split down the middle, gives an abstract rectangle dag of no greater length. -/
theorem rectDag_to_adag (s : ℕ)
    {ρ : List (Set (Fin (2 ^ (4 * s + 4) + 1) × Fin (4 * s + 4) → Bool))}
    (h : PEqualNP.Search.IsRectDagFor
      (fun v : Fin (2 ^ (4 * s + 4) + 1) × Fin (4 * s + 4) => decide (2 * v.2.val < 4 * s + 4))
      (PEqualNP.ProofComplexity.BPHP (2 ^ (4 * s + 4) + 1) (4 * s + 4)) ρ) :
    ∃ σ, ADagFor (16 ^ (s + 1)) (2 * s + 2) σ ∧ σ.length ≤ ρ.length := by
  have key : ∀ n, n = 16 ^ (s + 1) →
      ∀ ρ : List (Set (Fin (n + 1) × Fin (4 * s + 4) → Bool)),
      PEqualNP.Search.IsRectDagFor
        (fun v : Fin (n + 1) × Fin (4 * s + 4) => decide (2 * v.2.val < 4 * s + 4))
        (PEqualNP.ProofComplexity.BPHP (n + 1) (4 * s + 4)) ρ →
      ∃ σ, ADagFor (16 ^ (s + 1)) (2 * s + 2) σ ∧ σ.length ≤ ρ.length := by
    intro n hn ρ hρ
    subst hn
    exact rectDag_to_adag_gen (by ring) hρ
  exact key _ (two_pow_eq_sixteen_pow s) ρ h

/-- A polynomial with natural coefficients is at most the sum of its coefficients times
`N ^ natDegree`, for `N ≥ 1`. -/
theorem eval_le_sum_mul (p : Polynomial ℕ) {N : ℕ} (hN : 1 ≤ N) :
    p.eval N ≤ (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) * N ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right hN (by simp at hi; omega)

theorem two_mul_le_two_pow {A : ℕ} (hA : 1 ≤ A) : 2 * A ≤ 2 ^ A := by
  have h := Nat.lt_two_pow_self (n := A - 1)
  have : 2 ^ A = 2 * 2 ^ (A - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

/-- For every polynomial `p` some `s` has `p (16 ^ (s + 1)) < 2 ^ (2 ^ (s - 1) - 1)`. -/
theorem exists_eval_lt (p : Polynomial ℕ) :
    ∃ s : ℕ, p.eval (16 ^ (s + 1)) < 2 ^ (2 ^ (s - 1) - 1) := by
  set d := p.natDegree
  set C := ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i
  set A := 12 * d + C + 1
  set k := 2 * A
  refine ⟨k + 1, ?_⟩
  have hA : 1 ≤ A := by omega
  -- the exponent comparison
  have h2A := two_mul_le_two_pow hA
  have hkA : k = 2 * A := rfl
  have hk : 2 ^ k = 2 ^ A * 2 ^ A := by rw [hkA, two_mul, pow_add]
  have hbig : A * k < 2 ^ k := by
    rw [hk]
    have : 2 * A * (2 * A) ≤ 2 ^ A * 2 ^ A := Nat.mul_le_mul h2A h2A
    rw [hkA]
    nlinarith
  have hk1 : 1 ≤ k := by omega
  have hlin : (4 * (k + 1) + 4) * d + C + 1 ≤ A * k := by
    simp only [A]
    nlinarith
  have hexp : C + (4 * (k + 1) + 4) * d < 2 ^ (k + 1 - 1) - 1 := by
    simp only [Nat.add_sub_cancel]
    omega
  calc p.eval (16 ^ (k + 1 + 1)) ≤ C * (16 ^ (k + 1 + 1)) ^ d :=
        eval_le_sum_mul p (Nat.one_le_pow _ _ (by norm_num))
    _ ≤ 2 ^ C * 2 ^ ((4 * (k + 1) + 4) * d) := by
        apply Nat.mul_le_mul (Nat.lt_two_pow_self).le
        rw [← two_pow_eq_sixteen_pow, ← pow_mul]
    _ = 2 ^ (C + (4 * (k + 1) + 4) * d) := by rw [pow_add]
    _ < 2 ^ (2 ^ (k + 1 - 1) - 1) := Nat.pow_lt_pow_right (by norm_num) hexp

/-- FINAL: rectangle dags for bit pigeonhole, split down the middle, are superpolynomial in
the number of holes. -/
theorem bw_superpoly : ∀ p : Polynomial ℕ, ∃ l : ℕ,
    ∀ ρ : List (Set (Fin (2 ^ l + 1) × Fin l → Bool)),
      PEqualNP.Search.IsRectDagFor (fun v : Fin (2 ^ l + 1) × Fin l => decide (2 * v.2.val < l))
        (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) ρ → p.eval (2 ^ l) < ρ.length := by
  intro p
  obtain ⟨s, hs⟩ := exists_eval_lt p
  refine ⟨4 * s + 4, fun ρ hρ => ?_⟩
  obtain ⟨σ, hσ, hlen⟩ := rectDag_to_adag s hρ
  have := adag_lower' s σ hσ
  have e : p.eval (2 ^ (4 * s + 4)) = p.eval (16 ^ (s + 1)) := by
    rw [two_pow_eq_sixteen_pow]
  omega

end PEqualNP.Search.Helpers.BW
