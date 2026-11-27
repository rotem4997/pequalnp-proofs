import Mathlib

/-!
# Honest factor

If a point-only monotone function `Λ` AND a list `r` of monotone functions is true only at inputs
where an incident point and line are both on, and is true at the input with exactly point `p` and
line `w` on, then `r` is nonempty and some member is honest at `p`: false at `p` alone, and true at
`p` plus a line `u` only when `I p u`.

Proof: if no member is honest, the input with `p` and every line `u` with `¬ I p u` on makes every
member true (monotonicity), and `Λ` true (same points as the edge input), yet carries no incident
pair.
-/

namespace PEqualNP.MetaComplexity.HonestFactor

open Classical

theorem castAdd_ne_natAdd' {N : ℕ} (i j : Fin N) : Fin.castAdd N i ≠ Fin.natAdd N j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem pi_le_of_imp {α : Type*} {x y : α → Bool} (h : ∀ k, x k = true → y k = true) :
    x ≤ y := by
  intro k
  cases hx : x k
  · exact Bool.false_le _
  · rw [h k hx]

theorem eq_true_of_true_le' {b : Bool} (h : true ≤ b) : b = true := by
  revert h; cases b <;> decide

theorem castAdd_inj' {N : ℕ} (i j : Fin N) : Fin.castAdd N i = Fin.castAdd N j ↔ i = j := by
  constructor
  · intro h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · rintro rfl; rfl

theorem natAdd_inj' {N : ℕ} (i j : Fin N) : Fin.natAdd N i = Fin.natAdd N j ↔ i = j := by
  constructor
  · intro h
    have := congrArg Fin.val h
    simp only [Fin.val_natAdd] at this
    exact Fin.ext (by omega)
  · rintro rfl; rfl

theorem main (N : ℕ) (I : Fin N → Fin N → Prop) (Λ : (Fin (N + N) → Bool) → Bool)
    (r : List ((Fin (N + N) → Bool) → Bool)) (p w : Fin N) (_hΛ : Monotone Λ)
    (hpts : ∀ z z' : Fin (N + N) → Bool,
      (∀ i : Fin N, z (Fin.castAdd N i) = z' (Fin.castAdd N i)) → Λ z = Λ z')
    (hr : ∀ f ∈ r, Monotone f)
    (honly : ∀ z : Fin (N + N) → Bool, (Λ z && r.all (fun f => f z)) = true →
      ∃ a b : Fin N, I a b ∧ z (Fin.castAdd N a) = true ∧ z (Fin.natAdd N b) = true)
    (hedge : (Λ (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w)) &&
      r.all (fun f => f (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w)))) = true) :
    r ≠ [] ∧ ∃ f ∈ r, f (fun k => decide (k = Fin.castAdd N p)) = false ∧
      ∀ u : Fin N, f (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N u)) = true →
        I p u := by
  rw [Bool.and_eq_true] at hedge
  have hΛe := hedge.1
  -- Λ is true at any input whose point part is exactly p
  have hΛz : ∀ z : Fin (N + N) → Bool,
      (∀ i : Fin N, z (Fin.castAdd N i) = decide (i = p)) → Λ z = true := by
    intro z hz
    rw [← hΛe]
    apply hpts
    intro i
    rw [hz i]
    apply decide_eq_decide.mpr
    constructor
    · rintro rfl; exact Or.inl rfl
    · rintro (h | h)
      · exact (castAdd_inj' _ _).mp h
      · exact absurd h (castAdd_ne_natAdd' _ _)
  constructor
  · rintro rfl
    obtain ⟨a, b, -, -, hb⟩ := honly (fun k => decide (k = Fin.castAdd N p)) (by
      simp only [List.all_nil, Bool.and_true]
      apply hΛz
      intro i
      simp)
    exact castAdd_ne_natAdd' p b (of_decide_eq_true hb).symm
  · by_contra hno
    push Not at hno
    let z : Fin (N + N) → Bool :=
      fun k => decide (k = Fin.castAdd N p ∨ ∃ u, k = Fin.natAdd N u ∧ ¬ I p u)
    have hzf : ∀ f ∈ r, f z = true := by
      intro f hf
      by_cases h0 : f (fun k => decide (k = Fin.castAdd N p)) = false
      · obtain ⟨u, hu, hnI⟩ := hno f hf h0
        have hle : (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N u)) ≤ z := by
          apply pi_le_of_imp
          intro k hk
          simp only [z, decide_eq_true_eq] at hk ⊢
          rcases hk with hk | hk
          · exact Or.inl hk
          · exact Or.inr ⟨u, hk, hnI⟩
        have := hr f hf hle
        rw [hu] at this
        exact eq_true_of_true_le' this
      · have h1 : f (fun k => decide (k = Fin.castAdd N p)) = true := by
          simpa using h0
        have hle : (fun k => decide (k = Fin.castAdd N p)) ≤ z := by
          apply pi_le_of_imp
          intro k hk
          simp only [z, decide_eq_true_eq] at hk ⊢
          exact Or.inl hk
        have := hr f hf hle
        rw [h1] at this
        exact eq_true_of_true_le' this
    have hzΛ : Λ z = true := by
      apply hΛz
      intro i
      simp only [z, castAdd_inj', decide_eq_decide]
      constructor
      · rintro (h | ⟨u, hu, -⟩)
        · exact h
        · exact absurd hu (castAdd_ne_natAdd' _ _)
      · intro h; exact Or.inl h
    obtain ⟨a, b, hab, ha, hb⟩ := honly z (by
      rw [Bool.and_eq_true, List.all_eq_true]
      exact ⟨hzΛ, fun f hf => hzf f hf⟩)
    simp only [z, decide_eq_true_eq] at ha hb
    rcases hb with hb | ⟨u, hu, hnI⟩
    · exact absurd hb.symm (castAdd_ne_natAdd' _ _)
    · rw [natAdd_inj'] at hu
      subst hu
      rcases ha with ha | ⟨v, hv, -⟩
      · rw [castAdd_inj'] at ha
        subst ha
        exact hnI hab
      · exact absurd hv (castAdd_ne_natAdd' _ _)

end PEqualNP.MetaComplexity.HonestFactor
