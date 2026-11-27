import PEqualNP.Defs
import PEqualNP.Search.Helpers.ResLinQ
import Mathlib.Tactic

/-!
# Helpers: what semantic weakening gives to dag-like Res(lin) over the integers

Used by the refutation of `L-alg-004`.

The weakening rule of `IsResLinQDerivation` is semantic. Two consequences:

* a conjunction of literals is one equation with coefficients `1`, `-1`, `0` (`agreeEq`), so
  a line can say "some clause of the formula is falsified", and for an unsatisfiable formula
  that line is implied by anything;
* an equation that falsifies every literal of a clause is cut from the head of a line with
  three lines per literal (`cut`), reusing the line once per literal.

Together (`short_refutation`): a list `E` of equations that covers every 0/1 point, each
falsifying a clause of width at most `k`, gives a refutation with at most
`2 + |E| (3 k + 2)` lines. For the bit pigeonhole formula `E` is "pigeons `i`, `j` both sit
in hole `α`" (`bphp_short`).
-/

namespace PEqualNP.Search.Helpers

open PEqualNP.Search PEqualNP.ProofComplexity

section General

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The equation "the point agrees with `t` on every variable in `S`". -/
def agreeEq (S : V → Prop) [DecidablePred S] (t : V → Bool) : QEq V :=
  (fun v => if S v then (if t v then 1 else -1) else 0,
   ∑ v, if S v then (if t v then 1 else 0) else 0)

theorem agreeEq_holds (S : V → Prop) [DecidablePred S] (t x : V → Bool) :
    QEq.Holds x (agreeEq S t) ↔ ∀ v, S v → x v = t v := by
  unfold QEq.Holds agreeEq
  rw [Finset.sum_eq_sum_iff_of_le]
  · refine ⟨fun h v hv => ?_, fun h v _ => ?_⟩
    · have := h v (Finset.mem_univ v)
      simp only [hv, if_true] at this
      cases hx : x v <;> cases ht : t v <;> simp [hx, ht] at this ⊢
    · by_cases hv : S v
      · have := h v hv
        cases hx : x v <;> cases ht : t v <;> simp_all
      · simp [hv]
  · intro v _
    by_cases hv : S v <;> cases hx : x v <;> cases ht : t v <;> simp [hv, hx, ht]

theorem nat_size_le_self (n : ℕ) : Nat.size n ≤ n :=
  Nat.size_le.mpr Nat.lt_two_pow_self

theorem agreeEq_size (S : V → Prop) [DecidablePred S] (t : V → Bool) :
    (agreeEq S t).size ≤ 3 + 2 * Fintype.card V := by
  unfold QEq.size agreeEq
  have h1 : (∑ v : V, Nat.size (if S v then (if t v then (1 : ℤ) else -1) else 0).natAbs)
      ≤ Fintype.card V := by
    calc _ ≤ ∑ _v : V, 1 := Finset.sum_le_sum fun v _ => by
            by_cases hv : S v <;> cases ht : t v <;> simp [hv]
      _ = Fintype.card V := by simp
  have h2 : Nat.size (∑ v : V, if S v then (if t v then (1 : ℤ) else 0) else 0).natAbs
      ≤ Fintype.card V := by
    calc _ ≤ (∑ v : V, if S v then (if t v then (1 : ℤ) else 0) else 0).natAbs :=
            nat_size_le_self _
      _ ≤ ∑ v : V, (if S v then (if t v then (1 : ℤ) else 0) else 0).natAbs :=
            Int.natAbs_sum_le _ _
      _ ≤ ∑ _v : V, 1 := Finset.sum_le_sum fun v _ => by
            by_cases hv : S v <;> cases ht : t v <;> simp [hv]
      _ = Fintype.card V := by simp
  dsimp only
  omega

theorem litQEq_size (l : V × Bool) : (litQEq l).size ≤ 3 := by
  unfold QEq.size litQEq
  have h1 : (∑ v : V, Nat.size (if v = l.1 then (1 : ℤ) else 0).natAbs) = 1 := by
    have : ∀ v : V, Nat.size (if v = l.1 then (1 : ℤ) else 0).natAbs = if v = l.1 then 1 else 0 := by
      intro v; by_cases hv : v = l.1 <;> simp [hv]
    simp [this]
  have h2 : Nat.size (if l.2 = true then (1 : ℤ) else 0).natAbs ≤ 1 := by
    cases l.2 <;> simp
  simp only at h1 h2 ⊢
  omega

/-- The combination of a literal equation with the equation of the opposite literal. -/
def clashEq (l : V × Bool) : QEq V :=
  ((1 : ℤ) • (litQEq l).1 + (-1 : ℤ) • (litQEq (l.1, !l.2)).1,
    1 * (litQEq l).2 + (-1) * (litQEq (l.1, !l.2)).2)

theorem clashEq_not_holds (x : V → Bool) (l : V × Bool) : ¬ QEq.Holds x (clashEq l) := by
  unfold QEq.Holds clashEq litQEq
  cases l.2 <;> simp

theorem clashEq_size (l : V × Bool) : (clashEq l).size ≤ 3 := by
  unfold QEq.size clashEq litQEq
  cases l.2 <;> simp

/-- Cutting the literals of a list one by one against an equation that falsifies them. -/
theorem cut_aux (F : Set (PEqualNP.ProofComplexity.Clause V)) (e : QEq V) (R : QLine V) :
    ∀ (lits : List (V × Bool)),
      (∀ lit ∈ lits, ∀ x : V → Bool, QEq.Holds x e → x lit.1 = !lit.2) →
      ∀ π : List (QLine V), IsResLinQDerivation F π → (e :: R) ∈ π →
        (lits.map litQEq ++ R) ∈ π →
        ∃ ρ : List (QLine V), IsResLinQDerivation F (ρ ++ π) ∧ R ∈ ρ ++ π ∧
          ρ.length = 3 * lits.length ∧
          ∀ L ∈ ρ, L.length ≤ lits.length + 1 + 2 * R.length ∧
            ∀ e' ∈ L, e' ∈ R ∨ e'.size ≤ 3 := by
  intro lits
  induction lits with
  | nil =>
    intro _ π hπ _ hR
    exact ⟨[], by simpa using hπ, by simpa using hR, by simp, by simp⟩
  | cons lit rest ih =>
    intro hf π hπ he hD
    -- line 1: the opposite literal in front of `R`
    have h1 : IsResLinQDerivation F ((litQEq (lit.1, !lit.2) :: R) :: π) := by
      refine IsResLinQDerivation.weaken hπ he ?_
      rintro x ⟨e', he', hx⟩
      rcases List.mem_cons.mp he' with rfl | he'
      · exact ⟨_, List.mem_cons_self, litQEq_holds x (lit.1, !lit.2)
          (hf lit List.mem_cons_self x hx)⟩
      · exact ⟨e', List.mem_cons_of_mem _ he', hx⟩
    -- line 2: the combination
    have h2 : IsResLinQDerivation F
        ((clashEq lit :: ((rest.map litQEq ++ R) ++ R)) ::
          (litQEq (lit.1, !lit.2) :: R) :: π) :=
      IsResLinQDerivation.res (e := litQEq lit) (e' := litQEq (lit.1, !lit.2)) 1 (-1) h1
        (List.mem_cons_of_mem _ (by simpa using hD)) List.mem_cons_self
    -- line 3: drop the false equation and the copy of `R`
    have h3 : IsResLinQDerivation F
        ((rest.map litQEq ++ R) :: (clashEq lit :: ((rest.map litQEq ++ R) ++ R)) ::
          (litQEq (lit.1, !lit.2) :: R) :: π) := by
      refine IsResLinQDerivation.weaken h2 List.mem_cons_self ?_
      rintro x ⟨e', he', hx⟩
      rcases List.mem_cons.mp he' with rfl | he'
      · exact absurd hx (clashEq_not_holds x lit)
      · rcases List.mem_append.mp he' with he' | he'
        · exact ⟨e', he', hx⟩
        · exact ⟨e', List.mem_append_right _ he', hx⟩
    obtain ⟨ρ, hρ, hRρ, hlen, hb⟩ := ih (fun l hl => hf l (List.mem_cons_of_mem _ hl)) _ h3
      (by simp [he]) List.mem_cons_self
    refine ⟨ρ ++ [rest.map litQEq ++ R, clashEq lit :: ((rest.map litQEq ++ R) ++ R),
      litQEq (lit.1, !lit.2) :: R], by simpa using hρ, by simpa using hRρ, by simp [hlen]; omega,
      ?_⟩
    intro L hL
    rcases List.mem_append.mp hL with hL | hL
    · obtain ⟨hl, hs⟩ := hb L hL
      exact ⟨by simp only [List.length_cons]; omega, hs⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
      rcases hL with rfl | rfl | rfl
      · refine ⟨by simp; omega, fun e' he' => ?_⟩
        rcases List.mem_append.mp he' with he' | he'
        · obtain ⟨l', _, rfl⟩ := List.mem_map.mp he'
          exact Or.inr (litQEq_size l')
        · exact Or.inl he'
      · refine ⟨by simp; omega, fun e' he' => ?_⟩
        rcases List.mem_cons.mp he' with rfl | he'
        · exact Or.inr (clashEq_size lit)
        · rcases List.mem_append.mp he' with he' | he'
          · rcases List.mem_append.mp he' with he' | he'
            · obtain ⟨l', _, rfl⟩ := List.mem_map.mp he'
              exact Or.inr (litQEq_size l')
            · exact Or.inl he'
          · exact Or.inl he'
      · refine ⟨by simp; omega, fun e' he' => ?_⟩
        rcases List.mem_cons.mp he' with rfl | he'
        · exact Or.inr (litQEq_size _)
        · exact Or.inl he'

/-- The cut: an equation that falsifies every literal of a clause of the formula is removed
from the head of a line, with `3 |C| + 2` new lines. -/
theorem cut (F : Set (PEqualNP.ProofComplexity.Clause V)) (e : QEq V) (R : QLine V)
    (C : PEqualNP.ProofComplexity.Clause V) (hC : C ∈ F)
    (hf : ∀ lit ∈ C, ∀ x : V → Bool, QEq.Holds x e → x lit.1 = !lit.2)
    (π : List (QLine V)) (hπ : IsResLinQDerivation F π) (he : (e :: R) ∈ π) :
    ∃ ρ : List (QLine V), IsResLinQDerivation F (ρ ++ π) ∧ R ∈ ρ ++ π ∧
      ρ.length = 3 * C.card + 2 ∧
      ∀ L ∈ ρ, L.length ≤ C.card + 1 + 2 * R.length ∧
        ∀ e' ∈ L, e' ∈ R ∨ e'.size ≤ 3 := by
  have h1 : IsResLinQDerivation F (C.toList.map litQEq :: π) :=
    IsResLinQDerivation.ax C hπ hC (fun e' => by
      simp only [List.mem_map, Finset.mem_toList]
      exact ⟨fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩, fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩⟩)
  have h2 : IsResLinQDerivation F ((C.toList.map litQEq ++ R) :: C.toList.map litQEq :: π) := by
    refine IsResLinQDerivation.weaken h1 List.mem_cons_self ?_
    rintro x ⟨e', he', hx⟩
    exact ⟨e', List.mem_append_left _ he', hx⟩
  obtain ⟨ρ, hρ, hRρ, hlen, hb⟩ := cut_aux F e R C.toList
    (fun l hl => hf l (Finset.mem_toList.mp hl)) _ h2 (by simp [he]) List.mem_cons_self
  rw [Finset.length_toList] at hlen hb
  refine ⟨ρ ++ [C.toList.map litQEq ++ R, C.toList.map litQEq], by simpa using hρ,
    by simpa using hRρ, by simp [hlen], ?_⟩
  intro L hL
  rcases List.mem_append.mp hL with hL | hL
  · exact hb L hL
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl
    · refine ⟨by simp; omega, fun e' he' => ?_⟩
      rcases List.mem_append.mp he' with he' | he'
      · obtain ⟨l', _, rfl⟩ := List.mem_map.mp he'
        exact Or.inr (litQEq_size l')
      · exact Or.inl he'
    · refine ⟨by simp; omega, fun e' he' => ?_⟩
      obtain ⟨l', _, rfl⟩ := List.mem_map.mp he'
      exact Or.inr (litQEq_size l')

/-- Cutting every equation of a line in turn. -/
theorem cut_all (F : Set (PEqualNP.ProofComplexity.Clause V)) (k : ℕ) :
    ∀ (E : QLine V),
      (∀ e ∈ E, ∃ C ∈ F, C.card ≤ k ∧
        ∀ lit ∈ C, ∀ x : V → Bool, QEq.Holds x e → x lit.1 = !lit.2) →
      ∀ π : List (QLine V), IsResLinQDerivation F π → E ∈ π →
        ∃ ρ : List (QLine V), IsResLinQDerivation F (ρ ++ π) ∧ [] ∈ ρ ++ π ∧
          ρ.length ≤ E.length * (3 * k + 2) ∧
          ∀ L ∈ ρ, L.length ≤ k + 1 + 2 * E.length ∧
            ∀ e' ∈ L, e' ∈ E ∨ e'.size ≤ 3 := by
  intro E
  induction E with
  | nil =>
    intro _ π hπ hE
    exact ⟨[], by simpa using hπ, by simpa using hE, by simp, by simp⟩
  | cons e R ih =>
    intro hE π hπ he
    obtain ⟨C, hC, hk, hf⟩ := hE e List.mem_cons_self
    obtain ⟨ρ₁, hρ₁, hR, hlen₁, hb₁⟩ := cut F e R C hC hf π hπ he
    obtain ⟨ρ₂, hρ₂, hnil, hlen₂, hb₂⟩ :=
      ih (fun e' he' => hE e' (List.mem_cons_of_mem _ he')) _ hρ₁ hR
    refine ⟨ρ₂ ++ ρ₁, by simpa using hρ₂, by simpa using hnil, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, hlen₁]
      have : 3 * C.card + 2 ≤ 3 * k + 2 := by omega
      nlinarith
    · intro L hL
      rcases List.mem_append.mp hL with hL | hL
      · obtain ⟨hl, hs⟩ := hb₂ L hL
        refine ⟨by simp only [List.length_cons]; omega, fun e' he' => ?_⟩
        rcases hs e' he' with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
      · obtain ⟨hl, hs⟩ := hb₁ L hL
        refine ⟨by simp only [List.length_cons]; omega, fun e' he' => ?_⟩
        rcases hs e' he' with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

theorem resLinQSize_le (π : List (QLine V)) (W S : ℕ)
    (h : ∀ L ∈ π, L.length ≤ W ∧ ∀ e ∈ L, e.size ≤ S) :
    resLinQSize π ≤ π.length * (1 + W * S) := by
  unfold resLinQSize
  have := List.sum_le_card_nsmul (π.map fun L => 1 + (L.map QEq.size).sum) (1 + W * S) (by
    intro n hn
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hn
    obtain ⟨hl, hs⟩ := h L hL
    have h' := List.sum_le_card_nsmul (L.map QEq.size) S (by
      intro n hn
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hn
      exact hs e he)
    simp only [List.length_map, smul_eq_mul] at h'
    have : L.length * S ≤ W * S := Nat.mul_le_mul_right S hl
    omega)
  simpa using this

/-- A line of equations that covers every 0/1 point, each equation falsifying a clause of the
formula of width at most `k`, gives a short dag-like refutation. -/
theorem short_refutation (F : Set (PEqualNP.ProofComplexity.Clause V)) (k S : ℕ)
    (hS : 3 ≤ S) (E : QLine V)
    (hcover : ∀ x : V → Bool, QLine.Holds x E)
    (hE : ∀ e ∈ E, ∃ C ∈ F, C.card ≤ k ∧
      ∀ lit ∈ C, ∀ x : V → Bool, QEq.Holds x e → x lit.1 = !lit.2)
    (hsize : ∀ e ∈ E, e.size ≤ S) :
    ∃ π : List (QLine V), IsResLinQRefutation F π ∧
      resLinQSize π ≤ (2 + E.length * (3 * k + 2)) * (1 + (k + 1 + 2 * E.length) * S) := by
  obtain ⟨e₀, he₀, -⟩ := hcover (fun _ => false)
  obtain ⟨C₀, hC₀, hk₀, -⟩ := hE e₀ he₀
  have h1 : IsResLinQDerivation F [C₀.toList.map litQEq] :=
    IsResLinQDerivation.ax C₀ IsResLinQDerivation.nil hC₀ (fun e' => by
      simp only [List.mem_map, Finset.mem_toList]
      exact ⟨fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩, fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩⟩)
  have h2 : IsResLinQDerivation F [E, C₀.toList.map litQEq] :=
    IsResLinQDerivation.weaken h1 List.mem_cons_self (fun x _ => hcover x)
  obtain ⟨ρ, hρ, hnil, hlen, hb⟩ := cut_all F k E hE _ h2 List.mem_cons_self
  refine ⟨ρ ++ [E, C₀.toList.map litQEq], ⟨hρ, hnil⟩, ?_⟩
  refine (resLinQSize_le _ (k + 1 + 2 * E.length) S ?_).trans ?_
  · intro L hL
    rcases List.mem_append.mp hL with hL | hL
    · obtain ⟨hl, hs⟩ := hb L hL
      refine ⟨hl, fun e' he' => ?_⟩
      rcases hs e' he' with h | h
      · exact hsize e' h
      · exact h.trans hS
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
      rcases hL with rfl | rfl
      · exact ⟨by omega, hsize⟩
      · refine ⟨by simp; omega, fun e' he' => ?_⟩
        obtain ⟨l', _, rfl⟩ := List.mem_map.mp he'
        exact (litQEq_size l').trans hS
  · refine Nat.mul_le_mul_right _ ?_
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

end General

/-! ## The bit pigeonhole formula -/

/-- "Pigeons `i` and `j` both sit in hole `α`", as one equation. -/
def colEq (m l : ℕ) (t : Fin m × Fin m × (Fin l → Bool)) : QEq (Fin m × Fin l) :=
  agreeEq (fun v => v.1 = t.1 ∨ v.1 = t.2.1) (fun v => t.2.2 v.2)

/-- The line "some two different pigeons sit in the same hole". -/
noncomputable def colLine (m l : ℕ) : QLine (Fin m × Fin l) :=
  ((Finset.univ : Finset (Fin m × Fin m × (Fin l → Bool))).filter
    (fun t => t.1 ≠ t.2.1)).toList.map (colEq m l)

theorem colLine_length (m l : ℕ) : (colLine m l).length ≤ m * (m * 2 ^ l) := by
  unfold colLine
  rw [List.length_map, Finset.length_toList]
  refine (Finset.card_filter_le _ _).trans ?_
  simp

theorem colLine_cover (l : ℕ) (x : Fin (2 ^ l + 1) × Fin l → Bool) :
    QLine.Holds x (colLine (2 ^ l + 1) l) := by
  obtain ⟨i, j, hij, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun (i : Fin (2 ^ l + 1)) (b : Fin l) => x (i, b)) (by simp)
  refine ⟨colEq _ l (i, j, fun b => x (i, b)), ?_, ?_⟩
  · unfold colLine
    exact List.mem_map.mpr ⟨_, by simp [hij], rfl⟩
  · unfold colEq
    rw [agreeEq_holds]
    rintro ⟨p, b⟩ (hp | hp)
    · simp only at hp; subst hp; rfl
    · simp only at hp; subst hp; exact (congrFun h b).symm

theorem colLine_falsifies (m l : ℕ) :
    ∀ e ∈ colLine m l, ∃ C ∈ PEqualNP.ProofComplexity.BPHP m l, C.card ≤ 2 * l ∧
      ∀ lit ∈ C, ∀ x : Fin m × Fin l → Bool, QEq.Holds x e → x lit.1 = !lit.2 := by
  intro e he
  unfold colLine at he
  obtain ⟨⟨i, j, α⟩, ht, rfl⟩ := List.mem_map.mp he
  simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  refine ⟨_, ⟨i, j, α, ht, rfl⟩, ?_, ?_⟩
  · refine (Finset.card_union_le _ _).trans ?_
    have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin l)))
      (f := fun b : Fin l => ((i, b), !α b))
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin l)))
      (f := fun b : Fin l => ((j, b), !α b))
    simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
    omega
  · intro lit hlit x hx
    unfold colEq at hx
    rw [agreeEq_holds] at hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hlit
    rcases hlit with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · simpa using hx (i, b) (Or.inl rfl)
    · simpa using hx (j, b) (Or.inr rfl)

/-- The polynomial that bounds the refutation of the bit pigeonhole formula, in `X = 2 ^ l`. -/
noncomputable def bphpPoly : Polynomial ℕ :=
  (2 + (Polynomial.X + 1) * ((Polynomial.X + 1) * Polynomial.X) * (6 * Polynomial.X + 2)) *
    (1 + (2 * Polynomial.X + 1 + 2 * ((Polynomial.X + 1) * ((Polynomial.X + 1) * Polynomial.X)))
      * (3 + 2 * ((Polynomial.X + 1) * Polynomial.X)))

/-- The bit pigeonhole formula with `2 ^ l + 1` pigeons has a dag-like refutation in Res(lin)
over the integers, with semantic weakening, of size polynomial in `2 ^ l`. -/
theorem bphp_short (l : ℕ) :
    ∃ π : List (QLine (Fin (2 ^ l + 1) × Fin l)),
      IsResLinQRefutation (BPHP (2 ^ l + 1) l) π ∧ resLinQSize π ≤ bphpPoly.eval (2 ^ l) := by
  obtain ⟨π, hπ, hs⟩ := short_refutation (BPHP (2 ^ l + 1) l) (2 * l)
    (3 + 2 * ((2 ^ l + 1) * l)) (by omega) (colLine (2 ^ l + 1) l) (colLine_cover l)
    (colLine_falsifies _ l) (by
      intro e he
      unfold colLine at he
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp he
      have := agreeEq_size (fun v : Fin (2 ^ l + 1) × Fin l => v.1 = t.1 ∨ v.1 = t.2.1)
        (fun v => t.2.2 v.2)
      simpa [colEq] using this)
  refine ⟨π, hπ, hs.trans ?_⟩
  have hl : l ≤ 2 ^ l := Nat.lt_two_pow_self.le
  have hE := colLine_length (2 ^ l + 1) l
  have hev : bphpPoly.eval (2 ^ l) =
      (2 + (2 ^ l + 1) * ((2 ^ l + 1) * 2 ^ l) * (6 * 2 ^ l + 2)) *
        (1 + (2 * 2 ^ l + 1 + 2 * ((2 ^ l + 1) * ((2 ^ l + 1) * 2 ^ l)))
          * (3 + 2 * ((2 ^ l + 1) * 2 ^ l))) := by
    simp [bphpPoly]
  rw [hev]
  generalize (colLine (2 ^ l + 1) l).length = M at hE ⊢
  generalize 2 ^ l = N at hl hE ⊢
  have h3 : 3 * (2 * l) + 2 ≤ 6 * N + 2 := by omega
  have h4 : 2 * l + 1 + 2 * M ≤ 2 * N + 1 + 2 * ((N + 1) * ((N + 1) * N)) := by omega
  have h5 : 3 + 2 * ((N + 1) * l) ≤ 3 + 2 * ((N + 1) * N) := by
    have := Nat.mul_le_mul_left (N + 1) hl
    omega
  gcongr

end PEqualNP.Search.Helpers
