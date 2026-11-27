import PEqualNP.Search.Helpers.Tree.Closure
import PEqualNP.Search.Helpers.Tree.Game
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Helpers for L-lib-103: the touched-injective Delayer

The Delayer's state is a set `T` of touched pigeons and a list `Φ` of coin equations; its set
is `DX T Φ`, the points that put the pigeons of `T` in different holes and falsify every
entry of `Φ`. The invariant `DGood r K T Φ` (pigeon density, threshold `r`):

* `Φ` has at most `K` entries;
* every entry is closed (touches no free pigeon) or dense (touches at least `r`);
* the potential `|T| + r * nc T Φ` is at most `r * |Φ|` (so `|T| ≤ r * |Φ|`);
* `DX T Φ` has a point.

With `128 Kmax^2 ≤ r` and `8 (r Kmax)^2 ≤ 2^l`, a Good state with `K ≤ Kmax` is never inside an
axiom cube (`delayer_axiom`), and with `K < Kmax` it extends by any equation some point of
`DX T Φ` falsifies (`delayer_extend`). The game of `Game.lean` then gives `2^Kmax` nodes.
-/

namespace PEqualNP.Search.Helpers.Tree

open PEqualNP.Search

open scoped Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι] {l : ℕ}

/-- The Delayer's invariant. -/
def DGood (r K : ℕ) (T : Finset ι) (Φ : List (QEq (ι × Fin l))) : Prop :=
  Φ.length ≤ K ∧ (∀ e ∈ Φ, kT T e = 0 ∨ r ≤ kT T e) ∧ T.card + r * nc T Φ ≤ r * Φ.length ∧
    ∃ x, Inj T x ∧ ∀ e ∈ Φ, ¬ QEq.Holds x e

/-- The Delayer's set. -/
def DX (T : Finset ι) (Φ : List (QEq (ι × Fin l))) : Set (ι × Fin l → Bool) :=
  {y | Inj T y ∧ ∀ e ∈ Φ, ¬ QEq.Holds y e}

theorem closed_false {T : Finset ι} {Φ : List (QEq (ι × Fin l))} {x y : ι × Fin l → Bool}
    (hx : ∀ e ∈ Φ, ¬ QEq.Holds x e) (hy : y ∈ Om x T) :
    ∀ e ∈ Φ, kT T e = 0 → ¬ QEq.Holds y e :=
  fun e he h0 h => hx e he ((closed_holds_iff h0 hy).mp h)

/-- L1: a Good state is never inside an axiom cube. -/
theorem delayer_axiom (r K Kmax : ℕ) (hK1 : 1 ≤ Kmax) (hr : 128 * Kmax ^ 2 ≤ r) (hl : 2 ≤ l)
    {T : Finset ι} {Φ : List (QEq (ι × Fin l))} (hG : DGood r K T Φ) (hK : K ≤ Kmax)
    (i i' : ι) (hii : i ≠ i') (α : Fin l → Bool) :
    ∃ y ∈ DX T Φ, ¬ (hole y i = α ∧ hole y i' = α) := by
  obtain ⟨hlen, hcd, -, x, hxI, hxF⟩ := hG
  by_cases hxQ : hole x i = α ∧ hole x i' = α
  swap
  · exact ⟨x, ⟨hxI, hxF⟩, hxQ⟩
  set W := (Om x T).card
  have hW : 1 ≤ W := Finset.card_pos.mpr ⟨x, self_mem_Om x T⟩
  set cQ := ((Om x T).filter fun y => hole y i = α ∧ hole y i' = α).card
  have hQ : 4 * cQ ≤ W := by
    have h4 : 4 ≤ 2 ^ l :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
    have key : ∃ u, u ∉ T ∧ ((Om x T).filter fun y => hole y i = α ∧ hole y i' = α) ⊆
        (Om x T).filter fun y => hole y u = α := by
      by_cases hiT : i ∈ T
      · by_cases hi'T : i' ∈ T
        · exact absurd (hxQ.1.trans hxQ.2.symm) (hxI i hiT i' hi'T hii)
        · refine ⟨i', hi'T, fun y hy => ?_⟩
          simp only [Finset.mem_filter] at hy ⊢
          exact ⟨hy.1, hy.2.2⟩
      · refine ⟨i, hiT, fun y hy => ?_⟩
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, hy.2.1⟩
    obtain ⟨u, hu, hsub⟩ := key
    have hc := cube_small x T u hu (fun _ => α) (fun _ _ _ => rfl)
    have h2 : cQ ≤ ((Om x T).filter fun y => hole y u = α).card := Finset.card_le_card hsub
    calc 4 * cQ ≤ 2 ^ l * cQ := Nat.mul_le_mul_right _ h4
      _ ≤ 2 ^ l * ((Om x T).filter fun y => hole y u = α).card := Nat.mul_le_mul_left _ h2
      _ = ((Om x T).filter fun y => hole y u = α).card * 2 ^ l := by ring
      _ ≤ W := hc
  set D := ((Om x T).filter fun y => ∃ d ∈ Φ, kT T d ≠ 0 ∧ QEq.Holds y d).card
  have hD := dense_list_bound x T Kmax r hr hl Φ hcd
  have hD' : 4 * D ≤ W := by
    have : Kmax * (4 * D) ≤ Kmax * W :=
      calc Kmax * (4 * D) = 4 * Kmax * D := by ring
        _ ≤ Φ.length * W := hD
        _ ≤ Kmax * W := Nat.mul_le_mul_right _ (hlen.trans hK)
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hbad : ((Om x T).filter fun y => (hole y i = α ∧ hole y i' = α) ∨
      ∃ d ∈ Φ, kT T d ≠ 0 ∧ QEq.Holds y d).card < W := by
    have hsub : ((Om x T).filter fun y => (hole y i = α ∧ hole y i' = α) ∨
        ∃ d ∈ Φ, kT T d ≠ 0 ∧ QEq.Holds y d) ⊆
        ((Om x T).filter fun y => hole y i = α ∧ hole y i' = α) ∪
          ((Om x T).filter fun y => ∃ d ∈ Φ, kT T d ≠ 0 ∧ QEq.Holds y d) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      rcases hy.2 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy.1, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy.1, h⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  obtain ⟨y, hyO, hyb⟩ := exists_not_of_card_lt _ _ hbad
  push Not at hyb
  refine ⟨y, ⟨inj_of_mem_Om hxI hyO, fun e he h => ?_⟩, fun h => hyb.1 h.1 h.2⟩
  by_cases h0 : kT T e = 0
  · exact closed_false hxF hyO e he h0 h
  · exact hyb.2 e he h0 h

/-- L2: a Good state with a coin left extends by any equation one of its points falsifies. -/
theorem delayer_extend (r K Kmax : ℕ) (hr : 128 * Kmax ^ 2 ≤ r)
    (hn : 8 * (r * Kmax) ^ 2 ≤ 2 ^ l) (hl : 2 ≤ l)
    {T : Finset ι} {Φ : List (QEq (ι × Fin l))} (hG : DGood r K T Φ) (hK : K < Kmax)
    (e : QEq (ι × Fin l)) (hz : ∃ z ∈ DX T Φ, ¬ QEq.Holds z e) :
    ∃ T', T ⊆ T' ∧ DGood r (K + 1) T' (e :: Φ) := by
  obtain ⟨hlen, hcd, hpot, x, hxI, hxF⟩ := hG
  by_cases h0 : kT T e = 0
  · obtain ⟨z, ⟨hzI, hzF⟩, hze⟩ := hz
    refine ⟨T, Finset.Subset.refl _, ?_, ?_, ?_, z, hzI, ?_⟩
    · rw [List.length_cons]; omega
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact Or.inl h0
      · exact hcd d hd
    · rw [nc_cons, if_neg (by simpa using h0), add_zero, List.length_cons, Nat.mul_succ]
      omega
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hze
      · exact hzF d hd
  · obtain ⟨T2, hsub, hcd2, hpot2⟩ := closure r (e :: Φ) T
    have hncT : nc T (e :: Φ) = nc T Φ + 1 := by rw [nc_cons, if_pos h0]
    rw [hncT, Nat.mul_succ] at hpot2
    have hpot3 : T2.card + r * nc T2 (e :: Φ) ≤ r * (e :: Φ).length := by
      rw [List.length_cons, Nat.mul_succ]; omega
    have hcard : T2.card ≤ r * Kmax := by
      have : r * (e :: Φ).length ≤ r * Kmax :=
        Nat.mul_le_mul_left _ (by rw [List.length_cons]; omega)
      omega
    set W := (Om x T).card
    have hW : 1 ≤ W := Finset.card_pos.mpr ⟨x, self_mem_Om x T⟩
    -- collisions
    set cG := ((Om x T).filter fun y => ¬ Inj T2 y).card
    have hC4 := collision_bound x T T2 hxI
    have h8 : 8 * cG ≤ W := by
      have : 8 * cG * 2 ^ l ≤ W * 2 ^ l :=
        calc 8 * cG * 2 ^ l = 8 * (cG * 2 ^ l) := by ring
          _ ≤ 8 * (T2.card ^ 2 * W) := Nat.mul_le_mul_left _ hC4
          _ ≤ 8 * ((r * Kmax) ^ 2 * W) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hcard 2))
          _ = (8 * (r * Kmax) ^ 2) * W := by ring
          _ ≤ 2 ^ l * W := Nat.mul_le_mul_right _ hn
          _ = W * 2 ^ l := by ring
      exact Nat.le_of_mul_le_mul_right this (by positivity)
    -- the new equation
    set cB := ((Om x T).filter fun y => QEq.Holds y e).card
    have hB : 2 * cB ≤ W := half_bound x T e (by omega)
    -- the dense entries
    set D := ((Om x T).filter fun y => ∃ d ∈ Φ, kT T d ≠ 0 ∧ QEq.Holds y d).card
    have hD := dense_list_bound x T Kmax r hr hl Φ hcd
    have hD' : 4 * D < W := by
      have : Kmax * (4 * D) < Kmax * W :=
        calc Kmax * (4 * D) = 4 * Kmax * D := by ring
          _ ≤ Φ.length * W := hD
          _ ≤ K * W := Nat.mul_le_mul_right _ hlen
          _ < Kmax * W := Nat.mul_lt_mul_of_pos_right hK (by omega)
      exact Nat.lt_of_mul_lt_mul_left this
    have hbad : ((Om x T).filter fun y => ¬ Inj T2 y ∨ QEq.Holds y e ∨
        ∃ d ∈ Φ, kT T d ≠ 0 ∧ QEq.Holds y d).card < W := by
      have hsub : ((Om x T).filter fun y => ¬ Inj T2 y ∨ QEq.Holds y e ∨
          ∃ d ∈ Φ, kT T d ≠ 0 ∧ QEq.Holds y d) ⊆
          ((Om x T).filter fun y => ¬ Inj T2 y) ∪ (((Om x T).filter fun y => QEq.Holds y e) ∪
            ((Om x T).filter fun y => ∃ d ∈ Φ, kT T d ≠ 0 ∧ QEq.Holds y d)) := by
        intro y hy
        rw [Finset.mem_filter] at hy
        rcases hy.2 with h | h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy.1, h⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy.1, h⟩))
        · exact Finset.mem_union_right _
            (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy.1, h⟩))
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le ((Om x T).filter fun y => ¬ Inj T2 y)
        (((Om x T).filter fun y => QEq.Holds y e) ∪
            ((Om x T).filter fun y => ∃ d ∈ Φ, kT T d ≠ 0 ∧ QEq.Holds y d))
      have h3 := Finset.card_union_le ((Om x T).filter fun y => QEq.Holds y e)
            ((Om x T).filter fun y => ∃ d ∈ Φ, kT T d ≠ 0 ∧ QEq.Holds y d)
      omega
    obtain ⟨y, hyO, hyb⟩ := exists_not_of_card_lt _ _ hbad
    push Not at hyb
    obtain ⟨hyI, hye, hyd⟩ := hyb
    refine ⟨T2, hsub, ?_, hcd2, hpot3, y, hyI, ?_⟩
    · rw [List.length_cons]; omega
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hye
      · by_cases hd0 : kT T d = 0
        · exact closed_false hxF hyO d hd hd0
        · exact hyd d hd hd0

/-- The Delayer as a predicate on coins left and sets. -/
def GoodG (r Kmax : ℕ) (c : ℕ) (S : Set (ι × Fin l → Bool)) : Prop :=
  c ≤ Kmax ∧ ∃ (T : Finset ι) (Φ : List (QEq (ι × Fin l))), DGood r (Kmax - c) T Φ ∧ S = DX T Φ

/-- The main bound: with `128 Kmax^2 ≤ r` and `8 (r Kmax)^2 ≤ 2^l`, every tree-like Res(lin)
refutation of bit pigeonhole with `m` pigeons and `l` bits has at least `2^Kmax` lines. -/
theorem tree_lower (m Kmax r : ℕ) (hK1 : 1 ≤ Kmax) (hr : 128 * Kmax ^ 2 ≤ r)
    (hn : 8 * (r * Kmax) ^ 2 ≤ 2 ^ l) (hl : 2 ≤ l)
    (t : ResLinQTree (PEqualNP.ProofComplexity.BPHP m l) []) : 2 ^ Kmax ≤ t.size := by
  refine game_refutation (GoodG (ι := Fin m) (l := l) r Kmax) ?_ ?_ t Kmax Set.univ ?_
  · rintro c S L C hc ⟨hcK, T, Φ, hG, rfl⟩ hS hC hL
    obtain ⟨i, i', α, hne, rfl⟩ := hC
    obtain ⟨y, hyX, hyQ⟩ := delayer_axiom r (Kmax - c) Kmax hK1 hr hl hG (by omega) i i' hne α
    have hyF := hS hyX
    have hh : ∀ j : Fin m, (j = i ∨ j = i') → hole y j = α := by
      intro j hj
      funext b
      have hm : litQEq ((j, b), !α b) ∈ L := by
        refine (hL _).mpr ⟨((j, b), !α b), ?_, rfl⟩
        rcases hj with rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
      have hf := hyF _ hm
      show y (j, b) = α b
      by_contra hb
      exact hf (PEqualNP.Search.Helpers.litQEq_holds y _ (by
        simp only
        cases h1 : y (j, b) <;> cases h2 : α b <;> simp_all))
    exact hyQ ⟨hh i (Or.inl rfl), hh i' (Or.inr rfl)⟩
  · rintro c S e e' hc ⟨hcK, T, Φ, hG, rfl⟩ hcov
    have hKc : Kmax - (c - 1) = Kmax - c + 1 := by omega
    by_cases h1 : ∃ z ∈ DX T Φ, ¬ QEq.Holds z e
    · by_cases h2 : ∃ z ∈ DX T Φ, ¬ QEq.Holds z e'
      · obtain ⟨T1, hT1, hG1⟩ := delayer_extend r (Kmax - c) Kmax hr hn hl hG (by omega) e h1
        obtain ⟨T2, hT2, hG2⟩ := delayer_extend r (Kmax - c) Kmax hr hn hl hG (by omega) e' h2
        right; right
        refine ⟨⟨DX T1 (e :: Φ), ?_, by omega, T1, e :: Φ, by rw [hKc]; exact hG1, rfl⟩,
          ⟨DX T2 (e' :: Φ), ?_, by omega, T2, e' :: Φ, by rw [hKc]; exact hG2, rfl⟩⟩
        · intro y hy
          exact ⟨⟨inj_mono hT1 hy.1, fun d hd => hy.2 d (List.mem_cons_of_mem _ hd)⟩,
            hy.2 e List.mem_cons_self⟩
        · intro y hy
          exact ⟨⟨inj_mono hT2 hy.1, fun d hd => hy.2 d (List.mem_cons_of_mem _ hd)⟩,
            hy.2 e' List.mem_cons_self⟩
      · left
        refine ⟨DX T Φ, fun y hy => ⟨hy, ?_⟩, hcK, T, Φ, hG, rfl⟩
        rcases hcov hy with h | h
        · exact h
        · exact absurd ⟨y, hy, h⟩ h2
    · right; left
      refine ⟨DX T Φ, fun y hy => ⟨hy, ?_⟩, hcK, T, Φ, hG, rfl⟩
      rcases hcov hy with h | h
      · exact absurd ⟨y, hy, h⟩ h1
      · exact h
  · refine ⟨le_refl _, ∅, [], ⟨by simp, by simp, by simp [nc], fun _ => false, ?_, by simp⟩, ?_⟩
    · intro i hi; simp at hi
    · ext y; simp [DX, Inj]

/-! ## Beating a polynomial -/

theorem tree_eval_le_sum_mul (p : Polynomial ℕ) {N : ℕ} (hN : 1 ≤ N) :
    p.eval N ≤ (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) * N ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right hN (by simp at hi; omega)

theorem tree_two_mul_le_two_pow {A : ℕ} (hA : 1 ≤ A) : 2 * A ≤ 2 ^ A := by
  have h := Nat.lt_two_pow_self (n := A - 1)
  have : 2 ^ A = 2 * 2 ^ (A - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

/-- For every polynomial `p` some `j` has `p (2 ^ (6 j + 17)) < 2 ^ (2 ^ j)`. -/
theorem tree_exists_eval_lt (p : Polynomial ℕ) :
    ∃ j : ℕ, p.eval (2 ^ (6 * j + 17)) < 2 ^ (2 ^ j) := by
  set d := p.natDegree
  set C := ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i
  set A := 17 * d + C + 1
  refine ⟨2 * A, ?_⟩
  have hA : 1 ≤ A := by omega
  have h2A := tree_two_mul_le_two_pow hA
  have hk : 2 ^ (2 * A) = 2 ^ A * 2 ^ A := by rw [two_mul, pow_add]
  have hsq : 2 * A * (2 * A) ≤ 2 ^ (2 * A) := by rw [hk]; exact Nat.mul_le_mul h2A h2A
  have hexp : C + (6 * (2 * A) + 17) * d < 2 ^ (2 * A) := by
    have : C + (6 * (2 * A) + 17) * d < 2 * A * (2 * A) := by
      simp only [A]
      nlinarith
    omega
  calc p.eval (2 ^ (6 * (2 * A) + 17)) ≤ C * (2 ^ (6 * (2 * A) + 17)) ^ d :=
        tree_eval_le_sum_mul p (Nat.one_le_pow _ _ (by norm_num))
    _ ≤ 2 ^ C * 2 ^ ((6 * (2 * A) + 17) * d) := by
        apply Nat.mul_le_mul (Nat.lt_two_pow_self).le
        rw [← pow_mul]
    _ = 2 ^ (C + (6 * (2 * A) + 17) * d) := by rw [pow_add]
    _ < 2 ^ (2 ^ (2 * A)) := Nat.pow_lt_pow_right (by norm_num) hexp

/-- L-lib-103 in helper form. -/
theorem tree_superpoly : ∀ p : Polynomial ℕ, ∃ l : ℕ,
    ∀ T : ResLinQTree (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) [],
      p.eval (2 ^ l) < T.size := by
  intro p
  obtain ⟨j, hj⟩ := tree_exists_eval_lt p
  refine ⟨6 * j + 17, fun T => ?_⟩
  have hn : 8 * (128 * (2 ^ j) ^ 2 * 2 ^ j) ^ 2 ≤ 2 ^ (6 * j + 17) := by
    have : 8 * (128 * (2 ^ j) ^ 2 * 2 ^ j) ^ 2 = 2 ^ (6 * j + 17) := by
      rw [show (2 : ℕ) ^ (6 * j + 17) = 2 ^ 17 * (2 ^ j) ^ 6 by
        rw [← pow_mul, ← pow_add]; congr 1; ring]
      ring
    omega
  have := tree_lower (2 ^ (6 * j + 17) + 1) (2 ^ j) (128 * (2 ^ j) ^ 2)
    (Nat.one_le_two_pow) (le_refl _) hn (by omega) T
  omega

end PEqualNP.Search.Helpers.Tree
