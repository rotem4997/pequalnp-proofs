import PEqualNP.Defs.ProofComplexityChain
import PEqualNP.ProofComplexity.Helpers.PCToolkit

/-!
# Helpers: from the bit pigeonhole system to the functional pigeonhole system

`chainA`: for `l ≥ 2`, the bit decoder turns a polynomial calculus derivation of degree `B`
from `bitPHPSystem m l` into a derivation of degree `B` from `funPHPSystem m (2 ^ l)`.

The proof replays the derivation under the decoder. The image of a Boolean axiom is handled
by the Boolean and row axioms in degree 2. The image of a pair axiom has degree `l`; its
partial product over the first `k` bits is shown, for `2 ≤ k`, to agree in degree `k` with
the sum of `X (i, j) * X (i', j')` over the pairs of holes that agree on the first `k`
bits. For `k = l` this sum consists of column axioms.
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial

section General

variable {m N : ℕ}

/-- The sum of the variables of row `i` over the holes that satisfy `P`. -/
noncomputable def rowPart (i : Fin m) (P : Fin N → Prop) [DecidablePred P] :
    MvPolynomial (Fin m × Fin N) (ZMod 2) :=
  ∑ j : Fin N, if P j then X (i, j) else 0

theorem totalDegree_add_le_of {σ : Type} {p q : MvPolynomial σ (ZMod 2)} {n : ℕ}
    (hp : p.totalDegree ≤ n) (hq : q.totalDegree ≤ n) : (p + q).totalDegree ≤ n :=
  (totalDegree_add p q).trans (max_le hp hq)

theorem totalDegree_X_mul_X_le {σ : Type} (v w : σ) :
    (X v * X w : MvPolynomial σ (ZMod 2)).totalDegree ≤ 2 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X, totalDegree_X]

theorem two_eq_zero_mvPolynomial {σ : Type} : (2 : MvPolynomial σ (ZMod 2)) = 0 := by
  have h : (2 : ZMod 2) = 0 := rfl
  have h' : (2 : MvPolynomial σ (ZMod 2)) = C (2 : ZMod 2) := (map_ofNat C 2).symm
  rw [h', h, map_zero]

theorem totalDegree_rowPart_le (i : Fin m) (P : Fin N → Prop) [DecidablePred P] :
    (rowPart i P).totalDegree ≤ 1 := by
  refine totalDegree_finsetSum_le fun j _ => ?_
  split_ifs
  · exact (totalDegree_X _).le
  · simp

/-- Multiplication of a derived line by a polynomial inside a fixed degree bound. -/
theorem pcDerivable_mul_of_le {σ : Type} {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {g : MvPolynomial σ (ZMod 2)} (hg : PCDerivable F B g) (q : MvPolynomial σ (ZMod 2))
    (h : q.totalDegree + g.totalDegree ≤ B) : PCDerivable F B (q * g) := by
  have := pcDerivable_mul_left hg q
  rwa [max_eq_left h] at this

theorem totalDegree_X_mul_rowPart_le (i i₀ : Fin m) (j : Fin N) (Q : Fin N → Prop)
    [DecidablePred Q] :
    (X (i, j) * rowPart i₀ Q + if Q j then X (i, j) else 0).totalDegree ≤ 2 := by
  refine totalDegree_add_le_of ?_ ?_
  · refine (totalDegree_mul _ _).trans ?_
    have := totalDegree_rowPart_le i₀ Q
    rw [totalDegree_X]
    omega
  · split_ifs
    · rw [totalDegree_X]; omega
    · simp

/-- A variable of row `i` times a part of row `i` is the variable or zero, in degree 2. -/
theorem fun_X_mul_rowPart (i : Fin m) (j : Fin N) (Q : Fin N → Prop) [DecidablePred Q] :
    PCDerivable (funPHPSystem m N) 2
      (X (i, j) * rowPart i Q + if Q j then X (i, j) else 0) := by
  have hk : ∀ k : Fin N,
      (if Q k then (if k = j then X (i, j) * X (i, j) + X (i, j) else X (i, j) * X (i, k))
        else 0 : MvPolynomial (Fin m × Fin N) (ZMod 2))
      = X (i, j) * (if Q k then X (i, k) else 0)
        + (if k = j then (if Q j then X (i, j) else 0) else 0) := by
    intro k
    by_cases hkj : k = j
    · subst hkj
      by_cases hq : Q k <;> simp [hq]
    · by_cases hq : Q k <;> simp [hq, hkj]
  have h : X (i, j) * rowPart i Q + (if Q j then X (i, j) else 0)
      = ∑ k : Fin N, if Q k then
          (if k = j then X (i, j) * X (i, j) + X (i, j) else X (i, j) * X (i, k))
        else 0 := by
    simp only [hk, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    rfl
  rw [h]
  refine pcDerivable_sum _ _ fun k _ => ?_
  by_cases hq : Q k
  · rw [if_pos hq]
    by_cases hkj : k = j
    · rw [if_pos hkj]
      refine .ax (Or.inl ⟨(i, j), rfl⟩) (totalDegree_add_le_of (totalDegree_X_mul_X_le _ _) ?_)
      rw [totalDegree_X]; omega
    · rw [if_neg hkj]
      exact .ax (Or.inr (Or.inl ⟨i, j, k, Ne.symm hkj, rfl⟩)) (totalDegree_X_mul_X_le _ _)
  · rw [if_neg hq]
    exact .zero

/-- The product of two parts of the same row is the part of the intersection, in degree 2. -/
theorem fun_rowPart_mul (i : Fin m) (P Q : Fin N → Prop) [DecidablePred P] [DecidablePred Q] :
    PCDerivable (funPHPSystem m N) 2
      (rowPart i P * rowPart i Q + rowPart i (fun j => P j ∧ Q j)) := by
  have h : rowPart i P * rowPart i Q + rowPart i (fun j => P j ∧ Q j)
      = ∑ j : Fin N, if P j then (X (i, j) * rowPart i Q + if Q j then X (i, j) else 0)
          else 0 := by
    unfold rowPart
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hp : P j <;> by_cases hq : Q j <;> simp [hp, hq]
  rw [h]
  refine pcDerivable_sum _ _ fun j _ => ?_
  by_cases hp : P j
  · rw [if_pos hp]
    exact fun_X_mul_rowPart i j Q
  · rw [if_neg hp]
    exact .zero

theorem fun_rowPart_sq (i : Fin m) (P : Fin N → Prop) [DecidablePred P] :
    PCDerivable (funPHPSystem m N) 2 (rowPart i P * rowPart i P + rowPart i P) := by
  have h := fun_rowPart_mul i P P
  have e : rowPart i (fun j => P j ∧ P j) = rowPart i P := by
    unfold rowPart
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hp : P j <;> simp [hp]
  rwa [e] at h

theorem fun_rowPart_disj (i : Fin m) (P Q : Fin N → Prop) [DecidablePred P] [DecidablePred Q]
    (hd : ∀ j, ¬ (P j ∧ Q j)) :
    PCDerivable (funPHPSystem m N) 2 (rowPart i P * rowPart i Q) := by
  have h := fun_rowPart_mul i P Q
  have e : rowPart i (fun j => P j ∧ Q j) = 0 := by
    unfold rowPart
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (hd j)]
  rwa [e, add_zero] at h

/-- The holes whose bit `t` is set. -/
def bitP (t : ℕ) (j : Fin N) : Prop := j.val.testBit t = true

instance (t : ℕ) : DecidablePred (bitP (N := N) t) := fun j =>
  inferInstanceAs (Decidable (j.val.testBit t = true))

/-- The holes whose bits `0` and `1` are `β0` and `β1`. -/
def cls (β0 β1 : Bool) (j : Fin N) : Prop := j.val.testBit 0 = β0 ∧ j.val.testBit 1 = β1

instance (β0 β1 : Bool) : DecidablePred (cls (N := N) β0 β1) := fun j =>
  inferInstanceAs (Decidable (j.val.testBit 0 = β0 ∧ j.val.testBit 1 = β1))

/-- Two holes agree on the first `k` bits. -/
def agree (k : ℕ) (j j' : Fin N) : Prop := ∀ t < k, j.val.testBit t = j'.val.testBit t

instance (k : ℕ) (j j' : Fin N) : Decidable (agree k j j') :=
  inferInstanceAs (Decidable (∀ t < k, j.val.testBit t = j'.val.testBit t))

theorem agree_succ (k : ℕ) (j j' : Fin N) :
    agree (k + 1) j j' ↔ agree k j j' ∧ j.val.testBit k = j'.val.testBit k :=
  Nat.forall_lt_succ_right

theorem agree_two (j j' : Fin N) :
    agree 2 j j' ↔ j.val.testBit 0 = j'.val.testBit 0 ∧ j.val.testBit 1 = j'.val.testBit 1 := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega)⟩
  · rintro ⟨h0, h1⟩ t ht
    interval_cases t <;> assumption

/-- The factor of bit `t` of the decoded pair axiom. -/
noncomputable def pairF (i i' : Fin m) (t : ℕ) : MvPolynomial (Fin m × Fin N) (ZMod 2) :=
  1 + rowPart i (bitP t) + rowPart i' (bitP t)

/-- The sum of `X (i, j) * X (i', j')` over the holes that agree on the first `k` bits. -/
noncomputable def pairS (i i' : Fin m) (k : ℕ) : MvPolynomial (Fin m × Fin N) (ZMod 2) :=
  ∑ j : Fin N, ∑ j' : Fin N, if agree k j j' then X (i, j) * X (i', j') else 0

theorem totalDegree_pairF_le (i i' : Fin m) (t : ℕ) :
    (pairF (N := N) i i' t).totalDegree ≤ 1 := by
  refine totalDegree_add_le_of (totalDegree_add_le_of ?_ (totalDegree_rowPart_le _ _))
    (totalDegree_rowPart_le _ _)
  simp

theorem totalDegree_pairS_le (i i' : Fin m) (k : ℕ) :
    (pairS (N := N) i i' k).totalDegree ≤ 2 := by
  refine totalDegree_finsetSum_le fun j _ => totalDegree_finsetSum_le fun j' _ => ?_
  split_ifs
  · exact totalDegree_X_mul_X_le _ _
  · simp

/-- One more bit: in degree 3. -/
theorem fun_pair_step (i i' : Fin m) (k : ℕ) :
    PCDerivable (funPHPSystem m N) 3
      (pairS i i' k * pairF i i' k + pairS i i' (k + 1)) := by
  rw [pairS, pairS, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine pcDerivable_sum _ _ fun j _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine pcDerivable_sum _ _ fun j' _ => ?_
  by_cases ha : agree k j j'
  · have h2 := two_eq_zero_mvPolynomial (σ := Fin m × Fin N)
    have e : (if agree k j j' then X (i, j) * X (i', j') else 0) * pairF i i' k
        + (if agree (k + 1) j j' then X (i, j) * X (i', j') else 0)
        = X (i', j') * (X (i, j) * rowPart i (bitP k) + if bitP k j then X (i, j) else 0)
          + X (i, j) * (X (i', j') * rowPart i' (bitP k)
            + if bitP k j' then X (i', j') else 0) := by
      rw [if_pos ha]
      cases hb : j.val.testBit k <;> cases hb' : j'.val.testBit k <;>
        simp only [agree_succ, ha, hb, hb', bitP, pairF, true_and, ite_true, ite_false,
          Bool.false_eq_true, reduceCtorEq] <;>
        first
          | ring1
          | linear_combination (X (i, j) * X (i', j')) * h2
    rw [e]
    refine .add ?_ ?_
    · refine pcDerivable_mul_of_le
        (pcDerivable_mono (fun_X_mul_rowPart i j (bitP k)) (by omega) subset_rfl) _ ?_
      have := totalDegree_X_mul_rowPart_le i i j (bitP k)
      rw [totalDegree_X]; omega
    · refine pcDerivable_mul_of_le
        (pcDerivable_mono (fun_X_mul_rowPart i' j' (bitP k)) (by omega) subset_rfl) _ ?_
      have := totalDegree_X_mul_rowPart_le i' i' j' (bitP k)
      rw [totalDegree_X]; omega
  · have ha' : ¬ agree (k + 1) j j' := fun h => ha ((agree_succ k j j').mp h).1
    rw [if_neg ha, if_neg ha', zero_mul, add_zero]
    exact .zero

theorem rowPart_bit0 (i : Fin m) :
    rowPart (N := N) i (bitP 0) = rowPart i (cls true false) + rowPart i (cls true true) := by
  unfold rowPart
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases h0 : j.val.testBit 0 <;> cases h1 : j.val.testBit 1 <;> simp [bitP, cls, h0, h1]

theorem rowPart_bit1 (i : Fin m) :
    rowPart (N := N) i (bitP 1) = rowPart i (cls false true) + rowPart i (cls true true) := by
  unfold rowPart
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases h0 : j.val.testBit 0 <;> cases h1 : j.val.testBit 1 <;> simp [bitP, cls, h0, h1]

theorem rowSum_cls (i : Fin m) :
    (∑ j : Fin N, (X (i, j) : MvPolynomial (Fin m × Fin N) (ZMod 2)))
      = rowPart i (cls false false) + rowPart i (cls false true)
        + rowPart i (cls true false) + rowPart i (cls true true) := by
  unfold rowPart
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases h0 : j.val.testBit 0 <;> cases h1 : j.val.testBit 1 <;> simp [cls, h0, h1]

theorem pairS_two (i i' : Fin m) :
    pairS (N := N) i i' 2
      = rowPart i (cls false false) * rowPart i' (cls false false)
        + rowPart i (cls false true) * rowPart i' (cls false true)
        + rowPart i (cls true false) * rowPart i' (cls true false)
        + rowPart i (cls true true) * rowPart i' (cls true true) := by
  unfold rowPart pairS
  simp only [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  cases h0 : j.val.testBit 0 <;> cases h1 : j.val.testBit 1 <;>
    cases h0' : j'.val.testBit 0 <;> cases h1' : j'.val.testBit 1 <;>
    simp [agree_two, cls, h0, h1, h0', h1']

theorem char2_pair_identity {K : Type} [CommRing K] (h2 : (2 : K) = 0)
    (a b c d a' b' c' d' : K) :
    (1 + (c + d) + (c' + d')) * (1 + (b + d) + (b' + d'))
        + (a * a' + b * b' + c * c' + d * d')
      = (c * b + c * d + d * b + (d * d + d))
        + (c' * b' + c' * d' + d' * b' + (d' * d' + d'))
        + (1 + a' + (a' + b' + c' + d')) * (a + b + c + d + 1)
        + a * (a' + b' + c' + d' + 1) := by
  linear_combination
    (d * d' - a - a' - a * a' - a' * b - a' * c - a' * d - a * b' - a * c' - a * d') * h2

theorem fun_cls_block (i : Fin m) :
    PCDerivable (funPHPSystem m N) 2
      (rowPart i (cls true false) * rowPart i (cls false true)
        + rowPart i (cls true false) * rowPart i (cls true true)
        + rowPart i (cls true true) * rowPart i (cls false true)
        + (rowPart i (cls true true) * rowPart i (cls true true)
          + rowPart i (cls true true))) := by
  refine .add (.add (.add ?_ ?_) ?_) (fun_rowPart_sq i _)
  · refine fun_rowPart_disj i _ _ fun j h => ?_
    simp only [cls] at h
    have := h.1.1.symm.trans h.2.1
    simp at this
  · refine fun_rowPart_disj i _ _ fun j h => ?_
    simp only [cls] at h
    have := h.1.2.symm.trans h.2.2
    simp at this
  · refine fun_rowPart_disj i _ _ fun j h => ?_
    simp only [cls] at h
    have := h.1.1.symm.trans h.2.1
    simp at this

theorem fun_rowAxiom (i : Fin m) :
    PCDerivable (funPHPSystem m N) 2
      (rowPart i (cls false false) + rowPart i (cls false true)
        + rowPart i (cls true false) + rowPart i (cls true true) + 1) ∧
    (rowPart (N := N) i (cls false false) + rowPart i (cls false true)
        + rowPart i (cls true false) + rowPart i (cls true true) + 1).totalDegree ≤ 1 := by
  have hdeg : (rowPart (N := N) i (cls false false) + rowPart i (cls false true)
        + rowPart i (cls true false) + rowPart i (cls true true) + 1).totalDegree ≤ 1 := by
    refine totalDegree_add_le_of (totalDegree_add_le_of (totalDegree_add_le_of
      (totalDegree_add_le_of ?_ ?_) ?_) ?_) (by simp) <;>
      exact totalDegree_rowPart_le _ _
  refine ⟨?_, hdeg⟩
  rw [← rowSum_cls]
  refine .ax (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))) ?_
  rw [rowSum_cls]
  omega

/-- The first two bits: in degree 2. -/
theorem fun_pair_base (i i' : Fin m) :
    PCDerivable (funPHPSystem m N) 2 (pairF i i' 0 * pairF i i' 1 + pairS i i' 2) := by
  have h2 := two_eq_zero_mvPolynomial (σ := Fin m × Fin N)
  have e : pairF (N := N) i i' 0 * pairF i i' 1 + pairS i i' 2
      = (rowPart (N := N) i (cls true false) * rowPart (N := N) i (cls false true)
          + rowPart (N := N) i (cls true false) * rowPart (N := N) i (cls true true)
          + rowPart (N := N) i (cls true true) * rowPart (N := N) i (cls false true)
          + (rowPart (N := N) i (cls true true) * rowPart (N := N) i (cls true true)
            + rowPart (N := N) i (cls true true)))
        + (rowPart (N := N) i' (cls true false) * rowPart (N := N) i' (cls false true)
          + rowPart (N := N) i' (cls true false) * rowPart (N := N) i' (cls true true)
          + rowPart (N := N) i' (cls true true) * rowPart (N := N) i' (cls false true)
          + (rowPart (N := N) i' (cls true true) * rowPart (N := N) i' (cls true true)
            + rowPart (N := N) i' (cls true true)))
        + (1 + rowPart (N := N) i' (cls false false)
            + (rowPart (N := N) i' (cls false false) + rowPart (N := N) i' (cls false true)
              + rowPart (N := N) i' (cls true false) + rowPart (N := N) i' (cls true true)))
          * (rowPart (N := N) i (cls false false) + rowPart (N := N) i (cls false true)
            + rowPart (N := N) i (cls true false) + rowPart (N := N) i (cls true true) + 1)
        + rowPart (N := N) i (cls false false)
          * (rowPart (N := N) i' (cls false false) + rowPart (N := N) i' (cls false true)
            + rowPart (N := N) i' (cls true false) + rowPart (N := N) i' (cls true true) + 1) := by
    rw [pairF, pairF, rowPart_bit0, rowPart_bit0, rowPart_bit1, rowPart_bit1, pairS_two]
    linear_combination char2_pair_identity h2
      (rowPart (N := N) i (cls false false)) (rowPart (N := N) i (cls false true))
      (rowPart (N := N) i (cls true false)) (rowPart (N := N) i (cls true true))
      (rowPart (N := N) i' (cls false false)) (rowPart (N := N) i' (cls false true))
      (rowPart (N := N) i' (cls true false)) (rowPart (N := N) i' (cls true true))
  rw [e]
  obtain ⟨hR, hRd⟩ := fun_rowAxiom (N := N) i
  obtain ⟨hR', hRd'⟩ := fun_rowAxiom (N := N) i'
  refine .add (.add (.add (fun_cls_block i) (fun_cls_block i')) ?_) ?_
  · refine pcDerivable_mul_of_le hR _ ?_
    have : (1 + rowPart (N := N) i' (cls false false)
        + (rowPart i' (cls false false) + rowPart i' (cls false true)
          + rowPart i' (cls true false) + rowPart i' (cls true true))).totalDegree ≤ 1 := by
      refine totalDegree_add_le_of (totalDegree_add_le_of (by simp) ?_)
        (totalDegree_add_le_of (totalDegree_add_le_of (totalDegree_add_le_of ?_ ?_) ?_) ?_) <;>
        exact totalDegree_rowPart_le _ _
    omega
  · refine pcDerivable_mul_of_le hR' _ ?_
    have := totalDegree_rowPart_le (N := N) i (cls false false)
    omega

/-- The partial product over the first `k ≥ 2` bits, in degree `k`. -/
theorem fun_pair_partial (i i' : Fin m) (k : ℕ) (hk : 2 ≤ k) :
    PCDerivable (funPHPSystem m N) k
      (∏ t ∈ Finset.range k, pairF i i' t + pairS i i' k) := by
  have h2 := two_eq_zero_mvPolynomial (σ := Fin m × Fin N)
  induction k, hk using Nat.le_induction with
  | base =>
    have e : ∏ t ∈ Finset.range 2, pairF (N := N) i i' t = pairF i i' 0 * pairF i i' 1 := by
      simp [Finset.prod_range_succ]
    rw [e]
    exact fun_pair_base i i'
  | succ k hk ih =>
    have e : ∏ t ∈ Finset.range (k + 1), pairF (N := N) i i' t + pairS i i' (k + 1)
        = pairF i i' k * (∏ t ∈ Finset.range k, pairF i i' t + pairS i i' k)
          + (pairS i i' k * pairF i i' k + pairS i i' (k + 1)) := by
      rw [Finset.prod_range_succ]
      linear_combination (-(pairS i i' k * pairF i i' k)) * h2
    rw [e]
    refine .add ?_ (pcDerivable_mono (fun_pair_step i i' k) (by omega) subset_rfl)
    refine pcDerivable_mul_of_le (pcDerivable_mono ih (by omega) subset_rfl) _ ?_
    have h1 := totalDegree_pairF_le (N := N) i i' k
    have h3 : (∏ t ∈ Finset.range k, pairF (N := N) i i' t + pairS i i' k).totalDegree ≤ k := by
      refine totalDegree_add_le_of ?_ ((totalDegree_pairS_le i i' k).trans hk)
      refine (totalDegree_finsetProd _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ 1 fun t _ => totalDegree_pairF_le i i' t).trans ?_
      simp
    omega

end General

/-- The decoded pair axiom is derivable in degree `l` from the functional system. -/
theorem fun_pair_full (m l : ℕ) (hl : 2 ≤ l) (i i' : Fin m) (hne : i ≠ i') :
    PCDerivable (funPHPSystem m (2 ^ l)) l (∏ t ∈ Finset.range l, pairF (N := 2 ^ l) i i' t) := by
  have h2 := two_eq_zero_mvPolynomial (σ := Fin m × Fin (2 ^ l))
  have hS : PCDerivable (funPHPSystem m (2 ^ l)) l (pairS (N := 2 ^ l) i i' l) := by
    refine pcDerivable_sum _ _ fun j _ => pcDerivable_sum _ _ fun j' _ => ?_
    by_cases ha : agree l j j'
    · rw [if_pos ha]
      have hjj : j = j' := by
        apply Fin.ext
        apply Nat.eq_of_testBit_eq
        intro t
        by_cases ht : t < l
        · exact ha t ht
        · have hp : 2 ^ l ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) (by omega)
          rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le j.isLt hp),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le j'.isLt hp)]
      subst hjj
      exact .ax (Or.inr (Or.inr (Or.inl ⟨i, i', j, hne, rfl⟩)))
        ((totalDegree_X_mul_X_le _ _).trans hl)
    · rw [if_neg ha]
      exact .zero
  have e : ∏ t ∈ Finset.range l, pairF (N := 2 ^ l) i i' t
      = (∏ t ∈ Finset.range l, pairF (N := 2 ^ l) i i' t + pairS i i' l) + pairS i i' l := by
    linear_combination (-(pairS (N := 2 ^ l) i i' l)) * h2
  rw [e]
  exact .add (fun_pair_partial i i' l hl) hS

theorem totalDegree_prod_eq_sum {σ ι : Type} (s : Finset ι)
    (g : ι → MvPolynomial σ (ZMod 2)) (h : ∀ t ∈ s, g t ≠ 0) :
    (∏ t ∈ s, g t).totalDegree = ∑ t ∈ s, (g t).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ t ∈ s, g t ≠ 0 := fun t ht => h t (Finset.mem_insert_of_mem ht)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      totalDegree_mul_of_isDomain (h a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr hs), ih hs]

theorem one_le_totalDegree_pairFactor {σ : Type} [DecidableEq σ] (a b : σ) (hab : a ≠ b) :
    1 ≤ (1 + X a + X b : MvPolynomial σ (ZMod 2)).totalDegree := by
  have hmem : Finsupp.single a 1 ∈ (1 + X a + X b : MvPolynomial σ (ZMod 2)).support := by
    rw [mem_support_iff]
    have h1 : (Finsupp.single b 1 : σ →₀ ℕ) ≠ Finsupp.single a 1 := by
      intro h
      have := Finsupp.single_left_injective (by norm_num : (1 : ℕ) ≠ 0) h
      exact hab this.symm
    have h0 : (0 : σ →₀ ℕ) ≠ Finsupp.single a 1 := by
      intro h
      have := congrArg (fun f => f a) h
      simp at this
    simp [coeff_X, coeff_one, h1, h0]
  have := le_totalDegree hmem
  rwa [Finsupp.sum_single_index rfl] at this

/-- The pair axiom of the bit system has total degree at least `l`. -/
theorem le_totalDegree_bitPair (m l : ℕ) (i i' : Fin m) (hne : i ≠ i') :
    l ≤ (∏ t : Fin l, (1 + X (i, t) + X (i', t) :
      MvPolynomial (Fin m × Fin l) (ZMod 2))).totalDegree := by
  have hf : ∀ t : Fin l, 1 ≤ (1 + X (i, t) + X (i', t) :
      MvPolynomial (Fin m × Fin l) (ZMod 2)).totalDegree := fun t =>
    one_le_totalDegree_pairFactor _ _ (fun h => hne (congrArg Prod.fst h))
  rw [totalDegree_prod_eq_sum]
  · have := Finset.card_nsmul_le_sum Finset.univ
      (fun t : Fin l => (1 + X (i, t) + X (i', t) :
        MvPolynomial (Fin m × Fin l) (ZMod 2)).totalDegree) 1 (fun t _ => hf t)
    simpa using this
  · intro t _ h0
    have := hf t
    rw [h0, totalDegree_zero] at this
    omega

theorem chainA : ∀ (m l B : ℕ) (q : MvPolynomial (Fin m × Fin l) (ZMod 2)), 2 ≤ l → PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.bitPHPSystem m l) B q → PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.funPHPSystem m (2 ^ l)) B (PEqualNP.ProofComplexity.bitDecoder m l q) := by
  intro m l B q hl h
  let φ : Fin m × Fin l → MvPolynomial (Fin m × Fin (2 ^ l)) (ZMod 2) := fun v =>
    ∑ j : Fin (2 ^ l), if j.val.testBit v.2.val = true then X (v.1, j) else 0
  have hφr : ∀ v, φ v = rowPart (N := 2 ^ l) v.1 (bitP v.2.val) := fun v => rfl
  have hφ : ∀ v, (φ v).totalDegree ≤ 1 := fun v => by
    rw [hφr]; exact totalDegree_rowPart_le _ _
  have key : ∀ a ∈ bitPHPSystem m l, a.totalDegree ≤ B →
      PCDerivable (funPHPSystem m (2 ^ l)) (1 * B + 0) (1 * bind₁ φ a) := by
    intro a ha hdeg
    rw [one_mul, one_mul, add_zero]
    rcases ha with ⟨v, rfl⟩ | ⟨i, i', hne, rfl⟩
    · have hB : 2 ≤ B := by
        have h1 : (X v * X v : MvPolynomial (Fin m × Fin l) (ZMod 2)).totalDegree = 2 := by
          rw [totalDegree_mul_of_isDomain (X_ne_zero v) (X_ne_zero v), totalDegree_X]
        have h3 : (X v * X v + X v : MvPolynomial (Fin m × Fin l) (ZMod 2)).totalDegree = 2 := by
          rw [totalDegree_add_eq_left_of_totalDegree_lt, h1]
          rw [h1, totalDegree_X]; omega
        omega
      have e : bind₁ φ (X v * X v + X v)
          = rowPart (N := 2 ^ l) v.1 (bitP v.2.val) * rowPart v.1 (bitP v.2.val)
            + rowPart v.1 (bitP v.2.val) := by
        simp only [map_add, map_mul, bind₁_X_right, hφr]
      rw [e]
      exact pcDerivable_mono (fun_rowPart_sq _ _) hB subset_rfl
    · have hB : l ≤ B := (le_totalDegree_bitPair m l i i' hne).trans hdeg
      have e : bind₁ φ (∏ t : Fin l, (1 + X (i, t) + X (i', t)))
          = ∏ t ∈ Finset.range l, pairF (N := 2 ^ l) i i' t := by
        rw [← Fin.prod_univ_eq_prod_range (fun t => pairF (N := 2 ^ l) i i' t) l, map_prod]
        refine Finset.prod_congr rfl fun t _ => ?_
        simp only [map_add, map_one, bind₁_X_right, hφr, pairF]
      rw [e]
      exact pcDerivable_mono (fun_pair_full m l hl i i' hne) hB subset_rfl
  have := pcDerivable_replay φ hφ 1 (by simp) key h
  rw [one_mul, one_mul, add_zero] at this
  exact this

end PEqualNP.ProofComplexity.Helpers
