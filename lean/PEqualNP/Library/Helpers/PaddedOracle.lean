import PEqualNP.Library.L066
import PEqualNP.Library.Machines.Clock
import PEqualNP.Library.Helpers.OutputLength
import Mathlib.Data.Finsupp.Encodable

/-!
# Padded oracles

Helper module (proofs only, no statement may use it).

Ingredients for the padded-oracle proof of Baker, Gill and Solovay's Theorem 1 (an oracle `A`
with `P^A = NP^A`):

* `exists_fix`: a set of strings defined by recursion on length, where membership of `s` may
  depend on the members shorter than `s`.
* `pad a k x`: `a` ones, a zero, `(|x| + 2)^k` ones, then `x`; it is injective in `a` and,
  for fixed `a` and `k`, in `x`, and computable in polynomial time for fixed `a` and `k`.
* `exists_pad_exp`: the padding exponent can be made to dominate any polynomial.
* `exists_surj_poly`: a surjection from `ℕ` onto `Polynomial ℕ`.
-/

namespace PEqualNP.Library.Helpers.PaddedOracle

open PEqualNP.Library

/-- The members of length below `m` of the set defined by `ψ`. -/
def T (ψ : List Bool → Language Bool → Prop) (m : ℕ) : Language Bool :=
  {y | ∃ _ : y.length < m, ψ y (T ψ y.length)}
termination_by m
decreasing_by assumption

theorem mem_T (ψ : List Bool → Language Bool → Prop) (m : ℕ) (y : List Bool) :
    y ∈ T ψ m ↔ y.length < m ∧ ψ y (T ψ y.length) := by
  rw [T]
  exact ⟨fun ⟨h, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩

/-- A set defined by recursion on length. -/
theorem exists_fix (ψ : List Bool → Language Bool → Prop) :
    ∃ A : Language Bool, ∀ s : List Bool,
      s ∈ A ↔ ψ s {y | y ∈ A ∧ y.length < s.length} := by
  let A : Language Bool := {y | y ∈ T ψ (y.length + 1)}
  have hA : ∀ y, y ∈ A ↔ ψ y (T ψ y.length) := fun y => by
    show y ∈ T ψ (y.length + 1) ↔ _
    rw [mem_T]
    exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_self _, h⟩⟩
  have hT : ∀ m, T ψ m = {y | y ∈ A ∧ y.length < m} := fun m => by
    ext y
    rw [mem_T]
    show _ ↔ y ∈ A ∧ _
    rw [hA]
    exact And.comm
  refine ⟨A, fun s => ?_⟩
  rw [hA, hT]

/-- The padded string. -/
noncomputable def pad (a k : ℕ) (x : List Bool) : List Bool :=
  (List.replicate a true ++ [false]) ++
    (List.replicate (((Polynomial.X + 2) ^ k : Polynomial ℕ).eval x.length) true ++ x)

theorem eval_padPoly (k n : ℕ) :
    ((Polynomial.X + 2) ^ k : Polynomial ℕ).eval n = (n + 2) ^ k := by
  simp

theorem pad_length (a k : ℕ) (x : List Bool) :
    (pad a k x).length = a + 1 + ((x.length + 2) ^ k + x.length) := by
  simp [pad]
  omega

private theorem rep_false (a b : ℕ) (u v : List Bool)
    (h : List.replicate a true ++ false :: u = List.replicate b true ++ false :: v) :
    a = b ∧ u = v := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa using h
    | succ b => simp [List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [List.replicate_succ] at h
    | succ b =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      have := ih b h
      exact ⟨by omega, this.2⟩

theorem pad_prefix {a k a' k' : ℕ} {x x' : List Bool} (h : pad a k x = pad a' k' x') :
    a = a' := by
  unfold pad at h
  simp only [List.append_assoc, List.singleton_append] at h
  exact (rep_false a a' _ _ h).1

theorem pad_inj {a k : ℕ} {x x' : List Bool} (h : pad a k x = pad a k x') : x = x' := by
  unfold pad at h
  simp only [List.append_assoc, List.singleton_append] at h
  have h2 := (rep_false a a _ _ h).2
  rw [eval_padPoly, eval_padPoly] at h2
  have hl := congrArg List.length h2
  simp only [List.length_append, List.length_replicate] at hl
  have hn : x.length = x'.length := by
    rcases lt_trichotomy x.length x'.length with hlt | heq | hgt
    · have : (x.length + 2) ^ k ≤ (x'.length + 2) ^ k := Nat.pow_le_pow_left (by omega) k
      omega
    · exact heq
    · have : (x'.length + 2) ^ k ≤ (x.length + 2) ^ k := Nat.pow_le_pow_left (by omega) k
      omega
  rw [hn] at h2
  exact List.append_cancel_left h2

theorem pad_cpt (a k : ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (pad a k) := by
  have h1 := Machines.clock_polyTime L066 ((Polynomial.X + 2) ^ k)
  have h2 := Machines.cpt_comp (Machines.cpt_pair h1 Machines.cpt_id) Machines.cpt_append
  have h3 := Machines.cpt_comp
    (Machines.cpt_pair (L066 (List.replicate a true ++ [false])) h2) Machines.cpt_append
  exact h3

theorem eval_mono (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add hp hq
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

theorem exists_pad_exp (r p : Polynomial ℕ) :
    ∃ k : ℕ, ∀ n m : ℕ, m ≤ p.eval n → r.eval (n + m) < (n + 2) ^ k := by
  obtain ⟨a, d, hs⟩ := poly_le_monomial (r.comp (Polynomial.X + p))
  refine ⟨d + a, fun n m hm => ?_⟩
  have h1 : a < 2 ^ a := Nat.lt_two_pow_self
  have h2 : 2 ^ a ≤ (n + 2) ^ a := Nat.pow_le_pow_left (by omega) a
  have h3 : 0 < (n + 2) ^ d := by positivity
  calc r.eval (n + m) ≤ r.eval (n + p.eval n) := eval_mono r (by omega)
    _ = (r.comp (Polynomial.X + p)).eval n := by simp [Polynomial.eval_comp]
    _ ≤ (r.comp (Polynomial.X + p)).eval (n + 2) := eval_mono _ (by omega)
    _ ≤ a * (n + 2) ^ d := hs _ (by omega)
    _ < (n + 2) ^ (d + a) := by
      rw [pow_add, Nat.mul_comm a]
      exact Nat.mul_lt_mul_of_pos_left (by omega) h3

theorem exists_surj_poly : ∃ e : ℕ → Polynomial ℕ, Function.Surjective e := by
  have : Countable (Polynomial ℕ) :=
    Function.Injective.countable (AddMonoidAlgebra.coeff_injective (R := ℕ) (M := ℕ))
  exact exists_surjective_nat _

end PEqualNP.Library.Helpers.PaddedOracle
