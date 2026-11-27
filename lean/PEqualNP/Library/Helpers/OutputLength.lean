import PEqualNP.Library.Machines.Run
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The output of a polynomial-time function is polynomially long

Helper module (proofs only, no statement may use it). A stack grows by a bounded number of
symbols per step, so the output of a polynomial-time function on strings is at most a monomial
in the input length. Applied to the binary encoding of CNF formulas: a formula naming the
variable `2 ^ n` has a short code, so no polynomial-time function can output an assignment as
a list indexed by variable number.
-/

namespace PEqualNP.Library.Helpers
open Turing PEqualNP.Library PEqualNP.Library.Machines

/-- A polynomial with natural coefficients is below a monomial from 1 on. -/
theorem poly_le_monomial (p : Polynomial ℕ) : ∃ a d : ℕ, ∀ m : ℕ, 1 ≤ m → p.eval m ≤ a * m ^ d := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, d, h⟩ := hp
    obtain ⟨b, e, h'⟩ := hq
    refine ⟨a + b, d + e, fun m hm => ?_⟩
    rw [Polynomial.eval_add, Nat.add_mul]
    have h1 : m ^ d ≤ m ^ (d + e) := Nat.pow_le_pow_right hm (by omega)
    have h2 : m ^ e ≤ m ^ (d + e) := Nat.pow_le_pow_right hm (by omega)
    exact add_le_add ((h m hm).trans (Nat.mul_le_mul_left _ h1))
      ((h' m hm).trans (Nat.mul_le_mul_left _ h2))
  | monomial d c => exact ⟨c, d, fun m _ => by rw [Polynomial.eval_monomial]⟩

/-- An exponential beats a monomial somewhere above any threshold. -/
theorem exists_pow_lt (A D N : ℕ) : ∃ n : ℕ, N ≤ n ∧ A * n ^ D < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt D (show (1 : ℝ) < 2 by norm_num)
  have hpos : (0 : ℝ) < 1 / (A + 1) := by positivity
  have ev := (h.eventually (gt_mem_nhds hpos)).and (Filter.eventually_ge_atTop N)
  obtain ⟨n, hn, hN⟩ := ev.exists
  refine ⟨n, hN, ?_⟩
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity)] at hn
  have : ((A * n ^ D : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by
    push_cast
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ D := by positivity
    nlinarith
  exact_mod_cast this

/-- The output of a polynomial-time function on strings is at most a monomial in the input
length (for nonempty inputs). -/
theorem output_length_le (f : List Bool → List Bool)
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ∃ a d : ℕ, ∀ x : List Bool, 1 ≤ x.length → (f x).length ≤ a * x.length ^ d := by
  obtain ⟨c⟩ := hf
  obtain ⟨a, d, had⟩ := poly_le_monomial c.time
  refine ⟨1 + maxPush c.tm * a, d + 1, fun x hx => ?_⟩
  obtain ⟨⟨steps, hev⟩, hle⟩ := c.outputsFun x
  have hev' : (flip bind (TM2.step c.tm.m))^[steps]
      (some (⟨some c.tm.main, c.tm.initialState, Function.update (fun _ => []) c.tm.k₀
        (List.map c.inputAlphabet.invFun x)⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ)) =
      some (⟨none, c.tm.initialState, Function.update (fun _ => []) c.tm.k₁
        (List.map c.outputAlphabet.invFun (f x))⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ) := by
    rw [← initList_eq, ← haltList_eq]; exact hev
  have key := run_length c.tm c.tm.k₁ steps _ _ hev'
  simp only [Function.update_self, List.length_map] at key
  have hin : ((Function.update (fun _ => ([] : List _)) c.tm.k₀
      (List.map c.inputAlphabet.invFun x) : ∀ k, List (c.tm.Γ k)) c.tm.k₁).length ≤ x.length := by
    by_cases hk : c.tm.k₁ = c.tm.k₀
    · rw [hk]; simp
    · rw [Function.update_of_ne hk]; simp
  have hsteps : steps ≤ a * x.length ^ d := hle.trans (had _ hx)
  have h1 : x.length ≤ x.length ^ (d + 1) := by
    calc x.length = x.length ^ 1 := (pow_one _).symm
      _ ≤ x.length ^ (d + 1) := Nat.pow_le_pow_right hx (by omega)
  have h2 : x.length ^ d ≤ x.length ^ (d + 1) := Nat.pow_le_pow_right hx (by omega)
  calc (f x).length ≤ x.length + maxPush c.tm * steps := key.trans (by omega)
    _ ≤ x.length ^ (d + 1) + maxPush c.tm * (a * x.length ^ (d + 1)) :=
      add_le_add h1 (Nat.mul_le_mul_left _ (hsteps.trans (Nat.mul_le_mul_left _ h2)))
    _ = (1 + maxPush c.tm * a) * x.length ^ (d + 1) := by ring

open PEqualNP.Search in
theorem code_length (n : ℕ) : (encodeCNF [[(2 ^ n, true)]]).length = 2 * n + 8 := by
  have hb : ∀ bs : List Bool, (bs.flatMap fun d => [true, d]).length = 2 * bs.length := by
    intro bs; induction bs with
    | nil => rfl
    | cons b bs ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.length_nil]; omega
  have hs : (2 ^ n).bits.length = n + 1 := by
    rw [Nat.size_eq_bits_len, Nat.size_pow]
  simp [encodeCNF, encodeClause, encodeLiteral, hb, hs]
  omega

open PEqualNP.Search in
/-- No polynomial-time function outputs satisfying assignments indexed by variable number. -/
theorem no_indexed_assignment : ¬ ∃ f : List Bool → List Bool,
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f ∧
      ∀ φ : CNF, Satisfiable φ →
        CNF.eval (fun i : ℕ => (f (encodeCNF φ)).getD i false) φ = true := by
  rintro ⟨f, hf, h⟩
  obtain ⟨a, d, hlen⟩ := output_length_le f hf
  obtain ⟨n, hn8, hn⟩ := exists_pow_lt (a * 3 ^ d) d 8
  have hsat : Satisfiable [[(2 ^ n, true)]] :=
    ⟨fun _ => true, by simp [CNF.eval, Clause.eval, Literal.eval]⟩
  have hv := h _ hsat
  simp only [CNF.eval, Clause.eval, Literal.eval, List.all_cons, List.all_nil, List.any_cons,
    List.any_nil, Bool.or_false, Bool.and_true, beq_iff_eq] at hv
  have hlt : 2 ^ n < (f (encodeCNF [[(2 ^ n, true)]])).length := by
    by_contra hge
    rw [List.getD_eq_default _ _ (not_lt.mp hge)] at hv
    exact Bool.false_ne_true hv
  have hb := hlen (encodeCNF [[(2 ^ n, true)]]) (by rw [code_length]; omega)
  rw [code_length] at hb
  have h3 : (2 * n + 8) ^ d ≤ (3 * n) ^ d := Nat.pow_le_pow_left (by omega) d
  have : a * (2 * n + 8) ^ d ≤ a * 3 ^ d * n ^ d := by
    calc a * (2 * n + 8) ^ d ≤ a * (3 * n) ^ d := Nat.mul_le_mul_left _ h3
      _ = a * 3 ^ d * n ^ d := by rw [Nat.mul_pow, Nat.mul_assoc]
  omega
end PEqualNP.Library.Helpers
