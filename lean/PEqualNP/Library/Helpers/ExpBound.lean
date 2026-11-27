import Mathlib.Tactic
import PEqualNP.Library.Helpers.PolyExp
import PEqualNP.Library.Machines.Run

/-!
# Functions below `2 ^ (A * (n + 1) ^ D)`

Helper module (proofs only, no statement may use it). The class of functions `f : ℕ → ℕ` with
`f n ≤ 2 ^ (A * (n + 1) ^ D)` for some `A`, `D` is closed under sums, products, constants and
polynomials, contains `2 ^ (g n ^ K)` for `g` below a monomial, and every member is below
`2 ^ (n ^ j) + j` for some `j`.
-/

namespace PEqualNP.Library.Helpers

/-- `f` is below `2 ^ (A * (n + 1) ^ D)` for some `A`, `D`. -/
def ExpBound (f : ℕ → ℕ) : Prop := ∃ A D : ℕ, ∀ n, f n ≤ 2 ^ (A * (n + 1) ^ D)

theorem eb_mono {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) (hg : ExpBound g) : ExpBound f := by
  obtain ⟨A, D, hA⟩ := hg
  exact ⟨A, D, fun n => (h n).trans (hA n)⟩

theorem eb_const (c : ℕ) : ExpBound (fun _ => c) :=
  ⟨c, 0, fun n => by simpa using (Nat.lt_two_pow_self (n := c)).le⟩

private theorem exp_le_merge (A B D E n : ℕ) :
    A * (n + 1) ^ D + B * (n + 1) ^ E ≤ (A + B) * (n + 1) ^ (D + E) := by
  have h1 : (n + 1) ^ D ≤ (n + 1) ^ (D + E) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (n + 1) ^ E ≤ (n + 1) ^ (D + E) := Nat.pow_le_pow_right (by omega) (by omega)
  have := Nat.mul_le_mul_left A h1
  have := Nat.mul_le_mul_left B h2
  nlinarith

theorem eb_mul {f g : ℕ → ℕ} (hf : ExpBound f) (hg : ExpBound g) :
    ExpBound (fun n => f n * g n) := by
  obtain ⟨A, D, hA⟩ := hf
  obtain ⟨B, E, hB⟩ := hg
  refine ⟨A + B, D + E, fun n => ?_⟩
  calc f n * g n ≤ 2 ^ (A * (n + 1) ^ D) * 2 ^ (B * (n + 1) ^ E) :=
        Nat.mul_le_mul (hA n) (hB n)
    _ = 2 ^ (A * (n + 1) ^ D + B * (n + 1) ^ E) := (pow_add _ _ _).symm
    _ ≤ 2 ^ ((A + B) * (n + 1) ^ (D + E)) :=
        Nat.pow_le_pow_right (by norm_num) (exp_le_merge A B D E n)

theorem eb_add {f g : ℕ → ℕ} (hf : ExpBound f) (hg : ExpBound g) :
    ExpBound (fun n => f n + g n) := by
  obtain ⟨A, D, hA⟩ := hf
  obtain ⟨B, E, hB⟩ := hg
  refine ⟨A + B + 1, D + E, fun n => ?_⟩
  have hm := exp_le_merge A B D E n
  have h1 : 1 ≤ (n + 1) ^ (D + E) := Nat.one_le_pow _ _ (by omega)
  have ha : (2 : ℕ) ^ (A * (n + 1) ^ D) ≤ 2 ^ ((A + B) * (n + 1) ^ (D + E)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb : (2 : ℕ) ^ (B * (n + 1) ^ E) ≤ 2 ^ ((A + B) * (n + 1) ^ (D + E)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc : (2 : ℕ) ^ ((A + B) * (n + 1) ^ (D + E)) * 2 ≤ 2 ^ ((A + B + 1) * (n + 1) ^ (D + E)) := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have := hA n
  have := hB n
  show f n + g n ≤ _
  omega

theorem eb_of_le_monomial {f : ℕ → ℕ} (A D : ℕ) (hf : ∀ n, f n ≤ A * (n + 1) ^ D) :
    ExpBound f :=
  ⟨A, D, fun n => (hf n).trans Nat.lt_two_pow_self.le⟩

theorem eb_id : ExpBound (fun n => n) :=
  eb_of_le_monomial 1 1 (fun n => by simp)

theorem eb_two_pow {f : ℕ → ℕ} (A D K : ℕ) (hf : ∀ n, f n ≤ A * (n + 1) ^ D) :
    ExpBound (fun n => 2 ^ (f n ^ K)) := by
  refine ⟨A ^ K, D * K, fun n => Nat.pow_le_pow_right (by norm_num) ?_⟩
  calc f n ^ K ≤ (A * (n + 1) ^ D) ^ K := Nat.pow_le_pow_left (hf n) K
    _ = A ^ K * (n + 1) ^ (D * K) := by rw [mul_pow, ← pow_mul]

theorem eb_poly (p : Polynomial ℕ) {f : ℕ → ℕ} (hf : ExpBound f) :
    ExpBound (fun n => p.eval (f n)) := by
  obtain ⟨s, hs⟩ := polynomial_le_pow_add p
  obtain ⟨A, D, hA⟩ := hf
  have h : ExpBound (fun n => (2 ^ (A * (n + 1) ^ D)) ^ s + s) := by
    refine eb_add ⟨A * s, D, fun n => ?_⟩ (eb_const s)
    show (2 ^ (A * (n + 1) ^ D)) ^ s ≤ _
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [mul_right_comm])
  exact eb_mono (fun n => (PEqualNP.Library.Machines.eval_mono p (hA n)).trans (hs _)) h

/-- Every member is below `2 ^ (n ^ j) + j` for some `j`. -/
theorem eb_final {f : ℕ → ℕ} (hf : ExpBound f) : ∃ j, ∀ n, f n ≤ 2 ^ (n ^ j) + j := by
  obtain ⟨A, D, hA⟩ := hf
  refine ⟨A + 2 * D + f 0 + f 1, fun n => ?_⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · have : f n ≤ A + 2 * D + f 0 + f 1 := by
      have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl
      · generalize f 0 = a; generalize f 1 = b; omega
      · generalize f 0 = a; generalize f 1 = b; omega
    exact this.trans (Nat.le_add_left _ _)
  · have h1 : A ≤ n ^ A := by
      have h2 : A < 2 ^ A := Nat.lt_two_pow_self
      have h3 : 2 ^ A ≤ n ^ A := Nat.pow_le_pow_left h A
      omega
    have h4 : (n + 1) ^ D ≤ n ^ (2 * D) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left (by nlinarith) D
    have h5 : A * (n + 1) ^ D ≤ n ^ (A + 2 * D) := by
      rw [pow_add]; exact Nat.mul_le_mul h1 h4
    have h6 : n ^ (A + 2 * D) ≤ n ^ (A + 2 * D + f 0 + f 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h7 : (2 : ℕ) ^ (A * (n + 1) ^ D) ≤ 2 ^ (n ^ (A + 2 * D + f 0 + f 1)) :=
      Nat.pow_le_pow_right (by norm_num) (h5.trans h6)
    have := hA n
    omega

end PEqualNP.Library.Helpers
