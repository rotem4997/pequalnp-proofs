import PEqualNP.Library.L094
import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.Helpers.OutputLength
import PEqualNP.Library.Helpers.FirstTimeGen
import PEqualNP.Library.Helpers.ExpBound

/-!
# A polynomial-time test on an exponentially padded pair

Helper module (proofs only, no statement may use it). For polynomial-time `u`, `v` and a
polynomial-time test `h` on pairs, `z ↦ h (1 ^ (2 ^ (|u z| ^ k) + k) 0 (u z), v z)` runs within
`2 ^ (n ^ j) + j` steps for some `j`. The machine computes the pair `(u z, v z)`, pads the first
component (L-lib-094 for `k ≥ 1`, three transducers for `k = 0`), then runs `h`.
-/

namespace PEqualNP.Library.Helpers

open PEqualNP.Library PEqualNP.Library.Machines

/-- Transducer writing one extra `false` in front. -/
def consFδ : Bool → Bool → Bool × Option Bool × Option Bool
  | false, b => (true, some false, some b)
  | true, b => (true, some b, none)

/-- End of input: write the extra `false` if it was not written. -/
def consFFin : Bool → Option Bool
  | false => some false
  | true => none

theorem consF_run_true (y : List Bool) : fstRun2 consFδ consFFin true y = y := by
  induction y with
  | nil => rfl
  | cons b y ih => simp [fstRun2, consFδ, ih]

theorem consF_run_false (y : List Bool) : fstRun2 consFδ consFFin false y = false :: y := by
  cases y with
  | nil => rfl
  | cons b y => simp [fstRun2, consFδ, consF_run_true]

theorem consFalse_time : PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
    (fun x : List Bool => x) (fun y : List Bool => false :: y) (fun n => 2 * n + 3) :=
  fst2_time _ _ _ consFδ consFFin false (fun y => (consF_run_false y).symm)

/-- The padding for `k = 0` is `x ↦ 1 1 0 x`, linear time. -/
theorem pad0_time : PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
    (fun x : List Bool => x) (fun x : List Bool => true :: true :: false :: x)
    (fun n => 30 * 2 ^ n + 30) := by
  have h2 := comp_time (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => x)
    (fun y : List Bool => false :: y) (fun y : List Bool => true :: y)
    _ (fun n => 2 * n + 3) (fun n => n + 1) consFalse_time consTrue_time
    (fun a b h => by dsimp; omega) (fun x => by simp)
  have h3 := comp_time (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => x)
    (fun y : List Bool => true :: false :: y) (fun y : List Bool => true :: y)
    _ (fun n => 2 * n + 3) (fun n => n + 2) h2 consTrue_time
    (fun a b h => by dsimp; omega) (fun x => by simp)
  refine time_mono h3 fun n => ?_
  have : n < 2 ^ n := Nat.lt_two_pow_self
  omega

/-- The padding map, for every `k`, with a time bound `c * 2 ^ (n ^ K) + c` (`K ≥ 1`) and an
output length bound. -/
theorem pad_time_gen (k : ℕ) : ∃ c K : ℕ, 1 ≤ K ∧
    PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)
      (fun n : ℕ => c * 2 ^ (n ^ K) + c) ∧
    ∀ x : List Bool, (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x).length ≤
      2 * 2 ^ (x.length ^ K) + k + 1 + x.length := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨30, 1, le_rfl, ?_, fun x => ?_⟩
    · have e : (fun x : List Bool => List.replicate (2 ^ (x.length ^ 0) + 0) true ++ false :: x) =
          fun x : List Bool => true :: true :: false :: x := by
        funext x; simp [List.replicate]
      rw [e]
      simpa using pad0_time
    · have : 1 ≤ 2 ^ x.length := Nat.one_le_two_pow
      simp
      omega
  · obtain ⟨c, hc⟩ := PEqualNP.Library.L094 k hk
    refine ⟨c, k, hk, hc, fun x => ?_⟩
    simp
    omega

theorem two_pow_pow_mono (K : ℕ) : Monotone (fun n : ℕ => 2 ^ (n ^ K)) :=
  fun _ _ h => Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left h K)

theorem padTest : ∀ (k : ℕ) (u v : List Bool → List Bool) (h : List Bool × List Bool → Bool),
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u →
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v →
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair Computability.encodeBool h →
    ∃ j : ℕ, PEqualNP.Library.ComputableInTime (fun x : List Bool => x) Computability.encodeBool
      (fun z : List Bool => h (List.replicate (2 ^ ((u z).length ^ k) + k) true ++ false :: u z,
        v z)) (fun n : ℕ => 2 ^ (n ^ j) + j) := by
  intro k u v h hu hv hh
  obtain ⟨c, K, hK, hpad, hpadlen⟩ := pad_time_gen k
  obtain ⟨a, d, had⟩ := output_length_le u hu
  obtain ⟨b, e, hbe⟩ := output_length_le v hv
  -- the lengths of `u z` and `v z` are below a monomial in `|z| + 1`
  let A := a + (u []).length + b + (v []).length + 1
  let D := d + e
  have hU : ∀ z : List Bool, (u z).length + (v z).length ≤ A * (z.length + 1) ^ D := by
    intro z
    have h1 : 1 ≤ (z.length + 1) ^ D := Nat.one_le_pow _ _ (by omega)
    rcases Nat.eq_zero_or_pos z.length with h0 | h0
    · rw [List.length_eq_zero_iff.mp h0]
      simp only [List.length_nil, zero_add, one_pow, mul_one, A]
      omega
    · have hd : z.length ^ d ≤ (z.length + 1) ^ D :=
        (Nat.pow_le_pow_left (by omega) d).trans (Nat.pow_le_pow_right (by omega) (by omega))
      have he : z.length ^ e ≤ (z.length + 1) ^ D :=
        (Nat.pow_le_pow_left (by omega) e).trans (Nat.pow_le_pow_right (by omega) (by omega))
      have e1 := (had z h0).trans (Nat.mul_le_mul_left a hd)
      have e2 := (hbe z h0).trans (Nat.mul_le_mul_left b he)
      have e3 : A * (z.length + 1) ^ D = a * (z.length + 1) ^ D + b * (z.length + 1) ^ D +
          ((u []).length + (v []).length + 1) * (z.length + 1) ^ D := by
        simp only [A]; ring
      have e4 : (u []).length + (v []).length + 1 ≤
          ((u []).length + (v []).length + 1) * (z.length + 1) ^ D := Nat.le_mul_of_pos_right _ h1
      omega
  let ℓ : ℕ → ℕ := fun n => A * (n + 1) ^ D
  have hℓ : Monotone ℓ := fun x y hxy =>
    Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by omega) D)
  -- step 1: the pair
  obtain ⟨p1, h1⟩ := time_of_polyTime (cpt_pair hu hv)
  -- step 2: padding the first component
  let len2 : ℕ → ℕ := fun n => 2 * 2 ^ (n ^ K) + k + 1 + n
  have hlen2 : Monotone len2 := fun x y hxy => by
    have : 2 ^ (x ^ K) ≤ 2 ^ (y ^ K) := two_pow_pow_mono K hxy
    simp only [len2]; omega
  let t2 : ℕ → ℕ := fun n => c * 2 ^ (n ^ K) + c
  have ht2 : Monotone t2 := fun x y hxy => by
    have : c * 2 ^ (x ^ K) ≤ c * 2 ^ (y ^ K) := Nat.mul_le_mul_left c (two_pow_pow_mono K hxy)
    simp only [t2]; omega
  have h2 := first_time
    (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)
    t2 len2 ht2 hlen2 hpadlen hpad
  have hmono2 : Monotone (fun n => t2 n + 2 * n + 2 * len2 n + 5) := fun x y hxy => by
    have := ht2 hxy
    have := hlen2 hxy
    dsimp only; omega
  have h12 := comp_time (fun x : List Bool => x) PEqualNP.Library.encodePair
    PEqualNP.Library.encodePair (fun z : List Bool => (u z, v z))
    (fun p : List Bool × List Bool =>
      (List.replicate (2 ^ (p.1.length ^ k) + k) true ++ false :: p.1, p.2))
    _ _ ℓ h1 h2 hmono2 (fun z => by rw [encodePair_length]; exact hU z)
  -- step 3: the test
  obtain ⟨ph, h3⟩ := time_of_polyTime hh
  have h123 := comp_time (fun x : List Bool => x) PEqualNP.Library.encodePair
    Computability.encodeBool
    (fun z : List Bool => (List.replicate (2 ^ ((u z).length ^ k) + k) true ++ false :: u z, v z))
    h _ (fun n => ph.eval n) (fun n => len2 (ℓ n)) h12 h3
    (fun _ _ hxy => eval_mono ph hxy) (fun z => by
      rw [encodePair_length]
      have e1 := hpadlen (u z)
      have e2 : (u z).length + (v z).length ≤ ℓ z.length := hU z
      have e3 : 2 ^ ((u z).length ^ K) ≤ 2 ^ ((ℓ z.length) ^ K) := two_pow_pow_mono K (by omega)
      simp only [len2] at e1 ⊢
      omega)
  -- the arithmetic
  have hEℓ : ExpBound ℓ := eb_of_le_monomial A D (fun n => le_rfl)
  have hEG : ExpBound (fun n => 2 ^ (ℓ n ^ K)) := eb_two_pow A D K (fun n => le_rfl)
  have hEL : ExpBound (fun n => len2 (ℓ n)) :=
    eb_add (eb_add (eb_mul (eb_const 2) hEG) (eb_const (k + 1))) hEℓ |> eb_mono (fun n => by
      simp only [len2]; omega)
  have hEt2 : ExpBound (fun n => t2 (ℓ n)) :=
    eb_add (eb_mul (eb_const c) hEG) (eb_const c)
  have hE1 : ExpBound (fun n => p1.eval n) := eb_poly p1 eb_id
  have hE3 : ExpBound (fun n => ph.eval (len2 (ℓ n))) := eb_poly ph hEL
  have hEall : ExpBound (fun n => p1.eval n + (2 * ℓ n + 2) + (t2 (ℓ n) + 2 * ℓ n +
      2 * len2 (ℓ n) + 5) + (2 * len2 (ℓ n) + 2) + ph.eval (len2 (ℓ n))) := by
    have hlin : ExpBound (fun n => 5 * ℓ n + 4 * len2 (ℓ n) + 9) :=
      eb_add (eb_add (eb_mul (eb_const 5) hEℓ) (eb_mul (eb_const 4) hEL)) (eb_const 9)
    exact eb_mono (fun n => by omega) (eb_add (eb_add (eb_add hE1 hlin) hEt2) hE3)
  obtain ⟨j, hj⟩ := eb_final hEall
  exact ⟨j, time_mono h123 hj⟩

end PEqualNP.Library.Helpers
