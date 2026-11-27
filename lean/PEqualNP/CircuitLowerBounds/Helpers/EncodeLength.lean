import Mathlib
import PEqualNP.Defs
import PEqualNP.CircuitLowerBounds.Helpers.WeightBound

/-!
# Short descriptions of depth-two threshold circuits

A language with depth-two threshold circuits with `s n` bottom gates has, at every length `n`,
such a circuit given as data (`ThrCircuit`) whose binary code has length at most
`100 * (n + s n + 3) ^ 4`.

Route: replace the weights of every gate by small integer weights (`threshold_small_weights`),
clamp every threshold to the range of the weighted sum, and count the bits of the code.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open PEqualNP.CircuitLowerBounds

/-! ## Small weights and a small threshold -/

/-- Small weights with a clamped threshold: every weight and the threshold are small. -/
theorem threshold_small_all (m : ℕ) (c : Fin m → ℤ) (t0 : ℤ) :
    ∃ (c' : Fin m → ℤ) (t0' : ℤ), (∀ j, |c' j| ≤ ((m : ℤ) + 2) ^ (m + 2)) ∧
      |t0'| ≤ ((m : ℤ) + 2) ^ (m + 2) + 1 ∧
      ∀ g : Fin m → Bool, (t0 ≤ ∑ j : Fin m, c j * (if g j = true then 1 else 0)) ↔
        (t0' ≤ ∑ j : Fin m, c' j * (if g j = true then 1 else 0)) := by
  obtain ⟨c', t1, hW, hc'⟩ := threshold_small_weights m c t0
  set W : ℤ := ∑ j : Fin m, |c' j| with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨c', max (-W) (min t1 (W + 1)), ?_, ?_, ?_⟩
  · intro j
    have : |c' j| ≤ W :=
      Finset.single_le_sum (f := fun j => |c' j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
    exact this.trans hW
  · have h1 : |max (-W) (min t1 (W + 1))| ≤ W + 1 := by
      rw [abs_le]
      constructor
      · exact le_trans (by linarith) (le_max_left _ _)
      · exact max_le (by linarith) (min_le_right _ _)
    linarith
  · intro g
    rw [hc' g]
    set S : ℤ := ∑ j : Fin m, c' j * (if g j = true then 1 else 0) with hS
    have habs : |S| ≤ W := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      split_ifs <;> simp
    have h2 := abs_le.mp habs
    constructor
    · intro h
      exact max_le h2.1 ((min_le_left _ _).trans h)
    · intro h
      have h3 : min t1 (W + 1) ≤ S := (le_max_right _ _).trans h
      rcases min_le_iff.mp h3 with h4 | h4
      · exact h4
      · linarith

/-- A small integer has few bits. -/
theorem natAbs_lt_two_pow (m N : ℕ) (h : m + 3 ≤ N) (z : ℤ)
    (hz : |z| ≤ ((m : ℤ) + 2) ^ (m + 2) + 1) : z.natAbs < 2 ^ (N * N) := by
  have h1 : z.natAbs ≤ (m + 2) ^ (m + 2) + 1 := by
    have : (z.natAbs : ℤ) ≤ (((m + 2) ^ (m + 2) + 1 : ℕ) : ℤ) := by
      rw [← Int.abs_eq_natAbs]
      push_cast
      exact hz
    exact_mod_cast this
  have h2 : (m + 2) ^ (m + 2) < (m + 3) ^ (m + 2) :=
    Nat.pow_lt_pow_left (by omega) (by omega)
  have h3 : (m + 3) ^ (m + 2) ≤ N ^ (m + 2) := Nat.pow_le_pow_left h _
  have h4 : N ^ (m + 2) ≤ N ^ N := Nat.pow_le_pow_right (by omega) (by omega)
  have h5 : N ^ N < (2 ^ N) ^ N := Nat.pow_lt_pow_left Nat.lt_two_pow_self (by omega)
  rw [pow_mul]
  omega

/-! ## The value of the circuit as data -/

/-- The weighted sum over zipped lists is the weighted sum over `Fin n`. -/
theorem zip_sum_ofFn : ∀ (n : ℕ) (w : Fin n → ℤ) (x : Fin n → Bool),
    (((List.ofFn w).zip (List.ofFn x)).map fun p => if p.2 = true then p.1 else 0).sum =
      ∑ i : Fin n, w i * (if x i = true then 1 else 0)
  | 0, _, _ => by simp
  | n + 1, w, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.zip_cons_cons, List.map_cons, List.sum_cons,
      Fin.sum_univ_succ, zip_sum_ofFn n (fun i => w i.succ) (fun i => x i.succ)]
    congr 1
    split_ifs <;> simp

/-- A bound on all elements bounds the fold by `max`. -/
theorem foldr_max_le (l : List ℕ) (n : ℕ) (h : ∀ a ∈ l, a ≤ n) : l.foldr max 0 ≤ n := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-! ## Lengths of the codes -/

theorem encodeNat_length (m : ℕ) : (encodeNat m).length = 2 * m.size + 1 := by
  have h : ∀ l : List Bool, (l.flatMap fun b => [true, b]).length = 2 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [List.flatMap_cons, ih]; omega
  rw [encodeNat, List.length_append, h, Nat.size_eq_bits_len]
  simp

theorem encodeInt_length_le (z : ℤ) (b : ℕ) (hz : z.natAbs < 2 ^ b) :
    (encodeInt z).length ≤ 2 * b + 2 := by
  have h : z.natAbs.size ≤ b := Nat.size_le.mpr hz
  rw [encodeInt, List.length_cons, encodeNat_length]
  omega

theorem encodeList_length_le {α : Type} (e : α → List Bool) (B : ℕ) (l : List α)
    (h : ∀ a ∈ l, (e a).length ≤ B) : (encodeList e l).length ≤ l.length * (1 + B) + 1 := by
  have h' : (l.flatMap fun a => true :: e a).length ≤ l.length * (1 + B) := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have h1 := h a (by simp)
      have h2 := ih fun b hb => h b (by simp [hb])
      rw [List.flatMap_cons, List.length_append, List.length_cons, List.length_cons,
        Nat.succ_mul]
      omega
  rw [encodeList, List.length_append]
  simpa using h'

/-- The code of a circuit with at most `N` gates, each with at most `N` weights, all of whose
integers have at most `N * N` bits, is short. -/
theorem encodeThr_length_le (c : ThrCircuit) (N : ℕ) (hN : 3 ≤ N) (hK : c.gates.length ≤ N)
    (hg : ∀ g ∈ c.gates, g.1.length ≤ N ∧ (∀ z ∈ g.1, z.natAbs < 2 ^ (N * N)) ∧
      g.2.1.natAbs < 2 ^ (N * N) ∧ g.2.2.natAbs < 2 ^ (N * N))
    (htop : c.top.natAbs < 2 ^ (N * N)) : (encodeThr c).length ≤ 100 * N ^ 4 := by
  set I : ℕ := 2 * (N * N) + 2 with hI
  set G : ℕ := N * (1 + I) + 1 + I + I with hG
  have hgate : ∀ g ∈ c.gates,
      (encodeList encodeInt g.1 ++ encodeInt g.2.1 ++ encodeInt g.2.2).length ≤ G := by
    intro g hgm
    obtain ⟨h1, h2, h3, h4⟩ := hg g hgm
    have e1 := encodeList_length_le encodeInt I g.1 fun z hz =>
      encodeInt_length_le z _ (h2 z hz)
    have e2 := encodeInt_length_le _ _ h3
    have e3 := encodeInt_length_le _ _ h4
    have e4 : g.1.length * (1 + I) ≤ N * (1 + I) := Nat.mul_le_mul_right _ h1
    rw [List.length_append, List.length_append]
    omega
  have e5 := encodeList_length_le
    (fun g : List ℤ × ℤ × ℤ => encodeList encodeInt g.1 ++ encodeInt g.2.1 ++ encodeInt g.2.2)
    G c.gates hgate
  have e6 := encodeInt_length_le _ _ htop
  have e7 : c.gates.length * (1 + G) ≤ N * (1 + G) := Nat.mul_le_mul_right _ hK
  have e8 : (encodeThr c).length ≤ N * (1 + G) + 1 + I := by
    rw [encodeThr, List.length_append]
    omega
  have e9 : N * (1 + G) + 1 + I = 2 * N ^ 4 + 4 * N ^ 3 + 5 * N ^ 2 + 6 * N + 3 := by
    rw [hG, hI]
    ring
  have p1 : N ^ 1 ≤ N ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have p2 : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have p3 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have p4 : 1 ≤ N ^ 4 := Nat.one_le_pow _ _ (by omega)
  rw [pow_one] at p1
  omega

/-! ## The main statement -/

/-- A language with depth-two threshold circuits has, at every length, a circuit as data that
decides it and has a short code. -/
theorem thrthr_short_code (s : ℕ → ℕ) (L : Language Bool) (hL : L ∈ THRTHR s) (n : ℕ) :
    ∃ c : ThrCircuit, c.inputs = n ∧
      (∀ x : Fin n → Bool, List.ofFn x ∈ L ↔ c.eval (List.ofFn x) = true) ∧
      (encodeThr c).length ≤ 100 * (n + s n + 3) ^ 4 := by
  obtain ⟨k, w, t, a, t0, hk, hx⟩ := hL n
  choose w' t' hw' ht' hwt using fun j => threshold_small_all n (w j) (t j)
  obtain ⟨a', t0', ha', ht0', hat⟩ := threshold_small_all k a t0
  set N : ℕ := n + s n + 3 with hN
  have hz0 : (0 : ℤ).natAbs < 2 ^ (N * N) := by simp
  have hz1 : (1 : ℤ).natAbs < 2 ^ (N * N) := by
    simp only [Int.natAbs_one]
    exact Nat.one_lt_two_pow (by rw [hN]; positivity)
  refine ⟨⟨(List.replicate n 0, 1, 0) ::
    List.ofFn (fun j => (List.ofFn (w' j), t' j, a' j)), t0'⟩, ?_, ?_, ?_⟩
  · -- the number of inputs
    simp only [ThrCircuit.inputs, List.map_cons, List.foldr_cons, List.length_replicate]
    refine max_eq_left (foldr_max_le _ _ ?_)
    intro b hb
    simp only [List.map_ofFn, List.mem_ofFn] at hb
    obtain ⟨j, rfl⟩ := hb
    simp
  · -- the value
    intro x
    rw [hx x]
    have h1 : ∀ j : Fin k,
        (t j ≤ ∑ i : Fin n, w j i * (if x i = true then 1 else 0)) ↔
          (t' j ≤ ∑ i : Fin n, w' j i * (if x i = true then 1 else 0)) := fun j => hwt j x
    have h2 := hat fun j => decide (t' j ≤ ∑ i : Fin n, w' j i * (if x i = true then 1 else 0))
    simp only [decide_eq_true_eq] at h2
    simp only [h1]
    rw [h2]
    simp only [ThrCircuit.eval, List.map_cons, List.sum_cons, zero_mul, zero_add,
      decide_eq_true_eq, List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_def, zip_sum_ofFn]
  · -- the length of the code
    refine encodeThr_length_le _ N (by omega) ?_ ?_ ?_
    · simp only [List.length_cons, List.length_ofFn]
      omega
    · intro g hgm
      rcases List.mem_cons.mp hgm with rfl | hgm
      · refine ⟨by simp; omega, ?_, hz1, hz0⟩
        intro z hz
        rw [List.eq_of_mem_replicate hz]
        exact hz0
      · obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hgm
        refine ⟨by simp; omega, ?_, ?_, ?_⟩
        · intro z hz
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hz
          exact natAbs_lt_two_pow n N (by omega) _ (by linarith [hw' j i])
        · exact natAbs_lt_two_pow n N (by omega) _ (ht' j)
        · exact natAbs_lt_two_pow k N (by omega) _ (by have := ha' j; show |a' j| ≤ _; linarith)
    · exact natAbs_lt_two_pow k N (by omega) _ ht0'

end PEqualNP.CircuitLowerBounds.Helpers
