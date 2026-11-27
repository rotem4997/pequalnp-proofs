import PEqualNP.MetaComplexity.Helpers.LocalCoreWf
import PEqualNP.MetaComplexity.Helpers.ZeroCompletion

/-!
# The price of a local reduction of parity: an explicit hard function

Helper module (proofs only, no statement may use it). Built on `LocalCoreWf.core_wf`
(L-meta-036) and on the zero completion of `ZeroCompletion`.

A `q`-local map that reduces parity on `n` bits to partial MCSP, with outputs of length at most
`M`, sends the all-false input to an instance `(s, T)`. Three forms of the same fact:

* `zero_table_hard`: the completion of `T` by `false` (a total function on `n'` variables) has
  no circuit of size `s`, and `s` obeys the closed inequality
  `(n - 3 q) / (4 q) < (2 s + 3) (log2 M + 3) + log2 q`, so `s` is about `n / (8 q log2 M)`.
* `price_size`: a language in `SIZE S` whose inputs `i ++ c` answer "entry `i` of `T` is defined
  as `true`" has `s ≤ S (n' + |c|)`, hence the same inequality with `S (n' + |c|)` for `s`.
* `price_uniform`: for a polynomial-time `r` and an exponent `k` there is one language in EXP
  such that every size bound `S` of it pays the price at every string `x` for which
  `r (1 ^ (2 ^ (|x| ^ k) + k) 0 x)` is the image of the all-false input under a local
  reduction of parity. It takes the bit language fact of `LocalPriceBit` as a hypothesis: the
  machine side of the library is on the `Columns` side of the import clash and `core_wf` is on
  the `Counting` side.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalPrice

open PEqualNP.Library PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-- The counting inequality of L-meta-036 in closed form, when the bound `s` and the table fit
in the length `M`. -/
theorem closed_form (e q M s : ℕ) (hM : s + 3 ≤ M)
    (h : 2 ^ e ≤ 8 * q * ((s + 1) * ((s + 1) * ((3 * ((Nat.log 2 M + s + 2) *
      (Nat.log 2 M + s + 2))) ^ s * (Nat.log 2 M + s + 1))))) :
    e < (2 * s + 3) * (Nat.log 2 M + 3) + Nat.log 2 q := by
  set L := Nat.log 2 M with hL
  set lq := Nat.log 2 q with hlq
  have hM1 : M < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
  have hLM : L < M := Nat.log_lt_self 2 (by omega)
  have hq1 : q < 2 ^ (lq + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have h8q : 8 * q < 2 ^ (lq + 4) := by
    have : 2 ^ (lq + 4) = 8 * 2 ^ (lq + 1) := by ring
    omega
  have h1 : s + 1 ≤ 2 ^ (L + 1) := by omega
  have hP : L + s + 2 ≤ 2 ^ (L + 2) := by
    have : 2 ^ (L + 2) = 2 * 2 ^ (L + 1) := by ring
    omega
  have h4 : L + s + 1 ≤ 2 ^ (L + 2) := by omega
  have h3 : 3 * ((L + s + 2) * (L + s + 2)) ≤ 2 ^ (2 * L + 6) := by
    have h5 : (L + s + 2) * (L + s + 2) ≤ 2 ^ (L + 2) * 2 ^ (L + 2) := Nat.mul_le_mul hP hP
    have : 2 ^ (2 * L + 6) = 4 * (2 ^ (L + 2) * 2 ^ (L + 2)) := by ring
    omega
  have hpow : (3 * ((L + s + 2) * (L + s + 2))) ^ s ≤ 2 ^ ((2 * L + 6) * s) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left h3 s
  have hR : 8 * q * ((s + 1) * ((s + 1) * ((3 * ((L + s + 2) * (L + s + 2))) ^ s *
      (L + s + 1)))) <
      2 ^ (lq + 4) * (2 ^ (L + 1) * (2 ^ (L + 1) * (2 ^ ((2 * L + 6) * s) * 2 ^ (L + 2)))) :=
    Nat.mul_lt_mul_of_lt_of_le h8q
      (Nat.mul_le_mul h1 (Nat.mul_le_mul h1 (Nat.mul_le_mul hpow h4))) (by positivity)
  have hlt : 2 ^ e < 2 ^ (lq + 4 + (L + 1 + (L + 1 + ((2 * L + 6) * s + (L + 2))))) := by
    simp only [pow_add] at hR ⊢
    exact lt_of_le_of_lt h hR
  have hexp := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hlt
  have e1 : (2 * L + 6) * s = 2 * (L * s) + 6 * s := by ring
  have e2 : (2 * s + 3) * (L + 3) = 2 * (L * s) + 6 * s + 3 * L + 9 := by ring
  omega

/-- The code of a partial table has two bits per entry. -/
theorem length_code (T : List (Option Bool)) :
    (encodePartial T).length = 2 * T.length := by
  induction T with
  | nil => rfl
  | cons o T ih =>
    have e : encodePartial (o :: T) =
        (match o with
          | none => [false, false]
          | some b => [true, b]) ++ encodePartial T := rfl
    rw [e, List.length_append, ih]
    rcases o with _ | b <;> simp <;> omega

/-- The completion of a partial table by `false` is consistent with the table. -/
theorem completion_consistent (n : ℕ) (T : List (Option Bool)) :
    Consistent n T
      (fun y : Fin n → Bool => decide (T.getD (tableIndex y) none = some true)) := by
  intro y b hb
  show decide (T.getD (tableIndex y) none = some true) = b
  rw [hb]
  cases b <;> simp

/-- The explicit hard function of a local reduction of parity: the completion by `false` of the
table at the all-false input has no circuit of the size bound `s` of that instance, and `s` is
at least about `n / (8 q log2 M)`. -/
theorem zero_table_hard : ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → 3 * q < n → ∀ (n' s : ℕ) (T : List (Option Bool)), w (fun _ : Fin n => false) = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → (¬ PEqualNP.MetaComplexity.HasCircuitSize n' (fun x : Fin n' → Bool => decide (T.getD (PEqualNP.MetaComplexity.tableIndex x) none = some true)) s) ∧ (n - 3 * q) / (4 * q) < (2 * s + 3) * (Nat.log 2 M + 3) + Nat.log 2 q := by
  intro n q M w hq hloc hlen hred hn n' s T e hT
  obtain ⟨hno, hb⟩ := LocalCoreWf.core_wf n q M w hq hloc hlen hred hn n' s T e hT
  refine ⟨fun h => hno ⟨_, completion_consistent n' T, h⟩, ?_⟩
  have h0 := hlen (fun _ : Fin n => false)
  rw [e] at h0
  simp only [List.length_append, List.length_replicate, List.length_cons,
    length_code, hT] at h0
  have hpos : 0 < 2 ^ n' := by positivity
  exact closed_form _ q M s (by omega) hb

/-- The completion through a language in `SIZE S`, for any size function `S` (L-meta-024 has it
for polynomials). -/
theorem zero_completion_size (B : Language Bool) (S : ℕ → ℕ) (n : ℕ) (T : List (Option Bool))
    (c : List Bool) (hB : B ∈ PEqualNP.CircuitLowerBounds.SIZE S)
    (hT : ∀ i : List Bool, i.length = n → (i ++ c ∈ B ↔
      T.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 i)
        none = some true)) :
    HasCircuitSize n
      (fun x : Fin n → Bool => decide (T.getD (tableIndex x) none = some true))
      (S (n + c.length) + 1) := by
  obtain ⟨F, hF, hsz⟩ := (PEqualNP.MetaComplexity.L019 _ B).1 hB (n + c.length)
  have h := hardwire n c.length F c.get _ hsz
  have e : (fun y : Fin n → Bool => F (Fin.append y c.get))
      = fun x : Fin n → Bool => decide (T.getD (tableIndex x) none = some true) := by
    funext x
    rw [Bool.eq_iff_iff, decide_eq_true_iff, hF, List.ofFn_fin_append, List.ofFn_get,
      hT _ (List.length_ofFn), foldr_ofFn_eq_tableIndex]
  rw [← e]
  exact h

/-- The price in `SIZE` terms: a language with circuits of size `S` that reads the `true`
entries of the table at the all-false input, on inputs `i ++ c`, has
`s ≤ S (n' + |c|)`, so `S (n' + |c|)` is at least about `n / (8 q log2 M)`. -/
theorem price_size : ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → 3 * q < n → ∀ (n' s : ℕ) (T : List (Option Bool)), w (fun _ : Fin n => false) = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → ∀ (B : Language Bool) (S : ℕ → ℕ) (c : List Bool), B ∈ PEqualNP.CircuitLowerBounds.SIZE S → (∀ i : List Bool, i.length = n' → (i ++ c ∈ B ↔ T.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 i) none = some true)) → s ≤ S (n' + c.length) ∧ (n - 3 * q) / (4 * q) < (2 * S (n' + c.length) + 3) * (Nat.log 2 M + 3) + Nat.log 2 q := by
  intro n q M w hq hloc hlen hred hn n' s T e hT B S c hB hBT
  obtain ⟨hno, hb⟩ := zero_table_hard n q M w hq hloc hlen hred hn n' s T e hT
  have hz := zero_completion_size B S n' T c hB hBT
  have hs : s ≤ S (n' + c.length) := by
    by_contra hlt
    exact hno (hasCircuitSize_mono (by omega) hz)
  refine ⟨hs, lt_of_lt_of_le hb ?_⟩
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _

/-- The uniform form, from the bit language of a polynomial-time table producer (proved as
`LocalPriceBit.bit_language`; that module and this one cannot be imported together, so the fact
is taken here as a hypothesis). For a polynomial-time map `r` and an exponent `k` there is one
language in EXP such that every size bound `S` of it pays the price wherever `r` outputs the
image of the all-false input under a local reduction of parity. -/
theorem price_uniform
    (hbit : ∀ (r : List Bool → List Bool) (k : ℕ), PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) r → ∃ L : Language Bool, L ∈ PEqualNP.Library.EXP ∧ ∀ (x : List Bool) (s : ℕ) (T : List (Option Bool)), r (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → ∃ c : List Bool, c.length = 2 * x.length + 1 ∧ ∀ i : List Bool, (i ++ c ∈ L ↔ T.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 i) none = some true)) :
    ∀ (r : List Bool → List Bool) (k : ℕ), PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) r → ∃ L : Language Bool, L ∈ PEqualNP.Library.EXP ∧ ∀ S : ℕ → ℕ, L ∈ PEqualNP.CircuitLowerBounds.SIZE S → ∀ (x : List Bool) (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ y : Fin n → Bool, (w y).length ≤ M) → (∀ y : Fin n → Bool, (Finset.univ.filter fun i : Fin n => y i = true).card % 2 = 1 ↔ w y ∈ PEqualNP.MetaComplexity.PartialMCSP) → 3 * q < n → w (fun _ : Fin n => false) = r (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) → ∀ (n' s : ℕ) (T : List (Option Bool)), r (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → s ≤ S (n' + (2 * x.length + 1)) ∧ (n - 3 * q) / (4 * q) < (2 * S (n' + (2 * x.length + 1)) + 3) * (Nat.log 2 M + 3) + Nat.log 2 q := by
  intro r k hr
  obtain ⟨L, hL, hspec⟩ := hbit r k hr
  refine ⟨L, hL, ?_⟩
  intro S hS x n q M w hq hloc hlen hred hn hw n' s T e hT
  obtain ⟨c, hc, hci⟩ := hspec x s T e
  have h := price_size n q M w hq hloc hlen hred hn n' s T (hw.trans e) hT L S c hS
    (fun i _ => hci i)
  rw [hc] at h
  exact h

end PEqualNP.MetaComplexity.Helpers.LocalPrice
