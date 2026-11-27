import PEqualNP.MetaComplexity.Helpers.LocalConstruct

/-!
# The hypotheses of the lemmas on local reductions are satisfiable

Witness lemmas for `L-meta-036`, `L-meta-038` and `L-meta-044`. The construction of `L-meta-035`
(`LocalConstruct.main`) is restated with its instance format exposed, and its instances are
packaged in the shape of the hypotheses of those lemmas.

* `fixed_format` (W1): for `0 < n` and `0 < q` there is a `q`-local reduction of parity on `n`
  bits to partial MCSP all of whose outputs are instances of ONE format: size bound
  `(n + q - 1) / q - 1` and a partial table on `2 * ((n + q - 1) / q)` variables.
* `local_one_witness` (W2): the case `q = 1`, in the shape of the hypotheses of `L-meta-038`
  and `L-meta-044`.
* `local_witness` (W3): for `3 * q < n`, the hypotheses of `L-meta-036` hold for some map, and
  its output at the zero input is an instance, of size bound `(n + q - 1) / q - 1`.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalWitness

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.LocalConstruct

/-- W1. The reduction of `L-meta-035` with its format exposed. -/
theorem fixed_format : ∀ n q : ℕ, 0 < n → 0 < q →
    ∃ (w : (Fin n → Bool) → List Bool) (T : (Fin n → Bool) → List (Option Bool)),
      QueryLocal n q w ∧
      (∀ x : Fin n → Bool,
        w x = List.replicate ((n + q - 1) / q - 1) true ++ false :: encodePartial (T x) ∧
          (T x).length = 2 ^ (2 * ((n + q - 1) / q))) ∧
      ∀ x : Fin n → Bool,
        (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP := by
  intro n q hn hq
  have hpos : 0 < (n + q - 1) / q := Nat.div_pos (by omega) hq
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (n + q - 1) / q = m + 1 := ⟨(n + q - 1) / q - 1, by omega⟩
  have hm' : (n + q - 1) / q - 1 = m := by omega
  have hcover : ∀ j : Fin n, (j : ℕ) / q ≤ m := by
    intro j
    have h1 := Nat.div_add_mod (n + q - 1) q
    have h2 := Nat.mod_lt (n + q - 1) hq
    rw [hm] at h1
    have h3 : (j : ℕ) < q * (m + 1) := by
      have := j.isLt
      omega
    have h4 : (j : ℕ) / q < m + 1 := (Nat.div_lt_iff_lt_mul hq).2 (by rw [Nat.mul_comm]; exact h3)
    omega
  refine ⟨fun x => word m (blockPar n q x), fun x => table m (blockPar n q x), ?_, ?_, ?_⟩
  · intro j x
    refine ⟨Finset.univ.filter fun i : Fin n => (i : ℕ) / q = ix m ((j - (m + 1)) / 2),
      block_card n q _ hq, fun x' hx' => ?_⟩
    apply word_get
    apply blockPar_congr
    intro i hi
    exact hx' i (by simp [hi])
  · intro x
    rw [hm', hm]
    exact ⟨rfl, length_table m _⟩
  · intro x
    rw [word_mem_iff, par_blockPar]
    have e : (Finset.univ.filter fun j : Fin n => (j : ℕ) / q ≤ m ∧ x j = true)
        = Finset.univ.filter fun i : Fin n => x i = true := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hcover j, h⟩⟩
    rw [e]
    simp

/-- W2. The hypotheses of `L-meta-038` and `L-meta-044` hold for some map, for every `n ≥ 1`. -/
theorem local_one_witness : ∀ n : ℕ, 0 < n →
    ∃ (n' s : ℕ) (w : (Fin n → Bool) → List Bool) (T : (Fin n → Bool) → List (Option Bool)),
      QueryLocal n 1 w ∧
      (∀ x : Fin n → Bool,
        w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n') ∧
      ∀ x : Fin n → Bool,
        (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP := by
  intro n hn
  obtain ⟨w, T, h1, h2, h3⟩ := fixed_format n 1 hn Nat.one_pos
  exact ⟨_, _, w, T, h1, h2, h3⟩

/-- W2 with the format named: bound `n - 1`, tables on `2 * n` variables. -/
theorem local_one_witness_explicit : ∀ n : ℕ, 0 < n →
    ∃ (w : (Fin n → Bool) → List Bool) (T : (Fin n → Bool) → List (Option Bool)),
      QueryLocal n 1 w ∧
      (∀ x : Fin n → Bool,
        w x = List.replicate (n - 1) true ++ false :: encodePartial (T x) ∧
          (T x).length = 2 ^ (2 * n)) ∧
      ∀ x : Fin n → Bool,
        (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP := by
  intro n hn
  have h := fixed_format n 1 hn Nat.one_pos
  have e : (n + 1 - 1) / 1 = n := by simp
  rw [e] at h
  exact h

/-- W3, with the bound at the zero input named. The hypotheses of `L-meta-036` hold for some
map, and its output at the zero input is an instance of size bound `(n + q - 1) / q - 1`. -/
theorem local_witness_explicit : ∀ n q : ℕ, 0 < q → 3 * q < n →
    ∃ (M : ℕ) (w : (Fin n → Bool) → List Bool),
      QueryLocal n q w ∧
      (∀ x : Fin n → Bool, (w x).length ≤ M) ∧
      (∀ x : Fin n → Bool,
        (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP) ∧
      ∃ (n' : ℕ) (T : List (Option Bool)),
        w (fun _ : Fin n => false)
          = List.replicate ((n + q - 1) / q - 1) true ++ false :: encodePartial T ∧
        T.length = 2 ^ n' := by
  intro n q hq hn
  obtain ⟨w, T, h1, h2, h3⟩ := fixed_format n q (by omega) hq
  refine ⟨(n + q - 1) / q - 1 + (2 * 2 ^ (2 * ((n + q - 1) / q)) + 1), w, h1, ?_, h3,
    _, T _, (h2 _).1, (h2 _).2⟩
  intro x
  rw [(h2 x).1, List.length_append, List.length_replicate, List.length_cons,
    LocalFormat.length_encodePartial, (h2 x).2]

/-- W3. The hypotheses of `L-meta-036` hold for some map, and its output at the zero input is
an instance, so the conclusion of `L-meta-036` speaks of something. -/
theorem local_witness : ∀ n q : ℕ, 0 < q → 3 * q < n →
    ∃ (M : ℕ) (w : (Fin n → Bool) → List Bool),
      QueryLocal n q w ∧
      (∀ x : Fin n → Bool, (w x).length ≤ M) ∧
      (∀ x : Fin n → Bool,
        (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP) ∧
      ∃ (n' s : ℕ) (T : List (Option Bool)),
        w (fun _ : Fin n => false) = List.replicate s true ++ false :: encodePartial T ∧
        T.length = 2 ^ n' := by
  intro n q hq hn
  obtain ⟨M, w, h1, h2, h3, n', T, h4, h5⟩ := local_witness_explicit n q hq hn
  exact ⟨M, w, h1, h2, h3, n', _, T, h4, h5⟩

end PEqualNP.MetaComplexity.Helpers.LocalWitness
