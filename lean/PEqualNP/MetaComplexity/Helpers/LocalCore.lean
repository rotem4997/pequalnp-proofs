import PEqualNP.MetaComplexity.Helpers.Counting

/-!
# The core of the local reduction chain

Helper for `L-meta-030`. A `q`-local map that reduces parity on `n` bits to partial MCSP sends
the all-false input to a well-formed instance that is not a member and whose size field is
large. The proof is conditional on two statements, taken here as hypotheses: the depth-3 parity
bound (`L-meta-028`) and well-formedness at the all-false input (`L-meta-029`).

The argument: fix to `false` the at most `3 q` input positions that certify the length of the
output and its separator bit on the all-false input. On that subcube every output has the same
length and a separator no later than `s`, so the odd inputs of the subcube are covered by the
sets "the output is the instance with size field `s'` and a table consistent with `f`", over
`s' ≤ s` and `f` with a circuit of size `s'`. A non-member of such a set is excluded by at most
`2 q` positions, since the condition fails on at most two output bits. The parity bound then
bounds the number of pairs `(s', f)` from below, and the circuit count bounds it from above.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalCore

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-! ## The count of functions with small circuits -/

/-- The bound on the number of functions on `n` inputs with a circuit of size at most `s`. -/
def cnt (n s : ℕ) : ℕ := (s + 1) * ((3 * ((n + s + 2) * (n + s + 2))) ^ s * (n + s + 1))

theorem cnt_mono {n n' s s' : ℕ} (hn : n ≤ n') (hs : s ≤ s') : cnt n s ≤ cnt n' s' := by
  unfold cnt
  have hb : n + s + 2 ≤ n' + s' + 2 := by omega
  have ha : 3 * ((n + s + 2) * (n + s + 2)) ≤ 3 * ((n' + s' + 2) * (n' + s' + 2)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul hb hb)
  have h1 : 0 < 3 * ((n' + s' + 2) * (n' + s' + 2)) := by positivity
  exact Nat.mul_le_mul (by omega)
    (Nat.mul_le_mul ((Nat.pow_le_pow_left ha s).trans (Nat.pow_le_pow_right h1 hs)) (by omega))

/-- Few functions have small circuits. -/
theorem count_le (n s : ℕ) :
    {f : (Fin n → Bool) → Bool | HasCircuitSize n f s}.ncard ≤
      (s + 1) * ((3 * ((n + s + 2) * (n + s + 2))) ^ s * (n + s + 1)) := by
  classical
  let φ : (Σ t : Fin (s + 1), Code (n + s) t) → ((Fin n → Bool) → Bool) := fun p => sem n p.2
  have hsub : {f : (Fin n → Bool) → Bool | HasCircuitSize n f s} ⊆ Set.range φ := by
    intro f hf
    obtain ⟨t, c, hc⟩ := exists_code n s f hf
    exact ⟨⟨t, c⟩, hc⟩
  have h1 : {f : (Fin n → Bool) → Bool | HasCircuitSize n f s}.ncard ≤ (Set.range φ).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : (Set.range φ).ncard ≤ Fintype.card (Σ t : Fin (s + 1), Code (n + s) t) := by
    rw [← Set.image_univ]
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  have hterm : ∀ t : Fin (s + 1), Fintype.card (Code (n + s) t)
      ≤ (3 * ((n + s + 2) * (n + s + 2))) ^ s * (n + s + 1) := by
    intro t
    have e : Fintype.card (Code (n + s) t)
        = (3 * ((n + s + 2) * (n + s + 2))) ^ (t : ℕ) * (n + s + 1) := by
      simp [Code, GCode]
    rw [e]
    have h0 : 0 < 3 * ((n + s + 2) * (n + s + 2)) := by positivity
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right h0 (by omega))
  have h3 : Fintype.card (Σ t : Fin (s + 1), Code (n + s) t)
      ≤ (s + 1) * ((3 * ((n + s + 2) * (n + s + 2))) ^ s * (n + s + 1)) := by
    rw [Fintype.card_sigma]
    calc (Finset.univ.sum fun t : Fin (s + 1) => Fintype.card (Code (n + s) t))
        ≤ Finset.univ.sum fun _ : Fin (s + 1) =>
            (3 * ((n + s + 2) * (n + s + 2))) ^ s * (n + s + 1) :=
          Finset.sum_le_sum (fun t _ => hterm t)
      _ = (s + 1) * ((3 * ((n + s + 2) * (n + s + 2))) ^ s * (n + s + 1)) := by simp
  exact h1.trans (h2.trans h3)

/-! ## The code of a partial table, bit by bit -/

theorem enc_none (T : List (Option Bool)) :
    encodePartial (none :: T) = false :: false :: encodePartial T := by
  simp [encodePartial]

theorem enc_some (b : Bool) (T : List (Option Bool)) :
    encodePartial (some b :: T) = true :: b :: encodePartial T := by
  simp [encodePartial]

theorem length_enc (T : List (Option Bool)) : (encodePartial T).length = 2 * T.length := by
  induction T with
  | nil => rfl
  | cons o T ih =>
    cases o with
    | none => rw [enc_none]; simp only [List.length_cons, ih]; omega
    | some b => rw [enc_some]; simp only [List.length_cons, ih]; omega

theorem get_cc (a b : Bool) (r : List Bool) (i : ℕ) :
    (a :: b :: r)[2 * (i + 1)]? = r[2 * i]? ∧ (a :: b :: r)[2 * (i + 1) + 1]? = r[2 * i + 1]? := by
  have e : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
  rw [e]
  constructor <;> simp

/-- A code has no pair `false, true`, and a pair `true, b` is the entry `some b`. -/
theorem enc_get (T : List (Option Bool)) : ∀ i : ℕ,
    ((encodePartial T)[2 * i]? = some false → (encodePartial T)[2 * i + 1]? = some true → False) ∧
    (∀ b : Bool, (encodePartial T)[2 * i]? = some true → (encodePartial T)[2 * i + 1]? = some b →
      T.getD i none = some b) := by
  induction T with
  | nil => intro i; simp [encodePartial]
  | cons o T ih =>
    intro i
    cases i with
    | zero =>
      cases o with
      | none => simp [enc_none]
      | some c => simp [enc_some]
    | succ i =>
      cases o with
      | none =>
        rw [enc_none, (get_cc _ _ _ i).1, (get_cc _ _ _ i).2, List.getD_cons_succ]
        exact ih i
      | some c =>
        rw [enc_some, (get_cc _ _ _ i).1, (get_cc _ _ _ i).2, List.getD_cons_succ]
        exact ih i

/-- A string of even length with no pair `false, true` is a code. -/
theorem dec_exists : ∀ (K : ℕ) (r : List Bool), r.length = 2 * K →
    (∀ i : ℕ, r[2 * i]? = some false → r[2 * i + 1]? = some true → False) →
    ∃ T : List (Option Bool), r = encodePartial T ∧ T.length = K ∧
      ∀ (i : ℕ) (b : Bool), T.getD i none = some b →
        r[2 * i]? = some true ∧ r[2 * i + 1]? = some b := by
  intro K
  induction K with
  | zero =>
    intro r hr _
    have : r = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    exact ⟨[], rfl, rfl, by simp⟩
  | succ K ih =>
    intro r hr h
    match r, hr, h with
    | [], hr, _ => simp at hr
    | [a], hr, _ => simp at hr; omega
    | a :: b :: r', hr, h =>
      have hr' : r'.length = 2 * K := by simp only [List.length_cons] at hr; omega
      have h' : ∀ i : ℕ, r'[2 * i]? = some false → r'[2 * i + 1]? = some true → False := by
        intro i h1 h2
        apply h (i + 1)
        · rw [(get_cc a b r' i).1]; exact h1
        · rw [(get_cc a b r' i).2]; exact h2
      obtain ⟨T, e, hl, hc⟩ := ih r' hr' h'
      cases a with
      | false =>
        have hb : b = false := by
          cases b with
          | false => rfl
          | true => exact (h 0 (by simp) (by simp)).elim
        subst hb
        refine ⟨none :: T, by rw [enc_none, ← e], by simp [hl], ?_⟩
        intro i c hic
        cases i with
        | zero => simp at hic
        | succ i =>
          rw [List.getD_cons_succ] at hic
          rw [(get_cc _ _ r' i).1, (get_cc _ _ r' i).2]
          exact hc i c hic
      | true =>
        refine ⟨some b :: T, by rw [enc_some, ← e], by simp [hl], ?_⟩
        intro i c hic
        cases i with
        | zero =>
          simp only [List.getD_cons_zero, Option.some.injEq] at hic
          subst hic
          simp
        | succ i =>
          rw [List.getD_cons_succ] at hic
          rw [(get_cc _ _ r' i).1, (get_cc _ _ r' i).2]
          exact hc i c hic

/-! ## The instance format, bit by bit -/

theorem get_fmt (s : ℕ) (r : List Bool) :
    (∀ j : ℕ, j < s → (List.replicate s true ++ false :: r)[j]? = some true) ∧
    (List.replicate s true ++ false :: r)[s]? = some false ∧
    ∀ k : ℕ, (List.replicate s true ++ false :: r)[s + 1 + k]? = r[k]? := by
  refine ⟨fun j hj => ?_, ?_, fun k => ?_⟩
  · rw [List.getElem?_append_left (by simpa using hj)]
    simp [hj]
  · rw [List.getElem?_append_right (by simp)]
    simp
  · rw [List.getElem?_append_right (by simp; omega)]
    have e : s + 1 + k - (List.replicate s true).length = k + 1 := by
      simp only [List.length_replicate]; omega
    rw [e]
    simp

theorem fmt_of_bits (s : ℕ) (v : List Bool) (h1 : ∀ j : ℕ, j < s → v[j]? = some true)
    (h2 : v[s]? = some false) : v = List.replicate s true ++ false :: v.drop (s + 1) := by
  obtain ⟨g1, g2, g3⟩ := get_fmt s (v.drop (s + 1))
  apply List.ext_getElem?
  intro i
  rcases lt_trichotomy i s with h | h | h
  · rw [h1 i h, g1 i h]
  · subst h; rw [h2, g2]
  · obtain ⟨k, rfl⟩ : ∃ k, i = s + 1 + k := ⟨i - (s + 1), by omega⟩
    rw [g3 k, List.getElem?_drop]

/-- The string `v` is the instance with size field `s` and a table on `nn` inputs with which
`f` is consistent. -/
def Fmt (s nn : ℕ) (f : (Fin nn → Bool) → Bool) (v : List Bool) : Prop :=
  ∃ T : List (Option Bool), v = List.replicate s true ++ false :: encodePartial T ∧
    T.length = 2 ^ nn ∧ Consistent nn T f

/-- A string of the right length that is not such an instance fails on at most two bits. -/
theorem fmt_witness (s nn : ℕ) (f : (Fin nn → Bool) → Bool) (v : List Bool)
    (hlen : v.length = s + 1 + 2 * 2 ^ nn) (hv : ¬ Fmt s nn f v) :
    ∃ (p1 p2 : ℕ) (b1 b2 : Bool), v[p1]? = some b1 ∧ v[p2]? = some b2 ∧
      ∀ v' : List Bool, v'[p1]? = some b1 → v'[p2]? = some b2 → ¬ Fmt s nn f v' := by
  by_cases c1 : ∃ j, j < s ∧ v[j]? = some false
  · obtain ⟨j, hj, hjv⟩ := c1
    refine ⟨j, j, false, false, hjv, hjv, ?_⟩
    rintro v' a1 - ⟨T, rfl, -, -⟩
    rw [(get_fmt s _).1 j hj] at a1
    simp at a1
  by_cases c2 : v[s]? = some true
  · refine ⟨s, s, true, true, c2, c2, ?_⟩
    rintro v' a1 - ⟨T, rfl, -, -⟩
    rw [(get_fmt s _).2.1] at a1
    simp at a1
  have h1 : ∀ j : ℕ, j < s → v[j]? = some true := by
    intro j hj
    have hj' : j < v.length := by omega
    obtain ⟨b, hb⟩ : ∃ b, v[j]? = some b := ⟨v[j], List.getElem?_eq_getElem hj'⟩
    cases b with
    | false => exact (c1 ⟨j, hj, hb⟩).elim
    | true => exact hb
  have h2 : v[s]? = some false := by
    have hs' : s < v.length := by omega
    obtain ⟨b, hb⟩ : ∃ b, v[s]? = some b := ⟨v[s], List.getElem?_eq_getElem hs'⟩
    cases b with
    | false => exact hb
    | true => exact (c2 hb).elim
  have hv0 := fmt_of_bits s v h1 h2
  obtain ⟨r, hr⟩ : ∃ r, r = v.drop (s + 1) := ⟨_, rfl⟩
  rw [← hr] at hv0
  have hrl : r.length = 2 * 2 ^ nn := by rw [hr, List.length_drop, hlen]; omega
  have g3 := (get_fmt s r).2.2
  by_cases c3 : ∃ i, r[2 * i]? = some false ∧ r[2 * i + 1]? = some true
  · obtain ⟨i, hi1, hi2⟩ := c3
    refine ⟨s + 1 + 2 * i, s + 1 + (2 * i + 1), false, true, ?_, ?_, ?_⟩
    · rw [hv0, g3]; exact hi1
    · rw [hv0, g3]; exact hi2
    · rintro v' a1 a2 ⟨T, rfl, -, -⟩
      rw [(get_fmt s _).2.2] at a1 a2
      exact (enc_get T i).1 a1 a2
  obtain ⟨T, hT, hTl, hTc⟩ := dec_exists (2 ^ nn) r hrl (fun i a b => c3 ⟨i, a, b⟩)
  have hnc : ¬ Consistent nn T f := fun hc => hv ⟨T, by rw [← hT]; exact hv0, hTl, hc⟩
  unfold Consistent at hnc
  push Not at hnc
  obtain ⟨x, b, hxb, hne⟩ := hnc
  obtain ⟨e1, e2⟩ := hTc _ _ hxb
  have hb : b = !f x := by
    cases b <;> cases hf : f x <;> first | rfl | exact (hne hf).elim
  refine ⟨s + 1 + 2 * tableIndex x, s + 1 + (2 * tableIndex x + 1), true, !f x, ?_, ?_, ?_⟩
  · rw [hv0, g3]; exact e1
  · rw [hv0, g3, ← hb]; exact e2
  · rintro v' a1 a2 ⟨T', rfl, -, hc'⟩
    rw [(get_fmt s _).2.2] at a1 a2
    have h3 := hc' x _ ((enc_get T' _).2 _ a1 a2)
    cases hf : f x <;> rw [hf] at h3 <;> exact absurd h3 (by decide)

/-! ## A subcube as a cube -/

/-- Fixing the positions of `U` to `false` leaves a cube on the other positions: the weight is
kept, and a set of positions of the big cube pulls back to a set that is no larger. -/
theorem subcube (n : ℕ) (U : Finset (Fin n)) :
    ∃ (m : ℕ) (ext : (Fin m → Bool) → (Fin n → Bool)),
      n ≤ m + U.card ∧ (∀ (y : Fin m → Bool), ∀ i ∈ U, ext y i = false) ∧
      (∀ y : Fin m → Bool, (Finset.univ.filter fun i : Fin n => ext y i = true).card =
        (Finset.univ.filter fun j : Fin m => y j = true).card) ∧
      ∀ S : Finset (Fin n), ∃ V : Finset (Fin m), V.card ≤ S.card ∧
        ∀ y y' : Fin m → Bool, (∀ j ∈ V, y' j = y j) → ∀ i ∈ S, ext y' i = ext y i := by
  classical
  let e : {i : Fin n // i ∉ U} ≃ Fin (Fintype.card {i : Fin n // i ∉ U}) := Fintype.equivFin _
  have hinj : Function.Injective (fun j => (e.symm j).1) :=
    fun a b h => e.symm.injective (Subtype.ext h)
  refine ⟨_, fun y i => if h : i ∈ U then false else y (e ⟨i, h⟩), ?_, ?_, ?_, ?_⟩
  · have h := Fintype.card_subtype_compl (fun i : Fin n => i ∈ U)
    simp only [Fintype.card_fin, Fintype.card_coe] at h
    have hle := Finset.card_le_univ U
    simp only [Fintype.card_fin] at hle
    omega
  · intro y i hi
    simp [hi]
  · intro y
    rw [← Finset.card_image_of_injective _ hinj]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      by_cases hi : i ∈ U
      · simp [hi] at h
      · rw [dite_eq_right hi] at h
        exact ⟨e ⟨i, hi⟩, h, by simp⟩
    · rintro ⟨j, hj, rfl⟩
      rw [dite_eq_right (e.symm j).2]
      simpa using hj
  · intro S
    refine ⟨Finset.univ.filter (fun j => (e.symm j).1 ∈ S), ?_, ?_⟩
    · apply Finset.card_le_card_of_injOn (fun j => (e.symm j).1)
      · intro j hj
        simpa using hj
      · exact hinj.injOn
    · intro y y' h i hi
      by_cases hiU : i ∈ U
      · simp [hiU]
      · simp only [dite_eq_right hiU]
        exact h _ (by simp [hi])

/-! ## The index of the cover -/

/-- The number of inputs of a table in an instance of length `L` with size field `s`. -/
def nn (L s : ℕ) : ℕ := Nat.log 2 ((L - (s + 1)) / 2)

theorem nn_le (L s : ℕ) : nn L s ≤ Nat.log 2 L :=
  Nat.log_mono_right ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))

theorem nn_eq (s k : ℕ) : nn (s + 1 + 2 * 2 ^ k) s = k := by
  unfold nn
  have e : (s + 1 + 2 * 2 ^ k - (s + 1)) / 2 = 2 ^ k := by omega
  rw [e, Nat.log_pow (by norm_num)]

/-- The pairs: a size field `s ≤ s0` and a function with a circuit of size `s` on the number of
inputs that an instance of length `L` with size field `s` has. -/
abbrev Idx (L s0 : ℕ) : Type :=
  Σ s : Fin (s0 + 1), {f : (Fin (nn L (s : ℕ)) → Bool) → Bool // HasCircuitSize (nn L s) f s}

open Classical in
noncomputable instance (L s0 : ℕ) : Fintype (Idx L s0) := inferInstance

theorem card_idx (L s0 D : ℕ) (h : Nat.log 2 L ≤ D) :
    Fintype.card (Idx L s0) ≤ (s0 + 1) * cnt D s0 := by
  classical
  have hterm : ∀ s : Fin (s0 + 1),
      Fintype.card {f : (Fin (nn L (s : ℕ)) → Bool) → Bool // HasCircuitSize (nn L s) f s}
        ≤ cnt D s0 := by
    intro s
    have e : Fintype.card {f : (Fin (nn L (s : ℕ)) → Bool) → Bool // HasCircuitSize (nn L s) f s}
        = {f : (Fin (nn L (s : ℕ)) → Bool) → Bool | HasCircuitSize (nn L s) f s}.ncard := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_coe_set_eq
        {f : (Fin (nn L (s : ℕ)) → Bool) → Bool | HasCircuitSize (nn L s) f s}
    rw [e]
    exact (count_le _ _).trans (cnt_mono ((nn_le L s).trans h) (by omega))
  unfold Idx
  rw [Fintype.card_sigma]
  calc (Finset.univ.sum fun s : Fin (s0 + 1) =>
          Fintype.card {f : (Fin (nn L (s : ℕ)) → Bool) → Bool // HasCircuitSize (nn L s) f s})
      ≤ Finset.univ.sum fun _ : Fin (s0 + 1) => cnt D s0 :=
        Finset.sum_le_sum (fun s _ => hterm s)
    _ = (s0 + 1) * cnt D s0 := by simp

/-! ## The core -/

/-- The core of the chain, from the depth-3 parity bound `hA` (`L-meta-028`) and
well-formedness at the all-false input `hB` (`L-meta-029`). -/
theorem core_of
    (hA : ∀ (m k N : ℕ) (E : Fin N → Finset (Fin m → Bool)), 0 < k → 0 < m →
      (∀ (a : Fin N) (x : Fin m → Bool), x ∉ E a → ∃ V : Finset (Fin m), V.card ≤ k ∧
        ∀ y : Fin m → Bool, (∀ i ∈ V, y i = x i) → y ∉ E a) →
      (∀ x : Fin m → Bool, (∃ a : Fin N, x ∈ E a) ↔
        (Finset.univ.filter fun i : Fin m => x i = true).card % 2 = 1) →
      2 ^ m ≤ N * (4 * k * 2 ^ (m - m / (2 * k))))
    (hB : ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool),
      PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) →
      (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 →
        w x ∈ PEqualNP.MetaComplexity.PartialMCSP) →
      2 * q * (Nat.log 2 M + 2) < n →
      ∃ (n' s : ℕ) (T : List (Option Bool)),
        w (fun _ : Fin n => false) =
          List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T ∧
        T.length = 2 ^ n') :
    ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q →
      PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) →
      (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔
        w x ∈ PEqualNP.MetaComplexity.PartialMCSP) →
      2 * q * (Nat.log 2 M + 2) < n →
      ∃ (n' s : ℕ) (T : List (Option Bool)),
        w (fun _ : Fin n => false) =
          List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T ∧
        T.length = 2 ^ n' ∧
        (¬ ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T f ∧
          PEqualNP.MetaComplexity.HasCircuitSize n' f s) ∧
        2 ^ ((n - 3 * q) / (4 * q)) ≤ 8 * q * ((s + 1) * ((s + 1) *
          ((3 * ((Nat.log 2 M + s + 2) * (Nat.log 2 M + s + 2))) ^ s *
            (Nat.log 2 M + s + 1)))) := by
  classical
  intro n q M w hq hloc hlen hcor hn
  obtain ⟨n0, s0, T0, hz, hT0⟩ := hB n q M w hloc hlen (fun x hx => (hcor x).mp hx) hn
  refine ⟨n0, s0, T0, hz, hT0, ?_, ?_⟩
  · rintro ⟨f, hc, hs⟩
    have hmem : w (fun _ : Fin n => false) ∈ PartialMCSP := ⟨n0, s0, T0, hz, hT0, f, hc, hs⟩
    have := (hcor _).mpr hmem
    simp at this
  -- the all-false input and the length of its image
  obtain ⟨z, hzdef⟩ : ∃ z : Fin n → Bool, z = fun _ => false := ⟨_, rfl⟩
  rw [← hzdef] at hz
  obtain ⟨L0, hL0⟩ : ∃ L0, L0 = (w z).length := ⟨_, rfl⟩
  have hL0' : L0 = s0 + 1 + 2 * 2 ^ n0 := by
    rw [hL0, hz]
    simp only [List.length_append, List.length_replicate, List.length_cons, length_enc, hT0]
    omega
  have hL0M : L0 ≤ M := hL0 ▸ hlen z
  -- the three certificates
  obtain ⟨S1, c1, h1⟩ := hloc (L0 - 1) z
  obtain ⟨S2, c2, h2⟩ := hloc L0 z
  obtain ⟨S3, c3, h3⟩ := hloc s0 z
  have hU : (S1 ∪ S2 ∪ S3).card ≤ 3 * q := by
    have a := Finset.card_union_le (S1 ∪ S2) S3
    have b := Finset.card_union_le S1 S2
    omega
  obtain ⟨m, ext, hm, hextU, hpar, hV⟩ := subcube n (S1 ∪ S2 ∪ S3)
  have hzi : ∀ i : Fin n, z i = false := fun i => by rw [hzdef]
  -- on the subcube: constant length, separator bit false
  have len : ∀ y : Fin m → Bool, (w (ext y)).length = L0 := by
    intro y
    have a1 := h1 (ext y) (fun i hi => by
      rw [hzi, hextU y i (by simp [hi])])
    have a2 := h2 (ext y) (fun i hi => by
      rw [hzi, hextU y i (by simp [hi])])
    have b1 : L0 ≤ (w (ext y)).length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega), eq_comm, List.getElem?_eq_none_iff] at a1
      omega
    have b2 : (w (ext y)).length ≤ L0 := by
      rw [List.getElem?_eq_none (l := w z) (by omega), List.getElem?_eq_none_iff] at a2
      exact a2
    omega
  have sep : ∀ y : Fin m → Bool, (w (ext y))[s0]? = some false := by
    intro y
    have a3 := h3 (ext y) (fun i hi => by
      rw [hzi, hextU y i (by simp [hi])])
    rw [a3, hz]
    exact (get_fmt s0 _).2.1
  -- the cover
  let E : Idx L0 s0 → Finset (Fin m → Bool) := fun a =>
    Finset.univ.filter (fun y => Fmt a.1 (nn L0 a.1) a.2.1 (w (ext y)))
  let eqv : Idx L0 s0 ≃ Fin (Fintype.card (Idx L0 s0)) := Fintype.equivFin _
  have hm0 : 0 < m := by
    have : 2 * q * 2 ≤ 2 * q * (Nat.log 2 M + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hfin := hA m (2 * q) (Fintype.card (Idx L0 s0)) (fun a => E (eqv.symm a)) (by omega) hm0
    (by
      intro a y hy
      obtain ⟨⟨s, f⟩, hsf⟩ : ∃ p, p = eqv.symm a := ⟨_, rfl⟩
      simp only [← hsf] at hy ⊢
      have hy' : ¬ Fmt s (nn L0 s) f.1 (w (ext y)) :=
        fun h => hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      by_cases hl : L0 = (s : ℕ) + 1 + 2 * 2 ^ nn L0 s
      · obtain ⟨p1, p2, b1, b2, e1, e2, hw⟩ :=
          fmt_witness s (nn L0 s) f.1 (w (ext y)) ((len y).trans hl) hy'
        obtain ⟨Sa, ca, ha⟩ := hloc p1 (ext y)
        obtain ⟨Sb, cb, hb⟩ := hloc p2 (ext y)
        obtain ⟨V, cV, hVV⟩ := hV (Sa ∪ Sb)
        have cab := Finset.card_union_le Sa Sb
        refine ⟨V, by omega, fun y' hy'' hmem => ?_⟩
        have agree := hVV y y' hy''
        exact hw (w (ext y'))
          ((ha (ext y') (fun i hi => agree i (Finset.mem_union_left _ hi))).trans e1)
          ((hb (ext y') (fun i hi => agree i (Finset.mem_union_right _ hi))).trans e2)
          (Finset.mem_filter.mp hmem).2
      · refine ⟨∅, by simp, fun y' _ hmem => ?_⟩
        obtain ⟨T, e, hTl, -⟩ := (Finset.mem_filter.mp hmem).2
        have hlen' := len y'
        rw [e] at hlen'
        simp only [List.length_append, List.length_replicate, List.length_cons, length_enc,
          hTl] at hlen'
        omega)
    (by
      intro y
      constructor
      · rintro ⟨a, ha⟩
        obtain ⟨T, e, hTl, hc⟩ := (Finset.mem_filter.mp ha).2
        have hmem : w (ext y) ∈ PartialMCSP :=
          ⟨_, _, T, e, hTl, (eqv.symm a).2.1, hc, (eqv.symm a).2.2⟩
        rw [← hpar y]
        exact (hcor _).mpr hmem
      · intro hodd
        obtain ⟨n'', s, T, e, hTl, f, hc, hs⟩ := (hcor (ext y)).mp (by rw [hpar y]; exact hodd)
        have hs0 : s ≤ s0 := by
          by_contra hgt
          have a := (get_fmt s (encodePartial T)).1 s0 (by omega)
          rw [← e, sep y] at a
          simp at a
        have hLs : L0 = s + 1 + 2 * 2 ^ n'' := by
          have hlen' := len y
          rw [e] at hlen'
          simp only [List.length_append, List.length_replicate, List.length_cons, length_enc,
            hTl] at hlen'
          omega
        have hnn : n'' = nn L0 s := by rw [hLs, nn_eq]
        subst hnn
        refine ⟨eqv ⟨⟨s, by omega⟩, ⟨f, hs⟩⟩, ?_⟩
        show y ∈ E (eqv.symm (eqv _))
        rw [Equiv.symm_apply_apply]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, T, e, hTl, hc⟩)
  -- the arithmetic
  have hN := card_idx L0 s0 (Nat.log 2 M) (Nat.log_mono_right hL0M)
  obtain ⟨N, hNdef⟩ : ∃ N, N = Fintype.card (Idx L0 s0) := ⟨_, rfl⟩
  rw [← hNdef] at hfin hN
  obtain ⟨d, hd⟩ : ∃ d, d = m / (2 * (2 * q)) := ⟨_, rfl⟩
  rw [← hd] at hfin
  have hdm : d ≤ m := hd ▸ Nat.div_le_self _ _
  have h2 : 2 ^ m = 2 ^ (m - d) * 2 ^ d := by
    rw [← pow_add]; congr 1; omega
  have h3 : 2 ^ d ≤ 8 * q * N := by
    have h4 : 2 ^ (m - d) * 2 ^ d ≤ 2 ^ (m - d) * (8 * q * N) := by
      rw [← h2]
      calc 2 ^ m ≤ N * (4 * (2 * q) * 2 ^ (m - d)) := hfin
        _ = 2 ^ (m - d) * (8 * q * N) := by ring
    exact Nat.le_of_mul_le_mul_left h4 (by positivity)
  have h5 : (n - 3 * q) / (4 * q) ≤ d := by
    rw [hd, show 4 * q = 2 * (2 * q) by ring]
    exact Nat.div_le_div_right (by omega)
  calc 2 ^ ((n - 3 * q) / (4 * q)) ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) h5
    _ ≤ 8 * q * N := h3
    _ ≤ 8 * q * ((s0 + 1) * cnt (Nat.log 2 M) s0) := Nat.mul_le_mul_left _ hN

end PEqualNP.MetaComplexity.Helpers.LocalCore
