import PEqualNP.Defs.MetaComplexityLocal

/-!
# The instance format of partial MCSP is a local condition

Helper for the local reduction chain. An instance of partial MCSP is
`replicate s true ++ false :: encodePartial T`. For a fixed separator position `s`, being of
this shape is a conjunction of conditions each on at most two positions of the word
(`formed_iff`), so its failure is witnessed by two positions (`not_formed_witness`). For a
`QueryLocal` map this turns into certificates on the input side:

* `cert_bit`, `cert_two`: one or two output positions are fixed by `q` or `2 * q` inputs;
* `cert_false`: "output position `j` is `false`" has a certificate of `q` inputs;
* `cert_length`: the output length has a certificate of `2 * q` inputs;
* `cert_not_formed`: "not an instance with separator `s`" has a certificate of `2 * q` inputs;
* `formed_of_odd`: a local map sending the odd inputs into partial MCSP sends the all-false
  input to a word of the instance format.

This file imports only the definitions, so it can be imported next to any other helper.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalFormat

open PEqualNP.MetaComplexity

/-- The word `u` has the instance format with separator at position `s`: `s` times `true`, one
`false`, then the code of some partial table (of any length). -/
def Formed (s : ℕ) (u : List Bool) : Prop :=
  ∃ T : List (Option Bool), u = List.replicate s true ++ false :: encodePartial T

/-- The two symbols `p`, `r` at positions `2 i`, `2 i + 1` of a word are compatible with a code
of a partial table: both absent, or `false, false`, or `true` followed by a bit. -/
def PairOK (p r : Option Bool) : Prop :=
  (p = none ∧ r = none) ∨ (p = some false ∧ r = some false) ∨ (p = some true ∧ r ≠ none)

theorem encodePartial_cons (o : Option Bool) (T : List (Option Bool)) :
    encodePartial (o :: T) =
      (match o with
        | none => [false, false]
        | some b => [true, b]) ++ encodePartial T := by
  cases o <;> simp [encodePartial, List.flatMap_cons]

theorem length_encodePartial (T : List (Option Bool)) :
    (encodePartial T).length = 2 * T.length := by
  induction T with
  | nil => rfl
  | cons o T ih =>
    rw [encodePartial_cons, List.length_append, ih, List.length_cons]
    cases o <;> simp <;> omega

/-- Every pair of a code is compatible. -/
theorem pairOK_encodePartial : ∀ (T : List (Option Bool)) (i : ℕ),
    PairOK (encodePartial T)[2 * i]? (encodePartial T)[2 * i + 1]?
  | [], i => Or.inl (by simp [encodePartial])
  | o :: T, 0 => by
    rw [encodePartial_cons]
    cases o with
    | none => simp [PairOK]
    | some b => cases b <;> simp [PairOK]
  | o :: T, i + 1 => by
    have h := pairOK_encodePartial T i
    rw [encodePartial_cons, show 2 * (i + 1) = 2 * i + 2 by ring,
      show 2 * i + 2 + 1 = 2 * i + 1 + 2 by ring]
    cases o <;> simpa using h

/-- A word all of whose pairs are compatible is a code. -/
theorem exists_of_pairOK : ∀ v : List Bool, (∀ i : ℕ, PairOK v[2 * i]? v[2 * i + 1]?) →
    ∃ T : List (Option Bool), v = encodePartial T
  | [], _ => ⟨[], rfl⟩
  | [a], h => by
    have h0 := h 0
    simp [PairOK] at h0
  | a :: b :: v, h => by
    obtain ⟨T, hT⟩ := exists_of_pairOK v (fun i => by
      have h1 := h (i + 1)
      rw [show 2 * (i + 1) = 2 * i + 2 by ring,
        show 2 * i + 2 + 1 = 2 * i + 1 + 2 by ring] at h1
      simpa using h1)
    have h0 := h 0
    cases a with
    | false =>
      cases b with
      | false => exact ⟨none :: T, by subst hT; simp [encodePartial_cons]⟩
      | true => simp [PairOK] at h0
    | true => exact ⟨some b :: T, by subst hT; simp [encodePartial_cons]⟩

theorem getElem?_replicate_append_lt (s j : ℕ) (l : List Bool) (h : j < s) :
    (List.replicate s true ++ l)[j]? = some true := by
  have h' : j < (List.replicate s true).length := by simpa using h
  rw [List.getElem?_append_left h']
  simp [h]

theorem getElem?_replicate_append_add (s k : ℕ) (l : List Bool) :
    (List.replicate s true ++ l)[s + k]? = l[k]? := by
  have h : (List.replicate s true).length ≤ s + k := by simp
  rw [List.getElem?_append_right h]
  simp

theorem eq_replicate_append_drop : ∀ (s : ℕ) (u : List Bool),
    (∀ j : ℕ, j < s → u[j]? = some true) → u = List.replicate s true ++ u.drop s
  | 0, u, _ => by simp
  | s + 1, [], h => by
    have h0 := h 0 (by omega)
    simp at h0
  | s + 1, a :: u, h => by
    have h0 := h 0 (by omega)
    simp at h0
    subst h0
    have ih := eq_replicate_append_drop s u (fun j hj => by
      have h1 := h (j + 1) (by omega)
      simpa using h1)
    simpa [List.replicate_succ] using ih

/-- The instance format with separator `s`, as a conjunction of conditions on one or two
positions each. -/
theorem formed_iff (s : ℕ) (u : List Bool) :
    Formed s u ↔ (∀ j : ℕ, j < s → u[j]? = some true) ∧ u[s]? = some false ∧
      ∀ i : ℕ, PairOK u[s + 1 + 2 * i]? u[s + 1 + 2 * i + 1]? := by
  constructor
  · rintro ⟨T, rfl⟩
    refine ⟨fun j hj => getElem?_replicate_append_lt s j _ hj, ?_, fun i => ?_⟩
    · have h := getElem?_replicate_append_add s 0 (false :: encodePartial T)
      rw [Nat.add_zero] at h
      rw [h]
      simp
    · have h1 := getElem?_replicate_append_add s (2 * i + 1) (false :: encodePartial T)
      have h2 := getElem?_replicate_append_add s (2 * i + 1 + 1) (false :: encodePartial T)
      rw [show s + 1 + 2 * i = s + (2 * i + 1) by ring,
        show s + (2 * i + 1) + 1 = s + (2 * i + 1 + 1) by ring, h1, h2]
      simpa using pairOK_encodePartial T i
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨hlt, hs⟩ := List.getElem?_eq_some_iff.1 h2
    obtain ⟨T, hT⟩ := exists_of_pairOK (u.drop (s + 1)) (fun i => by
      rw [List.getElem?_drop, List.getElem?_drop, ← Nat.add_assoc]
      exact h3 i)
    refine ⟨T, ?_⟩
    have e1 := eq_replicate_append_drop s u h1
    have e2 : u.drop s = false :: u.drop (s + 1) := by
      rw [List.drop_eq_getElem_cons hlt, hs]
    rw [← hT, ← e2]
    exact e1

/-- A word that is not an instance with separator `s` stays so whenever two of its positions
(possibly equal) are kept, whatever the rest and whatever the length. -/
theorem not_formed_witness (s : ℕ) (u : List Bool) (h : ¬ Formed s u) :
    ∃ j₁ j₂ : ℕ, ∀ u' : List Bool, u'[j₁]? = u[j₁]? → u'[j₂]? = u[j₂]? → ¬ Formed s u' := by
  rw [formed_iff] at h
  by_cases h1 : ∀ j : ℕ, j < s → u[j]? = some true
  · by_cases h2 : u[s]? = some false
    · have h3 : ¬ ∀ i : ℕ, PairOK u[s + 1 + 2 * i]? u[s + 1 + 2 * i + 1]? :=
        fun h3 => h ⟨h1, h2, h3⟩
      rw [not_forall] at h3
      obtain ⟨i, hi⟩ := h3
      exact ⟨s + 1 + 2 * i, s + 1 + 2 * i + 1, fun u' e1 e2 hf =>
        hi (by rw [← e1, ← e2]; exact ((formed_iff s u').1 hf).2.2 i)⟩
    · exact ⟨s, s, fun u' e1 _ hf => h2 (by rw [← e1]; exact ((formed_iff s u').1 hf).2.1)⟩
  · rw [not_forall] at h1
    obtain ⟨j, hj⟩ := h1
    rw [Classical.not_imp] at hj
    exact ⟨j, j, fun u' e1 _ hf =>
      hj.2 (by rw [← e1]; exact ((formed_iff s u').1 hf).1 j hj.1)⟩

/-- A word of the instance format with separator `s` and a table of length `m` has length
`s + 1 + 2 * m`. -/
theorem length_of_eq (s : ℕ) (T : List (Option Bool)) (u : List Bool)
    (h : u = List.replicate s true ++ false :: encodePartial T) :
    u.length = s + (2 * T.length + 1) := by
  rw [h, List.length_append, List.length_replicate, List.length_cons, length_encodePartial]

/-! ## Certificates for a local map -/

variable {n q : ℕ} {w : (Fin n → Bool) → List Bool}

/-- One output position: the definition, restated. -/
theorem cert_bit (h : QueryLocal n q w) (j : ℕ) (x : Fin n → Bool) :
    ∃ S : Finset (Fin n), S.card ≤ q ∧
      ∀ y : Fin n → Bool, (∀ i ∈ S, y i = x i) → (w y)[j]? = (w x)[j]? :=
  h j x

/-- Two output positions are fixed by `2 * q` input positions. -/
theorem cert_two (h : QueryLocal n q w) (j₁ j₂ : ℕ) (x : Fin n → Bool) :
    ∃ S : Finset (Fin n), S.card ≤ 2 * q ∧
      ∀ y : Fin n → Bool, (∀ i ∈ S, y i = x i) →
        (w y)[j₁]? = (w x)[j₁]? ∧ (w y)[j₂]? = (w x)[j₂]? := by
  obtain ⟨S₁, c₁, h₁⟩ := h j₁ x
  obtain ⟨S₂, c₂, h₂⟩ := h j₂ x
  refine ⟨S₁ ∪ S₂, ?_, fun y hy => ⟨?_, ?_⟩⟩
  · have := Finset.card_union_le S₁ S₂
    omega
  · exact h₁ y (fun i hi => hy i (Finset.mem_union_left _ hi))
  · exact h₂ y (fun i hi => hy i (Finset.mem_union_right _ hi))

/-- "Output position `j` is `false`" at `x` has a certificate of `q` input positions. -/
theorem cert_false (h : QueryLocal n q w) (j : ℕ) (x : Fin n → Bool)
    (hx : (w x)[j]? = some false) :
    ∃ S : Finset (Fin n), S.card ≤ q ∧
      ∀ y : Fin n → Bool, (∀ i ∈ S, y i = x i) → (w y)[j]? = some false := by
  obtain ⟨S, c, hS⟩ := h j x
  exact ⟨S, c, fun y hy => by rw [hS y hy, hx]⟩

/-- The output length at `x` has a certificate of `2 * q` input positions. -/
theorem cert_length (h : QueryLocal n q w) (x : Fin n → Bool) :
    ∃ S : Finset (Fin n), S.card ≤ 2 * q ∧
      ∀ y : Fin n → Bool, (∀ i ∈ S, y i = x i) → (w y).length = (w x).length := by
  obtain ⟨S, c, hS⟩ := cert_two h ((w x).length - 1) (w x).length x
  refine ⟨S, c, fun y hy => ?_⟩
  obtain ⟨e1, e2⟩ := hS y hy
  have hle : (w y).length ≤ (w x).length := by
    have h0 : (w y)[(w x).length]? = none := by
      rw [e2]
      exact List.getElem?_eq_none_iff.2 (Nat.le_refl _)
    exact List.getElem?_eq_none_iff.1 h0
  have hge : (w x).length ≤ (w y).length := by
    by_contra hlt
    have h0 : (w y)[(w x).length - 1]? = none := List.getElem?_eq_none_iff.2 (by omega)
    rw [e1] at h0
    have h1 := List.getElem?_eq_none_iff.1 h0
    omega
  omega

/-- "Not an instance with separator `s`" at `x` has a certificate of `2 * q` input positions:
every input agreeing with `x` on it is also sent to a word that is not an instance with
separator `s`. No assumption on the output lengths. -/
theorem cert_not_formed (h : QueryLocal n q w) (s : ℕ) (x : Fin n → Bool)
    (hx : ¬ Formed s (w x)) :
    ∃ S : Finset (Fin n), S.card ≤ 2 * q ∧
      ∀ y : Fin n → Bool, (∀ i ∈ S, y i = x i) → ¬ Formed s (w y) := by
  obtain ⟨j₁, j₂, hj⟩ := not_formed_witness s (w x) hx
  obtain ⟨S, c, hS⟩ := cert_two h j₁ j₂ x
  exact ⟨S, c, fun y hy => hj (w y) (hS y hy).1 (hS y hy).2⟩

/-- The input with a single `true`, at position `j`. -/
def unit {n : ℕ} (j : Fin n) : Fin n → Bool := fun i => decide (i = j)

theorem unit_odd {n : ℕ} (j : Fin n) :
    (Finset.univ.filter fun i : Fin n => unit j i = true).card % 2 = 1 := by
  have h : (Finset.univ.filter fun i : Fin n => unit j i = true) = {j} := by
    ext i
    simp [unit]
  rw [h]
  simp

theorem unit_agree {n : ℕ} (j : Fin n) (U : Finset (Fin n)) (hj : j ∉ U) :
    ∀ i ∈ U, unit j i = (fun _ : Fin n => false) i := by
  intro i hi
  have hne : i ≠ j := fun e => hj (e ▸ hi)
  simp [unit, hne]

/-- A set of fewer than `n` input positions misses one. -/
theorem exists_notMem {n : ℕ} (U : Finset (Fin n)) (h : U.card < n) : ∃ j : Fin n, j ∉ U := by
  by_contra hall
  have hU : U = Finset.univ :=
    Finset.eq_univ_iff_forall.2 (fun j => Classical.byContradiction (fun hj => hall ⟨j, hj⟩))
  rw [hU, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- A `q`-local map with outputs of length at most `M` that sends every input of odd weight
into partial MCSP sends the all-false input to a word of the instance format, as soon as
`2 * q * (log M + 2) < n`. -/
theorem formed_of_odd (n q M : ℕ) (w : (Fin n → Bool) → List Bool)
    (hq : QueryLocal n q w) (hM : ∀ x : Fin n → Bool, (w x).length ≤ M)
    (hodd : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 → w x ∈ PartialMCSP)
    (hn : 2 * q * (Nat.log 2 M + 2) < n) :
    ∃ (n' s : ℕ) (T : List (Option Bool)),
      w (fun _ : Fin n => false) = List.replicate s true ++ false :: encodePartial T ∧
        T.length = 2 ^ n' := by
  by_contra hcon
  obtain ⟨S0, hS0c, hS0⟩ := cert_length hq (fun _ : Fin n => false)
  have key : ∀ k : ℕ, ∃ S : Finset (Fin n), S.card ≤ 2 * q ∧
      ∀ s : ℕ, (w (fun _ : Fin n => false)).length = s + 1 + 2 * 2 ^ k →
        ∀ y : Fin n → Bool, (∀ i ∈ S, y i = (fun _ : Fin n => false) i) →
          ¬ Formed s (w y) := by
    intro k
    by_cases hk : 1 + 2 * 2 ^ k ≤ (w (fun _ : Fin n => false)).length
    · have hnf : ¬ Formed ((w (fun _ : Fin n => false)).length - (1 + 2 * 2 ^ k))
          (w (fun _ : Fin n => false)) := by
        rintro ⟨T, hT⟩
        apply hcon
        refine ⟨k, _, T, hT, ?_⟩
        have hl := length_of_eq _ T _ hT
        omega
      obtain ⟨S, hSc, hS⟩ := cert_not_formed hq _ _ hnf
      refine ⟨S, hSc, fun s hs y hy => ?_⟩
      have es : s = (w (fun _ : Fin n => false)).length - (1 + 2 * 2 ^ k) := by omega
      rw [es]
      exact hS y hy
    · exact ⟨∅, by simp, fun s hs => (hk (by omega)).elim⟩
  choose S hSc hS using key
  have hU : (S0 ∪ (Finset.range (Nat.log 2 M + 1)).biUnion S).card
      ≤ 2 * q * (Nat.log 2 M + 2) := by
    have h1 := Finset.card_union_le S0 ((Finset.range (Nat.log 2 M + 1)).biUnion S)
    have h2 := Finset.card_biUnion_le_card_mul (Finset.range (Nat.log 2 M + 1)) S (2 * q)
      (fun k _ => hSc k)
    rw [Finset.card_range] at h2
    calc (S0 ∪ (Finset.range (Nat.log 2 M + 1)).biUnion S).card
        ≤ 2 * q + (Nat.log 2 M + 1) * (2 * q) := le_trans h1 (Nat.add_le_add hS0c h2)
      _ = 2 * q * (Nat.log 2 M + 2) := by ring
  obtain ⟨j, hj⟩ := exists_notMem _ (lt_of_le_of_lt hU hn)
  have hagree := unit_agree j _ hj
  obtain ⟨n', s, T, hT, hlen, -⟩ := hodd (unit j) (unit_odd j)
  have hL : (w (unit j)).length = (w (fun _ : Fin n => false)).length :=
    hS0 (unit j) (fun i hi => hagree i (Finset.mem_union_left _ hi))
  have hl := length_of_eq s T _ hT
  rw [hlen, hL] at hl
  have hM0 := hM (fun _ : Fin n => false)
  have hn' : n' < Nat.log 2 M + 1 := by
    have hp : 2 ^ (n' + 1) ≤ M := by
      rw [pow_succ]
      omega
    have hlog := Nat.le_log_of_pow_le (by norm_num) hp
    omega
  exact hS n' s (by omega) (unit j)
    (fun i hi => hagree i (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨n', Finset.mem_range.2 hn', hi⟩))) ⟨T, hT⟩

end PEqualNP.MetaComplexity.Helpers.LocalFormat
