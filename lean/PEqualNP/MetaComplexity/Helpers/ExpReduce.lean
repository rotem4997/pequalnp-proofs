import PEqualNP.MetaComplexity.Helpers.LocalConstruct
import PEqualNP.MetaComplexity.Helpers.SparseCore

/-!
# The exponential-size reduction of hitting set and of SAT to partial MCSP

Helper for the open problem `L-meta-013`. Nothing here is new mathematics: it is the known
exponential-size deterministic reduction, written on the root definitions. No machine appears.

A family `F` of subsets of `n` points becomes the dense partial truth table `tbl n F` on `n`
variables: `false` at the zero point, `true` at the indicator of every nonempty set of `F`,
undefined elsewhere. Entry `j` of the table is read off the binary digits of `j`. With the bound
`s` in unary in front, this is the word `word n F s`, of length `2 ^ (n + 1) + s + 1`. By the
hitting set lemma (`hitting_iff`, `L-meta-015`) the word is in partial MCSP exactly when the
nonempty sets of `F` have a hitting set with at most `s + 1` points (`word_iff`).

Two corners cannot be written in a table of this shape: a family that contains the empty set
(it has no hitting set, and the table cannot say so, since the zero point has one entry), and
the bound zero on the size of the hitting set (the circuit bound `s` stands for `s + 1`
points). Both are sent to the fixed word `noWord n`, which is not in partial MCSP: it asks for
a circuit with no gate that is true at the zero point. This gives the total statement
`total_iff`.

For a CNF formula `φ` with `N` literal occurrences, the family of `SparseCore` (one pair of
points per occurrence, one set per clause, on `2 * N` points) gives a word of length
`2 ^ (2 * N + 1) + N` (for `N ≥ 1`) that is in partial MCSP exactly when `φ` is satisfiable
(`cnf_iff`, `cnf_total_iff`).

The final statements `S1`, `S1_total`, `S1_length`, `S2`, `S2_total`, `S2_length` are written
over root definitions and Mathlib only.
-/

namespace PEqualNP.MetaComplexity.Helpers.ExpReduce

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers PEqualNP.CircuitLowerBounds
open PEqualNP.Search

/-! ## The table and the word of a family -/

/-- The dense partial table of a family on `n` points. Entry `j` is `false` for `j = 0`, `true`
when the set of the binary digits of `j` is in the family, undefined otherwise. -/
def tbl (n : ℕ) (F : Finset (Finset (Fin n))) : List (Option Bool) :=
  (List.range (2 ^ n)).map fun j : ℕ =>
    if j = 0 then some false
    else if (Finset.univ.filter fun i : Fin n => Nat.testBit j (i : ℕ) = true) ∈ F then some true
    else none

/-- The instance: the bound `s` in unary, the separator, the code of the table. -/
def word (n : ℕ) (F : Finset (Finset (Fin n))) (s : ℕ) : List Bool :=
  List.replicate s true ++ false :: encodePartial (tbl n F)

/-- A fixed word of the right shape that is not in partial MCSP: bound zero, and a table on `n`
variables whose only defined entry is `true` at the zero point. -/
def noWord (n : ℕ) : List Bool :=
  false :: encodePartial (some true :: List.replicate (2 ^ n - 1) none)

theorem length_tbl (n : ℕ) (F : Finset (Finset (Fin n))) : (tbl n F).length = 2 ^ n := by
  simp [tbl]

theorem length_word (n : ℕ) (F : Finset (Finset (Fin n))) (s : ℕ) :
    (word n F s).length = 2 ^ (n + 1) + s + 1 := by
  unfold word
  rw [List.length_append, List.length_replicate, List.length_cons,
    LocalFormat.length_encodePartial, length_tbl, pow_succ]
  omega

theorem length_noWord (n : ℕ) : (noWord n).length = 2 ^ (n + 1) + 1 := by
  unfold noWord
  have h : 0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)
  rw [List.length_cons, LocalFormat.length_encodePartial, List.length_cons,
    List.length_replicate, pow_succ]
  omega

theorem tableIndex_zero (n : ℕ) : tableIndex (fun _ : Fin n => false) = 0 := by
  simp [tableIndex]

theorem tableIndex_eq_zero {n : ℕ} (z : Fin n → Bool) :
    tableIndex z = 0 ↔ z = fun _ : Fin n => false :=
  ⟨fun h => tableIndex_injective (h.trans (tableIndex_zero n).symm),
    fun h => by rw [h]; exact tableIndex_zero n⟩

theorem getD_tbl (n : ℕ) (F : Finset (Finset (Fin n))) (z : Fin n → Bool) :
    (tbl n F).getD (tableIndex z) none =
      if z = (fun _ : Fin n => false) then some false
      else if (Finset.univ.filter fun i : Fin n => z i = true) ∈ F then some true else none := by
  unfold tbl
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (tableIndex_lt z),
    Option.map_some, Option.getD_some]
  have e : (Finset.univ.filter fun i : Fin n => Nat.testBit (tableIndex z) (i : ℕ) = true)
      = Finset.univ.filter fun i : Fin n => z i = true := by
    ext i
    have hi : Nat.testBit (tableIndex z) (i : ℕ) = z i := congrFun (bitsOf_tableIndex z) i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi]
  rw [e]
  by_cases hz : z = fun _ : Fin n => false
  · rw [ite_eq_left hz, ite_eq_left ((tableIndex_eq_zero z).2 hz)]
  · rw [ite_eq_right hz, ite_eq_right (fun h => hz ((tableIndex_eq_zero z).1 h))]

theorem consistent_iff (n : ℕ) (F : Finset (Finset (Fin n))) (f : (Fin n → Bool) → Bool) :
    Consistent n (tbl n F) f ↔
      f (fun _ : Fin n => false) = false ∧
        ∀ S ∈ F, S.Nonempty → f (fun i : Fin n => decide (i ∈ S)) = true := by
  constructor
  · intro h
    refine ⟨h _ false (by rw [getD_tbl]; simp), fun S hS hne => h _ true ?_⟩
    obtain ⟨a, ha⟩ := hne
    have hz : (fun i : Fin n => decide (i ∈ S)) ≠ (fun _ : Fin n => false) := by
      intro e
      have := congrFun e a
      simp [ha] at this
    have hs : (Finset.univ.filter fun i : Fin n => decide (i ∈ S) = true) = S := by
      ext i
      simp
    rw [getD_tbl, ite_eq_right hz, hs, ite_eq_left hS]
  · rintro ⟨h0, h1⟩ z b hb
    rw [getD_tbl] at hb
    split_ifs at hb with hz hP
    · rw [hz, h0]
      exact Option.some.inj hb
    · have e : z = fun i : Fin n => decide (i ∈ Finset.univ.filter fun i : Fin n => z i = true) := by
        funext i
        simp
      have hne : (Finset.univ.filter fun i : Fin n => z i = true).Nonempty := by
        by_contra hc
        rw [Finset.not_nonempty_iff_eq_empty] at hc
        apply hz
        funext i
        have hi : i ∉ Finset.univ.filter fun i : Fin n => z i = true := by
          rw [hc]
          exact Finset.notMem_empty i
        simpa using hi
      have h2 := h1 _ hP hne
      rw [← e] at h2
      rw [h2]
      exact Option.some.inj hb

/-- Membership of the word in partial MCSP is the existence of a function as in `L-meta-015`,
for the nonempty sets of the family. -/
theorem word_mem (n : ℕ) (F : Finset (Finset (Fin n))) (s : ℕ) :
    word n F s ∈ PartialMCSP ↔
      ∃ f : (Fin n → Bool) → Bool, f (fun _ : Fin n => false) = false ∧
        (∀ S ∈ F, S.Nonempty → f (fun i : Fin n => decide (i ∈ S)) = true) ∧
          HasCircuitSize n f s := by
  constructor
  · rintro ⟨n', s', T, hw, hlen, f, hc, hs⟩
    obtain ⟨e1, e2⟩ := LocalConstruct.split_unique s s' _ _ hw
    have e3 := LocalConstruct.encodePartial_injective _ _ e2
    subst e1
    subst e3
    rw [length_tbl] at hlen
    have e4 : n = n' := Nat.pow_right_injective (Nat.le_refl 2) hlen
    subst e4
    obtain ⟨h0, h1⟩ := (consistent_iff n F f).1 hc
    exact ⟨f, h0, h1, hs⟩
  · rintro ⟨f, h0, h1, hs⟩
    exact ⟨n, s, tbl n F, rfl, length_tbl n F, f, (consistent_iff n F f).2 ⟨h0, h1⟩, hs⟩

/-- The word of a family is in partial MCSP exactly when the nonempty sets of the family have a
hitting set with at most `s + 1` points. No hypothesis on the family. -/
theorem word_iff (n : ℕ) (F : Finset (Finset (Fin n))) (s : ℕ) :
    word n F s ∈ PartialMCSP ↔
      ∃ H : Finset (Fin n), (∀ S ∈ F, S.Nonempty → (H ∩ S).Nonempty) ∧ H.card ≤ s + 1 := by
  rw [word_mem]
  have key := hitting_iff n (F.filter fun S : Finset (Fin n) => S.Nonempty) s
  simp only [Finset.mem_filter, and_imp] at key
  exact key

/-- The fixed word is not in partial MCSP: a circuit with no gate is false at the zero point. -/
theorem noWord_notMem (n : ℕ) : noWord n ∉ PartialMCSP := by
  rintro ⟨n', s, T, hw, -, f, hc, C, -, hsz, hev⟩
  have hw' : List.replicate 0 true ++
      false :: encodePartial (some true :: List.replicate (2 ^ n - 1) none)
      = List.replicate s true ++ false :: encodePartial T := hw
  obtain ⟨e1, e2⟩ := LocalConstruct.split_unique 0 s _ _ hw'
  have e3 := LocalConstruct.encodePartial_injective _ _ e2
  subst e1
  subst e3
  have h1 : f (fun _ : Fin n' => false) = true :=
    hc _ true (by rw [tableIndex_zero]; rfl)
  have hg : C.gates = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hsz)
  have h2 := hev (fun _ : Fin n' => false)
  rw [h1] at h2
  obtain ⟨gates, out⟩ := C
  simp only at hg
  subst hg
  have h3 : (List.ofFn fun _ : Fin n' => false).getD out false = true := h2
  rw [List.getD_eq_getElem?_getD] at h3
  rcases Nat.lt_or_ge out n' with ho | ho
  · rw [List.getElem?_ofFn] at h3
    simp [ho] at h3
  · rw [List.getElem?_eq_none_iff.2 (by simp [ho])] at h3
    simp at h3

/-- The total map: every family and every bound `k` on the size of the hitting set. A family
with the empty set, and the bound zero for a family that is not empty, go to the fixed word. -/
theorem total_iff (n : ℕ) (F : Finset (Finset (Fin n))) (k : ℕ) :
    (if ∅ ∈ F ∨ (k = 0 ∧ F ≠ ∅) then noWord n else word n F (k - 1)) ∈ PartialMCSP ↔
      ∃ H : Finset (Fin n), (∀ S ∈ F, (H ∩ S).Nonempty) ∧ H.card ≤ k := by
  by_cases hbad : ∅ ∈ F ∨ (k = 0 ∧ F ≠ ∅)
  · rw [ite_eq_left hbad]
    constructor
    · intro h
      exact absurd h (noWord_notMem n)
    · rintro ⟨H, hhit, hcard⟩
      exfalso
      rcases hbad with he | ⟨hk, hF⟩
      · have := hhit ∅ he
        simp at this
      · obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.2 hF
        have hH : H = ∅ := Finset.card_eq_zero.1 (by omega)
        have := hhit S hS
        rw [hH] at this
        simp at this
  · rw [ite_eq_right hbad, word_iff]
    have he : ∅ ∉ F := fun h => hbad (Or.inl h)
    have hne : ∀ S ∈ F, S.Nonempty := by
      intro S hS
      rw [Finset.nonempty_iff_ne_empty]
      intro e
      exact he (e ▸ hS)
    by_cases hk : k = 0
    · have hF : F = ∅ := by
        by_contra hF
        exact hbad (Or.inr ⟨hk, hF⟩)
      subst hF
      subst hk
      constructor
      · intro _
        exact ⟨∅, by simp, by simp⟩
      · intro _
        exact ⟨∅, by simp, by simp⟩
    · have hk' : k - 1 + 1 = k := by omega
      rw [hk']
      constructor
      · rintro ⟨H, hhit, hcard⟩
        exact ⟨H, fun S hS => hhit S hS (hne S hS), hcard⟩
      · rintro ⟨H, hhit, hcard⟩
        exact ⟨H, fun S hS _ => hhit S hS, hcard⟩

/-! ## CNF formulas -/

/-- Every set of the family of a formula with no empty clause is nonempty. -/
theorem family_nonempty (φ : CNF) (hφ : [] ∉ φ) :
    ∀ S ∈ (Sparse.family φ).toFinset, S.Nonempty := by
  intro S hS
  rw [List.mem_toFinset, Sparse.family, List.mem_append] at hS
  rcases hS with hS | hS
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hS
    have hj' : j < (Sparse.occVars φ).length := List.mem_range.1 hj
    refine ⟨⟨2 * j, by omega⟩, ?_⟩
    simp [Sparse.pairSet]
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hS
    rcases c with _ | ⟨l, c⟩
    · exact absurd hc hφ
    · refine ⟨⟨Sparse.litPos φ l, Sparse.litPos_lt hc List.mem_cons_self⟩, ?_⟩
      simp only [Sparse.clauseSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨l, List.mem_cons_self, rfl⟩

/-- The word of the family of a formula with no empty clause is in partial MCSP exactly when
the formula is satisfiable. -/
theorem cnf_iff (φ : CNF) (hφ : [] ∉ φ) :
    word (2 * (Sparse.occVars φ).length) (Sparse.family φ).toFinset
      ((Sparse.occVars φ).length - 1) ∈ PartialMCSP ↔ Satisfiable φ := by
  rw [word_iff, Sparse.satisfiable_iff]
  constructor
  · rintro ⟨H, hhit, hcard⟩
    exact Sparse.sat_of_hit φ H (fun S hS => hhit S hS (family_nonempty φ hφ S hS)) hcard
  · rintro ⟨σ, hσ⟩
    obtain ⟨H, hhit, hcard⟩ := Sparse.hit_of_sat φ σ hσ
    exact ⟨H, fun S hS _ => hhit S hS, hcard⟩

/-- The total map on formulas: a formula with an empty clause goes to the fixed word. -/
theorem cnf_total_iff (φ : CNF) :
    (if [] ∈ φ then noWord (2 * (Sparse.occVars φ).length)
      else word (2 * (Sparse.occVars φ).length) (Sparse.family φ).toFinset
        ((Sparse.occVars φ).length - 1)) ∈ PartialMCSP ↔ Satisfiable φ := by
  by_cases hφ : [] ∈ φ
  · rw [ite_eq_left hφ]
    constructor
    · intro h
      exact absurd h (noWord_notMem _)
    · intro h
      obtain ⟨σ, hσ⟩ := (Sparse.satisfiable_iff φ).1 h
      obtain ⟨l, hl, -⟩ := hσ [] hφ
      simp at hl
  · rw [ite_eq_right hφ]
    exact cnf_iff φ hφ

theorem length_occVars (φ : CNF) : (Sparse.occVars φ).length = φ.flatten.length :=
  List.length_map _

/-! ## The statements, over root definitions and Mathlib only -/

/-- S1. The dense partial table of a family `F` on `n` points (entry `j` is `false` for `j = 0`,
`true` when the set of binary digits of `j` is in `F`, undefined otherwise) with the bound `s`
is in partial MCSP exactly when the nonempty sets of `F` have a hitting set with at most `s + 1`
points. -/
theorem S1 : ∀ (n : ℕ) (F : Finset (Finset (Fin n))) (s : ℕ), List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial ((List.range (2 ^ n)).map fun j : ℕ => if j = 0 then some false else if (Finset.univ.filter fun i : Fin n => Nat.testBit j (i : ℕ) = true) ∈ F then some true else none) ∈ PEqualNP.MetaComplexity.PartialMCSP ↔ ∃ H : Finset (Fin n), (∀ S ∈ F, S.Nonempty → (H ∩ S).Nonempty) ∧ H.card ≤ s + 1 :=
  word_iff

/-- S1, total form: every family and every bound `k` on the size of the hitting set, the two
corners (the empty set in the family; `k = 0` with a family that is not empty) sent to a fixed
word that is not a member. -/
theorem S1_total : ∀ (n : ℕ) (F : Finset (Finset (Fin n))) (k : ℕ), (if ∅ ∈ F ∨ (k = 0 ∧ F ≠ ∅) then false :: PEqualNP.MetaComplexity.encodePartial (some true :: List.replicate (2 ^ n - 1) none) else List.replicate (k - 1) true ++ false :: PEqualNP.MetaComplexity.encodePartial ((List.range (2 ^ n)).map fun j : ℕ => if j = 0 then some false else if (Finset.univ.filter fun i : Fin n => Nat.testBit j (i : ℕ) = true) ∈ F then some true else none)) ∈ PEqualNP.MetaComplexity.PartialMCSP ↔ ∃ H : Finset (Fin n), (∀ S ∈ F, (H ∩ S).Nonempty) ∧ H.card ≤ k :=
  total_iff

/-- The length of the instance of S1 and of the fixed word: `2 ^ (n + 1)` plus the bound plus
one. The length depends on `n` and `s` only. -/
theorem S1_length : ∀ (n : ℕ) (F : Finset (Finset (Fin n))) (s : ℕ), (List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial ((List.range (2 ^ n)).map fun j : ℕ => if j = 0 then some false else if (Finset.univ.filter fun i : Fin n => Nat.testBit j (i : ℕ) = true) ∈ F then some true else none)).length = 2 ^ (n + 1) + s + 1 ∧ (false :: PEqualNP.MetaComplexity.encodePartial (some true :: List.replicate (2 ^ n - 1) none)).length = 2 ^ (n + 1) + 1 :=
  fun n F s => ⟨length_word n F s, length_noWord n⟩

/-- S2. A CNF formula `φ` with `N` literal occurrences and no empty clause. The family on
`2 * N` points has the pair `{2 * j, 2 * j + 1}` for every `j < N` and, for every clause, the
set of the points `2 * (first occurrence of the variable) + (1 for a positive literal)` of its
literals. Its dense table with the bound `N - 1` is in partial MCSP exactly when `φ` is
satisfiable. -/
theorem S2 : ∀ (φ : PEqualNP.Search.CNF) (N : ℕ), N = (φ.flatten.map Prod.fst).length → [] ∉ φ → (List.replicate (N - 1) true ++ false :: PEqualNP.MetaComplexity.encodePartial ((List.range (2 ^ (2 * N))).map fun j : ℕ => if j = 0 then some false else if (Finset.univ.filter fun i : Fin (2 * N) => Nat.testBit j (i : ℕ) = true) ∈ (((List.range N).map fun a : ℕ => Finset.univ.filter fun i : Fin (2 * N) => (i : ℕ) / 2 = a) ++ φ.map fun c : PEqualNP.Search.Clause => Finset.univ.filter fun i : Fin (2 * N) => ∃ l ∈ c, (i : ℕ) = 2 * (φ.flatten.map Prod.fst).idxOf l.1 + (if l.2 = true then 1 else 0)).toFinset then some true else none) ∈ PEqualNP.MetaComplexity.PartialMCSP ↔ PEqualNP.Search.Satisfiable φ) := by
  intro φ N hN hφ
  subst hN
  exact cnf_iff φ hφ

/-- S2, total form: every CNF formula, a formula with an empty clause sent to a fixed word that
is not a member. -/
theorem S2_total : ∀ (φ : PEqualNP.Search.CNF) (N : ℕ), N = (φ.flatten.map Prod.fst).length → ((if [] ∈ φ then false :: PEqualNP.MetaComplexity.encodePartial (some true :: List.replicate (2 ^ (2 * N) - 1) none) else List.replicate (N - 1) true ++ false :: PEqualNP.MetaComplexity.encodePartial ((List.range (2 ^ (2 * N))).map fun j : ℕ => if j = 0 then some false else if (Finset.univ.filter fun i : Fin (2 * N) => Nat.testBit j (i : ℕ) = true) ∈ (((List.range N).map fun a : ℕ => Finset.univ.filter fun i : Fin (2 * N) => (i : ℕ) / 2 = a) ++ φ.map fun c : PEqualNP.Search.Clause => Finset.univ.filter fun i : Fin (2 * N) => ∃ l ∈ c, (i : ℕ) = 2 * (φ.flatten.map Prod.fst).idxOf l.1 + (if l.2 = true then 1 else 0)).toFinset then some true else none)) ∈ PEqualNP.MetaComplexity.PartialMCSP ↔ PEqualNP.Search.Satisfiable φ) := by
  intro φ N hN
  subst hN
  exact cnf_total_iff φ

/-- The number `N` of S2 is the number of literal occurrences of the formula, and it is at most
a quarter of the length of the code of the formula. -/
theorem S2_length : ∀ φ : PEqualNP.Search.CNF, (φ.flatten.map Prod.fst).length = φ.flatten.length ∧ 4 * φ.flatten.length ≤ (PEqualNP.Search.encodeCNF φ).length := by
  intro φ
  refine ⟨List.length_map _, ?_⟩
  induction φ with
  | nil => simp
  | cons c φ ih =>
    have hc : 4 * c.length ≤ (encodeClause c).length := by
      induction c with
      | nil => simp
      | cons l c ihc =>
        have e : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by
          simp [encodeClause]
        have hl : 4 ≤ (encodeLiteral l).length := by
          simp [encodeLiteral]
        rw [e, List.length_append, List.length_cons]
        omega
    have e : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by
      simp [encodeCNF]
    rw [e, List.length_append, List.flatten_cons, List.length_append]
    omega

/-- The corner that forces the word "nonempty" in S1: on one point, the family whose only set is
the empty set has no hitting set, and its word with bound zero is in partial MCSP. -/
theorem S1_corner : (List.replicate 0 true ++ false :: PEqualNP.MetaComplexity.encodePartial ((List.range (2 ^ 1)).map fun j : ℕ => if j = 0 then some false else if (Finset.univ.filter fun i : Fin 1 => Nat.testBit j (i : ℕ) = true) ∈ ({∅} : Finset (Finset (Fin 1))) then some true else none) ∈ PEqualNP.MetaComplexity.PartialMCSP) ∧ ¬ ∃ H : Finset (Fin 1), (∀ S ∈ ({∅} : Finset (Finset (Fin 1))), (H ∩ S).Nonempty) ∧ H.card ≤ 0 + 1 := by
  refine ⟨(word_iff 1 {∅} 0).2 ⟨∅, ?_, by simp⟩, ?_⟩
  · intro S hS hne
    rw [Finset.mem_singleton] at hS
    rw [hS] at hne
    simp at hne
  · rintro ⟨H, hhit, -⟩
    have := hhit ∅ (Finset.mem_singleton_self _)
    simp at this

end PEqualNP.MetaComplexity.Helpers.ExpReduce
