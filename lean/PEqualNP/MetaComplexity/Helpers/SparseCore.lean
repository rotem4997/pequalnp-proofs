import PEqualNP.Defs.MetaComplexitySparse
import PEqualNP.Defs.Search
import PEqualNP.MetaComplexity.Helpers.HittingSet

/-!
# Helper module (proofs only): the combinatorial core of "SAT reduces to sparse partial MCSP"

No machine appears here. For a CNF formula `φ` with `N` literal occurrences in all, the
instance `sparseOfCnf φ` has `2 * N` circuit inputs. Occurrence number `j` owns the two inputs
`2 * j` (its variable is false) and `2 * j + 1` (its variable is true); a variable is
represented by its FIRST occurrence (`List.idxOf`), so no renaming or counting of distinct
variables is needed, and the inputs of later occurrences are padding. The rows are: the
all-false point with value `false`; for every `j < N` the indicator of the pair
`{2 * j, 2 * j + 1}` with value `true`; for every clause the indicator of the inputs of its
literals with value `true`. The size bound is `N - 1`.

By the hitting set lemma (`hitting_iff`, `L-meta-015`) the instance is a member exactly when
the family of pairs and clause sets has a hitting set of size at most `N`. Such a set takes
exactly one input from every pair, so it is an assignment (padding pairs are free), and it
hits every clause set exactly when the assignment satisfies every clause.

Main results: `sparseOfCnf_mem`, and `sparse_hitting_iff`, which is stated on definitions only.
-/

namespace PEqualNP.MetaComplexity.Helpers.Sparse

open PEqualNP.Search PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-! ## The instance format is read back uniquely -/

/-- The split at the first `false` is unique. -/
theorem split_unique : ∀ (s s' : ℕ) (A B : List Bool),
    List.replicate s true ++ false :: A = List.replicate s' true ++ false :: B →
      s = s' ∧ A = B
  | 0, 0, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.nil_append] at h
    exact ⟨rfl, (List.cons.inj h).2⟩
  | 0, s' + 1, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | s + 1, 0, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | s + 1, s' + 1, A, B, h => by
    rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append] at h
    obtain ⟨h1, h2⟩ := split_unique s s' A B (List.cons.inj h).2
    exact ⟨by rw [h1], h2⟩

theorem encodeRows_nil (m : ℕ) : encodeRows m [] = [] := rfl

theorem encodeRows_cons (m : ℕ) (r : (Fin m → Bool) × Bool) (rows : List ((Fin m → Bool) × Bool)) :
    encodeRows m (r :: rows) = (List.ofFn r.1 ++ [r.2]) ++ encodeRows m rows := by
  simp [encodeRows]

/-- The code of a list of rows determines it. -/
theorem encodeRows_injective (m : ℕ) : ∀ rows rows' : List ((Fin m → Bool) × Bool),
    encodeRows m rows = encodeRows m rows' → rows = rows'
  | [], [], _ => rfl
  | [], r :: rows', h => by
    rw [encodeRows_nil, encodeRows_cons] at h
    have := congrArg List.length h
    simp at this
  | r :: rows, [], h => by
    rw [encodeRows_nil, encodeRows_cons] at h
    have := congrArg List.length h
    simp at this
  | r :: rows, r' :: rows', h => by
    rw [encodeRows_cons, encodeRows_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    obtain ⟨h3, h4⟩ := List.append_inj h1 (by simp)
    have e1 : r.1 = r'.1 := List.ofFn_injective h3
    have e2 : r.2 = r'.2 := by simpa using h4
    rw [Prod.ext e1 e2, encodeRows_injective m rows rows' h2]

/-- Membership of a well-formed instance is the property of its parts. -/
theorem mem_sparse_iff (m s : ℕ) (rows : List ((Fin m → Bool) × Bool)) :
    List.replicate s true ++ false :: (List.replicate m true ++ false :: encodeRows m rows)
        ∈ SparsePartialMCSP ↔
      ∃ f : (Fin m → Bool) → Bool, (∀ r ∈ rows, f r.1 = r.2) ∧ HasCircuitSize m f s := by
  constructor
  · rintro ⟨m', s', rows', he, hf⟩
    obtain ⟨hs, he1⟩ := split_unique _ _ _ _ he
    obtain ⟨hm, he2⟩ := split_unique _ _ _ _ he1
    subst hs
    subst hm
    rw [encodeRows_injective m rows rows' he2]
    exact hf
  · intro hf
    exact ⟨m, s, rows, rfl, hf⟩

/-! ## The instance of a formula -/

/-- The variables of all literal occurrences of the formula, in order. -/
def occVars (φ : CNF) : List ℕ := φ.flatten.map Prod.fst

/-- The circuit input that stands for a literal: twice the number of the first occurrence of
its variable, plus one for a positive literal. -/
def litPos (φ : CNF) (l : Literal) : ℕ :=
  2 * (occVars φ).idxOf l.1 + (if l.2 = true then 1 else 0)

/-- The two inputs of occurrence `j`. -/
def pairSet (N j : ℕ) : Finset (Fin (2 * N)) :=
  Finset.univ.filter fun i : Fin (2 * N) => (i : ℕ) / 2 = j

/-- The inputs of the literals of a clause. -/
def clauseSet (φ : CNF) (c : Clause) : Finset (Fin (2 * (occVars φ).length)) :=
  Finset.univ.filter fun i : Fin (2 * (occVars φ).length) => ∃ l ∈ c, (i : ℕ) = litPos φ l

/-- The family to hit: one pair per occurrence, one set per clause. -/
def family (φ : CNF) : List (Finset (Fin (2 * (occVars φ).length))) :=
  (List.range (occVars φ).length).map (pairSet (occVars φ).length) ++ φ.map (clauseSet φ)

/-- The rows of a family: the all-false point with value `false`, then the indicator of every
set with value `true`. -/
def rowsOf {n : ℕ} (fam : List (Finset (Fin n))) : List ((Fin n → Bool) × Bool) :=
  ((fun _ : Fin n => false), false) ::
    fam.map fun S : Finset (Fin n) => ((fun i : Fin n => decide (i ∈ S)), true)

/-- The sparse partial MCSP instance of a CNF formula. -/
def sparseOfCnf (φ : CNF) : List Bool :=
  List.replicate ((occVars φ).length - 1) true ++ false ::
    (List.replicate (2 * (occVars φ).length) true ++ false ::
      encodeRows (2 * (occVars φ).length) (rowsOf (family φ)))

/-! ## Satisfiability and hitting sets -/

theorem satisfiable_iff (φ : CNF) :
    Satisfiable φ ↔ ∃ σ : Assignment, ∀ c ∈ φ, ∃ l ∈ c, σ l.1 = l.2 := by
  simp [Satisfiable, CNF.eval, Clause.eval, Literal.eval, List.all_eq_true, List.any_eq_true]

theorem mem_occVars {φ : CNF} {c : Clause} {l : Literal} (hc : c ∈ φ) (hl : l ∈ c) :
    l.1 ∈ occVars φ :=
  List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hc, hl⟩, rfl⟩

theorem litPos_lt {φ : CNF} {c : Clause} {l : Literal} (hc : c ∈ φ) (hl : l ∈ c) :
    litPos φ l < 2 * (occVars φ).length := by
  have h := List.idxOf_lt_length_iff.2 (mem_occVars hc hl)
  unfold litPos
  split <;> omega

/-- A satisfying assignment gives a hitting set with one input per occurrence. -/
theorem hit_of_sat (φ : CNF) (σ : Assignment) (hσ : ∀ c ∈ φ, ∃ l ∈ c, σ l.1 = l.2) :
    ∃ H : Finset (Fin (2 * (occVars φ).length)),
      (∀ S ∈ (family φ).toFinset, (H ∩ S).Nonempty) ∧ H.card ≤ (occVars φ).length - 1 + 1 := by
  let H : Finset (Fin (2 * (occVars φ).length)) := Finset.univ.filter fun i : Fin (2 * (occVars φ).length) =>
    (i : ℕ) % 2 = if σ ((occVars φ).getD ((i : ℕ) / 2) 0) = true then 1 else 0
  refine ⟨H, ?_, ?_⟩
  · intro S hS
    rw [List.mem_toFinset, family, List.mem_append] at hS
    rcases hS with hS | hS
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hS
      have hj' : j < (occVars φ).length := List.mem_range.1 hj
      refine ⟨⟨2 * j + (if σ ((occVars φ).getD j 0) = true then 1 else 0), by split <;> omega⟩, ?_⟩
      have hd : (2 * j + (if σ ((occVars φ).getD j 0) = true then 1 else 0)) / 2 = j := by
        split <;> omega
      rw [Finset.mem_inter]
      refine ⟨?_, ?_⟩
      · simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hd]
        split <;> omega
      · simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hd
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hS
      obtain ⟨l, hl, hσl⟩ := hσ c hc
      have hlt := litPos_lt hc hl
      have hidx : (occVars φ).idxOf l.1 < (occVars φ).length := List.idxOf_lt_length_iff.2 (mem_occVars hc hl)
      have hget : (occVars φ).getD ((occVars φ).idxOf l.1) 0 = l.1 := by
        rw [List.getD_eq_getElem _ _ hidx]
        exact List.getElem_idxOf hidx
      refine ⟨⟨litPos φ l, hlt⟩, ?_⟩
      rw [Finset.mem_inter]
      refine ⟨?_, ?_⟩
      · simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
        have hd : litPos φ l / 2 = (occVars φ).idxOf l.1 := by
          unfold litPos; split <;> omega
        rw [hd, hget, hσl]
        unfold litPos
        split <;> omega
      · simp only [clauseSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨l, hl, rfl⟩
  · have hc : H.card ≤ (Finset.range (occVars φ).length).card := by
      refine Finset.card_le_card_of_injOn (fun i : Fin (2 * (occVars φ).length) => (i : ℕ) / 2) ?_ ?_
      · intro i _
        have := i.isLt
        simp only [Finset.coe_range, Set.mem_Iio]
        omega
      · intro i hi k hk hik
        simp only [H, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hk
        have hik' : (i : ℕ) / 2 = (k : ℕ) / 2 := hik
        rw [hik'] at hi
        apply Fin.ext
        omega
    rw [Finset.card_range] at hc
    omega

/-- A hitting set with at most one input per occurrence gives a satisfying assignment. -/
theorem sat_of_hit (φ : CNF) (H : Finset (Fin (2 * (occVars φ).length)))
    (hhit : ∀ S ∈ (family φ).toFinset, (H ∩ S).Nonempty)
    (hcard : H.card ≤ (occVars φ).length - 1 + 1) :
    ∃ σ : Assignment, ∀ c ∈ φ, ∃ l ∈ c, σ l.1 = l.2 := by
  have hcard' : H.card ≤ (occVars φ).length := by
    have h1 : H.card ≤ 2 * (occVars φ).length := by simpa using Finset.card_le_univ H
    omega
  -- the hitting set takes at most one input of every pair
  have hinj : Set.InjOn (fun i : Fin (2 * (occVars φ).length) => (i : ℕ) / 2) (H : Set (Fin (2 * (occVars φ).length))) := by
    rw [← Finset.card_image_iff]
    apply le_antisymm Finset.card_image_le
    have hsub : Finset.range (occVars φ).length ⊆ H.image (fun i : Fin (2 * (occVars φ).length) => (i : ℕ) / 2) := by
      intro j hj
      have hmem : pairSet (occVars φ).length j ∈ (family φ).toFinset := by
        rw [List.mem_toFinset, family, List.mem_append]
        exact Or.inl (List.mem_map.2 ⟨j, List.mem_range.2 (Finset.mem_range.1 hj), rfl⟩)
      obtain ⟨i, hi⟩ := hhit _ hmem
      obtain ⟨hiH, hiP⟩ := Finset.mem_inter.1 hi
      simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiP
      exact Finset.mem_image.2 ⟨i, hiH, hiP⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega
  refine ⟨fun x => decide (∃ i ∈ H, (i : ℕ) = 2 * (occVars φ).idxOf x + 1), ?_⟩
  intro c hc
  have hmem : clauseSet φ c ∈ (family φ).toFinset := by
    rw [List.mem_toFinset, family, List.mem_append]
    exact Or.inr (List.mem_map.2 ⟨c, hc, rfl⟩)
  obtain ⟨i, hi⟩ := hhit _ hmem
  obtain ⟨hiH, hiC⟩ := Finset.mem_inter.1 hi
  simp only [clauseSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiC
  obtain ⟨l, hl, hil⟩ := hiC
  refine ⟨l, hl, ?_⟩
  obtain ⟨x, b⟩ := l
  cases b with
  | true =>
    simp only [litPos, ite_true] at hil
    exact decide_eq_true ⟨i, hiH, hil⟩
  | false =>
    simp only [litPos, Bool.false_eq_true, ite_false] at hil
    refine decide_eq_false ?_
    rintro ⟨k, hkH, hk⟩
    dsimp only at hk hil
    have hki : k = i := hinj hkH hiH (by
      show (k : ℕ) / 2 = (i : ℕ) / 2
      omega)
    rw [hki] at hk
    omega

/-- The combinatorial core: the instance of a formula is in sparse partial MCSP exactly when
the formula is satisfiable. -/
theorem sparseOfCnf_mem (φ : CNF) : sparseOfCnf φ ∈ SparsePartialMCSP ↔ Satisfiable φ := by
  unfold sparseOfCnf
  rw [mem_sparse_iff, satisfiable_iff]
  have hrows : ∀ f : (Fin (2 * (occVars φ).length) → Bool) → Bool,
      (∀ r ∈ rowsOf (family φ), f r.1 = r.2) ↔
        (f (fun _ => false) = false ∧
          ∀ S ∈ (family φ).toFinset, f (fun i => decide (i ∈ S)) = true) := by
    intro f
    simp [rowsOf]
  have key := hitting_iff (2 * (occVars φ).length) (family φ).toFinset ((occVars φ).length - 1)
  constructor
  · rintro ⟨f, hf, hsz⟩
    obtain ⟨h0, h1⟩ := (hrows f).1 hf
    obtain ⟨H, hhit, hcard⟩ := key.1 ⟨f, h0, h1, hsz⟩
    exact sat_of_hit φ H hhit hcard
  · rintro ⟨σ, hσ⟩
    obtain ⟨f, h0, h1, hsz⟩ := key.2 (hit_of_sat φ σ hσ)
    exact ⟨f, (hrows f).2 ⟨h0, h1⟩, hsz⟩

/-- Stated on definitions only: the instance whose rows are the all-false point with value
`false` and the indicator of every set of `F` with value `true` is in sparse partial MCSP with
bound `s` exactly when `F` has a hitting set of size at most `s + 1`. -/
theorem sparse_hitting_iff (n : ℕ) (F : List (Finset (Fin n))) (s : ℕ) :
    List.replicate s true ++ false :: (List.replicate n true ++ false ::
      encodeRows n (((fun _ : Fin n => false), false) ::
        F.map fun S : Finset (Fin n) => ((fun i : Fin n => decide (i ∈ S)), true)))
        ∈ SparsePartialMCSP ↔
      ∃ H : Finset (Fin n), (∀ S ∈ F, (H ∩ S).Nonempty) ∧ H.card ≤ s + 1 := by
  have key := hitting_iff n F.toFinset s
  simp only [List.mem_toFinset] at key
  rw [mem_sparse_iff, ← key]
  constructor
  · rintro ⟨f, hf, hsz⟩
    refine ⟨f, hf _ List.mem_cons_self, fun S hS => ?_, hsz⟩
    exact hf _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨S, hS, rfl⟩))
  · rintro ⟨f, h0, h1, hsz⟩
    refine ⟨f, fun r hr => ?_, hsz⟩
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h0
    · obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hr
      exact h1 S hS

end PEqualNP.MetaComplexity.Helpers.Sparse
