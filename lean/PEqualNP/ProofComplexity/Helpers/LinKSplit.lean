import PEqualNP.Defs.ProofComplexityLinK
import PEqualNP.ProofComplexity.Helpers.LinKOne
import PEqualNP.ProofComplexity.Helpers.LinKTrivial

/-!
# Helpers: the case split in Res(k, ⊕) with termwise weakening

Termwise weakening lets a term imply ONE term of the conclusion (or the disjunction of its
one-equation terms). The case split, a term `T` implying a disjunction of several terms of
more than one equation, is not a primitive. This file shows what it costs.

* `taut_line`: the tautology `{f = 0} ∨ {f = 1}` is one weakening away from any line.
* `rewrite_term`: a term is rewritten into any term it implies in one line.
* `split_one`: a term `T` with `T.card + 1 ≤ k` splits on one linear form in five lines.
* `split_tree`: a decision tree with `n` queries that may forget equations before each query
  (`Splits`) is simulated in at most `7 * n + 1` lines.
* `split_xor`: the example `{x + y = 1}` into `{x = 1, y = 0}` or `{x = 0, y = 1}` at `k = 2`.

* `split_any`: EVERY sound split (a term into any `c` terms of at most `k` equations whose
  disjunction it implies) is derivable within terms of at most `k` equations, with no
  hypothesis on the size of the term, in at most `splitCost k c ≤ 3 * (k + 1) ^ c` lines.
* `refutation_of_split`: the general split cannot be cheap. The split into the terms "clause
  `C` is false" of a formula `F` (sound from any term when `F` is unsatisfiable,
  `falseTerms_cover`) is, up to `2 * F.card` lines, a refutation of `F`.

So the split along a decision tree is cheap, every split is possible, and a bound polynomial
in `c` for the general split would bound polynomially the refutations of every formula of
width at most `k`.
-/

namespace PEqualNP.ProofComplexity.Helpers.LinKSplit

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
/-- Termwise weakening is monotone in the conclusion. -/
theorem weak_mono {L M M' : LinKLine V} (h : IsLinKWeakening L M) (hM : M ⊆ M') :
    IsLinKWeakening L M' := by
  intro T hT
  rcases h T hT with ⟨S, hS, himp⟩ | hb
  · exact Or.inl ⟨S, hM hS, himp⟩
  · refine Or.inr fun a ha => ?_
    obtain ⟨q, hq, hqs⟩ := hb a ha
    exact ⟨q, hM hq, hqs⟩

/-- The tautology `{f = 0} ∨ {f = 1}`. -/
def tautLine (f : Finset V) : LinKLine V := {{(f, false)}, {(f, true)}}

theorem mem_tautLine (f : Finset V) (S : LinTerm V) :
    S ∈ tautLine f ↔ S = {(f, false)} ∨ S = {(f, true)} := by
  simp [tautLine]

theorem tautLine_card (f : Finset V) : ∀ T ∈ tautLine f, T.card ≤ 1 := by
  intro T hT
  rcases (mem_tautLine f T).mp hT with rfl | rfl <;> simp

/-- Every line weakens termwise to the tautology `{f = 0} ∨ {f = 1}`: each term implies the
disjunction of its one-equation terms. -/
theorem weak_tautLine (L : LinKLine V) (f : Finset V) : IsLinKWeakening L (tautLine f) := by
  intro T _
  right
  intro a _
  by_cases h : Odd (f.filter (fun v => a v = true)).card
  · exact ⟨(f, true), (mem_tautLine f _).mpr (Or.inr rfl), by simp [LinEqSat, h]⟩
  · exact ⟨(f, false), (mem_tautLine f _).mpr (Or.inl rfl), by simp [LinEqSat, h]⟩

/-- (i) From a derivation holding any line, the tautology `{f = 0} ∨ {f = 1}` in one more
line, for `1 ≤ k`. -/
theorem taut_line {k : ℕ} (hk : 1 ≤ k) {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation k IsLinKWeakening F π) {L : LinKLine V} (hL : L ∈ π)
    (f : Finset V) : IsLinKDerivation k IsLinKWeakening F (tautLine f :: π) :=
  IsLinKDerivation.weak h hL (weak_tautLine L f)
    (fun T hT => (tautLine_card f T hT).trans hk)

/-- Replacing a term by a term it implies is a termwise weakening. -/
theorem weak_rewrite {L : LinKLine V} {T U : LinTerm V}
    (himp : ∀ a : V → Bool, LinTermSat a T → LinTermSat a U) :
    IsLinKWeakening L (L.erase T ∪ {U}) := by
  intro S hS
  left
  by_cases hST : S = T
  · rw [hST]
    exact ⟨U, Finset.mem_union_right _ (Finset.mem_singleton_self _), himp⟩
  · exact ⟨S, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hST, hS⟩), fun _ hs => hs⟩

/-- (iii) A term of a line is rewritten into any term it implies, in one more line. -/
theorem rewrite_term {k : ℕ} {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation k IsLinKWeakening F π) {L : LinKLine V} (hL : L ∈ π)
    {T U : LinTerm V} (hU : U.card ≤ k)
    (himp : ∀ a : V → Bool, LinTermSat a T → LinTermSat a U) :
    IsLinKDerivation k IsLinKWeakening F ((L.erase T ∪ {U}) :: π) := by
  refine IsLinKDerivation.weak h hL (weak_rewrite himp) ?_
  intro S hS
  rcases Finset.mem_union.mp hS with hS | hS
  · exact LinKOne.lines_card h L hL S (Finset.mem_of_mem_erase hS)
  · rw [Finset.mem_singleton.mp hS]
    exact hU

/-- The core of the split, four lines: the tautology on `f`, two and-introductions and one cut.
From a line `LA` holding `U0` and a line `LB` holding `U1`, a line `R` holding
`U0 ∪ {f = 0}` and `U1 ∪ {f = 1}` and otherwise only terms of the rest of `LA` and `LB`. -/
theorem split_core {k : ℕ} {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation k IsLinKWeakening F π) {LA LB : LinKLine V} (hLA : LA ∈ π)
    (hLB : LB ∈ π) {U0 U1 : LinTerm V} (h0 : U0 ∈ LA) (h1 : U1 ∈ LB)
    (hc0 : U0.card + 1 ≤ k) (hc1 : U1.card + 1 ≤ k) (f : Finset V) :
    ∃ A B R : LinKLine V,
      IsLinKDerivation k IsLinKWeakening F (R :: B :: A :: tautLine f :: π) ∧
      U0 ∪ {(f, false)} ∈ R ∧ U1 ∪ {(f, true)} ∈ R ∧
      ∀ S ∈ R, S ∈ LA.erase U0 ∨ S ∈ LB.erase U1 ∨ S = U0 ∪ {(f, false)} ∨
        S = U1 ∪ {(f, true)} := by
  have hk : 1 ≤ k := by omega
  have hπ1 := taut_line hk h hLA f
  have hne : ({(f, false)} : LinTerm V) ≠ {(f, true)} := by
    intro heq
    have := Finset.singleton_injective heq
    simp at this
  have ht0 : ({(f, false)} : LinTerm V) ∈ tautLine f := (mem_tautLine f _).mpr (Or.inl rfl)
  have ht1 : ({(f, true)} : LinTerm V) ∈ tautLine f := (mem_tautLine f _).mpr (Or.inr rfl)
  obtain ⟨A, hA⟩ : ∃ A : LinKLine V,
      A = (LA.erase U0 ∪ (tautLine f).erase {(f, false)}) ∪ {U0 ∪ {(f, false)}} := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : LinKLine V,
      B = (LB.erase U1 ∪ (tautLine f).erase {(f, true)}) ∪ {U1 ∪ {(f, true)}} := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : LinKLine V, R = B.erase {(f, false)} ∪
      (A \ ({(f, false)} : LinTerm V).image (fun e => ({negLinEq e} : LinTerm V))) := ⟨_, rfl⟩
  have hAmem : ∀ S : LinTerm V, S ∈ A ↔
      (S ∈ LA.erase U0 ∨ S ∈ (tautLine f).erase {(f, false)}) ∨ S = U0 ∪ {(f, false)} := by
    intro S
    rw [hA, Finset.mem_union, Finset.mem_union, Finset.mem_singleton]
  have hBmem : ∀ S : LinTerm V, S ∈ B ↔
      (S ∈ LB.erase U1 ∨ S ∈ (tautLine f).erase {(f, true)}) ∨ S = U1 ∪ {(f, true)} := by
    intro S
    rw [hB, Finset.mem_union, Finset.mem_union, Finset.mem_singleton]
  have hRmem : ∀ S : LinTerm V, S ∈ R ↔
      (S ≠ {(f, false)} ∧ S ∈ B) ∨ (S ∈ A ∧ ¬ S = {(f, true)}) := by
    intro S
    rw [hR, Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff, Finset.image_singleton,
      Finset.mem_singleton]
    exact Iff.rfl
  have hcA : ∀ S ∈ A, S.card ≤ k := by
    intro S hS
    rcases (hAmem S).mp hS with (hS | hS) | hS
    · exact LinKOne.lines_card h LA hLA S (Finset.mem_of_mem_erase hS)
    · exact (tautLine_card f S (Finset.mem_of_mem_erase hS)).trans hk
    · rw [hS]
      exact (Finset.card_union_le _ _).trans (by rw [Finset.card_singleton]; exact hc0)
  have hcB : ∀ S ∈ B, S.card ≤ k := by
    intro S hS
    rcases (hBmem S).mp hS with (hS | hS) | hS
    · exact LinKOne.lines_card h LB hLB S (Finset.mem_of_mem_erase hS)
    · exact (tautLine_card f S (Finset.mem_of_mem_erase hS)).trans hk
    · rw [hS]
      exact (Finset.card_union_le _ _).trans (by rw [Finset.card_singleton]; exact hc1)
  have hcR : ∀ S ∈ R, S.card ≤ k := by
    intro S hS
    rcases (hRmem S).mp hS with hS | hS
    · exact hcB S hS.2
    · exact hcA S hS.1
  have hπ2 : IsLinKDerivation k IsLinKWeakening F (A :: tautLine f :: π) :=
    IsLinKDerivation.andIntro hπ1 (List.mem_cons_of_mem _ hLA) List.mem_cons_self
      ⟨U0, {(f, false)}, h0, ht0, hA⟩ hcA
  have hπ3 : IsLinKDerivation k IsLinKWeakening F (B :: A :: tautLine f :: π) :=
    IsLinKDerivation.andIntro hπ2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hLB))
      (List.mem_cons_of_mem _ List.mem_cons_self) ⟨U1, {(f, true)}, h1, ht1, hB⟩ hcB
  have hfB : ({(f, false)} : LinTerm V) ∈ B :=
    (hBmem _).mpr (Or.inl (Or.inr (Finset.mem_erase.mpr ⟨hne, ht0⟩)))
  have hfA : ({(f, true)} : LinTerm V) ∈ A :=
    (hAmem _).mpr (Or.inl (Or.inr (Finset.mem_erase.mpr ⟨hne.symm, ht1⟩)))
  have hcut : IsLinKCut B A R := by
    refine ⟨{(f, false)}, hfB, ?_, hR⟩
    intro e he
    rw [Finset.mem_singleton.mp he]
    exact hfA
  have hπ4 : IsLinKDerivation k IsLinKWeakening F (R :: B :: A :: tautLine f :: π) :=
    IsLinKDerivation.cut hπ3 List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
      hcut hcR
  have hT0 : U0 ∪ {(f, false)} ≠ ({(f, true)} : LinTerm V) := by
    intro heq
    have hmem : (f, false) ∈ U0 ∪ {(f, false)} :=
      Finset.mem_union_right _ (Finset.mem_singleton_self _)
    rw [heq] at hmem
    simp at hmem
  have hT1 : U1 ∪ {(f, true)} ≠ ({(f, false)} : LinTerm V) := by
    intro heq
    have hmem : (f, true) ∈ U1 ∪ {(f, true)} :=
      Finset.mem_union_right _ (Finset.mem_singleton_self _)
    rw [heq] at hmem
    simp at hmem
  refine ⟨A, B, R, hπ4, (hRmem _).mpr (Or.inr ⟨(hAmem _).mpr (Or.inr rfl), hT0⟩),
    (hRmem _).mpr (Or.inl ⟨hT1, (hBmem _).mpr (Or.inr rfl)⟩), ?_⟩
  intro S hS
  rcases (hRmem S).mp hS with ⟨hne', hSB⟩ | ⟨hSA, hne'⟩
  · rcases (hBmem S).mp hSB with (hS' | hS') | hS'
    · exact Or.inr (Or.inl hS')
    · rcases (mem_tautLine f S).mp (Finset.mem_of_mem_erase hS') with h' | h'
      · exact absurd h' hne'
      · exact absurd h' (Finset.ne_of_mem_erase hS')
    · exact Or.inr (Or.inr (Or.inr hS'))
  · rcases (hAmem S).mp hSA with (hS' | hS') | hS'
    · exact Or.inl hS'
    · rcases (mem_tautLine f S).mp (Finset.mem_of_mem_erase hS') with h' | h'
      · exact absurd h' (Finset.ne_of_mem_erase hS')
      · exact absurd h' hne'
    · exact Or.inr (Or.inr (Or.inl hS'))

/-- (ii) The case split of a term on one linear form: from a line `L` holding `T` with
`T.card + 1 ≤ k`, the line `L` without `T` together with `T ∪ {f = 0}` and `T ∪ {f = 1}`, in
five more lines. -/
theorem split_one {k : ℕ} {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation k IsLinKWeakening F π) {L : LinKLine V} (hL : L ∈ π)
    {T : LinTerm V} (hT : T ∈ L) (hc : T.card + 1 ≤ k) (f : Finset V) :
    ∃ new : List (LinKLine V), new.length = 5 ∧
      IsLinKDerivation k IsLinKWeakening F (new ++ π) ∧
      L.erase T ∪ {T ∪ {(f, false)}, T ∪ {(f, true)}} ∈ new := by
  obtain ⟨A, B, R, hπ, hT0, hT1, hR⟩ := split_core h hL hL hT hT hc hc f
  have hcard := LinKOne.lines_card hπ R List.mem_cons_self
  refine ⟨[L.erase T ∪ {T ∪ {(f, false)}, T ∪ {(f, true)}}, R, B, A, tautLine f], rfl, ?_,
    List.mem_cons_self⟩
  refine IsLinKDerivation.weak hπ List.mem_cons_self ?_ ?_
  · intro S hS
    refine Or.inl ⟨S, ?_, fun _ hs => hs⟩
    rcases hR S hS with h' | h' | h' | h'
    · exact Finset.mem_union_left _ h'
    · exact Finset.mem_union_left _ h'
    · rw [h']
      exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    · rw [h']
      exact Finset.mem_union_right _
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  · intro S hS
    rcases Finset.mem_union.mp hS with hS | hS
    · exact LinKOne.lines_card h L hL S (Finset.mem_of_mem_erase hS)
    · rcases Finset.mem_insert.mp hS with hS | hS
      · rw [hS]
        exact hcard _ hT0
      · rw [Finset.mem_singleton.mp hS]
        exact hcard _ hT1

/-- `Splits k M T n`: a decision tree with `n` queries carries the term `T` into the line `M`
within terms of at most `k` equations. At a leaf the term implies one term of `M`, or the
disjunction of the one-equation terms of `M`. At a query on the linear form `f` the term is
first rewritten into a term `U0` it implies for the branch `f = 0` and a term `U1` it implies
for the branch `f = 1`, each with room for one more equation. -/
inductive Splits (k : ℕ) (M : LinKLine V) : LinTerm V → ℕ → Prop
  | leaf {T : LinTerm V} : IsLinKWeakening {T} M → Splits k M T 0
  | node {T U0 U1 : LinTerm V} {f : Finset V} {n0 n1 : ℕ} :
      (∀ a : V → Bool, LinTermSat a T → LinTermSat a U0) →
      (∀ a : V → Bool, LinTermSat a T → LinTermSat a U1) →
      U0.card + 1 ≤ k → U1.card + 1 ≤ k →
      Splits k M (U0 ∪ {(f, false)}) n0 → Splits k M (U1 ∪ {(f, true)}) n1 →
      Splits k M T (n0 + n1 + 1)

theorem Splits.mono {k : ℕ} {M M' : LinKLine V} (hM : M ⊆ M') {T : LinTerm V} {n : ℕ}
    (h : Splits k M T n) : Splits k M' T n := by
  induction h with
  | leaf hw => exact Splits.leaf (weak_mono hw hM)
  | node i0 i1 c0 c1 _ _ ih0 ih1 => exact Splits.node i0 i1 c0 c1 ih0 ih1

/-- The split along a decision tree, in the form that iterates: the target `M'` is any line
containing the leaves' line `M`, with terms of at most `k` equations, to which the rest of `L`
weakens termwise. -/
theorem split_tree_aux {k : ℕ} {F : Set (LinKLine V)} {M : LinKLine V} {T : LinTerm V}
    {n : ℕ} (hs : Splits k M T n) :
    ∀ (M' : LinKLine V) (π : List (LinKLine V)) (L : LinKLine V), M ⊆ M' →
      (∀ S ∈ M', S.card ≤ k) → IsLinKDerivation k IsLinKWeakening F π → L ∈ π → T ∈ L →
      IsLinKWeakening (L.erase T) M' →
      ∃ new : List (LinKLine V), new.length ≤ 7 * n + 1 ∧
        IsLinKDerivation k IsLinKWeakening F (new ++ π) ∧ M' ∈ new := by
  induction hs with
  | @leaf T hw =>
    intro M' π L hM hk hπ hL hT hrest
    refine ⟨[M'], by simp, IsLinKDerivation.weak hπ hL ?_ hk, List.mem_cons_self⟩
    intro S hS
    by_cases hST : S = T
    · rw [hST]
      exact weak_mono hw hM T (Finset.mem_singleton_self _)
    · exact hrest S (Finset.mem_erase.mpr ⟨hST, hS⟩)
  | @node T U0 U1 f n0 n1 i0 i1 c0 c1 _ _ ih0 ih1 =>
    intro M' π L hM hk hπ hL hT hrest
    have hπa := rewrite_term hπ hL (T := T) (U := U0) (by omega) i0
    have hπb := rewrite_term hπa (List.mem_cons_of_mem _ hL) (T := T) (U := U1) (by omega) i1
    obtain ⟨A, B, R, hπr, hT0, hT1, hR⟩ := split_core hπb
      (LA := L.erase T ∪ {U0}) (LB := L.erase T ∪ {U1})
      (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
      (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      (Finset.mem_union_right _ (Finset.mem_singleton_self _)) c0 c1 f
    have hcT1 : (U1 ∪ {(f, true)}).card ≤ k :=
      LinKOne.lines_card hπr R List.mem_cons_self _ hT1
    have hrestU : ∀ (U S : LinTerm V), S ∈ (L.erase T ∪ {U}).erase U → S ∈ L.erase T := by
      intro U S hS
      obtain ⟨hne, hS'⟩ := Finset.mem_erase.mp hS
      rcases Finset.mem_union.mp hS' with h' | h'
      · exact h'
      · exact absurd (Finset.mem_singleton.mp h') hne
    have hw0 : IsLinKWeakening (R.erase (U0 ∪ {(f, false)}))
        (insert (U1 ∪ {(f, true)}) M') := by
      intro S hS
      obtain ⟨hne, hSR⟩ := Finset.mem_erase.mp hS
      rcases hR S hSR with h' | h' | h' | h'
      · exact weak_mono hrest (Finset.subset_insert _ _) S (hrestU U0 S h')
      · exact weak_mono hrest (Finset.subset_insert _ _) S (hrestU U1 S h')
      · exact absurd h' hne
      · exact Or.inl ⟨S, by rw [h']; exact Finset.mem_insert_self _ _, fun _ hs => hs⟩
    have hk0 : ∀ S ∈ insert (U1 ∪ {(f, true)}) M', S.card ≤ k := by
      intro S hS
      rcases Finset.mem_insert.mp hS with hS | hS
      · rw [hS]
        exact hcT1
      · exact hk S hS
    obtain ⟨new0, hl0, hπ0, hm0⟩ := ih0 (insert (U1 ∪ {(f, true)}) M') _ R
      (hM.trans (Finset.subset_insert _ _)) hk0 hπr List.mem_cons_self hT0 hw0
    have hw1 : IsLinKWeakening ((insert (U1 ∪ {(f, true)}) M').erase (U1 ∪ {(f, true)}))
        M' := by
      intro S hS
      obtain ⟨hne, h'⟩ := Finset.mem_erase.mp hS
      exact Or.inl ⟨S, (Finset.mem_insert.mp h').resolve_left hne, fun _ hs => hs⟩
    obtain ⟨new1, hl1, hπ1, hm1⟩ := ih1 M' _ _ hM hk hπ0 (List.mem_append_left _ hm0)
      (Finset.mem_insert_self _ _) hw1
    refine ⟨new1 ++ (new0 ++ [R, B, A, tautLine f, L.erase T ∪ {U1}, L.erase T ∪ {U0}]),
      ?_, ?_, List.mem_append_left _ hm1⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · simpa [List.append_assoc] using hπ1

/-- The case split along a decision tree: if `T` is a term of a line `L` of a derivation, `M`
is a line with terms of at most `k` equations to which the rest of `L` weakens termwise, and a
decision tree with `n` queries carries `T` into `M`, then `M` is derived in at most
`7 * n + 1` more lines. -/
theorem split_tree {k : ℕ} {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation k IsLinKWeakening F π) {L : LinKLine V} (hL : L ∈ π)
    {T : LinTerm V} (hT : T ∈ L) {M : LinKLine V} (hk : ∀ S ∈ M, S.card ≤ k)
    (hrest : IsLinKWeakening (L.erase T) M) {n : ℕ} (hs : Splits k M T n) :
    ∃ new : List (LinKLine V), new.length ≤ 7 * n + 1 ∧
      IsLinKDerivation k IsLinKWeakening F (new ++ π) ∧ M ∈ new :=
  split_tree_aux hs M π L subset_rfl hk h hL hT hrest

/-- The case split in the usual shape: the term `T` of `L` is replaced by the terms of `S`. -/
theorem split_erase {k : ℕ} {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation k IsLinKWeakening F π) {L : LinKLine V} (hL : L ∈ π)
    {T : LinTerm V} (hT : T ∈ L) {S : LinKLine V} (hk : ∀ U ∈ S, U.card ≤ k) {n : ℕ}
    (hs : Splits k S T n) :
    ∃ new : List (LinKLine V), new.length ≤ 7 * n + 1 ∧
      IsLinKDerivation k IsLinKWeakening F (new ++ π) ∧ L.erase T ∪ S ∈ new := by
  refine split_tree h hL hT ?_ ?_ (hs.mono Finset.subset_union_right)
  · intro U hU
    rcases Finset.mem_union.mp hU with hU | hU
    · exact LinKOne.lines_card h L hL U (Finset.mem_of_mem_erase hU)
    · exact hk U hU
  · exact fun U hU => Or.inl ⟨U, Finset.mem_union_left _ hU, fun _ hs => hs⟩

omit [DecidableEq V] in
theorem sat_single (a : V → Bool) (x : V) (b : Bool) :
    LinEqSat a (({x} : Finset V), b) ↔ a x = b := by
  unfold LinEqSat
  rw [Finset.filter_singleton]
  cases h1 : a x <;> cases b <;> simp

theorem sat_pair (a : V → Bool) {x y : V} (hxy : x ≠ y) (b : Bool) :
    LinEqSat a (({x, y} : Finset V), b) ↔ (a x != a y) = b := by
  unfold LinEqSat
  rw [Finset.filter_insert, Finset.filter_singleton]
  cases h1 : a x <;> cases h2 : a y <;> cases b <;> simp [hxy]

/-- The example: at `k = 2` the term `{x + y = 1}` splits into `{x = 1, y = 0}` or
`{x = 0, y = 1}` in at most eight lines. -/
theorem split_xor {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation 2 IsLinKWeakening F π) {L : LinKLine V} (hL : L ∈ π) {x y : V}
    (hxy : x ≠ y) (hT : ({(({x, y} : Finset V), true)} : LinTerm V) ∈ L) :
    ∃ new : List (LinKLine V), new.length ≤ 8 ∧
      IsLinKDerivation 2 IsLinKWeakening F (new ++ π) ∧
      L.erase {(({x, y} : Finset V), true)} ∪
        {{(({x} : Finset V), true), (({y} : Finset V), false)},
         {(({x} : Finset V), false), (({y} : Finset V), true)}} ∈ new := by
  refine split_erase h hL hT ?_ (n := 0 + 0 + 1) ?_
  · intro U hU
    rcases Finset.mem_insert.mp hU with hU | hU
    · rw [hU]
      exact Finset.card_le_two
    · rw [Finset.mem_singleton.mp hU]
      exact Finset.card_le_two
  · refine Splits.node (U0 := {(({x, y} : Finset V), true)})
      (U1 := {(({x, y} : Finset V), true)}) (f := {x}) (fun _ hs => hs) (fun _ hs => hs)
      (by simp) (by simp) (Splits.leaf ?_) (Splits.leaf ?_)
    · intro S hS
      rw [Finset.mem_singleton.mp hS]
      refine Or.inl ⟨{(({x} : Finset V), false), (({y} : Finset V), true)},
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
      intro a hs
      have h1 := (sat_pair a hxy true).mp (hs _ (Finset.mem_union_left _
        (Finset.mem_singleton_self _)))
      have h2 := (sat_single a x false).mp (hs _ (Finset.mem_union_right _
        (Finset.mem_singleton_self _)))
      intro q hq
      rcases Finset.mem_insert.mp hq with hq | hq
      · rw [hq]
        exact (sat_single a x false).mpr h2
      · rw [Finset.mem_singleton.mp hq]
        refine (sat_single a y true).mpr ?_
        rw [h2] at h1
        simpa using h1
    · intro S hS
      rw [Finset.mem_singleton.mp hS]
      refine Or.inl ⟨{(({x} : Finset V), true), (({y} : Finset V), false)},
        Finset.mem_insert_self _ _, ?_⟩
      intro a hs
      have h1 := (sat_pair a hxy true).mp (hs _ (Finset.mem_union_left _
        (Finset.mem_singleton_self _)))
      have h2 := (sat_single a x true).mp (hs _ (Finset.mem_union_right _
        (Finset.mem_singleton_self _)))
      intro q hq
      rcases Finset.mem_insert.mp hq with hq | hq
      · rw [hq]
        exact (sat_single a x true).mpr h2
      · rw [Finset.mem_singleton.mp hq]
        refine (sat_single a y false).mpr ?_
        rw [h2] at h1
        simpa using h1

/-- The bound on the number of lines of the general split into `c` terms. -/
def splitCost (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | c + 1 => 2 + k * (splitCost k c + 1)

theorem splitCost_le {k : ℕ} (hk : 1 ≤ k) (c : ℕ) : splitCost k c + 2 ≤ 3 * (k + 1) ^ c := by
  induction c with
  | zero => simp [splitCost]
  | succ c ih =>
    have hP : 1 ≤ (k + 1) ^ c := Nat.one_le_pow _ _ (by omega)
    have h1 := Nat.mul_le_mul_left k ih
    have e1 : k * (splitCost k c + 1) = k * splitCost k c + k := by
      rw [Nat.mul_add, Nat.mul_one]
    have e2 : (k + 1) ^ c * (k + 1) = k * (k + 1) ^ c + (k + 1) ^ c := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
    have e3 : k * (splitCost k c + 2) = k * splitCost k c + 2 * k := by
      rw [Nat.mul_add, Nat.mul_comm k 2]
    have e4 : k * (3 * (k + 1) ^ c) = 3 * (k * (k + 1) ^ c) := Nat.mul_left_comm _ _ _
    rw [e3, e4] at h1
    simp only [splitCost, pow_succ]
    rw [e1, e2]
    omega

/-- The general split, in the form that iterates: if `T` implies the disjunction of the terms
of the list `Ss` and the equations of `G`, the line holding the rest of `L`, the terms of `Ss`
and the one-equation terms of `G` is derived in at most `splitCost k Ss.length` lines. The
disjunction of terms is expanded into its clauses, one and-introduction at a time. -/
theorem split_any_aux {k : ℕ} (hk : 1 ≤ k) {F : Set (LinKLine V)} (L : LinKLine V)
    (T : LinTerm V) :
    ∀ (Ss : List (LinTerm V)), (∀ U ∈ Ss, U.card ≤ k) →
      ∀ (G : Finset (LinEq V)) (π : List (LinKLine V)),
      IsLinKDerivation k IsLinKWeakening F π → L ∈ π →
      (∀ a : V → Bool, LinTermSat a T →
        (∃ U ∈ Ss, LinTermSat a U) ∨ ∃ q ∈ G, LinEqSat a q) →
      ∃ new : List (LinKLine V), new.length ≤ splitCost k Ss.length ∧
        IsLinKDerivation k IsLinKWeakening F (new ++ π) ∧
        (L.erase T ∪ Ss.toFinset) ∪ G.image (fun q => ({q} : LinTerm V)) ∈ new := by
  intro Ss
  induction Ss with
  | nil =>
    intro _ G π hπ hL hsem
    refine ⟨[_], by simp [splitCost], IsLinKDerivation.weak hπ hL ?_ ?_, List.mem_cons_self⟩
    · intro S hS
      by_cases hST : S = T
      · right
        intro a ha
        rw [hST] at ha
        rcases hsem a ha with ⟨U, hU, -⟩ | ⟨q, hq, hqs⟩
        · simp at hU
        · exact ⟨q, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq), hqs⟩
      · exact Or.inl ⟨S, Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨hST, hS⟩)), fun _ hs => hs⟩
    · intro S hS
      rcases Finset.mem_union.mp hS with hS | hS
      · rcases Finset.mem_union.mp hS with hS | hS
        · exact LinKOne.lines_card hπ L hL S (Finset.mem_of_mem_erase hS)
        · simp at hS
      · obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hS
        rw [Finset.card_singleton]
        exact hk
  | cons U Ss ih =>
    intro hcard G π hπ hL hsem
    have hcU := hcard U List.mem_cons_self
    have ih' := ih (fun U' hU' => hcard U' (List.mem_cons_of_mem _ hU'))
    obtain ⟨base, hbase⟩ : ∃ base : LinKLine V,
        base = (L.erase T ∪ Ss.toFinset) ∪ G.image (fun q => ({q} : LinTerm V)) := ⟨_, rfl⟩
    have inner : ∀ E : Finset (LinEq V), E ⊆ U → ∀ π : List (LinKLine V),
        IsLinKDerivation k IsLinKWeakening F π → L ∈ π →
        ∃ (new : List (LinKLine V)) (X : LinKLine V),
          new.length ≤ 1 + E.card * (splitCost k Ss.length + 1) ∧
          IsLinKDerivation k IsLinKWeakening F (new ++ π) ∧ X ∈ new ∧ E ∈ X ∧
          ∀ S ∈ X, S ∈ base ∨ S = E := by
      intro E
      induction E using Finset.induction_on with
      | empty =>
        intro _ π hπ hL
        refine ⟨[L.erase T ∪ {(∅ : LinTerm V)}], _, by simp,
          rewrite_term hπ hL (Nat.zero_le _)
            (fun _ _ q hq => absurd hq (Finset.notMem_empty q)),
          List.mem_cons_self, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
        intro S hS
        rcases Finset.mem_union.mp hS with hS | hS
        · left
          rw [hbase]
          exact Finset.mem_union_left _ (Finset.mem_union_left _ hS)
        · exact Or.inr (Finset.mem_singleton.mp hS)
      | insert e E' he ih2 =>
        intro hsub π hπ hL
        have hE' : E' ⊆ U := (Finset.subset_insert _ _).trans hsub
        have heU : e ∈ U := hsub (Finset.mem_insert_self _ _)
        obtain ⟨new1, X, hl1, hπ1, hX, hEX, hXall⟩ := ih2 hE' π hπ hL
        have hsem' : ∀ a : V → Bool, LinTermSat a T →
            (∃ U' ∈ Ss, LinTermSat a U') ∨ ∃ q ∈ insert e G, LinEqSat a q := by
          intro a ha
          rcases hsem a ha with ⟨U', hU', hs⟩ | ⟨q, hq, hqs⟩
          · rcases List.mem_cons.mp hU' with hU' | hU'
            · rw [hU'] at hs
              exact Or.inr ⟨e, Finset.mem_insert_self _ _, hs e heU⟩
            · exact Or.inl ⟨U', hU', hs⟩
          · exact Or.inr ⟨q, Finset.mem_insert_of_mem hq, hqs⟩
        obtain ⟨new2, hl2, hπ2, hY⟩ := ih' (insert e G) (new1 ++ π) hπ1
          (List.mem_append_right _ hL) hsem'
        obtain ⟨Y, hYdef⟩ : ∃ Y : LinKLine V, Y = (L.erase T ∪ Ss.toFinset) ∪
            (insert e G).image (fun q => ({q} : LinTerm V)) := ⟨_, rfl⟩
        rw [← hYdef] at hY
        have hYall : ∀ S ∈ Y, S ∈ base ∨ S = {e} := by
          intro S hS
          rw [hYdef] at hS
          rcases Finset.mem_union.mp hS with h' | h'
          · left
            rw [hbase]
            exact Finset.mem_union_left _ h'
          · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h'
            rcases Finset.mem_insert.mp hq with hq | hq
            · right
              rw [hq]
            · left
              rw [hbase]
              exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq)
        have heY : ({e} : LinTerm V) ∈ Y := by
          rw [hYdef]
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))
        have hXπ : X ∈ new2 ++ (new1 ++ π) :=
          List.mem_append_right _ (List.mem_append_left _ hX)
        have hYπ : Y ∈ new2 ++ (new1 ++ π) := List.mem_append_left _ hY
        obtain ⟨R, hR⟩ : ∃ R : LinKLine V,
            R = (X.erase E' ∪ Y.erase {e}) ∪ {E' ∪ {e}} := ⟨_, rfl⟩
        have hins : E' ∪ {e} = insert e E' := by
          rw [Finset.insert_eq, Finset.union_comm]
        have hRall : ∀ S ∈ R, S ∈ base ∨ S = insert e E' := by
          intro S hS
          rw [hR] at hS
          rcases Finset.mem_union.mp hS with h' | h'
          · rcases Finset.mem_union.mp h' with h' | h'
            · obtain ⟨hne, hSX⟩ := Finset.mem_erase.mp h'
              exact Or.inl ((hXall S hSX).resolve_right hne)
            · obtain ⟨hne, hSY⟩ := Finset.mem_erase.mp h'
              exact Or.inl ((hYall S hSY).resolve_right hne)
          · right
            rw [Finset.mem_singleton.mp h', hins]
        have hcR : ∀ S ∈ R, S.card ≤ k := by
          intro S hS
          rw [hR] at hS
          rcases Finset.mem_union.mp hS with h' | h'
          · rcases Finset.mem_union.mp h' with h' | h'
            · exact LinKOne.lines_card hπ2 X hXπ S (Finset.mem_of_mem_erase h')
            · exact LinKOne.lines_card hπ2 Y hYπ S (Finset.mem_of_mem_erase h')
          · rw [Finset.mem_singleton.mp h', hins]
            exact (Finset.card_le_card hsub).trans hcU
        have hπ3 : IsLinKDerivation k IsLinKWeakening F (R :: (new2 ++ (new1 ++ π))) :=
          IsLinKDerivation.andIntro hπ2 hXπ hYπ ⟨E', {e}, hEX, heY, hR⟩ hcR
        refine ⟨R :: (new2 ++ new1), R, ?_, ?_, List.mem_cons_self, ?_, hRall⟩
        · rw [Finset.card_insert_of_notMem he]
          simp only [List.length_cons, List.length_append]
          have : (E'.card + 1) * (splitCost k Ss.length + 1) =
              E'.card * (splitCost k Ss.length + 1) + (splitCost k Ss.length + 1) := by
            rw [Nat.add_mul, Nat.one_mul]
          omega
        · simpa [List.append_assoc] using hπ3
        · rw [hR, ← hins]
          exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    obtain ⟨new1, X, hl, hπ1, hX, hUX, hXall⟩ := inner U subset_rfl π hπ hL
    have hMmem : ∀ S : LinTerm V, S ∈ base ∨ S = U →
        S ∈ (L.erase T ∪ (U :: Ss).toFinset) ∪ G.image (fun q => ({q} : LinTerm V)) := by
      intro S hS
      rw [hbase] at hS
      simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at hS ⊢
      tauto
    refine ⟨_ :: new1, ?_, IsLinKDerivation.weak hπ1 (List.mem_append_left _ hX)
      (fun S hS => Or.inl ⟨S, hMmem S (hXall S hS), fun _ hs => hs⟩) ?_, List.mem_cons_self⟩
    · have := Nat.mul_le_mul_right (splitCost k Ss.length + 1) hcU
      simp only [List.length_cons, splitCost]
      omega
    · intro S hS
      rcases Finset.mem_union.mp hS with hS | hS
      · rcases Finset.mem_union.mp hS with hS | hS
        · exact LinKOne.lines_card hπ L hL S (Finset.mem_of_mem_erase hS)
        · exact hcard S (List.mem_toFinset.mp hS)
      · obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hS
        rw [Finset.card_singleton]
        exact hk

/-- Every sound split is derivable: if every assignment satisfying `T` satisfies some term of
`S`, and the terms of `S` have at most `k` equations, the line `L` without `T` together with
`S` is derived in at most `splitCost k S.card` more lines, with no hypothesis on the size of
`T`. The bound is exponential in `S.card` (`splitCost_le`). -/
theorem split_any {k : ℕ} (hk : 1 ≤ k) {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation k IsLinKWeakening F π) {L : LinKLine V} (hL : L ∈ π)
    (T : LinTerm V) (S : LinKLine V) (hS : ∀ U ∈ S, U.card ≤ k)
    (hsem : ∀ a : V → Bool, LinTermSat a T → ∃ U ∈ S, LinTermSat a U) :
    ∃ new : List (LinKLine V), new.length ≤ splitCost k S.card ∧
      IsLinKDerivation k IsLinKWeakening F (new ++ π) ∧ L.erase T ∪ S ∈ new := by
  obtain ⟨new, hl, hπ, hm⟩ := split_any_aux hk L T S.toList
    (fun U hU => hS U (Finset.mem_toList.mp hU)) ∅ π h hL
    (fun a ha => Or.inl (by
      obtain ⟨U, hU, hs⟩ := hsem a ha
      exact ⟨U, Finset.mem_toList.mpr hU, hs⟩))
  rw [Finset.length_toList] at hl
  rw [Finset.toList_toFinset, Finset.image_empty, Finset.union_empty] at hm
  exact ⟨new, hl, hπ, hm⟩

/-- If `F` is unsatisfiable, every assignment satisfies some term "clause `C` is false": the
split of any term into these terms is sound. -/
theorem falseTerms_cover (F : Finset (Clause V))
    (hunsat : ¬ Satisfiable (↑F : Set (Clause V))) (a : V → Bool) :
    ∃ U ∈ F.image LinKTrivial.falseTerm, LinTermSat a U := by
  by_contra hcon
  refine hunsat ⟨a, fun C hC => ?_⟩
  by_contra hns
  exact hcon ⟨LinKTrivial.falseTerm C, Finset.mem_image_of_mem _ (Finset.mem_coe.mp hC),
    LinKTrivial.falseTerm_sat a C hns⟩

/-- Axioms are added on top of a derivation. -/
theorem append_axioms {k : ℕ} {W : LinKLine V → LinKLine V → Prop} {F : Set (Clause V)}
    (l : List (Clause V)) (hF : ∀ C ∈ l, C ∈ F) (hk : ∀ C ∈ l, C.card ≤ k)
    {π : List (LinKLine V)} (h : IsLinKDerivation k W ((fun C => linKOfClause C) '' F) π) :
    IsLinKDerivation k W ((fun C => linKOfClause C) '' F) (l.map linKOfClause ++ π) := by
  induction l with
  | nil => exact h
  | cons C l ih =>
    refine IsLinKDerivation.ax
      (ih (fun D hD => hF D (List.mem_cons_of_mem _ hD))
        (fun D hD => hk D (List.mem_cons_of_mem _ hD)))
      ⟨C, hF C List.mem_cons_self, rfl⟩ ?_
    intro T hT
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨l', hl', -⟩ := Finset.mem_image.mp hq
    rw [Finset.card_singleton]
    exact (Finset.card_pos.mpr ⟨l', hl'⟩).trans_le (hk C List.mem_cons_self)

/-- One cut for each clause of the list `l` whose axiom is in the derivation, for any
weakening relation: from a line `L` to a line inside `L` holding no `falseTerm C` for `C` in
`l`. -/
theorem cut_steps (k : ℕ) (W : LinKLine V → LinKLine V → Prop) (F : Set (LinKLine V))
    (l : List (Clause V)) :
    ∀ (π : List (LinKLine V)) (L : LinKLine V), IsLinKDerivation k W F π → L ∈ π →
      (∀ T ∈ L, T.card ≤ k) → (∀ C ∈ l, linKOfClause C ∈ π) →
      ∃ (π' : List (LinKLine V)) (L' : LinKLine V), IsLinKDerivation k W F π' ∧
        L' ∈ π' ∧ L' ⊆ L ∧ (∀ C ∈ l, LinKTrivial.falseTerm C ∉ L') ∧
        π'.length ≤ π.length + l.length := by
  induction l with
  | nil =>
    intro π L hπ hL _ _
    exact ⟨π, L, hπ, hL, subset_rfl, by simp, by simp⟩
  | cons C l ih =>
    intro π L hπ hL hk hax
    by_cases hT : LinKTrivial.falseTerm C ∈ L
    · have hcut : IsLinKCut L (linKOfClause C) (L.erase (LinKTrivial.falseTerm C)) :=
        ⟨LinKTrivial.falseTerm C, hT, LinKTrivial.neg_mem_axiom C,
          by rw [LinKTrivial.leftover_empty, Finset.union_empty]⟩
      have hk' : ∀ T ∈ L.erase (LinKTrivial.falseTerm C), T.card ≤ k :=
        fun T hT' => hk T (Finset.mem_of_mem_erase hT')
      obtain ⟨π', L', hπ', hL', hsub, hno, hlen⟩ :=
        ih (L.erase (LinKTrivial.falseTerm C) :: π) _
          (IsLinKDerivation.cut hπ hL (hax C List.mem_cons_self) hcut hk')
          List.mem_cons_self hk'
          (fun D hD => List.mem_cons_of_mem _ (hax D (List.mem_cons_of_mem _ hD)))
      refine ⟨π', L', hπ', hL', hsub.trans (Finset.erase_subset _ _), ?_, ?_⟩
      · intro D hD
        rcases List.mem_cons.mp hD with rfl | hD
        · exact fun h => Finset.notMem_erase _ _ (hsub h)
        · exact hno D hD
      · simp only [List.length_cons] at hlen ⊢
        omega
    · obtain ⟨π', L', hπ', hL', hsub, hno, hlen⟩ :=
        ih π L hπ hL hk (fun D hD => hax D (List.mem_cons_of_mem _ hD))
      refine ⟨π', L', hπ', hL', hsub, ?_, ?_⟩
      · intro D hD
        rcases List.mem_cons.mp hD with rfl | hD
        · exact fun h => hT (hsub h)
        · exact hno D hD
      · simp only [List.length_cons]
        omega

/-- The general split is as hard as refuting. A derivation from the clauses of `F` (of width
at most `k`) that holds the line of the terms "clause `C` is false", which is the split of the
true term (`falseTerms_cover`), extends to a refutation of `F` by at most `2 * F.card` lines:
the axioms, and one cut against each. -/
theorem refutation_of_split (F : Finset (Clause V)) (k : ℕ) (hk : ∀ C ∈ F, C.card ≤ k)
    {π : List (LinKLine V)}
    (h : IsLinKDerivation k IsLinKWeakening
      ((fun C => linKOfClause C) '' (↑F : Set (Clause V))) π)
    (hL : F.image LinKTrivial.falseTerm ∈ π) :
    ∃ π' : List (LinKLine V), IsLinKRefutation k (↑F : Set (Clause V)) π' ∧
      π'.length ≤ π.length + 2 * F.card := by
  have h1 := append_axioms F.toList
    (fun C hC => Finset.mem_coe.mpr (Finset.mem_toList.mp hC))
    (fun C hC => hk C (Finset.mem_toList.mp hC)) h
  obtain ⟨π', L', hπ', hL', hsub, hno, hlen⟩ :=
    cut_steps k _ _ F.toList _ (F.image LinKTrivial.falseTerm) h1
      (List.mem_append_right _ hL) (LinKOne.lines_card h _ hL)
      (fun C hC => List.mem_append_left _ (List.mem_map.mpr ⟨C, hC, rfl⟩))
  have hempty : L' = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro T hT
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp (hsub hT)
    exact hno C (Finset.mem_toList.mpr hC) hT
  rw [hempty] at hL'
  refine ⟨π', ⟨hπ', hL'⟩, ?_⟩
  simp only [List.length_append, List.length_map, Finset.length_toList] at hlen
  omega

end PEqualNP.ProofComplexity.Helpers.LinKSplit
