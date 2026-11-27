import PEqualNP.Defs.ProofComplexityResK
import PEqualNP.ProofComplexity.Helpers.LinKOne

/-!
# Helpers: what Res(k, ⊕) with termwise weakening contains

Three checks that the definition is not accidentally weak. A derivation with terms of at most
`k` equations is one with terms of at most `k'` equations for `k ≤ k'`, so Res(⊕) sits inside
every Res(k, ⊕) with `1 ≤ k`. The `k`-DNF resolution Res(k) maps line by line into Res(k, ⊕):
a literal `(v, s)` goes to the equation `v = s`, weakening and and-elimination become termwise
weakening, and-introduction and cut go to the rules of the same name. And termwise weakening
contains both syntactic weakenings: adding terms, and shrinking one term.
-/

namespace PEqualNP.ProofComplexity.Helpers.LinKStrength

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- The bound on the size of terms can be raised. -/
theorem mono {k k' : ℕ} (hkk : k ≤ k') {W : LinKLine V → LinKLine V → Prop}
    {F : Set (LinKLine V)} {π : List (LinKLine V)} (h : IsLinKDerivation k W F π) :
    IsLinKDerivation k' W F π := by
  induction h with
  | nil => exact IsLinKDerivation.nil
  | ax _ hCF hk ih => exact IsLinKDerivation.ax ih hCF (fun T hT => (hk T hT).trans hkk)
  | cut _ hC hD hcut hk ih =>
    exact IsLinKDerivation.cut ih hC hD hcut (fun T hT => (hk T hT).trans hkk)
  | andIntro _ hC hD hand hk ih =>
    exact IsLinKDerivation.andIntro ih hC hD hand (fun T hT => (hk T hT).trans hkk)
  | weak _ hC hw hk ih =>
    exact IsLinKDerivation.weak ih hC hw (fun T hT => (hk T hT).trans hkk)

/-- A Res(⊕) refutation gives a Res(k, ⊕) refutation of the same length, for `1 ≤ k`. -/
theorem lin_to_linK (F : Set (Clause V)) {k : ℕ} (hk : 1 ≤ k) {π : List (LinClause V)}
    (h : IsLinRefutation F π) :
    ∃ π' : List (LinKLine V), IsLinKRefutation k F π' ∧ π'.length = π.length := by
  obtain ⟨π', ⟨hd, he⟩, hl⟩ := (LinKOne.lin_iff_linK_one F π.length).mp ⟨π, h, rfl⟩
  exact ⟨π', ⟨mono hk hd, he⟩, hl⟩

omit [DecidableEq V] in
/-- Adding terms is a termwise weakening. -/
theorem weak_of_subset {L M : LinKLine V} (h : L ⊆ M) : IsLinKWeakening L M :=
  fun T hT => Or.inl ⟨T, h hT, fun _ hs => hs⟩

/-- Replacing a term by a part of it (the empty part included) is a termwise weakening. -/
theorem weak_of_andElim {L M : LinKLine V} {T T' : LinTerm V} (hsub : T' ⊆ T)
    (hM : M = L.erase T ∪ {T'}) : IsLinKWeakening L M := by
  subst hM
  intro S hS
  left
  by_cases hST : S = T
  · subst hST
    exact ⟨T', Finset.mem_union_right _ (Finset.mem_singleton_self _),
      fun a hs q hq => hs q (hsub hq)⟩
  · exact ⟨S, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hST, hS⟩), fun _ hs => hs⟩

/-- The literal `(v, s)` as the equation `v = s`. -/
def eqOf (l : Literal V) : LinEq V := ({l.1}, l.2)

omit [DecidableEq V] in
theorem eqOf_injective : Function.Injective (eqOf : Literal V → LinEq V) := by
  rintro ⟨v, s⟩ ⟨w, t⟩ h
  simp only [eqOf, Prod.mk.injEq, Finset.singleton_inj] at h
  exact Prod.ext h.1 h.2

/-- A term of literals as a term of equations. -/
def termOf (T : KTerm V) : LinTerm V := T.image eqOf

theorem termOf_injective : Function.Injective (termOf : KTerm V → LinTerm V) :=
  Finset.image_injective eqOf_injective

theorem termOf_card (T : KTerm V) : (termOf T).card = T.card :=
  Finset.card_image_of_injective _ eqOf_injective

theorem termOf_union (S T : KTerm V) : termOf (S ∪ T) = termOf S ∪ termOf T :=
  Finset.image_union _ _

theorem termOf_neg (l : Literal V) :
    termOf ({(l.1, !l.2)} : KTerm V) = {negLinEq (eqOf l)} :=
  Finset.image_singleton _ _

/-- A line of Res(k) as a line of Res(k, ⊕). -/
def lineOf (L : KLine V) : LinKLine V := L.image termOf

theorem lineOf_card {k : ℕ} {L : KLine V} (h : ∀ T ∈ L, T.card ≤ k) :
    ∀ T ∈ lineOf L, T.card ≤ k := by
  intro T hT
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
  rw [termOf_card]
  exact h S hS

theorem lineOf_union (L M : KLine V) : lineOf (L ∪ M) = lineOf L ∪ lineOf M :=
  Finset.image_union _ _

theorem lineOf_singleton (T : KTerm V) : lineOf {T} = {termOf T} :=
  Finset.image_singleton _ _

theorem lineOf_erase (L : KLine V) (T : KTerm V) :
    lineOf (L.erase T) = (lineOf L).erase (termOf T) :=
  Finset.image_erase termOf_injective L T

theorem lineOf_sdiff (L M : KLine V) : lineOf (L \ M) = lineOf L \ lineOf M :=
  Finset.image_sdiff L M termOf_injective

theorem lineOf_negs (T : KTerm V) :
    lineOf (T.image (fun l => ({(l.1, !l.2)} : KTerm V))) =
      (termOf T).image (fun e => ({negLinEq e} : LinTerm V)) := by
  unfold lineOf
  rw [Finset.image_image]
  unfold termOf
  rw [Finset.image_image]
  exact Finset.image_congr (fun l _ => termOf_neg l)

theorem lineOf_clause (C : Clause V) : lineOf (kLineOfClause C) = linKOfClause C := by
  unfold lineOf kLineOfClause linKOfClause linOfClause
  rw [Finset.image_image, Finset.image_image]
  exact Finset.image_congr (fun l _ => Finset.image_singleton eqOf l)

/-- Every term of every line of a Res(k) derivation has at most `k` literals. -/
theorem resK_lines_card {k : ℕ} {F : Set (KLine V)} {π : List (KLine V)}
    (h : IsResKDerivation k F π) : ∀ L ∈ π, ∀ T ∈ L, T.card ≤ k := by
  induction h with
  | nil => intro L hL; simp at hL
  | ax _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | weak _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | andIntro _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | @andElim π C R _ hC hel ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hLR | hL
    · obtain ⟨T, T', hT, hsub, -, hR⟩ := hel
      rw [hLR, hR]
      intro S hS
      rcases Finset.mem_union.mp hS with hS | hS
      · exact ih C hC S (Finset.mem_of_mem_erase hS)
      · rw [Finset.mem_singleton.mp hS]
        exact (Finset.card_le_card hsub).trans (ih C hC T hT)
    · exact ih L hL
  | @cut π C D R _ hC hD hcut ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hLR | hL
    · obtain ⟨T, -, -, -, hR⟩ := hcut
      rw [hLR, hR]
      intro S hS
      rcases Finset.mem_union.mp hS with hS | hS
      · exact ih C hC S (Finset.mem_of_mem_erase hS)
      · exact ih D hD S (Finset.mem_sdiff.mp hS).1
    · exact ih L hL

/-- A Res(k) derivation maps, line by line, to a Res(k, ⊕) derivation with termwise
weakening. -/
theorem resK_to_linK {k : ℕ} {F : Set (KLine V)} {π : List (KLine V)}
    (h : IsResKDerivation k F π) :
    IsLinKDerivation k IsLinKWeakening (lineOf '' F) (π.map lineOf) := by
  induction h with
  | nil => exact IsLinKDerivation.nil
  | ax _ hCF hk ih => exact IsLinKDerivation.ax ih ⟨_, hCF, rfl⟩ (lineOf_card hk)
  | @weak π C D _ hC hw hk ih =>
    exact IsLinKDerivation.weak ih (List.mem_map_of_mem hC)
      (weak_of_subset (Finset.image_subset_image hw)) (lineOf_card hk)
  | @andIntro π C D R _ hC hD hand hk ih =>
    obtain ⟨T₁, T₂, h1, h2, hR⟩ := hand
    refine IsLinKDerivation.andIntro ih (List.mem_map_of_mem hC) (List.mem_map_of_mem hD)
      ⟨termOf T₁, termOf T₂, Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2, ?_⟩
      (lineOf_card hk)
    rw [hR, lineOf_union, lineOf_union, lineOf_singleton, termOf_union, lineOf_erase,
      lineOf_erase]
  | @andElim π C R hπ hC hel ih =>
    have hkR := resK_lines_card (IsResKDerivation.andElim hπ hC hel) R
      (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨T, T', hT, hsub, -, hR⟩ := hel
    refine IsLinKDerivation.weak ih (List.mem_map_of_mem hC)
      (weak_of_andElim (T := termOf T) (T' := termOf T') (Finset.image_subset_image hsub) ?_)
      (lineOf_card hkR)
    rw [hR, lineOf_union, lineOf_singleton, lineOf_erase]
  | @cut π C D R hπ hC hD hcut ih =>
    have hkR := resK_lines_card (IsResKDerivation.cut hπ hC hD hcut) R
      (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨T, hT, -, hneg, hR⟩ := hcut
    refine IsLinKDerivation.cut ih (List.mem_map_of_mem hC) (List.mem_map_of_mem hD)
      ⟨termOf T, Finset.mem_image_of_mem _ hT, ?_, ?_⟩ (lineOf_card hkR)
    · intro e he
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp he
      rw [← termOf_neg]
      exact Finset.mem_image_of_mem _ (hneg l hl)
    · rw [hR, lineOf_union, lineOf_erase, lineOf_sdiff, lineOf_negs]

/-- A Res(k) refutation gives a Res(k, ⊕) refutation of the same length. -/
theorem resK_refutation (F : Set (Clause V)) {k : ℕ} {π : List (KLine V)}
    (h : IsResKRefutation k F π) :
    ∃ π' : List (LinKLine V), IsLinKRefutation k F π' ∧ π'.length = π.length := by
  obtain ⟨hd, he⟩ := h
  refine ⟨π.map lineOf, ⟨?_, List.mem_map.mpr ⟨∅, he, rfl⟩⟩, List.length_map _⟩
  have h := resK_to_linK hd
  rw [Set.image_image] at h
  have hfun : (fun C : Clause V => lineOf (kLineOfClause C)) = fun C => linKOfClause C :=
    funext fun C => lineOf_clause C
  rw [hfun] at h
  exact h

end PEqualNP.ProofComplexity.Helpers.LinKStrength
