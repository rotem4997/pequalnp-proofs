import PEqualNP.ProofComplexity.Helpers.LiftRankPlan

/-!
# L-pcx-065, the width part: `StmtWidth` from the closure theorem

Every Res(⊕) refutation of the lifted linear system on an `(s, δ)` boundary expander has a
line `C` with `δ * s < 3 * linRank C`.

The argument works with `Covers` directly.

* Axioms are covered by one equation, a resolvent by the union of the covers of its premises,
  a weakening by the cover of its premise.
* No set of at most `s` equations covers the empty line: such a set is satisfiable in the
  gadget values (peel unique neighbours), and the gadget is onto.
* So some line `C` has a cover `U` of at most `s` equations and no cover of at most `s / 3`
  equations. Let `K` be its closure set (`closure`) and `U*` the union of the subsets of `U`
  whose unique neighbours all lie in `K`. Then `U*` covers `C` (peel the equations of `U`
  outside `U*` along unique neighbours off `K`, then realise the values with `closure`), and
  `δ * |U*| ≤ |K| ≤ linRank C`. Since `s < 3 * |U*|`, `δ * s < 3 * linRank C`.
-/

namespace PEqualNP.ProofComplexity.LiftRank

open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.ProofComplexity.Helpers

variable {m N : ℕ}

/-! ### Flipping one gadget value -/

/-- Changing a variable outside the support of an equation does not change whether it holds. -/
theorem linEqSat_update_of_not_mem (x : Fin N → Bool) {f : Finset (Fin N)} {j : Fin N}
    (hj : j ∉ f) (b b' : Bool) :
    LinEqSat (Function.update x j b') (f, b) ↔ LinEqSat x (f, b) := by
  unfold LinEqSat
  have hfe : f.filter (fun v => Function.update x j b' v = true) =
      f.filter (fun v => x v = true) := by
    refine Finset.filter_congr (fun v hv => ?_)
    have hne : v ≠ j := fun h => hj (h ▸ hv)
    rw [Function.update_of_ne hne]
  simp only
  rw [hfe]

/-- A variable of the support of an equation can be set so that the equation holds. -/
theorem exists_update_sat (x : Fin N → Bool) {f : Finset (Fin N)} {j : Fin N} (hj : j ∈ f)
    (b : Bool) : ∃ b' : Bool, LinEqSat (Function.update x j b') (f, b) := by
  classical
  have h : f.filter (fun v => Function.update x j true v = true) =
      insert j (f.filter (fun v => Function.update x j false v = true)) := by
    ext v
    by_cases hv : v = j
    · subst hv; simp [hj]
    · simp [hv]
  have hn : j ∉ f.filter (fun v => Function.update x j false v = true) := by simp
  by_cases ho : Odd (f.filter (fun v => Function.update x j false v = true)).card
  · cases b
    · refine ⟨true, ?_⟩
      unfold LinEqSat
      rw [h, Finset.card_insert_of_notMem hn, Nat.odd_add_one]
      simp [ho]
    · exact ⟨false, by unfold LinEqSat; simp [ho]⟩
  · cases b
    · exact ⟨false, by unfold LinEqSat; simp [ho]⟩
    · refine ⟨true, ?_⟩
      unfold LinEqSat
      rw [h, Finset.card_insert_of_notMem hn, Nat.odd_add_one]
      simp [ho]

/-! ### Peeling unique neighbours -/

/-- Peeling relative to a set `K` of blocks: if `x0` satisfies every equation of every
subset of `U` whose unique neighbours lie in `K`, then every `S ⊆ U` is satisfied by some
`x` agreeing with `x0` on `K`. -/
theorem peel (G : BipGraph m N) (c : Fin m → Bool) (K : Finset (Fin N)) (U : Finset (Fin m))
    (x0 : Fin N → Bool)
    (hyp : ∀ T ⊆ U, uniqueNbrs G T ⊆ K → ∀ i ∈ T, LinEqSat x0 (G i, c i)) :
    ∀ S ⊆ U, ∃ x : Fin N → Bool, (∀ j ∈ K, x j = x0 j) ∧ ∀ i ∈ S, LinEqSat x (G i, c i) := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    by_cases hK : uniqueNbrs G S ⊆ K
    · exact ⟨x0, fun _ _ => rfl, hyp S hS hK⟩
    · obtain ⟨j, hjU, hjK⟩ := Finset.not_subset.mp hK
      have hj1 : (S.filter (fun i => j ∈ G i)).card = 1 := (Finset.mem_filter.mp hjU).2
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hj1
      have hiF : i ∈ S.filter (fun i => j ∈ G i) := by
        rw [hi]; exact Finset.mem_singleton_self i
      have hiS : i ∈ S := (Finset.mem_filter.mp hiF).1
      have hji : j ∈ G i := (Finset.mem_filter.mp hiF).2
      have hother : ∀ i' ∈ S, i' ≠ i → j ∉ G i' := by
        intro i' hi' hne hj'
        have hmem : i' ∈ S.filter (fun i => j ∈ G i) := Finset.mem_filter.mpr ⟨hi', hj'⟩
        rw [hi] at hmem
        exact hne (Finset.mem_singleton.mp hmem)
      obtain ⟨x, hxK, hx⟩ := ih (S.erase i) (Finset.erase_ssubset hiS)
        ((Finset.erase_subset i S).trans hS)
      obtain ⟨b', hb'⟩ := exists_update_sat x hji (c i)
      refine ⟨Function.update x j b', fun j' hj' => ?_, fun i' hi' => ?_⟩
      · have hne : j' ≠ j := fun h => hjK (h ▸ hj')
        rw [Function.update_of_ne hne]
        exact hxK j' hj'
      · by_cases he : i' = i
        · subst he; exact hb'
        · exact (linEqSat_update_of_not_mem x (hother i' hi' he) _ _).mpr
            (hx i' (Finset.mem_erase.mpr ⟨he, hi'⟩))

/-- Every vector of gadget values is realised by an assignment of the lifted variables. -/
theorem exists_lift (x : Fin N → Bool) : ∃ a : Fin N × Fin 4 → Bool, gval a = x := by
  choose y hy using ip2_surj
  exact ⟨fun v => y (x v.1) v.2, funext fun j => hy (x j)⟩

/-! ### The rules and the empty line -/

/-- An axiom is covered by one equation. -/
theorem covers_axiom (G : BipGraph m N) (c : Fin m → Bool) {C : LinClause (Fin N × Fin 4)}
    (hC : C ∈ (fun C => linOfClause C) '' liftSys G c) : ∃ i : Fin m, Covers G c {i} C := by
  obtain ⟨C0, ⟨i, hi⟩, rfl⟩ := hC
  refine ⟨i, fun a ha => ⟨i, Finset.mem_singleton_self i, fun hs => ha ?_⟩⟩
  exact (linOfClause_sat a C0).mpr ((formula_sem m N G c a i).mpr hs C0 hi)

/-- A resolvent is covered by the union of the covers of its premises. -/
theorem covers_res (G : BipGraph m N) (c : Fin m → Bool) {U U' : Finset (Fin m)}
    {C D R : LinClause (Fin N × Fin 4)} (hR : IsLinResolvent C D R) (hC : Covers G c U C)
    (hD : Covers G c U' D) : Covers G c (U ∪ U') R := by
  classical
  intro a ha
  by_cases hCa : LinClauseSat a C
  · by_cases hDa : LinClauseSat a D
    · exact absurd (lin_resolvent_sound a hR hCa hDa) ha
    · obtain ⟨i, hi, h⟩ := hD a hDa
      exact ⟨i, Finset.mem_union_right _ hi, h⟩
  · obtain ⟨i, hi, h⟩ := hC a hCa
    exact ⟨i, Finset.mem_union_left _ hi, h⟩

/-- No set of at most `s` equations covers the empty line. -/
theorem not_covers_empty (G : BipGraph m N) (c : Fin m → Bool) (s δ : ℕ)
    (hG : IsBdryExpander G s δ) (hδ : 1 ≤ δ) (U : Finset (Fin m)) (hU : U.card ≤ s) :
    ¬ Covers G c U ∅ := by
  intro hcov
  obtain ⟨x, -, hx⟩ := peel G c ∅ U (fun _ => false) (by
    intro T hT hK i hi
    exfalso
    have h1 := hG T ((Finset.card_le_card hT).trans hU)
    rw [Finset.subset_empty.mp hK, Finset.card_empty] at h1
    have hpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨i, hi⟩
    have := Nat.mul_le_mul hδ hpos
    omega) U le_rfl
  obtain ⟨a, ha⟩ := exists_lift x
  obtain ⟨i, hi, hni⟩ := hcov a (by rintro ⟨q, hq, -⟩; simp at hq)
  apply hni
  unfold EqSat
  rw [ha]
  exact hx i hi

/-! ### The union of the subsets whose unique neighbours lie in `K` -/

/-- The union of the subsets of `U` whose unique neighbours all lie in `K`. -/
noncomputable def ustar (G : BipGraph m N) (K : Finset (Fin N)) (U : Finset (Fin m)) :
    Finset (Fin m) := by
  classical
  exact (U.powerset.filter (fun T => uniqueNbrs G T ⊆ K)).biUnion id

theorem mem_ustar (G : BipGraph m N) (K : Finset (Fin N)) (U : Finset (Fin m)) (i : Fin m) :
    i ∈ ustar G K U ↔ ∃ T ⊆ U, uniqueNbrs G T ⊆ K ∧ i ∈ T := by
  classical
  unfold ustar
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset, id]
  constructor
  · rintro ⟨T, ⟨hTU, hTK⟩, hiT⟩
    exact ⟨T, hTU, hTK, hiT⟩
  · rintro ⟨T, hTU, hTK, hiT⟩
    exact ⟨T, ⟨hTU, hTK⟩, hiT⟩

theorem ustar_subset (G : BipGraph m N) (K : Finset (Fin N)) (U : Finset (Fin m)) :
    ustar G K U ⊆ U := by
  intro i hi
  obtain ⟨T, hTU, -, hiT⟩ := (mem_ustar G K U i).mp hi
  exact hTU hiT

theorem subset_ustar (G : BipGraph m N) (K : Finset (Fin N)) (U T : Finset (Fin m))
    (hTU : T ⊆ U) (hTK : uniqueNbrs G T ⊆ K) : T ⊆ ustar G K U :=
  fun i hi => (mem_ustar G K U i).mpr ⟨T, hTU, hTK, hi⟩

/-- The unique neighbours of `ustar` lie in `K`: a unique neighbour of a union is a unique
neighbour of the part holding its one neighbour. -/
theorem uniqueNbrs_ustar (G : BipGraph m N) (K : Finset (Fin N)) (U : Finset (Fin m)) :
    uniqueNbrs G (ustar G K U) ⊆ K := by
  classical
  intro j hj
  have h1 : ((ustar G K U).filter (fun i => j ∈ G i)).card = 1 := (Finset.mem_filter.mp hj).2
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
  have hiF : i ∈ (ustar G K U).filter (fun i => j ∈ G i) := by
    rw [hi]; exact Finset.mem_singleton_self i
  obtain ⟨hiU, hji⟩ := Finset.mem_filter.mp hiF
  obtain ⟨T, hTU, hTK, hiT⟩ := (mem_ustar G K U i).mp hiU
  apply hTK
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hsub : T.filter (fun i => j ∈ G i) ⊆ (ustar G K U).filter (fun i => j ∈ G i) :=
    Finset.filter_subset_filter _ (subset_ustar G K U T hTU hTK)
  have hle := Finset.card_le_card hsub
  rw [h1] at hle
  have hpos : 0 < (T.filter (fun i => j ∈ G i)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hiT, hji⟩⟩
  omega

/-! ### A line with a cover of at most `s` equations and no cover of at most `s / 3` -/

/-- A cover `U` of a line, closed up along a closure set `K` of the line: `ustar G K U`
still covers it. -/
theorem covers_ustar (G : BipGraph m N) (c : Fin m → Bool) {C : LinClause (Fin N × Fin 4)}
    (K : Finset (Fin N))
    (hK : ∀ a : Fin N × Fin 4 → Bool, ¬ LinClauseSat a C → ∀ t : Fin N → Bool,
      ∃ a' : Fin N × Fin 4 → Bool, ¬ LinClauseSat a' C ∧
        (∀ j ∈ K, ∀ u : Fin 4, a' (j, u) = a (j, u)) ∧ ∀ j, j ∉ K → gval a' j = t j)
    (U : Finset (Fin m)) (hU : Covers G c U C) : Covers G c (ustar G K U) C := by
  classical
  intro a ha
  by_contra hn
  have hall : ∀ i ∈ ustar G K U, EqSat G c a i := fun i hi => by
    by_contra h
    exact hn ⟨i, hi, h⟩
  obtain ⟨x, hxK, hx⟩ := peel G c K U (gval a) (fun T hTU hTK i hi =>
    hall i (subset_ustar G K U T hTU hTK hi)) U le_rfl
  obtain ⟨a', ha', hagree, hoff⟩ := hK a ha x
  have hg : gval a' = x := by
    funext j
    by_cases hj : j ∈ K
    · rw [hxK j hj]
      unfold gval
      congr 1
      funext u
      exact hagree j hj u
    · exact hoff j hj
  obtain ⟨i, hi, hni⟩ := hU a' ha'
  apply hni
  unfold EqSat
  rw [hg]
  exact hx i hi

/-- A medium line has large rank. -/
theorem medium_rank (G : BipGraph m N) (c : Fin m → Bool) (s δ : ℕ)
    (hG : IsBdryExpander G s δ) (hδ : 1 ≤ δ) {C : LinClause (Fin N × Fin 4)}
    (U : Finset (Fin m)) (hU : Covers G c U C) (hUs : U.card ≤ s)
    (hmed : ∀ U' : Finset (Fin m), Covers G c U' C → s < 3 * U'.card) :
    δ * s < 3 * linRank C := by
  obtain ⟨K, hKcard, hK⟩ := PEqualNP.ProofComplexity.LiftRank.closure N C
  have hcov := covers_ustar G c K hK U hU
  have hbig := hmed _ hcov
  have hsize : (ustar G K U).card ≤ s := (Finset.card_le_card (ustar_subset G K U)).trans hUs
  have hexp := hG _ hsize
  have hun : (uniqueNbrs G (ustar G K U)).card ≤ K.card :=
    Finset.card_le_card (uniqueNbrs_ustar G K U)
  have h1 : δ * s < δ * (3 * (ustar G K U).card) := Nat.mul_lt_mul_of_pos_left hbig (by omega)
  have h2 : δ * (3 * (ustar G K U).card) = 3 * (δ * (ustar G K U).card) := by ring
  omega

/-! ### The induction along the derivation -/

/-- A line with a cover of at most `s / 3` equations. -/
def Small (G : BipGraph m N) (c : Fin m → Bool) (s : ℕ) (C : LinClause (Fin N × Fin 4)) :
    Prop :=
  ∃ U : Finset (Fin m), Covers G c U C ∧ 3 * U.card ≤ s

/-- A line with a cover of at most `s` equations and no cover of at most `s / 3`. -/
def Medium (G : BipGraph m N) (c : Fin m → Bool) (s : ℕ) (C : LinClause (Fin N × Fin 4)) :
    Prop :=
  (∃ U : Finset (Fin m), Covers G c U C ∧ U.card ≤ s) ∧
    ∀ U : Finset (Fin m), Covers G c U C → s < 3 * U.card

theorem medium_or_small_of_cover (G : BipGraph m N) (c : Fin m → Bool) (s : ℕ)
    {C : LinClause (Fin N × Fin 4)} (U : Finset (Fin m)) (hU : Covers G c U C)
    (hUs : U.card ≤ s) : Medium G c s C ∨ Small G c s C := by
  by_cases h : Small G c s C
  · exact Or.inr h
  · refine Or.inl ⟨⟨U, hU, hUs⟩, fun U' hU' => ?_⟩
    by_contra hn
    exact h ⟨U', hU', by omega⟩

theorem medium_or_small (G : BipGraph m N) (c : Fin m → Bool) (s : ℕ) (hs : 3 ≤ s)
    {π : List (LinClause (Fin N × Fin 4))}
    (hπ : IsLinDerivation ((fun C => linOfClause C) '' liftSys G c) π) :
    (∃ C ∈ π, Medium G c s C) ∨ ∀ C ∈ π, Small G c s C := by
  have close : ∀ (π : List (LinClause (Fin N × Fin 4))) (C : LinClause (Fin N × Fin 4)),
      (∀ E ∈ π, Small G c s E) → (Medium G c s C ∨ Small G c s C) →
      (∃ E ∈ C :: π, Medium G c s E) ∨ ∀ E ∈ C :: π, Small G c s E := by
    intro π C hsmall h
    rcases h with hmed | hsm
    · exact Or.inl ⟨C, List.mem_cons_self, hmed⟩
    · refine Or.inr fun E hE => ?_
      rcases List.mem_cons.mp hE with rfl | hE
      · exact hsm
      · exact hsmall E hE
  induction hπ with
  | nil => exact Or.inr (by simp)
  | @ax π C _ hC ih =>
    rcases ih with ⟨E, hE, hmed⟩ | hsmall
    · exact Or.inl ⟨E, List.mem_cons_of_mem _ hE, hmed⟩
    · obtain ⟨i, hi⟩ := covers_axiom G c hC
      exact close π C hsmall (Or.inr ⟨{i}, hi, by rw [Finset.card_singleton]; omega⟩)
  | @res π C D R _ hC hD hR ih =>
    rcases ih with ⟨E, hE, hmed⟩ | hsmall
    · exact Or.inl ⟨E, List.mem_cons_of_mem _ hE, hmed⟩
    · obtain ⟨S, hS, hScard⟩ := hsmall C hC
      obtain ⟨T, hT, hTcard⟩ := hsmall D hD
      have hUcard : (S ∪ T).card ≤ S.card + T.card := Finset.card_union_le S T
      exact close π R hsmall
        (medium_or_small_of_cover G c s _ (covers_res G c hR hS hT) (by omega))
  | @weak π C D _ hC hw ih =>
    rcases ih with ⟨E, hE, hmed⟩ | hsmall
    · exact Or.inl ⟨E, List.mem_cons_of_mem _ hE, hmed⟩
    · obtain ⟨S, hS, hScard⟩ := hsmall C hC
      have hSD : Covers G c S D := fun a ha => hS a (fun hCa => ha (hw a hCa))
      exact close π D hsmall (Or.inr ⟨S, hSD, hScard⟩)

/-! ### The theorem -/

/-- Every Res(⊕) refutation of the lifted formula on a boundary expander has a line of
large rank. -/
theorem width : StmtWidth := by
  intro m N G c s δ hG hs hδ π hπ
  rcases medium_or_small G c s hs hπ.1 with ⟨C, hC, ⟨U, hU, hUs⟩, hmed⟩ | hsmall
  · exact ⟨C, hC, medium_rank G c s δ hG hδ U hU hUs hmed⟩
  · obtain ⟨U, hU, hUs⟩ := hsmall ∅ hπ.2
    exact absurd hU (not_covers_empty G c s δ hG hδ U (by omega))

end PEqualNP.ProofComplexity.LiftRank
