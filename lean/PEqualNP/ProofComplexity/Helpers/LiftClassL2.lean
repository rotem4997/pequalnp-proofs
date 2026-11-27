import PEqualNP.ProofComplexity.Helpers.LiftClassPlan

/-!
# The piece `StmtL2` of the plan for L-pcx-074

A semantic refutation of `F` all of whose sets depend on at most `k` variables gives a
resolution refutation of `F`, with no weakening rule, of width at most `3 * k`.

A set `A` depending on `U` is represented by the full clauses on `U` (`cl U x`, one literal for
each variable of `U`, false at `x`) for the points `x` of `A`. Since the system has no weakening
rule, the invariant carried along the semantic derivation is subsumption: for every point `x`
of `A`, some subclause of `cl U x` has a derivation of width `3 * k`. The inference case and the
last step are a complete decision tree (`tree`).
-/

namespace PEqualNP.ProofComplexity.LiftClass

open PEqualNP.ProofComplexity
open PEqualNP.ProofComplexity.Helpers.SizeWidth

variable {V : Type} [DecidableEq V]

/-- The full clause on `U` that is false at `x`. -/
def cl (U : Finset V) (x : V → Bool) : Clause V := U.image (fun v => (v, !x v))

theorem cl_card_le (U : Finset V) (x : V → Bool) : (cl U x).card ≤ U.card :=
  Finset.card_image_le

theorem cl_mono {U U' : Finset V} (h : U ⊆ U') (x : V → Bool) : cl U x ⊆ cl U' x :=
  Finset.image_subset_image h

theorem cl_congr {U : Finset V} {x y : V → Bool} (h : ∀ v ∈ U, x v = y v) :
    cl U x = cl U y :=
  Finset.image_congr (fun v hv => by
    have := h v hv
    simp only [this])

theorem cl_insert (v : V) (U : Finset V) (x : V → Bool) :
    cl (insert v U) x = insert (v, !x v) (cl U x) :=
  Finset.image_insert _ _ _

/-- The complete decision tree: if every point `y` that agrees with `x` on `U` has a derived
subclause of its full clause on `T`, then it has a derived subclause of its full clause on any
`M` between `U` and a set that with `R` covers `T`, as long as the width allows. -/
theorem tree (F : Set (Clause V)) (W : ℕ) (U T : Finset V) (x : V → Bool)
    (hleaf : ∀ y : V → Bool, (∀ v ∈ U, y v = x v) → ∃ C' : Clause V, C' ⊆ cl T y ∧ Der F W C')
    (R : Finset V) : ∀ M : Finset V, U ⊆ M → T ⊆ M ∪ R → M.card + R.card ≤ W →
      ∀ y : V → Bool, (∀ v ∈ U, y v = x v) → ∃ C' : Clause V, C' ⊆ cl M y ∧ Der F W C' := by
  induction R using Finset.induction_on with
  | empty =>
    intro M _ hT _ y hy
    obtain ⟨C', hs, hd⟩ := hleaf y hy
    exact ⟨C', hs.trans (cl_mono (by simpa using hT) y), hd⟩
  | @insert v R hvR ih =>
    intro M hUM hT hW y hy
    have hcard : (insert v R).card = R.card + 1 := Finset.card_insert_of_notMem hvR
    by_cases hvM : v ∈ M
    · refine ih M hUM ?_ (by omega) y hy
      intro t ht
      rcases Finset.mem_union.1 (hT ht) with h | h
      · exact Finset.mem_union_left _ h
      · rcases Finset.mem_insert.1 h with rfl | h
        · exact Finset.mem_union_left _ hvM
        · exact Finset.mem_union_right _ h
    · have hvU : v ∉ U := fun h => hvM (hUM h)
      have hT' : T ⊆ insert v M ∪ R := by
        intro t ht
        rcases Finset.mem_union.1 (hT ht) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h)
        · rcases Finset.mem_insert.1 h with rfl | h
          · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
          · exact Finset.mem_union_right _ h
      have hW' : (insert v M).card + R.card ≤ W := by
        have := Finset.card_insert_le v M
        omega
      have hUM' : U ⊆ insert v M := hUM.trans (Finset.subset_insert _ _)
      let y' : V → Bool := Function.update y v (!y v)
      have hy'M : ∀ t ∈ M, y' t = y t := fun t ht =>
        Function.update_of_ne (fun e => hvM (by rw [← e]; exact ht)) _ _
      have hy' : ∀ t ∈ U, y' t = x t := fun t ht => (hy'M t (hUM ht)).trans (hy t ht)
      have hy'v : y' v = !y v := Function.update_self _ _ _
      obtain ⟨C1, hs1, hd1⟩ := ih (insert v M) hUM' hT' hW' y hy
      obtain ⟨C2, hs2, hd2⟩ := ih (insert v M) hUM' hT' hW' y' hy'
      rw [cl_insert] at hs1 hs2
      rw [cl_congr hy'M, hy'v] at hs2
      -- `hs1 : C1 ⊆ insert (v, !y v) (cl M y)`, `hs2 : C2 ⊆ insert (v, !!y v) (cl M y)`
      have hs2' : C2 ⊆ insert (neg (v, !y v)) (cl M y) := hs2
      generalize ((v, !y v) : Literal V) = l at hs1 hs2'
      by_cases hl : l ∈ C1
      · by_cases hnl : neg l ∈ C2
        · have hss : C1.erase l ∪ C2.erase (neg l) ⊆ cl M y := by
            intro z hz
            rcases Finset.mem_union.1 hz with hz | hz
            · obtain ⟨hne, hz⟩ := Finset.mem_erase.1 hz
              rcases Finset.mem_insert.1 (hs1 hz) with h | h
              · exact absurd h hne
              · exact h
            · obtain ⟨hne, hz⟩ := Finset.mem_erase.1 hz
              rcases Finset.mem_insert.1 (hs2' hz) with h | h
              · exact absurd h hne
              · exact h
          refine ⟨_, hss, Der.res l hd1 hd2 hl hnl ?_⟩
          have := (Finset.card_le_card hss).trans (cl_card_le M y)
          omega
        · refine ⟨C2, ?_, hd2⟩
          intro z hz
          rcases Finset.mem_insert.1 (hs2' hz) with h | h
          · exact absurd (h ▸ hz) hnl
          · exact h
      · refine ⟨C1, ?_, hd1⟩
        intro z hz
        rcases Finset.mem_insert.1 (hs1 hz) with h | h
        · exact absurd (h ▸ hz) hl
        · exact h

/-- The invariant along a semantic derivation. -/
theorem semDer_inv (F : Set (Clause V)) (k : ℕ) {σ : List (Set (V → Bool))}
    (h : SemDer F σ) (hdep : ∀ A ∈ σ, ∃ U : Finset V, U.card ≤ k ∧ DependsOn A U) :
    ∀ A ∈ σ, ∀ U : Finset V, U.card ≤ k → DependsOn A U → ∀ x ∈ A,
      ∃ C' : Clause V, C' ⊆ cl U x ∧ Der F (3 * k) C' := by
  induction h with
  | nil => intro A hA; simp at hA
  | @ax σ A C _ hC hfal ih =>
    have ih' := ih (fun B hB => hdep B (List.mem_cons_of_mem _ hB))
    intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · intro U hU hD x hx
      have hsub : C ⊆ cl U x := by
        rintro ⟨v, b⟩ hl
        have hxv : x v ≠ b := fun e => hfal x hx ⟨(v, b), hl, e⟩
        have hb : b = !x v := by
          cases b <;> cases hxb : x v <;> simp_all
        have hvU : v ∈ U := by
          by_contra hvU
          have hy : Function.update x v b ∈ B :=
            (hD x (Function.update x v b) (fun t ht => by
              rw [Function.update_of_ne (fun e => hvU (by rw [← e]; exact ht))])).1 hx
          exact hfal _ hy ⟨(v, b), hl, Function.update_self _ _ _⟩
        rw [hb]
        exact Finset.mem_image.2 ⟨v, hvU, rfl⟩
      refine ⟨C, hsub, Der.ax hC ?_⟩
      have := (Finset.card_le_card hsub).trans (cl_card_le U x)
      omega
    · exact ih' B hB
  | @inf σ A A₁ A₂ _ h1 h2 hsub ih =>
    have ih' := ih (fun B hB => hdep B (List.mem_cons_of_mem _ hB))
    intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · intro U hU hD x hx
      obtain ⟨U₁, hU₁, hD₁⟩ := hdep A₁ (List.mem_cons_of_mem _ h1)
      obtain ⟨U₂, hU₂, hD₂⟩ := hdep A₂ (List.mem_cons_of_mem _ h2)
      have hleaf : ∀ y : V → Bool, (∀ v ∈ U, y v = x v) →
          ∃ C' : Clause V, C' ⊆ cl (U₁ ∪ U₂) y ∧ Der F (3 * k) C' := by
        intro y hy
        have hyB : y ∈ B := (hD x y (fun v hv => (hy v hv).symm)).1 hx
        rcases hsub hyB with hy1 | hy2
        · obtain ⟨C', hs, hd⟩ := ih' A₁ h1 U₁ hU₁ hD₁ y hy1
          exact ⟨C', hs.trans (cl_mono Finset.subset_union_left y), hd⟩
        · obtain ⟨C', hs, hd⟩ := ih' A₂ h2 U₂ hU₂ hD₂ y hy2
          exact ⟨C', hs.trans (cl_mono Finset.subset_union_right y), hd⟩
      have hc := Finset.card_union_le U₁ U₂
      exact tree F (3 * k) U (U₁ ∪ U₂) x hleaf (U₁ ∪ U₂) U (Finset.Subset.refl _)
        Finset.subset_union_right (by omega) x (fun _ _ => rfl)
    · exact ih' B hB

theorem stmtL2 : StmtL2 := by
  intro V _ _ F σ k hσ huniv hdep
  obtain ⟨U₀, hU₀, hD₀⟩ := hdep Set.univ huniv
  have hinv := semDer_inv F k hσ hdep Set.univ huniv U₀ hU₀ hD₀
  have hleaf : ∀ y : V → Bool, (∀ v ∈ (∅ : Finset V), y v = (fun _ => false : V → Bool) v) →
      ∃ C' : Clause V, C' ⊆ cl U₀ y ∧ Der F (3 * k) C' :=
    fun y _ => hinv y (Set.mem_univ y)
  obtain ⟨C', hs, hd⟩ := tree F (3 * k) ∅ U₀ (fun _ => false) hleaf U₀ ∅
    (Finset.Subset.refl _) (by simp) (by simp; omega) (fun _ => false) (fun _ _ => rfl)
  have hC' : C' = ∅ := Finset.subset_empty.1 (by simpa [cl] using hs)
  rw [hC'] at hd
  obtain ⟨π, hπ, hemp, hw⟩ := hd.toList
  exact ⟨π, ⟨hπ, hemp⟩, hw⟩

end PEqualNP.ProofComplexity.LiftClass
