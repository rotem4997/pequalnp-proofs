import PEqualNP.ProofComplexity.Helpers.LiftQuadDefs

/-!
# L-pcx-072, leg B: the walk to a medium line (`StmtPath`)

Conjecture until the checker accepts it. A port of `Helpers.LiftRankWidth` to frozen covers
(`FCovers`) and generalised derivations (`GDeriv`), with a walk along `Step` added.

* `QSmall`: a line with a frozen cover of at most `s / 3` equations. Semantic axioms are small.
* `walk_of_gderiv`: by induction on the derivation, every entry that is not small starts a
  walk (a `Sublist` of the derivation, `Step` at each link) ending at a falsifiable line with a
  cover of at most `s` equations and no cover of at most `s / 3`.
* `not_small_empty`: by `Good`, the empty line is not small.
* `fcovers_ustar`, `qmedium_rank`: at the end of the walk, `ustar (K ∪ K₀) U` still covers
  the line, which gives `δ * s < 3 * (linRank z + |K₀|)`.
-/

namespace PEqualNP.ProofComplexity.LiftQuad

open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.ThreeCnfFamily PEqualNP.ProofComplexity.LiftRank

variable {m N : ℕ}

/-- A line with a frozen cover of at most `s / 3` equations. -/
def QSmall (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N)) (β : Fin N → Bool)
    (s : ℕ) (L : LinClause (Fin N × Fin 4)) : Prop :=
  ∃ U : Finset (Fin m), FCovers G c K₀ β U L ∧ 3 * U.card ≤ s

/-- The end of a walk: falsifiable, a cover of at most `s` equations, and not small. -/
def QEnd (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N)) (β : Fin N → Bool)
    (s : ℕ) (L : LinClause (Fin N × Fin 4)) : Prop :=
  Falsifiable L ∧ (∃ U : Finset (Fin m), FCovers G c K₀ β U L ∧ U.card ≤ s) ∧
    ¬ QSmall G c K₀ β s L

/-- A walk from `L` inside `π`. -/
def QWalk (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N)) (β : Fin N → Bool)
    (s : ℕ) (π : List (LinClause (Fin N × Fin 4))) (L : LinClause (Fin N × Fin 4)) : Prop :=
  ∃ path : List (LinClause (Fin N × Fin 4)), path.Sublist π ∧ path.head? = some L ∧
    path.IsChain Step ∧ ∃ z, path.getLast? = some z ∧ QEnd G c K₀ β s z

/-- A line that is not small is falsifiable (else the empty set covers it). -/
theorem falsifiable_of_not_small (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) (s : ℕ) {L : LinClause (Fin N × Fin 4)}
    (h : ¬ QSmall G c K₀ β s L) : Falsifiable L := by
  by_contra hf
  apply h
  refine ⟨∅, fun a ha => absurd ⟨a, ha⟩ hf, by simp⟩

/-- A one-line walk at an end line. -/
theorem qwalk_single (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) (s : ℕ) {π : List (LinClause (Fin N × Fin 4))}
    {L : LinClause (Fin N × Fin 4)} (hL : L ∈ π) (hE : QEnd G c K₀ β s L) :
    QWalk G c K₀ β s π L :=
  ⟨[L], List.singleton_sublist.mpr hL, rfl, List.isChain_singleton L, L, rfl, hE⟩

/-- A walk in `π` is a walk in `R :: π`. -/
theorem qwalk_cons (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) (s : ℕ) {π : List (LinClause (Fin N × Fin 4))}
    {L R : LinClause (Fin N × Fin 4)} (h : QWalk G c K₀ β s π L) :
    QWalk G c K₀ β s (R :: π) L := by
  obtain ⟨path, hsub, hhead, hchain, z, hz, hE⟩ := h
  exact ⟨path, hsub.cons R, hhead, hchain, z, hz, hE⟩

/-- A step from the new line `R` to a line `P` with a walk in `π` gives a walk from `R`. -/
theorem qwalk_step (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) (s : ℕ) {π : List (LinClause (Fin N × Fin 4))}
    {P R : LinClause (Fin N × Fin 4)} (hst : Step R P) (h : QWalk G c K₀ β s π P) :
    QWalk G c K₀ β s (R :: π) R := by
  obtain ⟨path, hsub, hhead, hchain, z, hz, hE⟩ := h
  obtain ⟨rest, rfl⟩ : ∃ rest, path = P :: rest := by
    cases path with
    | nil => simp at hhead
    | cons x rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      exact ⟨rest, by rw [hhead]⟩
  refine ⟨R :: P :: rest, hsub.cons_cons R, rfl, List.IsChain.cons_cons hst hchain, z, ?_, hE⟩
  rw [List.getLast?_cons_cons]
  exact hz

theorem linEqSat_false_of_not_true {V : Type} (a : V → Bool) (f : Finset V)
    (h : ¬ LinEqSat a (f, true)) : LinEqSat a (f, false) := by
  unfold LinEqSat at h ⊢
  simp only [iff_true, Bool.false_eq_true, iff_false] at h ⊢
  exact h

theorem not_true_of_linEqSat_false {V : Type} (a : V → Bool) (f : Finset V)
    (h : LinEqSat a (f, false)) : ¬ LinEqSat a (f, true) := by
  unfold LinEqSat at h ⊢
  simp only [iff_true, Bool.false_eq_true, iff_false] at h ⊢
  exact h

/-- Every entry of a generalised derivation that is not small starts a walk. -/
theorem walk_of_gderiv (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) (s : ℕ) (hs : 3 ≤ s) {π : List (LinClause (Fin N × Fin 4))}
    (hπ : GDeriv G c K₀ β π) :
    ∀ L ∈ π, ¬ QSmall G c K₀ β s L → QWalk G c K₀ β s π L := by
  classical
  induction hπ with
  | nil => intro L hL; simp at hL
  | @ax π L _ hL ih =>
    intro E hE hns
    rcases List.mem_cons.mp hE with rfl | hE
    · obtain ⟨i, hi⟩ := hL
      exact absurd ⟨{i}, hi, by rw [Finset.card_singleton]; omega⟩ hns
    · exact qwalk_cons G c K₀ β s (ih E hE hns)
  | @res π C D R _ hC hD hR ih =>
    intro E hE hns
    rcases List.mem_cons.mp hE with rfl | hE
    · obtain ⟨f, hf⟩ := hR
      by_cases h1 : (∃ a, ¬ LinClauseSat a E ∧ LinEqSat a (f, true)) ∧
          ¬ QSmall G c K₀ β s C
      · refine qwalk_step G c K₀ β s (Or.inr ⟨f, true, h1.1, fun a ha hfa => ?_⟩)
          (ih C hC h1.2)
        exact (hf a ha).1 hfa
      by_cases h0 : (∃ a, ¬ LinClauseSat a E ∧ LinEqSat a (f, false)) ∧
          ¬ QSmall G c K₀ β s D
      · refine qwalk_step G c K₀ β s (Or.inr ⟨f, false, h0.1, fun a ha hfa => ?_⟩)
          (ih D hD h0.2)
        exact (hf a ha).2 (not_true_of_linEqSat_false a f hfa)
      -- otherwise `E` has a cover of at most `2 s / 3` equations
      obtain ⟨UC, hUC, hUCs⟩ : ∃ UC : Finset (Fin m), (∀ a, ¬ LinClauseSat a E →
          LinEqSat a (f, true) → ∃ i ∈ UC, ¬ LinEqSat (fval K₀ β a) (G i, c i)) ∧
          3 * UC.card ≤ s := by
        by_cases hsC : QSmall G c K₀ β s C
        · obtain ⟨U, hU, hUs⟩ := hsC
          exact ⟨U, fun a ha hfa => hU a ((hf a ha).1 hfa), hUs⟩
        · refine ⟨∅, fun a ha hfa => absurd ⟨⟨a, ha, hfa⟩, hsC⟩ h1, by simp⟩
      obtain ⟨UD, hUD, hUDs⟩ : ∃ UD : Finset (Fin m), (∀ a, ¬ LinClauseSat a E →
          ¬ LinEqSat a (f, true) → ∃ i ∈ UD, ¬ LinEqSat (fval K₀ β a) (G i, c i)) ∧
          3 * UD.card ≤ s := by
        by_cases hsD : QSmall G c K₀ β s D
        · obtain ⟨U, hU, hUs⟩ := hsD
          exact ⟨U, fun a ha hfa => hU a ((hf a ha).2 hfa), hUs⟩
        · refine ⟨∅, fun a ha hfa =>
            absurd ⟨⟨a, ha, linEqSat_false_of_not_true a f hfa⟩, hsD⟩ h0, by simp⟩
      refine qwalk_single G c K₀ β s List.mem_cons_self
        ⟨falsifiable_of_not_small G c K₀ β s hns, ⟨UC ∪ UD, fun a ha => ?_, ?_⟩, hns⟩
      · by_cases hfa : LinEqSat a (f, true)
        · obtain ⟨i, hi, h⟩ := hUC a ha hfa
          exact ⟨i, Finset.mem_union_left _ hi, h⟩
        · obtain ⟨i, hi, h⟩ := hUD a ha hfa
          exact ⟨i, Finset.mem_union_right _ hi, h⟩
      · have := Finset.card_union_le UC UD
        omega
    · exact qwalk_cons G c K₀ β s (ih E hE hns)
  | @weak π C D _ hC hw ih =>
    intro E hE hns
    rcases List.mem_cons.mp hE with rfl | hE
    · have hnsC : ¬ QSmall G c K₀ β s C := by
        rintro ⟨U, hU, hUs⟩
        exact hns ⟨U, fun a ha => hU a (fun hCa => ha (hw a hCa)), hUs⟩
      exact qwalk_step G c K₀ β s (Or.inl fun a ha hCa => ha (hw a hCa)) (ih C hC hnsC)
    · exact qwalk_cons G c K₀ β s (ih E hE hns)

/-- By local consistency, no set of at most `s` equations covers the empty line. -/
theorem not_small_empty (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) (s : ℕ) (hgood : Good G c s K₀ β) :
    ¬ QSmall G c K₀ β s ∅ := by
  classical
  rintro ⟨U, hU, hUs⟩
  obtain ⟨x, hxK, hx⟩ := hgood U (by omega)
  obtain ⟨a, ha⟩ := exists_lift x
  have hf : fval K₀ β a = x := by
    funext j
    unfold fval
    by_cases hj : j ∈ K₀
    · simp only [hj, ↓reduceIte]; rw [hxK j hj]
    · simp only [hj, ↓reduceIte]; rw [ha]
  obtain ⟨i, hi, hni⟩ := hU a (by rintro ⟨q, hq, -⟩; simp at hq)
  rw [hf] at hni
  exact hni (hx i hi)

/-- A frozen cover `U` of a line, closed up along `K ∪ K₀` for a closure set `K` of the
line: `ustar G (K ∪ K₀) U` still covers it. -/
theorem fcovers_ustar (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) {C : LinClause (Fin N × Fin 4)} (K : Finset (Fin N))
    (hK : ∀ a : Fin N × Fin 4 → Bool, ¬ LinClauseSat a C → ∀ t : Fin N → Bool,
      ∃ a' : Fin N × Fin 4 → Bool, ¬ LinClauseSat a' C ∧
        (∀ j ∈ K, ∀ u : Fin 4, a' (j, u) = a (j, u)) ∧ ∀ j, j ∉ K → gval a' j = t j)
    (U : Finset (Fin m)) (hU : FCovers G c K₀ β U C) :
    FCovers G c K₀ β (ustar G (K ∪ K₀) U) C := by
  classical
  intro a ha
  by_contra hn
  have hall : ∀ i ∈ ustar G (K ∪ K₀) U, LinEqSat (fval K₀ β a) (G i, c i) := fun i hi => by
    by_contra h
    exact hn ⟨i, hi, h⟩
  obtain ⟨x, hxK, hx⟩ := peel G c (K ∪ K₀) U (fval K₀ β a) (fun T hTU hTK i hi =>
    hall i (subset_ustar G (K ∪ K₀) U T hTU hTK hi)) U le_rfl
  obtain ⟨a', ha', hagree, hoff⟩ := hK a ha x
  have hg : fval K₀ β a' = x := by
    funext j
    by_cases hj0 : j ∈ K₀
    · have h1 := hxK j (Finset.mem_union_right _ hj0)
      unfold fval at h1 ⊢
      simp only [hj0, ↓reduceIte] at h1 ⊢
      exact h1.symm
    · by_cases hj : j ∈ K
      · have h1 := hxK j (Finset.mem_union_left _ hj)
        unfold fval at h1 ⊢
        simp only [hj0, ↓reduceIte] at h1 ⊢
        rw [h1]
        unfold gval
        congr 1
        funext u
        exact hagree j hj u
      · unfold fval
        simp only [hj0, ↓reduceIte]
        exact hoff j hj
  obtain ⟨i, hi, hni⟩ := hU a' ha'
  rw [hg] at hni
  exact hni (hx i hi)

/-- An end line has large rank, counting the frozen blocks. -/
theorem qmedium_rank (G : BipGraph m N) (c : Fin m → Bool) (K₀ : Finset (Fin N))
    (β : Fin N → Bool) (s δ : ℕ) (hG : IsBdryExpander G s δ) (hδ : 1 ≤ δ)
    {C : LinClause (Fin N × Fin 4)} (U : Finset (Fin m)) (hU : FCovers G c K₀ β U C)
    (hUs : U.card ≤ s) (hns : ¬ QSmall G c K₀ β s C) :
    δ * s < 3 * (linRank C + K₀.card) := by
  classical
  obtain ⟨K, hKcard, hK⟩ := PEqualNP.ProofComplexity.LiftRank.closure N C
  have hcov := fcovers_ustar G c K₀ β K hK U hU
  have hbig : s < 3 * (ustar G (K ∪ K₀) U).card := by
    by_contra h
    exact hns ⟨_, hcov, by omega⟩
  have hsize : (ustar G (K ∪ K₀) U).card ≤ s :=
    (Finset.card_le_card (ustar_subset G (K ∪ K₀) U)).trans hUs
  have hexp := hG _ hsize
  have hun : (uniqueNbrs G (ustar G (K ∪ K₀) U)).card ≤ (K ∪ K₀).card :=
    Finset.card_le_card (uniqueNbrs_ustar G (K ∪ K₀) U)
  have hKK := Finset.card_union_le K K₀
  have h1 : δ * s < δ * (3 * (ustar G (K ∪ K₀) U).card) :=
    Nat.mul_lt_mul_of_pos_left hbig (by omega)
  have h2 : δ * (3 * (ustar G (K ∪ K₀) U).card) = 3 * (δ * (ustar G (K ∪ K₀) U).card) := by
    ring
  omega

/-- Leg B: the walk from the empty line to a medium line of large rank. -/
theorem path : StmtPath := by
  intro m N G c K₀ β s δ hG hs hδ hgood π hπ
  obtain ⟨p, hsub, hhead, hchain, z, hz, hzf, ⟨U, hU, hUs⟩, hns⟩ :=
    walk_of_gderiv G c K₀ β s hs hπ.1 ∅ hπ.2 (not_small_empty G c K₀ β s hgood)
  exact ⟨p, hsub, hhead, hchain, z, hz, hzf, qmedium_rank G c K₀ β s δ hG hδ U hU hUs hns⟩

end PEqualNP.ProofComplexity.LiftQuad
