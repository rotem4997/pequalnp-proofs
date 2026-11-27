import PEqualNP.ProofComplexity.Helpers.Lin
import PEqualNP.Defs.ProofComplexityRestrict

/-!
# Helpers: Res(⊕) is closed under restriction

Substituting a partial assignment `ρ` into a linear equation keeps its free variables and folds
the set ones into the constant. A Res(⊕) derivation from `F` maps line by line, at most two new
lines per old line, to a Res(⊕) derivation from the restriction of `F` by `ρ`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

/-- The assignment `a` overridden by the partial assignment `ρ` on the variables it sets. -/
def rstOverride {V : Type} (ρ : V → Option Bool) (a : V → Bool) : V → Bool :=
  fun v => (ρ v).getD (a v)

/-- Substitution of `ρ` into an equation: keep the free variables, add the parity of the
variables set to true into the constant. -/
def rstEq {V : Type} (ρ : V → Option Bool) (q : LinEq V) : LinEq V :=
  (q.1.filter (fun v => ρ v = none),
    xor q.2 (decide (Odd (q.1.filter (fun v => ρ v = some true)).card)))

/-- Substitution of `ρ` into a linear clause. -/
def rstLin {V : Type} [DecidableEq V] (ρ : V → Option Bool) (C : LinClause V) : LinClause V :=
  C.image (rstEq ρ)

theorem rstEq_sat {V : Type} [DecidableEq V] (ρ : V → Option Bool) (a : V → Bool) (q : LinEq V) :
    LinEqSat a (rstEq ρ q) ↔ LinEqSat (rstOverride ρ a) q := by
  unfold LinEqSat rstEq
  have hsplit : q.1.filter (fun v => rstOverride ρ a v = true) =
      (q.1.filter (fun v => ρ v = none)).filter (fun v => a v = true) ∪
        q.1.filter (fun v => ρ v = some true) := by
    ext v
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_filter]
    simp only [rstOverride]
    cases h : ρ v with
    | none => simp
    | some b => cases b <;> simp
  have hdisj : Disjoint ((q.1.filter (fun v => ρ v = none)).filter (fun v => a v = true))
      (q.1.filter (fun v => ρ v = some true)) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [Finset.mem_filter] at h1 h2
    rw [h1.1.2] at h2
    cases h2.2
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Nat.odd_add]
  generalize Odd ((q.1.filter (fun v => ρ v = none)).filter (fun v => a v = true)).card = P
  by_cases hy : Odd (q.1.filter (fun v => ρ v = some true)).card
  · have : ¬ Even (q.1.filter (fun v => ρ v = some true)).card := Nat.not_even_iff_odd.mpr hy
    cases q.2 <;> simp [hy, this]
  · have : Even (q.1.filter (fun v => ρ v = some true)).card := Nat.not_odd_iff_even.mp hy
    cases q.2 <;> simp [hy, this]

theorem rstLin_sat {V : Type} [DecidableEq V] (ρ : V → Option Bool) (a : V → Bool)
    (C : LinClause V) : LinClauseSat a (rstLin ρ C) ↔ LinClauseSat (rstOverride ρ a) C := by
  constructor
  · rintro ⟨q', hq', hs⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
    exact ⟨q, hq, (rstEq_sat ρ a q).mp hs⟩
  · rintro ⟨q, hq, hs⟩
    exact ⟨rstEq ρ q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, (rstEq_sat ρ a q).mpr hs⟩

theorem rst_erase_image_subset {α β : Type} [DecidableEq α] [DecidableEq β] (g : α → β)
    (C : Finset α) (q0 : α) : (C.image g).erase (g q0) ⊆ (C.erase q0).image g := by
  intro x hx
  obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  refine Finset.mem_image.mpr ⟨q, Finset.mem_erase.mpr ⟨?_, hq⟩, rfl⟩
  rintro rfl
  exact hne rfl

theorem rst_weak_of_subset {V : Type} {C D : LinClause V} (h : C ⊆ D) :
    ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D := by
  rintro a ⟨q, hq, hs⟩
  exact ⟨q, h hq, hs⟩

/-- The line-by-line simulation. -/
theorem rst_derivation {V : Type} [DecidableEq V] (F : Set (Clause V)) (ρ : V → Option Bool)
    (B : Clause V) (hB : B ∈ restrictCNF F ρ) {π : List (LinClause V)}
    (h : IsLinDerivation ((fun C => linOfClause C) '' F) π) :
    ∃ π' : List (LinClause V),
      IsLinDerivation ((fun C => linOfClause C) '' restrictCNF F ρ) π' ∧
      π'.length ≤ 2 * π.length ∧ ∀ L ∈ π, rstLin ρ L ∈ π' := by
  induction h with
  | nil => exact ⟨[], IsLinDerivation.nil, by simp, by simp⟩
  | @ax π L hπ hL ih =>
    obtain ⟨π', hd, hlen, hmem⟩ := ih
    obtain ⟨C, hC, rfl⟩ := hL
    -- the restricted axiom to weaken from, and the implication
    have key : ∃ B' ∈ restrictCNF F ρ, ∀ a : V → Bool,
        LinClauseSat a (linOfClause B') → LinClauseSat a (rstLin ρ (linOfClause C)) := by
      by_cases hs : ∃ l ∈ C, ρ l.1 = some l.2
      · refine ⟨B, hB, fun a _ => ?_⟩
        rw [rstLin_sat, linOfClause_sat]
        obtain ⟨l, hl, hρ⟩ := hs
        exact ⟨l, hl, by simp [rstOverride, hρ]⟩
      · refine ⟨C.filter fun l => ρ l.1 = none, ⟨C, hC, by simp [restrictClause, hs]⟩,
          fun a ha => ?_⟩
        rw [rstLin_sat, linOfClause_sat]
        rw [linOfClause_sat] at ha
        obtain ⟨l, hl, hal⟩ := ha
        obtain ⟨hl, hρ⟩ := Finset.mem_filter.mp hl
        exact ⟨l, hl, by simp [rstOverride, hρ, hal]⟩
    obtain ⟨B', hB', himp⟩ := key
    refine ⟨rstLin ρ (linOfClause C) :: linOfClause B' :: π', ?_, ?_, ?_⟩
    · exact IsLinDerivation.weak (IsLinDerivation.ax hd ⟨B', hB', rfl⟩)
        List.mem_cons_self himp
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem L hL))
  | @res π C D R hπ hC hD hR ih =>
    obtain ⟨π', hd, hlen, hmem⟩ := ih
    obtain ⟨f, hfC, hfD, rfl⟩ := hR
    have hTC := hmem C hC
    have hTD := hmem D hD
    have h0 : rstEq ρ (f, false) ∈ rstLin ρ C := Finset.mem_image_of_mem _ hfC
    have h1 : rstEq ρ (f, true) ∈ rstLin ρ D := Finset.mem_image_of_mem _ hfD
    have hsub : (rstLin ρ C).erase (rstEq ρ (f, false)) ∪
        (rstLin ρ D).erase (rstEq ρ (f, true)) ⊆
          rstLin ρ (C.erase (f, false) ∪ D.erase (f, true)) := by
      unfold rstLin
      rw [Finset.image_union]
      exact Finset.union_subset_union (rst_erase_image_subset _ _ _)
        (rst_erase_image_subset _ _ _)
    set p := decide (Odd ((f.filter (fun v => ρ v = some true)).card)) with hp
    set f' := f.filter (fun v => ρ v = none) with hf'
    have e0 : rstEq ρ (f, false) = (f', p) := by simp [rstEq, hp, hf']
    have e1 : rstEq ρ (f, true) = (f', !p) := by simp [rstEq, hp, hf']
    rw [e0] at h0 hsub
    rw [e1] at h1 hsub
    cases hpv : p with
    | false =>
      rw [hpv] at h0 h1 hsub
      refine ⟨rstLin ρ (C.erase (f, false) ∪ D.erase (f, true)) ::
        ((rstLin ρ C).erase (f', false) ∪ (rstLin ρ D).erase (f', true)) :: π', ?_, ?_, ?_⟩
      · exact IsLinDerivation.weak (IsLinDerivation.res hd hTC hTD ⟨f', h0, h1, rfl⟩)
          List.mem_cons_self (rst_weak_of_subset hsub)
      · simp only [List.length_cons]; omega
      · intro L hL
        rcases List.mem_cons.mp hL with rfl | hL
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem L hL))
    | true =>
      rw [hpv] at h0 h1 hsub
      rw [Finset.union_comm] at hsub
      refine ⟨rstLin ρ (C.erase (f, false) ∪ D.erase (f, true)) ::
        ((rstLin ρ D).erase (f', false) ∪ (rstLin ρ C).erase (f', true)) :: π', ?_, ?_, ?_⟩
      · exact IsLinDerivation.weak (IsLinDerivation.res hd hTD hTC ⟨f', h1, h0, rfl⟩)
          List.mem_cons_self (rst_weak_of_subset hsub)
      · simp only [List.length_cons]; omega
      · intro L hL
        rcases List.mem_cons.mp hL with rfl | hL
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem L hL))
  | @weak π C D hπ hC hw ih =>
    obtain ⟨π', hd, hlen, hmem⟩ := ih
    refine ⟨rstLin ρ D :: π', ?_, ?_, ?_⟩
    · refine IsLinDerivation.weak hd (hmem C hC) (fun a ha => ?_)
      rw [rstLin_sat] at ha ⊢
      exact hw _ ha
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hmem L hL)

/-- A refutable CNF leaves some clause unsatisfied by any partial assignment. -/
theorem rst_exists_clause {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (LinClause V)} (h : IsLinRefutation F π) (ρ : V → Option Bool) :
    ∃ B, B ∈ restrictCNF F ρ := by
  by_contra hne
  push Not at hne
  apply lin_refutation_unsat h
  refine ⟨fun v => (ρ v).getD false, fun C hC => ?_⟩
  by_cases hs : ∃ l ∈ C, ρ l.1 = some l.2
  · obtain ⟨l, hl, hρ⟩ := hs
    exact ⟨l, hl, by simp [hρ]⟩
  · exact absurd ⟨C, hC, by simp [restrictClause, hs]⟩ (hne (C.filter fun l => ρ l.1 = none))

theorem rst_refutation {V : Type} [DecidableEq V] (F : Set (Clause V)) (ρ : V → Option Bool)
    (π : List (LinClause V)) (h : IsLinRefutation F π) :
    ∃ π' : List (LinClause V), IsLinRefutation (restrictCNF F ρ) π' ∧
      π'.length ≤ 2 * π.length := by
  obtain ⟨B, hB⟩ := rst_exists_clause h ρ
  obtain ⟨π', hd, hlen, hmem⟩ := rst_derivation F ρ B hB h.1
  refine ⟨π', ⟨hd, ?_⟩, hlen⟩
  have := hmem ∅ h.2
  simpa [rstLin] using this

end PEqualNP.ProofComplexity.Helpers
