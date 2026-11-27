import PEqualNP.ProofComplexity.Helpers.Matching

/-!
# Helpers: resolution over linear equations

Soundness of Res(⊕), and the critical complexity of its lines on the pigeonhole formula.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

theorem linEqSat_singleton {V : Type} [DecidableEq V] (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a (({v} : Finset V), s) ↔ a v = s := by
  unfold LinEqSat
  rw [Finset.filter_singleton]
  cases h : a v <;> cases s <;> simp

theorem linOfClause_sat {V : Type} [DecidableEq V] (a : V → Bool) (C : Clause V) :
    LinClauseSat a (linOfClause C) ↔ ClauseSat a C := by
  constructor
  · rintro ⟨q, hq, hsat⟩
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨l, hl, (linEqSat_singleton a l.1 l.2).mp hsat⟩
  · rintro ⟨l, hl, hsat⟩
    exact ⟨_, Finset.mem_image.mpr ⟨l, hl, rfl⟩, (linEqSat_singleton a l.1 l.2).mpr hsat⟩

theorem lin_resolvent_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : LinClause V}
    (h : IsLinResolvent C D R) (hC : LinClauseSat a C) (hD : LinClauseSat a D) :
    LinClauseSat a R := by
  obtain ⟨f, -, -, rfl⟩ := h
  obtain ⟨q, hq, hqs⟩ := hC
  obtain ⟨q', hq', hqs'⟩ := hD
  by_cases h : q = (f, false)
  · subst h
    refine ⟨q', Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hq'⟩), hqs'⟩
    rintro rfl
    simp only [LinEqSat] at hqs hqs'
    simp_all
  · exact ⟨q, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hq⟩), hqs⟩

/-- A property of lines that holds of the axioms and is kept by both rules holds of every
line of a derivation. Here: being satisfied by a fixed assignment. -/
theorem lin_derivation_sound {V : Type} [DecidableEq V] (a : V → Bool) {F : Set (LinClause V)}
    {π : List (LinClause V)} (h : IsLinDerivation F π) (ha : ∀ C ∈ F, LinClauseSat a C) :
    ∀ C ∈ π, LinClauseSat a C := by
  induction h with
  | nil => intro C hC; simp at hC
  | ax _ hCF ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact ha _ hCF
    · exact ih E hE
  | res _ hC hD hR ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact lin_resolvent_sound a hR (ih _ hC) (ih _ hD)
    · exact ih E hE
  | weak _ hC hw ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact hw a (ih _ hC)
    · exact ih E hE

theorem lin_refutation_unsat {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (LinClause V)} (h : IsLinRefutation F π) : ¬ Satisfiable F := by
  rintro ⟨a, ha⟩
  have hax : ∀ C ∈ (fun C => linOfClause C) '' F, LinClauseSat a C := by
    rintro _ ⟨C, hC, rfl⟩
    exact (linOfClause_sat a C).mpr (ha C hC)
  obtain ⟨q, hq, -⟩ := lin_derivation_sound a h.1 hax ∅ h.2
  simp at hq

/-- Every critical assignment seating all of `S` satisfies the linear clause `C`. -/
def LImp {n : ℕ} (S : Finset (Fin (n + 1))) (C : LinClause (PVar n)) : Prop :=
  ∀ e : Crit n, (∀ i ∈ S, e i ≠ none) → LinClauseSat (asg e) C

theorem limp_axiom {n : ℕ} {C : LinClause (PVar n)}
    (hC : C ∈ (fun C => linOfClause C) '' PHP (n + 1) n) :
    ∃ S : Finset (Fin (n + 1)), LImp S C ∧ S.card ≤ 1 := by
  obtain ⟨C₀, hC₀, rfl⟩ := hC
  obtain ⟨S, hS, hcard⟩ := imp_axiom ∅ hC₀
  refine ⟨S, fun e he => ?_, hcard⟩
  exact (linOfClause_sat _ C₀).mpr (hS e (fun p hp => by simp at hp) he)

theorem univ_subset_of_limp_empty {n : ℕ} {S : Finset (Fin (n + 1))} (hS : LImp S ∅) :
    Finset.univ ⊆ S := by
  intro i _
  by_contra hiS
  obtain ⟨e, -, hei⟩ := valid_empty (n := n) i (by rw [freeP_empty]; exact Finset.mem_univ i)
  have hsat : LinClauseSat (asg e) ∅ := by
    apply hS e
    intro i' hi' h'
    exact hiS (e.injective (hei.trans h'.symm) ▸ hi')
  obtain ⟨q, hq, -⟩ := hsat
  simp at hq

theorem exists_min_limp {n : ℕ} {S : Finset (Fin (n + 1))} {C : LinClause (PVar n)}
    (hS : LImp S C) :
    ∃ S₀ : Finset (Fin (n + 1)), LImp S₀ C ∧ S₀.card ≤ S.card ∧
      ∀ S' : Finset (Fin (n + 1)), LImp S' C → S₀.card ≤ S'.card := by
  classical
  have hex : ∃ k, ∃ S' : Finset (Fin (n + 1)), LImp S' C ∧ S'.card = k := ⟨_, S, hS, rfl⟩
  obtain ⟨S₀, hS₀, hcard⟩ := Nat.find_spec hex
  refine ⟨S₀, hS₀, ?_, ?_⟩
  · rw [hcard]; exact Nat.find_min' hex ⟨S, hS, rfl⟩
  · intro S' hS'
    rw [hcard]; exact Nat.find_min' hex ⟨S', hS', rfl⟩

/-- A line is medium: its least implying set has size in `((n+1)/3, 2(n+1)/3]`. -/
def LMedium {n : ℕ} (C : LinClause (PVar n)) : Prop :=
  ∃ S : Finset (Fin (n + 1)), n + 1 < 3 * S.card ∧ 3 * S.card ≤ 2 * (n + 1) ∧ LImp S C ∧
    ∀ S' : Finset (Fin (n + 1)), LImp S' C → S.card ≤ S'.card

theorem lmedium_or_small {n : ℕ} (hn : 1 ≤ n) {π : List (LinClause (PVar n))}
    (hπ : IsLinDerivation ((fun C => linOfClause C) '' PHP (n + 1) n) π) :
    (∃ C ∈ π, LMedium C) ∨
      ∀ C ∈ π, ∃ S : Finset (Fin (n + 1)), LImp S C ∧ 3 * S.card ≤ n + 1 := by
  have step : ∀ (C : LinClause (PVar n)) (S : Finset (Fin (n + 1))), LImp S C →
      3 * S.card ≤ 2 * (n + 1) →
      LMedium C ∨ ∃ S : Finset (Fin (n + 1)), LImp S C ∧ 3 * S.card ≤ n + 1 := by
    intro C S hS hcard
    obtain ⟨S₀, hS₀, hle, hmin⟩ := exists_min_limp hS
    by_cases h : 3 * S₀.card ≤ n + 1
    · exact Or.inr ⟨S₀, hS₀, h⟩
    · exact Or.inl ⟨S₀, by omega, by omega, hS₀, hmin⟩
  have close : ∀ (π : List (LinClause (PVar n))) (C : LinClause (PVar n)),
      (∀ E ∈ π, ∃ S : Finset (Fin (n + 1)), LImp S E ∧ 3 * S.card ≤ n + 1) →
      (LMedium C ∨ ∃ S : Finset (Fin (n + 1)), LImp S C ∧ 3 * S.card ≤ n + 1) →
      (∃ E ∈ C :: π, LMedium E) ∨
        ∀ E ∈ C :: π, ∃ S : Finset (Fin (n + 1)), LImp S E ∧ 3 * S.card ≤ n + 1 := by
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
    · obtain ⟨S, hS, hcard⟩ := limp_axiom hC
      exact close π C hsmall (step C S hS (by omega))
  | @res π C D R _ hC hD hR ih =>
    rcases ih with ⟨E, hE, hmed⟩ | hsmall
    · exact Or.inl ⟨E, List.mem_cons_of_mem _ hE, hmed⟩
    · obtain ⟨S, hS, hScard⟩ := hsmall C hC
      obtain ⟨T, hT, hTcard⟩ := hsmall D hD
      have hU : LImp (S ∪ T) R := fun e he => lin_resolvent_sound _ hR
        (hS e fun i hi => he i (Finset.mem_union_left _ hi))
        (hT e fun i hi => he i (Finset.mem_union_right _ hi))
      have hUcard : (S ∪ T).card ≤ S.card + T.card := Finset.card_union_le S T
      exact close π R hsmall (step R (S ∪ T) hU (by omega))
  | @weak π C D _ hC hw ih =>
    rcases ih with ⟨E, hE, hmed⟩ | hsmall
    · exact Or.inl ⟨E, List.mem_cons_of_mem _ hE, hmed⟩
    · obtain ⟨S, hS, hScard⟩ := hsmall C hC
      exact close π D hsmall (step D S (fun e he => hw _ (hS e he)) (by omega))

theorem exists_lmedium {n : ℕ} (hn : 1 ≤ n) {π : List (LinClause (PVar n))}
    (hπ : IsLinRefutation (PHP (n + 1) n) π) : ∃ C ∈ π, LMedium C := by
  rcases lmedium_or_small hn hπ.1 with h | h
  · exact h
  · obtain ⟨S, hS, hcard⟩ := h ∅ hπ.2
    have := Finset.card_le_card (univ_subset_of_limp_empty hS)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega

end PEqualNP.ProofComplexity.Helpers
