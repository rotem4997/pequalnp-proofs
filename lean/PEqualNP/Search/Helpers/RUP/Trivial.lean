import Mathlib
import PEqualNP.Defs.SearchRUP

/-!
# Helpers: a clause learned by unit propagation has a short input resolution derivation

Helper module, proofs only. Used by `L-lib-111`. This is the trivial resolution of Beame,
Kautz and Sabharwal (2004), done with subclauses because the resolution of the definitions
has no weakening rule: if `C` is RUP over clauses each of which is an axiom or has a subclause
among the lines of a derivation, the derivation extends by at most `4 * (card V + 1)` lines to
one holding a subclause of `C`.

The tree-shaped `UPForces` proofs are first flattened to a `UPChain`: a duplicate-free list of
propagated literals, newest first, each with a reason clause whose other literals are made
false by the assumptions or by earlier members. The conflict clause is then resolved once per
member of the chain, newest first.
-/

namespace PEqualNP.Search.Helpers.RUP

open PEqualNP.ProofComplexity PEqualNP.Search

variable {V : Type}

/-- Complementation of literals is an involution. -/
theorem negLit_negLit (l : Literal V) : negLit (negLit l) = l := by
  rcases l with ⟨v, b⟩
  simp [negLit]

/-- Complementation of literals is injective. -/
theorem negLit_inj {l m : Literal V} (h : negLit l = negLit m) : l = m := by
  rw [← negLit_negLit l, h, negLit_negLit]

/-- `UPChain Γ A L`: the literals `L`, NEWEST FIRST and without repetition, are propagated in
turn: each has a reason clause in `Γ` containing it, all of whose other literals are made
false by the assumptions `A` or by earlier members of the list. -/
inductive UPChain (Γ : Set (Clause V)) (A : Set (Literal V)) : List (Literal V) → Prop
  | nil : UPChain Γ A []
  | cons {L : List (Literal V)} {l : Literal V} {D : Clause V} :
      UPChain Γ A L → l ∉ L → D ∈ Γ → l ∈ D →
      (∀ l' ∈ D, l' ≠ l → negLit l' ∈ A ∨ negLit l' ∈ L) → UPChain Γ A (l :: L)

/-- A propagation chain has no repeated literal. -/
theorem UPChain.nodup {Γ : Set (Clause V)} {A : Set (Literal V)} {L : List (Literal V)}
    (h : UPChain Γ A L) : L.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | cons _ hl _ _ _ ih => exact List.nodup_cons.mpr ⟨hl, ih⟩

/-- A propagation chain has at most `2 * card V` members. -/
theorem UPChain.length_le [Fintype V] {Γ : Set (Clause V)} {A : Set (Literal V)}
    {L : List (Literal V)} (h : UPChain Γ A L) : L.length ≤ 2 * Fintype.card V := by
  have := h.nodup.length_le_card
  simpa [Fintype.card_prod, Fintype.card_bool, mul_comm] using this

/-- If every literal of a finite set can be reached by extending any chain, all of them can be
reached by one extension. -/
theorem extend_finset [DecidableEq V] {Γ : Set (Clause V)} {A : Set (Literal V)}
    (T : Finset (Literal V))
    (h : ∀ m ∈ T, ∀ L, UPChain Γ A L →
      ∃ L', UPChain Γ A L' ∧ L ⊆ L' ∧ (negLit m ∈ A ∨ negLit m ∈ L')) :
    ∀ L, UPChain Γ A L →
      ∃ L', UPChain Γ A L' ∧ L ⊆ L' ∧ ∀ m ∈ T, negLit m ∈ A ∨ negLit m ∈ L' := by
  induction T using Finset.induction_on with
  | empty => intro L hL; exact ⟨L, hL, List.Subset.refl _, by simp⟩
  | insert a T _ ih =>
    intro L hL
    obtain ⟨L1, hL1, hs1, h1⟩ :=
      ih (fun m hm => h m (Finset.mem_insert_of_mem hm)) L hL
    obtain ⟨L2, hL2, hs2, h2⟩ := h a (Finset.mem_insert_self a T) L1 hL1
    refine ⟨L2, hL2, List.Subset.trans hs1 hs2, ?_⟩
    intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact h2
    · exact (h1 m hm).imp id (fun x => hs2 x)

/-- Flattening: a literal forced by unit propagation is assumed or is reached by extending any
given propagation chain. -/
theorem extend_of_forces [DecidableEq V] {Γ : Set (Clause V)} {A : Set (Literal V)}
    {l : Literal V} (h : UPForces Γ A l) :
    ∀ L, UPChain Γ A L → ∃ L', UPChain Γ A L' ∧ L ⊆ L' ∧ (l ∈ A ∨ l ∈ L') := by
  induction h with
  | hyp hl => intro L hL; exact ⟨L, hL, List.Subset.refl _, Or.inl hl⟩
  | @unit D l hD hlD _ ih =>
    intro L hL
    obtain ⟨L1, hL1, hs1, h1⟩ := extend_finset (D.erase l)
      (fun m hm => ih m (Finset.mem_of_mem_erase hm) (Finset.ne_of_mem_erase hm)) L hL
    by_cases hl : l ∈ L1
    · exact ⟨L1, hL1, hs1, Or.inr hl⟩
    · exact ⟨l :: L1,
        UPChain.cons hL1 hl hD hlD
          (fun l' h' hne => h1 l' (Finset.mem_erase.mpr ⟨hne, h'⟩)),
        List.subset_cons_of_subset _ hs1, Or.inr List.mem_cons_self⟩

/-- A clause that is an axiom or has a subclause among the lines has a subclause among the
lines after at most one more line. -/
theorem available [DecidableEq V] {F : Set (Clause V)} {π : List (Clause V)} {D : Clause V}
    (hπ : IsDerivation F π) (hD : D ∈ F ∨ ∃ D' ∈ π, D' ⊆ D) :
    ∃ π1 D', IsDerivation F π1 ∧ π ⊆ π1 ∧ π1.length ≤ π.length + 1 ∧ D' ∈ π1 ∧ D' ⊆ D := by
  rcases hD with hD | ⟨D', hD', hsub⟩
  · exact ⟨D :: π, D, IsDerivation.ax hπ hD, List.subset_cons_self _ _, le_rfl,
      List.mem_cons_self, Finset.Subset.refl _⟩
  · exact ⟨π, D', hπ, List.Subset.refl _, Nat.le_succ _, hD', hsub⟩

/-- Two clauses holding complementary literals resolve, in one of the two orders. -/
theorem resolvent_of_lit [DecidableEq V] {E D : Clause V} {l : Literal V}
    (hD : l ∈ D) (hE : negLit l ∈ E) :
    IsResolvent D E (E.erase (negLit l) ∪ D.erase l) ∨
      IsResolvent E D (E.erase (negLit l) ∪ D.erase l) := by
  rcases l with ⟨v, b⟩
  cases b with
  | true => exact Or.inl ⟨v, hD, hE, Finset.union_comm _ _⟩
  | false => exact Or.inr ⟨v, hE, hD, rfl⟩

/-- Trivial resolution along a propagation chain: a line all of whose literals are made false
by the assumptions or the chain is resolved, once per member of the chain at most, down to a
line all of whose literals are made false by the assumptions alone. -/
theorem trivial_resolution [DecidableEq V] {F Γ : Set (Clause V)} {A : Set (Literal V)}
    {π₀ : List (Clause V)} (hΓ : ∀ D ∈ Γ, D ∈ F ∨ ∃ D' ∈ π₀, D' ⊆ D)
    {L : List (Literal V)} (hL : UPChain Γ A L) :
    ∀ (π : List (Clause V)) (E : Clause V), IsDerivation F π → π₀ ⊆ π → E ∈ π →
      (∀ m ∈ E, negLit m ∈ A ∨ negLit m ∈ L) →
      ∃ π' E', IsDerivation F π' ∧ π ⊆ π' ∧ π'.length ≤ π.length + 2 * L.length ∧
        E' ∈ π' ∧ ∀ m ∈ E', negLit m ∈ A := by
  induction hL with
  | nil =>
    intro π E hπ _ hE hf
    exact ⟨π, E, hπ, List.Subset.refl _, by simp, hE, fun m hm => (hf m hm).resolve_right (by simp)⟩
  | @cons L l D _ _ hD hlD hfal ih =>
    intro π E hπ h0 hE hf
    by_cases hn : negLit l ∈ E
    · obtain ⟨π1, D', hπ1, hs1, hlen1, hD'1, hsub⟩ := available hπ
        ((hΓ D hD).imp id (fun ⟨D', h1, h2⟩ => ⟨D', h0 h1, h2⟩))
      by_cases hl' : l ∈ D'
      · have hres : IsDerivation F ((E.erase (negLit l) ∪ D'.erase l) :: π1) := by
          rcases resolvent_of_lit hl' hn with h | h
          · exact IsDerivation.res hπ1 hD'1 (hs1 hE) h
          · exact IsDerivation.res hπ1 (hs1 hE) hD'1 h
        obtain ⟨π', E', hπ', hs', hlen', hE', hf'⟩ :=
          ih ((E.erase (negLit l) ∪ D'.erase l) :: π1) _ hres
            (List.subset_cons_of_subset _ (List.Subset.trans h0 hs1)) List.mem_cons_self (by
              intro m hm
              rcases Finset.mem_union.mp hm with hm | hm
              · have hne := Finset.ne_of_mem_erase hm
                rcases hf m (Finset.mem_of_mem_erase hm) with h | h
                · exact Or.inl h
                · rcases List.mem_cons.mp h with h | h
                  · exact absurd (by rw [← h, negLit_negLit]) hne
                  · exact Or.inr h
              · exact hfal m (hsub (Finset.mem_of_mem_erase hm)) (Finset.ne_of_mem_erase hm))
        refine ⟨π', E', hπ', List.Subset.trans (List.Subset.trans hs1 (List.subset_cons_self _ _)) hs', ?_, hE', hf'⟩
        simp only [List.length_cons] at hlen' ⊢
        omega
      · obtain ⟨π', E', hπ', hs', hlen', hE', hf'⟩ :=
          ih π1 D' hπ1 (List.Subset.trans h0 hs1) hD'1 (fun m hm =>
            hfal m (hsub hm) (fun h => hl' (h ▸ hm)))
        refine ⟨π', E', hπ', List.Subset.trans hs1 hs', ?_, hE', hf'⟩
        simp only [List.length_cons] at hlen' ⊢
        omega
    · obtain ⟨π', E', hπ', hs', hlen', hE', hf'⟩ :=
        ih π E hπ h0 hE (fun m hm => by
          rcases hf m hm with h | h
          · exact Or.inl h
          · rcases List.mem_cons.mp h with h | h
            · exact absurd (by rw [← h, negLit_negLit]; exact hm) hn
            · exact Or.inr h)
      refine ⟨π', E', hπ', hs', ?_, hE', hf'⟩
      simp only [List.length_cons] at hlen' ⊢
      omega

/-- One learning step: if `C` is RUP over clauses each of which is an axiom or has a subclause
among the lines of a derivation, at most `4 * (card V + 1)` more lines give a derivation
holding a subclause of `C`. -/
theorem learn_step [Fintype V] [DecidableEq V] {F Γ : Set (Clause V)} {π : List (Clause V)}
    {C : Clause V} (hπ : IsDerivation F π) (hΓ : ∀ D ∈ Γ, D ∈ F ∨ ∃ D' ∈ π, D' ⊆ D)
    (h : IsRUP Γ C) :
    ∃ π' C', IsDerivation F π' ∧ π ⊆ π' ∧ π'.length ≤ π.length + 4 * (Fintype.card V + 1) ∧
      C' ∈ π' ∧ C' ⊆ C := by
  obtain ⟨D, hD, hf⟩ := h
  obtain ⟨L, hL, _, hall⟩ :=
    extend_finset D (fun m hm => extend_of_forces (hf m hm)) [] UPChain.nil
  obtain ⟨π1, D', hπ1, hs1, hlen1, hD'1, hsub⟩ := available hπ (hΓ D hD)
  obtain ⟨π', E', hπ', hs', hlen', hE', hf'⟩ :=
    trivial_resolution hΓ hL π1 D' hπ1 hs1 hD'1 (fun m hm => hall m (hsub hm))
  refine ⟨π', E', hπ', List.Subset.trans hs1 hs', ?_, hE', ?_⟩
  · have := hL.length_le
    omega
  · intro m hm
    obtain ⟨c, hc, hcm⟩ := hf' m hm
    rw [← negLit_inj hcm]
    exact hc

/-- Along a run, a derivation from the formula holds a subclause of every learned clause and
has at most `4 * (card V + 1)` lines per learned clause. -/
theorem derivation_of_run [Fintype V] [DecidableEq V] {F : Set (Clause V)}
    {ρ : List (Clause V)} (h : IsRUPRun F ρ) :
    ∃ π, IsDerivation F π ∧ (∀ C ∈ ρ, ∃ C' ∈ π, C' ⊆ C) ∧
      π.length ≤ 4 * (ρ.length * (Fintype.card V + 1)) := by
  induction h with
  | nil => exact ⟨[], IsDerivation.nil, by simp, by simp⟩
  | @learn ρ C _ hC ih =>
    obtain ⟨π, hπ, hav, hlen⟩ := ih
    obtain ⟨π', C', hπ', hs, hlen', hC', hsub⟩ := learn_step hπ (Γ := F ∪ {D | D ∈ ρ})
      (fun D hD => hD.imp id (fun hD => hav D hD)) hC
    refine ⟨π', hπ', ?_, ?_⟩
    · intro B hB
      rcases List.mem_cons.mp hB with rfl | hB
      · exact ⟨C', hC', hsub⟩
      · obtain ⟨B', hB', hBs⟩ := hav B hB
        exact ⟨B', hs hB', hBs⟩
    · simp only [List.length_cons]
      rw [Nat.add_mul, Nat.mul_add]
      omega

/-- A run that learns the empty clause yields a resolution refutation of at most
`4 * (number of learned clauses) * (card V + 1)` lines. -/
theorem refutation_of_run [Fintype V] [DecidableEq V] {F : Set (Clause V)}
    {ρ : List (Clause V)} (h : IsRUPRun F ρ) (he : (∅ : Clause V) ∈ ρ) :
    ∃ π, IsRefutation F π ∧ π.length ≤ 4 * (ρ.length * (Fintype.card V + 1)) := by
  obtain ⟨π, hπ, hav, hlen⟩ := derivation_of_run h
  obtain ⟨C', hC', hsub⟩ := hav ∅ he
  rw [Finset.subset_empty] at hsub
  exact ⟨π, ⟨hπ, hsub ▸ hC'⟩, hlen⟩

end PEqualNP.Search.Helpers.RUP
