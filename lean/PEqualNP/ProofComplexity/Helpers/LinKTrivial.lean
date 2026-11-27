import PEqualNP.Defs.ProofComplexityLinK
import Mathlib.Data.Finset.Card

/-!
# Helpers: Res(k, ⊕) with full semantic weakening is trivial

Once `k` reaches the clause width, an unsatisfiable formula with `m` clauses has a derivation
of the empty line with at most `2 * m + 1` lines: the axioms, the tautology whose terms say
"clause `C` is false", and one cut against each axiom.
-/

namespace PEqualNP.ProofComplexity.Helpers.LinKTrivial

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- The term saying that the clause `C` is false. -/
def falseTerm (C : Clause V) : LinTerm V := (linOfClause C).image negLinEq

omit [DecidableEq V] in
theorem negLinEq_negLinEq (q : LinEq V) : negLinEq (negLinEq q) = q := by
  rcases q with ⟨f, b⟩
  simp [negLinEq]

theorem falseTerm_card_le (C : Clause V) : (falseTerm C).card ≤ C.card :=
  Finset.card_image_le.trans Finset.card_image_le

theorem falseTerm_sat (a : V → Bool) (C : Clause V) (h : ¬ ClauseSat a C) :
    LinTermSat a (falseTerm C) := by
  intro q hq
  obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq'
  have hne : a l.1 ≠ l.2 := fun h' => h ⟨l, hl, h'⟩
  show Odd (({l.1} : Finset V).filter (fun v => a v = true)).card ↔ (!l.2) = true
  rw [Finset.filter_singleton]
  cases h1 : a l.1 <;> cases h2 : l.2 <;> simp_all

/-- The axiom of `C` holds the one-equation term of the complement of each equation of
`falseTerm C`. -/
theorem neg_mem_axiom (C : Clause V) :
    ∀ e ∈ falseTerm C, ({negLinEq e} : LinTerm V) ∈ linKOfClause C := by
  intro e he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
  rw [negLinEq_negLinEq]
  exact Finset.mem_image_of_mem _ hq

/-- The cut of a line against the axiom of `C` on `falseTerm C` leaves nothing of the axiom. -/
theorem leftover_empty (C : Clause V) :
    linKOfClause C \ (falseTerm C).image (fun e => ({negLinEq e} : LinTerm V)) = ∅ := by
  rw [Finset.sdiff_eq_empty_iff_subset]
  intro T hT
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hT
  exact Finset.mem_image.mpr
    ⟨negLinEq q, Finset.mem_image_of_mem _ hq, by rw [negLinEq_negLinEq]⟩

/-- The clauses of a list, as axioms, form a derivation. -/
theorem axioms_derivation (k : ℕ) (W : LinKLine V → LinKLine V → Prop) (F : Set (Clause V))
    (l : List (Clause V)) (hF : ∀ C ∈ l, C ∈ F) (hk : ∀ C ∈ l, C.card ≤ k) :
    IsLinKDerivation k W ((fun C => linKOfClause C) '' F) (l.map linKOfClause) := by
  induction l with
  | nil => exact IsLinKDerivation.nil
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

/-- One cut for each clause of the list `l` whose axiom is in the derivation: from a line `L`
to a line inside `L` holding no `falseTerm C` for `C` in `l`. -/
theorem cut_steps (k : ℕ) (F : Set (LinKLine V)) (l : List (Clause V)) :
    ∀ (π : List (LinKLine V)) (L : LinKLine V), IsLinKDerivation k LinKSemWeak F π → L ∈ π →
      (∀ T ∈ L, T.card ≤ k) → (∀ C ∈ l, linKOfClause C ∈ π) →
      ∃ (π' : List (LinKLine V)) (L' : LinKLine V), IsLinKDerivation k LinKSemWeak F π' ∧
        L' ∈ π' ∧ L' ⊆ L ∧ (∀ C ∈ l, falseTerm C ∉ L') ∧ π'.length ≤ π.length + l.length := by
  induction l with
  | nil =>
    intro π L hπ hL _ _
    exact ⟨π, L, hπ, hL, subset_rfl, by simp, by simp⟩
  | cons C l ih =>
    intro π L hπ hL hk hax
    by_cases hT : falseTerm C ∈ L
    · have hcut : IsLinKCut L (linKOfClause C) (L.erase (falseTerm C)) :=
        ⟨falseTerm C, hT, neg_mem_axiom C, by rw [leftover_empty, Finset.union_empty]⟩
      have hk' : ∀ T ∈ L.erase (falseTerm C), T.card ≤ k :=
        fun T hT' => hk T (Finset.mem_of_mem_erase hT')
      obtain ⟨π', L', hπ', hL', hsub, hno, hlen⟩ :=
        ih (L.erase (falseTerm C) :: π) _
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

/-- With full semantic weakening and `k` at least the clause width, an unsatisfiable formula
with `m` clauses has a derivation of the empty line with at most `2 * m + 1` lines. -/
theorem trivial_refutation (F : Finset (Clause V)) (k : ℕ) (hk : ∀ C ∈ F, C.card ≤ k)
    (hunsat : ¬ Satisfiable (↑F : Set (Clause V))) :
    ∃ π : List (LinKLine V),
      IsLinKDerivation k LinKSemWeak ((fun C => linKOfClause C) '' (↑F : Set (Clause V))) π ∧
        (∅ : LinKLine V) ∈ π ∧ π.length ≤ 2 * F.card + 1 := by
  have hne : ∃ C0, C0 ∈ F := by
    by_contra h
    exact hunsat ⟨fun _ => true, fun C hC => absurd ⟨C, Finset.mem_coe.mp hC⟩ h⟩
  obtain ⟨C0, hC0⟩ := hne
  have h0 : IsLinKDerivation k LinKSemWeak ((fun C => linKOfClause C) '' (↑F : Set (Clause V)))
      (F.toList.map linKOfClause) :=
    axioms_derivation k LinKSemWeak (↑F) F.toList
      (fun C hC => Finset.mem_coe.mpr (Finset.mem_toList.mp hC))
      (fun C hC => hk C (Finset.mem_toList.mp hC))
  have htk : ∀ T ∈ F.image falseTerm, T.card ≤ k := by
    intro T hT
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hT
    exact (falseTerm_card_le C).trans (hk C hC)
  have hweak : LinKSemWeak (linKOfClause C0) (F.image falseTerm) := by
    intro a _
    by_contra hcon
    refine hunsat ⟨a, fun C hC => ?_⟩
    by_contra hns
    exact hcon ⟨falseTerm C, Finset.mem_image_of_mem _ (Finset.mem_coe.mp hC),
      falseTerm_sat a C hns⟩
  have h1 := IsLinKDerivation.weak h0
    (List.mem_map.mpr ⟨C0, Finset.mem_toList.mpr hC0, rfl⟩) hweak htk
  obtain ⟨π', L', hπ', hL', hsub, hno, hlen⟩ :=
    cut_steps k _ F.toList _ (F.image falseTerm) h1 List.mem_cons_self htk
      (fun C hC => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨C, hC, rfl⟩))
  have hempty : L' = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro T hT
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp (hsub hT)
    exact hno C (Finset.mem_toList.mpr hC) hT
  subst hempty
  refine ⟨π', hπ', hL', ?_⟩
  simp only [List.length_cons, List.length_map, Finset.length_toList] at hlen
  omega

end PEqualNP.ProofComplexity.Helpers.LinKTrivial
