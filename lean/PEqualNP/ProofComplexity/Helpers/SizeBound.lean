import PEqualNP.Defs.ProofComplexityBit
import PEqualNP.ProofComplexity.Helpers.Lin
import Mathlib

/-!
# Helpers: the clause-counting size bound for the bit pigeonhole principle in Res(⊕)

The bit pigeonhole formula with `2 ^ l + 1` pigeons and `2 ^ l` holes is minimally
unsatisfiable: dropping the clause of the pigeons `i`, `i'` and the hole `α` leaves a formula
satisfied by the map that sends `i` and `i'` to `α` and the other pigeons one to one onto the
other holes. A sound proof system cannot refute a satisfiable formula, so every Res(⊕)
refutation lists every clause of the formula, and the empty clause on top of them. With
`n = 2 ^ l` holes this is `n * (n + 1 choose 2) + 1` lines, of order `n ^ 3 / 2`.

This is the baseline that any size lower bound for this formula has to beat: a bound below
the number of clauses says nothing new. The argument uses soundness alone, so it holds with
the semantic weakening rule and for dag-like refutations.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

/-- A line that does not occur in a derivation is not needed as an axiom. -/
theorem lin_derivation_diff {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} (A : LinClause V) (h : IsLinDerivation F π) (hA : A ∉ π) :
    IsLinDerivation (F \ {A}) π := by
  induction h with
  | nil => exact IsLinDerivation.nil
  | @ax π C _ hC ih =>
    rw [List.mem_cons, not_or] at hA
    exact IsLinDerivation.ax (ih hA.2) ⟨hC, fun hCA => hA.1 (Set.mem_singleton_iff.mp hCA).symm⟩
  | @res π C D R _ hC hD hR ih =>
    rw [List.mem_cons, not_or] at hA
    exact IsLinDerivation.res (ih hA.2) hC hD hR
  | @weak π C D _ hC hw ih =>
    rw [List.mem_cons, not_or] at hA
    exact IsLinDerivation.weak (ih hA.2) hC hw

section Pigeons

variable {m l : ℕ}

/-- The clause of the bit pigeonhole formula for the pigeons `i`, `i'` and the hole `α`. -/
def bax (i i' : Fin m) (α : Fin l → Bool) : Clause (Fin m × Fin l) :=
  Finset.univ.image (fun b : Fin l => ((i, b), !α b)) ∪
    Finset.univ.image (fun b : Fin l => ((i', b), !α b))

theorem bax_comm (i i' : Fin m) (α : Fin l → Bool) : bax i i' α = bax i' i α :=
  Finset.union_comm _ _

/-- A map from pigeons to holes whose only collision is `i`, `i'` at the hole `α`. -/
theorem exists_near_injective {l : ℕ} (i i' : Fin (2 ^ l + 1)) (hne : i ≠ i')
    (α : Fin l → Bool) :
    ∃ h : Fin (2 ^ l + 1) → (Fin l → Bool), h i = α ∧ h i' = α ∧
      ∀ j j', j ≠ j' → h j = h j' → h j = α ∧ ((j = i ∧ j' = i') ∨ (j = i' ∧ j' = i)) := by
  classical
  have hcard : Fintype.card {j : Fin (2 ^ l + 1) // j ≠ i' ∧ j ≠ i} ≤
      Fintype.card {β : Fin l → Bool // β ≠ α} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have h1 : (Finset.univ.filter fun j : Fin (2 ^ l + 1) => j ≠ i' ∧ j ≠ i) =
        (Finset.univ.erase i).erase i' := by
      ext j; simp
    have h2 : (Finset.univ.filter fun β : Fin l → Bool => β ≠ α) = Finset.univ.erase α := by
      ext β; simp
    rw [h1, h2, Finset.card_erase_of_mem (by simp [hne.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun j => if hj : j ≠ i' ∧ j ≠ i then (e ⟨j, hj⟩).1 else α, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro j j' hjj heq
    by_cases hj : j ≠ i' ∧ j ≠ i <;> by_cases hj' : j' ≠ i' ∧ j' ≠ i
    · have heq' : (e ⟨j, hj⟩).1 = (e ⟨j', hj'⟩).1 := by simpa only [dif_pos hj, dif_pos hj'] using heq
      have := e.injective (Subtype.ext heq')
      exact absurd (congrArg Subtype.val this) hjj
    · have heq' : (e ⟨j, hj⟩).1 = α := by simpa only [dif_pos hj, dif_neg hj'] using heq
      exact absurd heq' (e ⟨j, hj⟩).2
    · have heq' : α = (e ⟨j', hj'⟩).1 := by simpa only [dif_neg hj, dif_pos hj'] using heq
      exact absurd heq'.symm (e ⟨j', hj'⟩).2
    · refine ⟨by simp [hj], ?_⟩
      have a1 : j = i' ∨ j = i := by tauto
      have a2 : j' = i' ∨ j' = i := by tauto
      rcases a1 with rfl | rfl <;> rcases a2 with rfl | rfl <;> simp_all

/-- Minimal unsatisfiability: without one clause, the formula is satisfiable. -/
theorem bphp_critical {l : ℕ} (i i' : Fin (2 ^ l + 1)) (hne : i ≠ i') (α : Fin l → Bool) :
    ∃ a : Fin (2 ^ l + 1) × Fin l → Bool,
      ∀ C ∈ BPHP (2 ^ l + 1) l, C ≠ bax i i' α → ClauseSat a C := by
  obtain ⟨h, -, -, hinj⟩ := exists_near_injective i i' hne α
  refine ⟨fun v => h v.1 v.2, ?_⟩
  rintro C ⟨j, j', β, hjj, rfl⟩ hC
  by_contra hns
  have key : ∀ k : Fin (2 ^ l + 1), k = j ∨ k = j' → h k = β := by
    intro k hk
    funext b
    by_contra hb
    apply hns
    refine ⟨((k, b), !β b), ?_, ?_⟩
    · rcases hk with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
    · show h k b = !β b
      cases hh : h k b <;> cases hβ : β b <;> simp_all
  have hj := key j (Or.inl rfl)
  have hj' := key j' (Or.inr rfl)
  obtain ⟨hα, hpair⟩ := hinj j j' hjj (hj.trans hj'.symm)
  have hβ : β = α := hj.symm.trans hα
  subst hβ
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hC rfl
  · exact hC (bax_comm _ _ _)

/-- Every clause of the formula is a line of every refutation. -/
theorem bphp_axiom_in_refutation {l : ℕ} {π : List (LinClause (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsLinRefutation (BPHP (2 ^ l + 1) l) π) (i i' : Fin (2 ^ l + 1)) (hne : i ≠ i')
    (α : Fin l → Bool) : linOfClause (bax i i' α) ∈ π := by
  by_contra hA
  obtain ⟨a, ha⟩ := bphp_critical i i' hne α
  have hd := lin_derivation_diff _ hπ.1 hA
  have hax : ∀ C ∈ ((fun C => linOfClause C) '' BPHP (2 ^ l + 1) l) \ {linOfClause (bax i i' α)},
      LinClauseSat a C := by
    rintro _ ⟨⟨C, hC, rfl⟩, hCA⟩
    refine (linOfClause_sat a C).mpr (ha C hC ?_)
    rintro rfl
    exact hCA rfl
  obtain ⟨q, hq, -⟩ := lin_derivation_sound a hd hax ∅ hπ.2
  simp at hq

/-- The clause of a set `s` of pigeons and a hole `α`, as a linear clause. For a set of two
pigeons it is the matching clause of the formula. -/
def setClause (p : Finset (Fin m) × (Fin l → Bool)) : LinClause (Fin m × Fin l) :=
  (p.1 ×ˢ (Finset.univ : Finset (Fin l))).image
    (fun v => (({v} : Finset (Fin m × Fin l)), !p.2 v.2))

theorem setClause_pair (i i' : Fin m) (α : Fin l → Bool) :
    setClause (({i, i'} : Finset (Fin m)), α) = linOfClause (bax i i' α) := by
  ext ⟨f, c⟩
  simp only [setClause, linOfClause, bax, Finset.mem_image, Finset.mem_product,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, and_true, Finset.mem_union,
    Prod.mk.injEq, true_and]
  constructor
  · rintro ⟨⟨j, b⟩, hj, rfl, rfl⟩
    rcases hj with rfl | rfl
    · exact ⟨((j, b), !α b), Or.inl ⟨b, rfl⟩, rfl, rfl⟩
    · exact ⟨((j, b), !α b), Or.inr ⟨b, rfl⟩, rfl, rfl⟩
  · rintro ⟨lit, (⟨b, rfl⟩ | ⟨b, rfl⟩), rfl, rfl⟩
    · exact ⟨(i, b), Or.inl rfl, rfl, rfl⟩
    · exact ⟨(i', b), Or.inr rfl, rfl, rfl⟩

theorem mem_setClause {p : Finset (Fin m) × (Fin l → Bool)} {j : Fin m} {b : Fin l} {c : Bool} :
    (({(j, b)} : Finset (Fin m × Fin l)), c) ∈ setClause p ↔ j ∈ p.1 ∧ c = !p.2 b := by
  simp only [setClause, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true,
    Prod.mk.injEq, Finset.singleton_inj]
  constructor
  · rintro ⟨⟨j', b'⟩, hj, h1, rfl⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact ⟨hj, rfl⟩
  · rintro ⟨hj, rfl⟩
    exact ⟨(j, b), hj, rfl, rfl⟩

/-- Different pairs (nonempty set of pigeons, hole) give different clauses. -/
theorem setClause_inj (hl : 0 < l) {p p' : Finset (Fin m) × (Fin l → Bool)}
    (hp : p.1.Nonempty) (h : setClause p = setClause p') : p = p' := by
  have hmem : ∀ j b c, (j ∈ p.1 ∧ c = !p.2 b) ↔ (j ∈ p'.1 ∧ c = !p'.2 b) := by
    intro j b c
    rw [← mem_setClause, ← mem_setClause, h]
  have hs : p.1 = p'.1 := by
    ext j
    have := hmem j ⟨0, hl⟩
    constructor
    · intro hj
      exact ((this _).mp ⟨hj, rfl⟩).1
    · intro hj
      exact ((this _).mpr ⟨hj, rfl⟩).1
  obtain ⟨j, hj⟩ := hp
  have hα : p.2 = p'.2 := by
    funext b
    have := ((hmem j b _).mp ⟨hj, rfl⟩).2
    cases h1 : p.2 b <;> cases h2 : p'.2 b <;> simp_all
  exact Prod.ext hs hα

end Pigeons

/-- **The clause-counting bound.** Every Res(⊕) refutation of the bit pigeonhole formula with
`2 ^ l + 1` pigeons and `n = 2 ^ l` holes, `l ≥ 1`, has at least `n * (n + 1 choose 2) + 1`
lines: every clause of the formula, and the empty clause. -/
theorem bphp_size : ∀ (l : ℕ)
    (π : List (PEqualNP.ProofComplexity.LinClause (Fin (2 ^ l + 1) × Fin l))),
    0 < l →
    PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π →
    2 ^ l * (2 ^ l + 1).choose 2 + 1 ≤ π.length := by
  intro l π hl hπ
  classical
  let I : Finset (Finset (Fin (2 ^ l + 1)) × (Fin l → Bool)) :=
    (Finset.univ : Finset (Fin (2 ^ l + 1))).powersetCard 2 ×ˢ Finset.univ
  have hIcard : I.card = (2 ^ l + 1).choose 2 * 2 ^ l := by
    simp [I, Finset.card_product, Finset.card_powersetCard]
  have hinj : Set.InjOn setClause (I : Set (Finset (Fin (2 ^ l + 1)) × (Fin l → Bool))) := by
    intro p hp p' _ h
    have hp2 : p.1.card = 2 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
    exact setClause_inj hl (Finset.card_pos.mp (by omega)) h
  have hsub : I.image setClause ⊆ π.toFinset.erase ∅ := by
    intro C hC
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
    have hp2 : p.1.card = 2 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
    obtain ⟨i, i', hne, hs⟩ := Finset.card_eq_two.mp hp2
    have hpe : p = (({i, i'} : Finset (Fin (2 ^ l + 1))), p.2) := Prod.ext hs rfl
    rw [Finset.mem_erase, List.mem_toFinset]
    constructor
    · intro h0
      have : (({(i, (⟨0, hl⟩ : Fin l))} : Finset (Fin (2 ^ l + 1) × Fin l)), !p.2 ⟨0, hl⟩) ∈
          setClause p := mem_setClause.mpr ⟨by rw [hs]; simp, rfl⟩
      rw [h0] at this
      simp at this
    · rw [hpe, setClause_pair]
      exact bphp_axiom_in_refutation hπ i i' hne p.2
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, hIcard,
    Finset.card_erase_of_mem (List.mem_toFinset.mpr hπ.2)] at h1
  have h2 := List.toFinset_card_le π
  have h3 : 0 < π.toFinset.card := Finset.card_pos.mpr ⟨∅, List.mem_toFinset.mpr hπ.2⟩
  have h4 : 2 ^ l * (2 ^ l + 1).choose 2 = (2 ^ l + 1).choose 2 * 2 ^ l := Nat.mul_comm _ _
  omega

end PEqualNP.ProofComplexity.Helpers
