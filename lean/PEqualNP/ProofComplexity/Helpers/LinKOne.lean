import PEqualNP.Defs.ProofComplexityLinK
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
# Helpers: Res(1, ⊕) with termwise weakening is Res(⊕)

A linear clause goes up to the line of its one-equation terms; a line whose terms have at most
one equation goes down to the linear clause of its equations, except that a line holding the
empty term (which is true) goes down to the equation `0 = 0`. Each rule of one system maps to
one step of the other, so lengths are kept.
-/

namespace PEqualNP.ProofComplexity.Helpers.LinKOne

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- A linear clause as a line of one-equation terms. -/
def up (C : LinClause V) : LinKLine V := C.image (fun q => ({q} : LinTerm V))

theorem up_card (C : LinClause V) : ∀ T ∈ up C, T.card ≤ 1 := by
  intro T hT
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hT
  simp

theorem up_erase (C : LinClause V) (q : LinEq V) : up (C.erase q) = (up C).erase {q} :=
  Finset.image_erase Finset.singleton_injective C q

/-- A Res(⊕) derivation maps, line by line, to a Res(1, ⊕) derivation. -/
theorem forward {F : Set (LinClause V)} {π : List (LinClause V)} (h : IsLinDerivation F π) :
    IsLinKDerivation 1 IsLinKWeakening (up '' F) (π.map up) := by
  induction h with
  | nil => exact IsLinKDerivation.nil
  | ax _ hCF ih => exact IsLinKDerivation.ax ih ⟨_, hCF, rfl⟩ (up_card _)
  | @res π C D R _ hC hD hR ih =>
    obtain ⟨f, hfC, hfD, rfl⟩ := hR
    refine IsLinKDerivation.cut ih (List.mem_map_of_mem hC) (List.mem_map_of_mem hD)
      ⟨{(f, false)}, Finset.mem_image_of_mem _ hfC, ?_, ?_⟩ (up_card _)
    · intro e he
      rw [Finset.mem_singleton] at he
      subst he
      exact Finset.mem_image_of_mem _ hfD
    · rw [Finset.image_singleton, Finset.sdiff_singleton_eq_erase, ← up_erase, ← up_erase]
      exact Finset.image_union _ _
  | @weak π C D _ hC hw ih =>
    refine IsLinKDerivation.weak ih (List.mem_map_of_mem hC) ?_ (up_card _)
    intro T hT
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hT
    right
    intro a ha
    obtain ⟨q', hq', hs⟩ := hw a ⟨q, hq, ha q (Finset.mem_singleton_self q)⟩
    exact ⟨q', Finset.mem_image_of_mem _ hq', hs⟩

/-- A line as a linear clause: the equations of its terms, or `0 = 0` if it holds the empty
term. -/
def down (L : LinKLine V) : LinClause V :=
  if (∅ : LinTerm V) ∈ L then {((∅ : Finset V), false)} else L.biUnion id

theorem mem_biUnion_iff {L : LinKLine V} (hk : ∀ T ∈ L, T.card ≤ 1) (q : LinEq V) :
    q ∈ L.biUnion id ↔ ({q} : LinTerm V) ∈ L := by
  constructor
  · intro hq
    obtain ⟨T, hT, hqT⟩ := Finset.mem_biUnion.mp hq
    have hTq : T = {q} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hqT, fun x hx => Finset.card_le_one.mp (hk T hT) x hx q hqT⟩
    exact hTq ▸ hT
  · intro hq
    exact Finset.mem_biUnion.mpr ⟨{q}, hq, Finset.mem_singleton_self q⟩

/-- On lines whose terms have at most one equation, `down` keeps the meaning. -/
theorem down_sat (a : V → Bool) {L : LinKLine V} (hk : ∀ T ∈ L, T.card ≤ 1) :
    LinClauseSat a (down L) ↔ LinKLineSat a L := by
  unfold down
  split_ifs with h0
  · constructor
    · intro _
      exact ⟨∅, h0, fun q hq => absurd hq (Finset.notMem_empty q)⟩
    · intro _
      exact ⟨(∅, false), Finset.mem_singleton_self _, by simp [LinEqSat]⟩
  · constructor
    · rintro ⟨q, hq, hs⟩
      refine ⟨{q}, (mem_biUnion_iff hk q).mp hq, fun q' hq' => ?_⟩
      rw [Finset.mem_singleton.mp hq']
      exact hs
    · rintro ⟨T, hT, hs⟩
      have hne : T.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        exact h0 hT
      obtain ⟨q, hq⟩ := hne
      exact ⟨q, Finset.mem_biUnion.mpr ⟨T, hT, hq⟩, hs q hq⟩

theorem down_up (C : LinClause V) : down (up C) = C := by
  have h0 : (∅ : LinTerm V) ∉ up C := by
    intro h
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp h
    exact Finset.singleton_ne_empty q hq
  unfold down
  simp only [h0, ↓reduceIte]
  ext q
  rw [mem_biUnion_iff (up_card C)]
  exact ⟨fun h => by
    obtain ⟨q', hq', hqq⟩ := Finset.mem_image.mp h
    exact Finset.singleton_injective hqq ▸ hq', fun h => Finset.mem_image_of_mem _ h⟩

omit [DecidableEq V] in
theorem sat_mono {a : V → Bool} {L M : LinKLine V} (h : L ⊆ M) (hs : LinKLineSat a L) :
    LinKLineSat a M := by
  obtain ⟨T, hT, hTs⟩ := hs
  exact ⟨T, h hT, hTs⟩

omit [DecidableEq V] in
theorem weakening_sound {a : V → Bool} {L M : LinKLine V} (h : IsLinKWeakening L M)
    (hs : LinKLineSat a L) : LinKLineSat a M := by
  obtain ⟨T, hT, hTs⟩ := hs
  rcases h T hT with ⟨S, hS, himp⟩ | hb
  · exact ⟨S, hS, himp a hTs⟩
  · obtain ⟨q, hq, hqs⟩ := hb a hTs
    refine ⟨{q}, hq, fun q' hq' => ?_⟩
    rw [Finset.mem_singleton.mp hq']
    exact hqs

/-- Every term of every line of a derivation has at most `k` equations. -/
theorem lines_card {k : ℕ} {W : LinKLine V → LinKLine V → Prop} {F : Set (LinKLine V)}
    {π : List (LinKLine V)} (h : IsLinKDerivation k W F π) :
    ∀ L ∈ π, ∀ T ∈ L, T.card ≤ k := by
  induction h with
  | nil => intro L hL; simp at hL
  | ax _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | cut _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | andIntro _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | weak _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL

/-- A cut between lines of one-equation terms goes down to a resolution, in one of the two
orders, or to a semantic weakening of one premise. -/
theorem cut_down {C D R : LinKLine V} (hkC : ∀ T ∈ C, T.card ≤ 1) (hkD : ∀ T ∈ D, T.card ≤ 1)
    (hkR : ∀ T ∈ R, T.card ≤ 1) (hcut : IsLinKCut C D R) :
    IsLinResolvent (down C) (down D) (down R) ∨ IsLinResolvent (down D) (down C) (down R) ∨
      (∀ a : V → Bool, LinClauseSat a (down C) → LinClauseSat a (down R)) ∨
      (∀ a : V → Bool, LinClauseSat a (down D) → LinClauseSat a (down R)) := by
  obtain ⟨T, hT, hneg, hR⟩ := hcut
  by_cases hTe : T = ∅
  · subst hTe
    right; right; right
    intro a hs
    refine (down_sat a hkR).mpr (sat_mono ?_ ((down_sat a hkD).mp hs))
    rw [hR, Finset.image_empty, Finset.sdiff_empty]
    exact Finset.subset_union_right
  · obtain ⟨e, rfl⟩ : ∃ e, T = {e} :=
      Finset.card_eq_one.mp (le_antisymm (hkC T hT)
        (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hTe)))
    have hD : ({negLinEq e} : LinTerm V) ∈ D := hneg e (Finset.mem_singleton_self e)
    rw [Finset.image_singleton, Finset.sdiff_singleton_eq_erase] at hR
    by_cases h0 : (∅ : LinTerm V) ∈ C ∨ (∅ : LinTerm V) ∈ D
    · right; right; left
      intro a _
      refine (down_sat a hkR).mpr ⟨∅, ?_, fun q hq => absurd hq (Finset.notMem_empty q)⟩
      rw [hR]
      rcases h0 with h0 | h0
      · exact Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨(Finset.singleton_ne_empty e).symm, h0⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_erase.mpr ⟨(Finset.singleton_ne_empty _).symm, h0⟩)
    · have h0C : (∅ : LinTerm V) ∉ C := fun h => h0 (Or.inl h)
      have h0D : (∅ : LinTerm V) ∉ D := fun h => h0 (Or.inr h)
      have h0R : (∅ : LinTerm V) ∉ R := by
        rw [hR]
        intro h
        rcases Finset.mem_union.mp h with h | h
        · exact h0C (Finset.mem_of_mem_erase h)
        · exact h0D (Finset.mem_of_mem_erase h)
      have hdR : down R = (down C).erase e ∪ (down D).erase (negLinEq e) := by
        unfold down
        simp only [h0C, h0D, h0R, ↓reduceIte]
        ext q
        rw [mem_biUnion_iff hkR, Finset.mem_union, Finset.mem_erase, Finset.mem_erase,
          mem_biUnion_iff hkC, mem_biUnion_iff hkD, hR, Finset.mem_union, Finset.mem_erase,
          Finset.mem_erase, Ne, Ne, Finset.singleton_inj, Finset.singleton_inj]
      have heC : e ∈ down C := by
        unfold down
        simp only [h0C, ↓reduceIte]
        exact (mem_biUnion_iff hkC e).mpr hT
      have heD : negLinEq e ∈ down D := by
        unfold down
        simp only [h0D, ↓reduceIte]
        exact (mem_biUnion_iff hkD _).mpr hD
      rcases e with ⟨f, b⟩
      cases b
      · left
        exact ⟨f, heC, heD, hdR⟩
      · right; left
        exact ⟨f, heD, heC, hdR.trans (Finset.union_comm _ _)⟩

/-- And-introduction with the new term of at most one equation contains one of its premises. -/
theorem andIntro_superset {C D R : LinKLine V} (hkR : ∀ T ∈ R, T.card ≤ 1)
    (h : IsLinKAndIntro C D R) : C ⊆ R ∨ D ⊆ R := by
  obtain ⟨T₁, T₂, h1, h2, rfl⟩ := h
  have hcard : (T₁ ∪ T₂).card ≤ 1 :=
    hkR _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  by_cases hT₁ : T₁ = ∅
  · right
    intro T hT
    by_cases hTT : T = T₂
    · subst hTT
      refine Finset.mem_union_right _ (Finset.mem_singleton.mpr ?_)
      rw [hT₁, Finset.empty_union]
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hTT, hT⟩))
  · left
    have heq : T₁ = T₁ ∪ T₂ :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_left
        (hcard.trans (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT₁)))
    intro T hT
    by_cases hTT : T = T₁
    · subst hTT
      exact Finset.mem_union_right _ (Finset.mem_singleton.mpr heq)
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hTT, hT⟩))

/-- A Res(1, ⊕) derivation with termwise weakening maps, line by line, to a Res(⊕)
derivation. -/
theorem backward {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation 1 IsLinKWeakening F π) :
    IsLinDerivation (down '' F) (π.map down) := by
  induction h with
  | nil => exact IsLinDerivation.nil
  | ax _ hCF _ ih => exact IsLinDerivation.ax ih ⟨_, hCF, rfl⟩
  | @cut π C D R hπ hC hD hcut hk ih =>
    have hkC := lines_card hπ C hC
    have hkD := lines_card hπ D hD
    rcases cut_down hkC hkD hk hcut with h | h | h | h
    · exact IsLinDerivation.res ih (List.mem_map_of_mem hC) (List.mem_map_of_mem hD) h
    · exact IsLinDerivation.res ih (List.mem_map_of_mem hD) (List.mem_map_of_mem hC) h
    · exact IsLinDerivation.weak ih (List.mem_map_of_mem hC) h
    · exact IsLinDerivation.weak ih (List.mem_map_of_mem hD) h
  | @andIntro π C D R hπ hC hD hand hk ih =>
    have hkC := lines_card hπ C hC
    have hkD := lines_card hπ D hD
    rcases andIntro_superset hk hand with h | h
    · exact IsLinDerivation.weak ih (List.mem_map_of_mem hC)
        (fun a hs => (down_sat a hk).mpr (sat_mono h ((down_sat a hkC).mp hs)))
    · exact IsLinDerivation.weak ih (List.mem_map_of_mem hD)
        (fun a hs => (down_sat a hk).mpr (sat_mono h ((down_sat a hkD).mp hs)))
  | @weak π C D hπ hC hw hk ih =>
    have hkC := lines_card hπ C hC
    exact IsLinDerivation.weak ih (List.mem_map_of_mem hC)
      (fun a hs => (down_sat a hk).mpr (weakening_sound hw ((down_sat a hkC).mp hs)))

/-- Res(⊕) refutations and Res(1, ⊕) refutations with termwise weakening have the same
lengths. -/
theorem lin_iff_linK_one (F : Set (Clause V)) (n : ℕ) :
    (∃ π : List (LinClause V), IsLinRefutation F π ∧ π.length = n) ↔
      (∃ π : List (LinKLine V), IsLinKRefutation 1 F π ∧ π.length = n) := by
  constructor
  · rintro ⟨π, ⟨hd, he⟩, rfl⟩
    refine ⟨π.map up, ⟨?_, List.mem_map.mpr ⟨∅, he, rfl⟩⟩, List.length_map _⟩
    have h := forward hd
    rw [Set.image_image] at h
    exact h
  · rintro ⟨π, ⟨hd, he⟩, rfl⟩
    refine ⟨π.map down, ⟨?_, List.mem_map.mpr ⟨∅, he, by simp [down]⟩⟩, List.length_map _⟩
    have h := backward hd
    rw [Set.image_image] at h
    have hfun : (fun C : Clause V => down (linKOfClause C)) = fun C => linOfClause C :=
      funext fun C => down_up (linOfClause C)
    rw [hfun] at h
    exact h

end PEqualNP.ProofComplexity.Helpers.LinKOne
