import PEqualNP.ProofComplexity.Helpers.Lin

/-!
# Helpers: the list-based Res(lin) of `Defs/Search.lean` inside the finite-set Res(⊕)

Each list line becomes its finite set of equations. A list resolvent `C ++ D` is a weakening
of the finite-set resolvent, so one line costs at most two.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

theorem holds_iff_linEqSat {n : ℕ} (a : Fin n → Bool) (e : PEqualNP.Search.LinEq n) :
    PEqualNP.Search.LinEq.Holds a e ↔ LinEqSat a e := by
  unfold PEqualNP.Search.LinEq.Holds LinEqSat
  rw [Nat.odd_iff]

theorem holds_iff_linClauseSat {n : ℕ} (a : Fin n → Bool) (C : PEqualNP.Search.LinClause n) :
    PEqualNP.Search.LinClause.Holds a C ↔ LinClauseSat a C.toFinset := by
  constructor
  · rintro ⟨e, he, h⟩
    exact ⟨e, List.mem_toFinset.mpr he, (holds_iff_linEqSat a e).mp h⟩
  · rintro ⟨e, he, h⟩
    exact ⟨e, List.mem_toFinset.mp he, (holds_iff_linEqSat a e).mpr h⟩

theorem linSat_mono {V : Type} (a : V → Bool) {C D : LinClause V} (h : C ⊆ D)
    (hC : LinClauseSat a C) : LinClauseSat a D := by
  obtain ⟨q, hq, hs⟩ := hC
  exact ⟨q, h hq, hs⟩

theorem bridge_derivation {n : ℕ} {F : Set (Clause (Fin n))}
    {π : List (PEqualNP.Search.LinClause n)} (h : PEqualNP.Search.IsResLinDerivation F π) :
    ∃ π' : List (LinClause (Fin n)),
      IsLinDerivation ((fun C => linOfClause C) '' F) π' ∧ π'.length ≤ 2 * π.length ∧
        ∀ L ∈ π, L.toFinset ∈ π' := by
  induction h with
  | nil => exact ⟨[], IsLinDerivation.nil, by simp, by simp⟩
  | @ax π L C _ hC hL ih =>
    obtain ⟨π', hπ', hlen, hmem⟩ := ih
    have hLC : L.toFinset = linOfClause C := by
      ext e
      rw [List.mem_toFinset, hL e]
      unfold linOfClause
      rw [Finset.mem_image]
      constructor
      · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
      · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
    refine ⟨L.toFinset :: π', IsLinDerivation.ax hπ' ⟨C, hC, hLC.symm⟩, ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hmem M hM)
  | @res π e e' C D _ hC hD hvars hrhs ih =>
    obtain ⟨π', hπ', hlen, hmem⟩ := ih
    have hA := hmem _ hC
    have hB := hmem _ hD
    -- the finite-set resolvent, with the premise holding `f = 0` first
    have hres : ∃ R : LinClause (Fin n), (∃ X ∈ π', ∃ Y ∈ π', IsLinResolvent X Y R) ∧
        R ⊆ (C ++ D).toFinset := by
      obtain ⟨f, b⟩ := e
      obtain ⟨f', b'⟩ := e'
      simp only at hvars hrhs
      subst hvars
      have sub1 : ∀ q : LinEq (Fin n),
          ((q :: C).toFinset).erase q ⊆ (C ++ D).toFinset := by
        intro q x hx
        obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
        rcases List.mem_cons.mp (List.mem_toFinset.mp hx) with h | h
        · exact absurd h hne
        · exact List.mem_toFinset.mpr (List.mem_append_left _ h)
      have sub2 : ∀ q : LinEq (Fin n),
          ((q :: D).toFinset).erase q ⊆ (C ++ D).toFinset := by
        intro q x hx
        obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
        rcases List.mem_cons.mp (List.mem_toFinset.mp hx) with h | h
        · exact absurd h hne
        · exact List.mem_toFinset.mpr (List.mem_append_right _ h)
      cases b <;> cases b' <;> simp only [ne_eq, not_true_eq_false, reduceCtorEq,
        not_false_eq_true] at hrhs
      · exact ⟨_, ⟨_, hA, _, hB, f, by simp, by simp, rfl⟩,
          Finset.union_subset (sub1 _) (sub2 _)⟩
      · exact ⟨_, ⟨_, hB, _, hA, f, by simp, by simp, rfl⟩,
          Finset.union_subset (sub2 _) (sub1 _)⟩
    obtain ⟨R, ⟨X, hX, Y, hY, hR⟩, hsub⟩ := hres
    refine ⟨(C ++ D).toFinset :: R :: π', ?_, ?_, ?_⟩
    · exact IsLinDerivation.weak (IsLinDerivation.res hπ' hX hY hR) List.mem_cons_self
        (fun a => linSat_mono a hsub)
    · simp only [List.length_cons]; omega
    · intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem M hM))
  | @weaken π C D _ hC hw ih =>
    obtain ⟨π', hπ', hlen, hmem⟩ := ih
    refine ⟨D.toFinset :: π', IsLinDerivation.weak hπ' (hmem C hC) ?_, ?_, ?_⟩
    · intro a ha
      exact (holds_iff_linClauseSat a D).mp (hw a ((holds_iff_linClauseSat a C).mpr ha))
    · simp only [List.length_cons]; omega
    · intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hmem M hM)

end PEqualNP.ProofComplexity.Helpers
