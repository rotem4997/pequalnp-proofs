import PEqualNP.ProofComplexity.Helpers.Restrict
import PEqualNP.Defs.Expanders

/-!
# Helpers: re-typing a Res(⊕) refutation of the pigeonhole formula to the edges of a graph

Every equation over the variables `Fin m × Fin N` is pulled back to the edge variables of a
bipartite graph `G` by dropping the non-edge variables from its support (that is, substituting
false for them). An assignment of the edge variables extends by false to all variables, and the
pulled back equation holds under an assignment exactly when the original holds under its
extension. A Res(⊕) derivation from `PHP m N` maps line by line, at most two new lines per old
line, to a Res(⊕) derivation from `graphPHP G`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity PEqualNP.Expanders

/-- An assignment of the edge variables, extended by false to all variables. -/
def rtExt {m N : ℕ} (G : BipGraph m N) (a : GEdge G → Bool) : Fin m × Fin N → Bool :=
  fun v => if h : v.2 ∈ G v.1 then a ⟨v, h⟩ else false

/-- An equation pulled back to the edge variables: the non-edge variables leave the support. -/
def rtEq {m N : ℕ} (G : BipGraph m N) (q : LinEq (Fin m × Fin N)) : LinEq (GEdge G) :=
  (q.1.subtype (fun e => e.2 ∈ G e.1), q.2)

/-- A linear clause pulled back to the edge variables. -/
def rtLin {m N : ℕ} (G : BipGraph m N) (C : LinClause (Fin m × Fin N)) : LinClause (GEdge G) :=
  C.image (rtEq G)

theorem rtEq_sat {m N : ℕ} (G : BipGraph m N) (a : GEdge G → Bool) (q : LinEq (Fin m × Fin N)) :
    LinEqSat a (rtEq G q) ↔ LinEqSat (rtExt G a) q := by
  have hmap : ((q.1.subtype (fun e => e.2 ∈ G e.1)).filter (fun e => a e = true)).map
      (Function.Embedding.subtype _) = q.1.filter (fun v => rtExt G a v = true) := by
    ext v
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_subtype,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨e, ⟨he, hae⟩, rfl⟩
      exact ⟨he, by simp [rtExt, e.2, hae]⟩
    · rintro ⟨hv, hav⟩
      by_cases h : v.2 ∈ G v.1
      · exact ⟨⟨v, h⟩, ⟨hv, by simpa [rtExt, h] using hav⟩, rfl⟩
      · simp [rtExt, h] at hav
  unfold LinEqSat rtEq
  dsimp only
  rw [← hmap, Finset.card_map]

theorem rtLin_sat {m N : ℕ} (G : BipGraph m N) (a : GEdge G → Bool)
    (C : LinClause (Fin m × Fin N)) :
    LinClauseSat a (rtLin G C) ↔ LinClauseSat (rtExt G a) C := by
  constructor
  · rintro ⟨q', hq', hs⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
    exact ⟨q, hq, (rtEq_sat G a q).mp hs⟩
  · rintro ⟨q, hq, hs⟩
    exact ⟨rtEq G q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, (rtEq_sat G a q).mpr hs⟩

/-- Every clause of `PHP m N`, read under the extension by false, follows from one clause of
`graphPHP G`. -/
theorem rt_axiom {m N : ℕ} (G : BipGraph m N) :
    ∀ C ∈ PHP m N, ∃ B ∈ graphPHP G, ∀ a : GEdge G → Bool,
      ClauseSat a B → ClauseSat (rtExt G a) C := by
  rintro C (⟨i, rfl⟩ | ⟨i, i', j, hne, rfl⟩)
  · refine ⟨_, Or.inl ⟨i, rfl⟩, ?_⟩
    rintro a ⟨l, hl, hal⟩
    obtain ⟨-, rfl, hl2⟩ := Finset.mem_filter.mp hl
    refine ⟨((l.1.1.1, l.1.1.2), true),
      Finset.mem_image.mpr ⟨l.1.1.2, Finset.mem_univ _, rfl⟩, ?_⟩
    have h2 : rtExt G a l.1.1 = a l.1 := by simp [rtExt, l.1.2]
    show rtExt G a l.1.1 = true
    rw [h2, hal, hl2]
  · by_cases h : j ∈ G i ∧ j ∈ G i'
    · refine ⟨{((⟨(i, j), h.1⟩ : GEdge G), false), ((⟨(i', j), h.2⟩ : GEdge G), false)},
        Or.inr ⟨⟨(i, j), h.1⟩, ⟨(i', j), h.2⟩, rfl, hne, rfl⟩, ?_⟩
      rintro a ⟨l, hl, hal⟩
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact ⟨((i, j), false), by simp, by simpa [rtExt, h.1] using hal⟩
      · rw [Finset.mem_singleton] at hl
        subst hl
        exact ⟨((i', j), false), by simp, by simpa [rtExt, h.2] using hal⟩
    · refine ⟨_, Or.inl ⟨i, rfl⟩, fun a _ => ?_⟩
      by_cases h1 : j ∈ G i
      · have h2 : j ∉ G i' := fun h2 => h ⟨h1, h2⟩
        exact ⟨((i', j), false), by simp, by simp [rtExt, h2]⟩
      · exact ⟨((i, j), false), by simp, by simp [rtExt, h1]⟩

/-- The line-by-line simulation. -/
theorem rt_derivation {m N : ℕ} (G : BipGraph m N) {π : List (LinClause (Fin m × Fin N))}
    (h : IsLinDerivation ((fun C => linOfClause C) '' PHP m N) π) :
    ∃ π' : List (LinClause (GEdge G)),
      IsLinDerivation ((fun C => linOfClause C) '' graphPHP G) π' ∧
      π'.length ≤ 2 * π.length ∧ ∀ L ∈ π, rtLin G L ∈ π' := by
  induction h with
  | nil => exact ⟨[], IsLinDerivation.nil, by simp, by simp⟩
  | @ax π L hπ hL ih =>
    obtain ⟨π', hd, hlen, hmem⟩ := ih
    obtain ⟨C, hC, rfl⟩ := hL
    obtain ⟨B, hB, himp⟩ := rt_axiom G C hC
    refine ⟨rtLin G (linOfClause C) :: linOfClause B :: π', ?_, ?_, ?_⟩
    · refine IsLinDerivation.weak (IsLinDerivation.ax hd ⟨B, hB, rfl⟩)
        List.mem_cons_self (fun a ha => ?_)
      rw [rtLin_sat, linOfClause_sat]
      rw [linOfClause_sat] at ha
      exact himp a ha
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
    have h0 : rtEq G (f, false) ∈ rtLin G C := Finset.mem_image_of_mem _ hfC
    have h1 : rtEq G (f, true) ∈ rtLin G D := Finset.mem_image_of_mem _ hfD
    have hsub : (rtLin G C).erase (rtEq G (f, false)) ∪
        (rtLin G D).erase (rtEq G (f, true)) ⊆
          rtLin G (C.erase (f, false) ∪ D.erase (f, true)) := by
      unfold rtLin
      rw [Finset.image_union]
      exact Finset.union_subset_union (rst_erase_image_subset _ _ _)
        (rst_erase_image_subset _ _ _)
    refine ⟨rtLin G (C.erase (f, false) ∪ D.erase (f, true)) ::
      ((rtLin G C).erase (rtEq G (f, false)) ∪ (rtLin G D).erase (rtEq G (f, true))) :: π',
      ?_, ?_, ?_⟩
    · exact IsLinDerivation.weak
        (IsLinDerivation.res hd hTC hTD ⟨f.subtype (fun e => e.2 ∈ G e.1), h0, h1, rfl⟩)
        List.mem_cons_self (rst_weak_of_subset hsub)
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem L hL))
  | @weak π C D hπ hC hw ih =>
    obtain ⟨π', hd, hlen, hmem⟩ := ih
    refine ⟨rtLin G D :: π', ?_, ?_, ?_⟩
    · refine IsLinDerivation.weak hd (hmem C hC) (fun a ha => ?_)
      rw [rtLin_sat] at ha ⊢
      exact hw _ ha
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hmem L hL)

theorem rt_refutation {m N : ℕ} (G : BipGraph m N) (π : List (LinClause (Fin m × Fin N)))
    (h : IsLinRefutation (PHP m N) π) :
    ∃ π' : List (LinClause (GEdge G)), IsLinRefutation (graphPHP G) π' ∧
      π'.length ≤ 2 * π.length := by
  obtain ⟨π', hd, hlen, hmem⟩ := rt_derivation G h.1
  refine ⟨π', ⟨hd, ?_⟩, hlen⟩
  have := hmem ∅ h.2
  simpa [rtLin] using this

end PEqualNP.ProofComplexity.Helpers
