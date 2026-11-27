import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_4081_642
    (stars : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ (C : Circuit) (T : Finset (Sym2 (Fin 11))) (K : Finset ℕ),
      let U := Ustar G C
      let J := junk G C
      let F := fun g => T ∩ gammaE G C g
      C.size ≤ 21 → IsLeastAO G C → TopForm G C → 3 ≤ J.card →
      T ⊆ U → K ⊆ J → T.card + J.card = U.card + K.card →
      (∀ e ∈ T, ∃ g ∈ K, e ∈ F g) → (∀ g ∈ K, (F g).card ≠ 1) →
      (∀ g ∈ K, ∃ v : Fin 11, ∀ e ∈ F g, v ∈ e) →
      T.card ≤ 2 * (centreless G C).card + K.card + (orN G C \ lam G C).card)
    (triangles : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ (C : Circuit) (T : Finset (Sym2 (Fin 11))) (K : Finset ℕ),
      let U := Ustar G C
      let J := junk G C
      let F := fun g => T ∩ gammaE G C g
      C.size ≤ 21 → IsLeastAO G C → TopForm G C → 3 ≤ J.card →
      T ⊆ U → K ⊆ J → T.card + J.card = U.card + K.card →
      (∀ e ∈ T, ∃ g ∈ K, e ∈ F g) → (∀ g ∈ K, (F g).card ≠ 1) →
      (∀ g ∈ K, ∀ e ∈ F g, ∀ f ∈ F g, ¬ Disjoint e.toFinset f.toFinset) →
      (∃ g ∈ K, (F g = {s(1,4),s(1,8),s(4,8)} ∨
        F g = {s(3,6),s(3,7),s(6,7)} ∨ F g = {s(5,8),s(5,9),s(8,9)})) →
      T.card ≤ 2 * (centreless G C).card + K.card + (orN G C \ lam G C).card)
    (separated : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ (C : Circuit) (T : Finset (Sym2 (Fin 11))) (K : Finset ℕ),
      let U := Ustar G C
      let J := junk G C
      let F := fun g => T ∩ gammaE G C g
      C.size ≤ 21 → IsLeastAO G C → TopForm G C → 3 ≤ J.card →
      T ⊆ U → K ⊆ J → T.card + J.card = U.card + K.card →
      (∀ e ∈ T, ∃ g ∈ K, e ∈ F g) → (∀ g ∈ K, (F g).card ≠ 1) →
      (∃ g ∈ K, ∃ e ∈ F g, ∃ f ∈ F g, Disjoint e.toFinset f.toFinset) →
      T.card ≤ 2 * (centreless G C).card + K.card + (orN G C \ lam G C).card)
    : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∀ (x7 x8 : Fin (11 : ℕ)), s(x7, x8) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x10 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x10 (PEqualNP.EdgeOwnership.pairInput x7 x8) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  classical
  intro _ C budget least top many coverage _ _
  let U := Ustar G C
  let J := junk G C
  let F (T : Finset (Sym2 (Fin 11))) (g : ℕ) := T ∩ gammaE G C g
  let feasible (T : Finset (Sym2 (Fin 11))) (K : Finset ℕ) :=
    T ⊆ U ∧ K ⊆ J ∧ T.card + J.card = U.card + K.card ∧ ∀ e ∈ T, ∃ g ∈ K, e ∈ F T g
  have full : feasible U J := by
    refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, rfl, ?_⟩
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨g,hg,lit⟩ := coverage a b he
      refine ⟨g,hg,Finset.mem_inter.mpr ⟨he,?_⟩⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1, a,b,rfl,lit⟩
  let sizes (k : ℕ) := ∃ T K, feasible T K ∧ T.card = k
  have ex : ∃ k, sizes k := ⟨U.card,U,J,full,rfl⟩
  obtain ⟨T,K,⟨subT,subK,balance,covered⟩,minimal⟩ := Nat.find_spec ex
  have noSingle (g : ℕ) (hg : g ∈ K) : (F T g).card ≠ 1 := by
    intro one
    obtain ⟨e,hs⟩ := Finset.card_eq_one.mp one
    have ef : e ∈ F T g := hs.symm ▸ Finset.mem_singleton_self _
    have he := (Finset.mem_inter.mp ef).1
    have next : feasible (T.erase e) (K.erase g) := by
      refine ⟨(Finset.erase_subset _ _).trans subT,(Finset.erase_subset _ _).trans subK,?_,?_⟩
      · have := Finset.card_erase_add_one he
        have := Finset.card_erase_add_one hg
        omega
      · intro f hf
        obtain ⟨notE,fT⟩ := Finset.mem_erase.mp hf
        obtain ⟨b,hb,fb⟩ := covered f fT
        have ne : b ≠ g := by
          rintro rfl
          rw [hs] at fb
          exact notE (Finset.mem_singleton.mp fb)
        exact ⟨b,Finset.mem_erase.mpr ⟨ne,hb⟩,Finset.mem_inter.mpr ⟨hf,(Finset.mem_inter.mp fb).2⟩⟩
    have smaller : Nat.find ex ≤ (T.erase e).card := Nat.find_min' ex ⟨_,_,next,rfl⟩
    have := Finset.card_erase_lt_of_mem he
    omega
  have classification (a b c : Fin 11) : a ≠ b → a ≠ c → b ≠ c →
      G.Adj a b → G.Adj a c → G.Adj b c →
      ({s(a,b),s(a,c),s(b,c)} : Finset (Sym2 (Fin 11))) = {s(1,4),s(1,8),s(4,8)} ∨
      ({s(a,b),s(a,c),s(b,c)} : Finset (Sym2 (Fin 11))) = {s(3,6),s(3,7),s(6,7)} ∨
      ({s(a,b),s(a,c),s(b,c)} : Finset (Sym2 (Fin 11))) = {s(5,8),s(5,9),s(8,9)} := by
    revert a b c
    decide +kernel
  have charge : T.card ≤ 2 * (centreless G C).card + K.card + (orN G C \ lam G C).card := by
    by_cases far : ∃ g ∈ K, ∃ e ∈ F T g, ∃ f ∈ F T g, Disjoint e.toFinset f.toFinset
    · exact separated C T K budget least top many subT subK balance covered noSingle far
    by_cases centred : ∀ g ∈ K, ∃ v : Fin 11, ∀ e ∈ F T g, v ∈ e
    · exact stars C T K budget least top many subT subK balance covered noSingle centred
    have missing : ∃ g ∈ K, ¬ ∃ v : Fin 11, ∀ e ∈ F T g, v ∈ e := by
      by_contra no
      apply centred
      intro g hg
      by_contra noCentre
      exact no ⟨g,hg,noCentre⟩
    obtain ⟨g,hg,noCentre⟩ := missing
    let X := F T g
    change ¬ ∃ v : Fin 11, ∀ e ∈ X, v ∈ e at noCentre
    have close : ∀ e ∈ X, ∀ f ∈ X, ¬ Disjoint e.toFinset f.toFinset :=
      fun e he f hf dis => far ⟨g,hg,e,he,f,hf,dis⟩
    have intersects {e f : Sym2 (Fin 11)} (he : e ∈ X) (hf : f ∈ X) : ∃ v, v ∈ e ∧ v ∈ f := by
      obtain ⟨v,ve,vf⟩ := Finset.not_disjoint_iff.mp (close e he f hf)
      exact ⟨v,Sym2.mem_toFinset.mp ve,Sym2.mem_toFinset.mp vf⟩
    have meet {a b : Fin 11} {h : Sym2 (Fin 11)} (hab : s(a,b) ∈ X) (hh : h ∈ X) :
        a ∈ h ∨ b ∈ h := by
      obtain ⟨v,hv,vh⟩ := intersects hab hh
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact Or.inl vh
      · exact Or.inr vh
    have misses (v : Fin 11) : ∃ f ∈ X, v ∉ f := by
      by_contra! covers
      exact noCentre ⟨v,covers⟩
    obtain ⟨e,he,_⟩ := misses 0
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨f,hf,na⟩ := misses a
      have bf := (meet he hf).resolve_left na
      obtain ⟨c,hfeq⟩ := Sym2.mem_iff_exists.mp bf
      subst f
      have ac : a ≠ c := fun h => na (h ▸ Sym2.mem_mk_right _ _)
      have ab : a ≠ b := fun h => na (h ▸ Sym2.mem_mk_left _ _)
      obtain ⟨d,hd,nb⟩ := misses b
      have ad := (meet he hd).resolve_right nb
      have cd := (meet hf hd).resolve_left nb
      have bc : b ≠ c := fun h => nb (h ▸ cd)
      have deq := (Sym2.mem_and_mem_iff ac).mp ⟨ad,cd⟩
      subst d
      have inGraph {ed : Sym2 (Fin 11)} (hed : ed ∈ X) : ed ∈ G.edgeFinset :=
        (Finset.mem_sdiff.mp (subT (Finset.mem_inter.mp hed).1)).1
      have hab : G.Adj a b := by simpa using inGraph he
      have hac : G.Adj a c := by simpa using inGraph hd
      have hbc : G.Adj b c := by simpa using inGraph hf
      have allThree : ({s(a,b),s(a,c),s(b,c)} : Finset (Sym2 (Fin 11))) ⊆ X := by
        intro ed hed
        simp only [Finset.mem_insert,Finset.mem_singleton] at hed
        rcases hed with rfl | rfl | rfl
        · exact he
        · exact hd
        · exact hf
      have sub : X ⊆ {s(a,b),s(a,c),s(b,c)} := by
        intro ed hed
        simp only [Finset.mem_insert,Finset.mem_singleton]
        by_cases ah : a ∈ ed
        · by_cases bh : b ∈ ed
          · exact Or.inl ((Sym2.mem_and_mem_iff ab).mp ⟨ah,bh⟩)
          · exact Or.inr (Or.inl ((Sym2.mem_and_mem_iff ac).mp ⟨ah,(meet hf hed).resolve_left bh⟩))
        · exact Or.inr (Or.inr ((Sym2.mem_and_mem_iff bc).mp
            ⟨(meet he hed).resolve_left ah,(meet hd hed).resolve_left ah⟩))
      have eq : X = {s(a,b),s(a,c),s(b,c)} := Finset.Subset.antisymm sub allThree
      apply triangles C T K budget least top many subT subK balance covered noSingle
        (fun g hg e he f hf dis => far ⟨g,hg,e,he,f,hf,dis⟩)
      refine ⟨g,hg,?_⟩
      rcases classification a b c ab ac bc hab hac hbc with h | h | h
      · exact Or.inl (eq.trans h)
      · exact Or.inr (Or.inl (eq.trans h))
      · exact Or.inr (Or.inr (eq.trans h))
  change U.card ≤ 2 * (centreless G C).card + J.card + (orN G C \ lam G C).card
  omega
