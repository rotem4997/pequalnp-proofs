import PEqualNP.Defs

-- Adapted from the merged Apache-2.0 proof of `L_pcx_148` (`PHP 4 3` resolution lower bound)
-- in `open-goat/pequalnp-proofs`, generalized from `PHP 4 3` to `PHP 5 4` (`45 + 40 + 16 = 101 > 99`).

namespace PEqualNP.Outside.L_pcx_160_aux

open PEqualNP.ProofComplexity

abbrev Row := Fin 5
abbrev Hole := Fin 4
abbrev V := Row × Hole
abbrev C := Clause V

def rowAx (i : Row) (J : Finset Hole) : C := J.image (fun j => ((i, j), true))

def colAx (i k : Row) (j : Hole) : C := {((i, j), false), ((k, j), false)}

def Collision (I : Finset Row) (J : Finset Hole) (N : C) : Prop :=
  ∃ i ∈ I, ∃ k ∈ I, ∃ j ∈ J, i ≠ k ∧ N = colAx i k j

abbrev Coll (N : C) : Prop := Collision Finset.univ Finset.univ N

def NegsIn (S : Finset V) (R : C) : Prop :=
  ∀ v : V, (v, false) ∈ R → v ∈ S

def Hits (S : Finset V) (R : C) : Prop :=
  ∃ v : V, (v, false) ∈ R ∧ v ∈ S

def SatOn (a : V → Bool) (A : Finset C) : Prop :=
  ∀ R ∈ A, R ∈ PHP 5 4 → ClauseSat a R

def Absorbs (π : List C) (A : Finset C) : Prop :=
  ∀ a : V → Bool, SatOn a A → ∀ R ∈ π, ClauseSat a R

def Controls (π : List C) (U : Finset C) (S : Finset V) : Prop :=
  ∀ (U' : Finset C) (S' : Finset V), U ⊆ U' → S ⊆ S' →
  ∀ a : V → Bool, (∀ B ∈ PHP 5 4, ¬ Coll B → ClauseSat a B) →
    (∀ B ∈ U', Coll B → Hits S' B → ClauseSat a B) →
    ∀ R ∈ π, ¬ Coll R → NegsIn S' R → ClauseSat a R

theorem satResolve {a : V → Bool} {P N R : C} {v : V}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false))
    (hP : ClauseSat a P) (hN : ClauseSat a N) : ClauseSat a R := by
  obtain ⟨p, hp, hpa⟩ := hP
  by_cases h : p = (v, true)
  · subst p
    obtain ⟨n, hn, hna⟩ := hN
    have hn' : n ≠ (v, false) := by
      intro e
      subst n
      change a v = false at hna
      change a v = true at hpa
      simp [hpa] at hna
    refine ⟨n, ?_, hna⟩
    rw [hR]
    exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hn', hn⟩)
  · refine ⟨p, ?_, hpa⟩
    rw [hR]
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hp⟩)

theorem collisionNoPos {N : C} (hN : Coll N) (v : V) : (v, true) ∉ N := by
  obtain ⟨i, _, k, _, j, _, _, rfl⟩ := hN
  simp [colAx]

theorem collisionOther {N : C} {v : V} (hN : Coll N) (hv : (v, false) ∈ N) :
    ∃ u : V, u ≠ v ∧ (u, false) ∈ N := by
  obtain ⟨i, _, k, _, j, _, hik, rfl⟩ := hN
  have hv' : v = (i, j) ∨ v = (k, j) := by simpa [colAx] using hv
  rcases hv' with rfl | rfl
  · exact ⟨(k, j), fun e => hik (congrArg Prod.fst e).symm, by simp [colAx]⟩
  · exact ⟨(i, j), fun e => hik (congrArg Prod.fst e), by simp [colAx]⟩

theorem collisionNonempty {N : C} (hN : Coll N) : N ≠ ∅ := by
  obtain ⟨i, _, k, _, j, _, _, rfl⟩ := hN
  simp [colAx]

theorem negLeft {v : V} {P N R : C}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false)) {u : V} (hu : (u, false) ∈ P) :
    (u, false) ∈ R := by
  rw [hR]
  exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, hu⟩)

theorem negRight {v : V} {P N R : C}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false)) {u : V} (hu : (u, false) ∈ N)
    (hne : u ≠ v) : (u, false) ∈ R := by
  rw [hR]
  exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simpa using hne, hu⟩)

theorem controlStep {π : List C} {U : Finset C} {S : Finset V} {v : V} {P N R : C}
    (h : Controls π U S) (hP : P ∈ π) (hN : N ∈ π)
    (hp : (v, true) ∈ P) (hn : (v, false) ∈ N)
    (hR : R = P.erase (v, true) ∪ N.erase (v, false)) :
    ∀ (U' : Finset C) (S' : Finset V), U ⊆ U' → S ⊆ S' →
    (Coll N → N ∈ U') → (¬ Coll N → v ∈ S') →
    ∀ a : V → Bool, (∀ B ∈ PHP 5 4, ¬ Coll B → ClauseSat a B) →
      (∀ B ∈ U', Coll B → Hits S' B → ClauseSat a B) →
      ∀ Q ∈ R :: π, ¬ Coll Q → NegsIn S' Q → ClauseSat a Q := by
  classical
  intro U' S' hU hS hmark hpivot a hrows hcols Q hQ hnQ hneg
  have ih := h U' S' hU hS a hrows hcols
  rcases List.mem_cons.mp hQ with rfl | hQ
  · have sP : ClauseSat a P :=
      ih P hP (fun hcol => collisionNoPos hcol v hp) (fun u hu => hneg u (negLeft hR hu))
    have sN : ClauseSat a N := by
      by_cases hcol : Coll N
      · obtain ⟨u, huv, hu⟩ := collisionOther hcol hn
        exact hcols N (hmark hcol) hcol ⟨u, hu, hneg u (negRight hR hu huv)⟩
      · refine ih N hN hcol (fun u hu => ?_)
        by_cases hu' : u = v
        · simpa [hu'] using hpivot hcol
        · exact hneg u (negRight hR hu hu')
    exact satResolve hR sP sN
  · exact ih Q hQ hnQ hneg

theorem collect {π : List C} (h : IsDerivation (PHP 5 4) π) :
    ∃ (A U : Finset C) (S : Finset V), A.card + U.card + S.card ≤ π.length ∧
      Absorbs π A ∧ Controls π U S := by
  classical
  induction h with
  | nil =>
    refine ⟨∅, ∅, ∅, by simp, ?_, ?_⟩
    · simp [Absorbs]
    · simp [Controls]
  | @ax π R _ hR ih =>
    obtain ⟨A, U, S, hbudget, hs, hc⟩ := ih
    refine ⟨insert R A, U, S, ?_, ?_, ?_⟩
    · have := Finset.card_insert_le R A
      simp only [List.length_cons]
      omega
    · intro a ha Q hQ
      rcases List.mem_cons.mp hQ with hEq | hQ
      · subst Q
        exact ha R (Finset.mem_insert_self _ _) hR
      · exact hs a (fun B hB hB' => ha B (Finset.mem_insert_of_mem hB) hB') Q hQ
    · intro U' S' hU hS a hrows hcols Q hQ hnc hneg
      rcases List.mem_cons.mp hQ with hEq | hQ
      · subst Q
        exact hrows R hR hnc
      · exact hc U' S' hU hS a hrows hcols Q hQ hnc hneg
  | @res π P N R _ hP hN hR ih =>
    obtain ⟨v, hp, hn, heq⟩ := hR
    obtain ⟨A, U, S, hbudget, hs, hc⟩ := ih
    have ha : Absorbs (R :: π) A := by
      intro a hA Q hQ
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact satResolve heq (hs a hA P hP) (hs a hA N hN)
      · exact hs a hA Q hQ
    have hstep := controlStep hc hP hN hp hn heq
    by_cases hm : Coll N
    · refine ⟨A, insert N U, S, ?_, ha, ?_⟩
      · have := Finset.card_insert_le N U
        simp only [List.length_cons]
        omega
      · intro U' S' hU hS
        exact hstep U' S' ((Finset.subset_insert N U).trans hU) hS
          (fun _ => hU (Finset.mem_insert_self _ _)) (fun h => (h hm).elim)
    · refine ⟨A, U, insert v S, ?_, ha, ?_⟩
      · have := Finset.card_insert_le v S
        simp only [List.length_cons]
        omega
      · intro U' S' hU hS
        exact hstep U' S' hU ((Finset.subset_insert v S).trans hS)
          (fun h => (hm h).elim) (fun _ => hS (Finset.mem_insert_self _ _))

theorem coverSize (S : Finset V)
    (hS : ∀ B : C, Coll B → Hits S B) : 16 ≤ S.card := by
  have hle : (Sᶜ).card ≤ (Finset.univ : Finset Hole).card := by
    apply Finset.card_le_card_of_injOn Prod.snd (fun _ _ => Finset.mem_univ _)
    intro v hv w hw hej
    have hv' : v ∉ S := Finset.mem_compl.mp (Finset.mem_coe.mp hv)
    have hw' : w ∉ S := Finset.mem_compl.mp (Finset.mem_coe.mp hw)
    by_contra hne
    have hij : v.1 ≠ w.1 := fun h => hne (Prod.ext h hej)
    have hB : Coll (colAx v.1 w.1 v.2) :=
      ⟨v.1, Finset.mem_univ _, w.1, Finset.mem_univ _, v.2, Finset.mem_univ _, hij, rfl⟩
    obtain ⟨u, hu, huS⟩ := hS _ hB
    have hu' : u = (v.1, v.2) ∨ u = (w.1, v.2) := by simpa [colAx] using hu
    rcases hu' with h | h
    · have heq : u = v := h.trans (Prod.eta v)
      exact hv' (heq ▸ huS)
    · have heq : u = w := h.trans (Prod.ext rfl hej)
      exact hw' (heq ▸ huS)
  have hsum := Finset.card_add_card_compl S
  have hV : Fintype.card V = 20 := by decide +kernel
  have hH : (Finset.univ : Finset Hole).card = 4 := by decide +kernel
  omega

theorem collisionPHP {B : C} (hB : Coll B) : B ∈ PHP 5 4 := by
  obtain ⟨i, _, k, _, j, _, hik, rfl⟩ := hB
  exact Or.inr ⟨i, k, j, hik, rfl⟩

theorem emptyUnsat (a : V → Bool) : ¬ ClauseSat a (∅ : C) := by
  rintro ⟨l, hl, _⟩
  simp at hl

private theorem indispensableMatching {B : Finset Row} {K : Finset Hole}
    (h : B.card = K.card) : ∃ a : V → Bool,
    (∀ r ∈ B, ∃ j ∈ K, a (r, j) = true) ∧
    (∀ {r j}, a (r, j) = true → r ∈ B ∧ j ∈ K) ∧
    (∀ {r s j}, a (r, j) = true → a (s, j) = true → r = s) := by
  let e : ↥B ≃ ↥K := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using h)
  let a : V → Bool := fun w =>
    if hr : w.1 ∈ B then decide ((e ⟨w.1, hr⟩ : Hole) = w.2) else false
  have ha (r : Row) (j : Hole) : a (r, j) = true ↔
      ∃ hr : r ∈ B, (e ⟨r, hr⟩ : Hole) = j := by
    by_cases hr : r ∈ B
    · have he : a (r, j) = true ↔ (e ⟨r, hr⟩ : Hole) = j := by simp [a, hr]
      exact he.trans ⟨fun h' => ⟨hr, h'⟩, fun ⟨_, h'⟩ => h'⟩
    · simp [a, hr]
  refine ⟨a, ?_, ?_, ?_⟩
  · intro r hr
    exact ⟨e ⟨r, hr⟩, (e ⟨r, hr⟩).property, (ha r _).2 ⟨hr, rfl⟩⟩
  · intro r j ht
    obtain ⟨hr, hj⟩ := (ha r j).1 ht
    exact ⟨hr, hj ▸ (e ⟨r, hr⟩).property⟩
  · intro r s j hr hs
    obtain ⟨hrB, hrj⟩ := (ha r j).1 hr
    obtain ⟨hsB, hsj⟩ := (ha s j).1 hs
    have he : e ⟨r, hrB⟩ = e ⟨s, hsB⟩ := Subtype.ext (hrj.trans hsj.symm)
    exact congrArg Subtype.val (e.injective he)

private theorem indispensableSatRow {a : V → Bool} {J : Finset Hole} {r : Row} {j : Hole}
    (hj : j ∈ J) (h : a (r, j) = true) : ClauseSat a (rowAx r J) :=
  ⟨((r, j), true), Finset.mem_image.mpr ⟨j, hj, rfl⟩, h⟩

private theorem indispensableSatCol {a : V → Bool} {r s : Row} {j : Hole}
    (h : ¬ (a (r, j) = true ∧ a (s, j) = true)) : ClauseSat a (colAx r s j) := by
  by_cases hr : a (r, j) = true
  · by_cases hs : a (s, j) = true
    · exact (h ⟨hr, hs⟩).elim
    · exact ⟨((s, j), false), by simp [colAx], Bool.eq_false_iff.mpr hs⟩
  · exact ⟨((r, j), false), by simp [colAx], Bool.eq_false_iff.mpr hr⟩

private theorem indispensablePHP {B : C} : B ∈ PHP 5 4 ↔
    (∃ r : Row, B = rowAx r Finset.univ) ∨ Collision Finset.univ Finset.univ B := by
  change ((∃ r : Row, B = rowAx r Finset.univ) ∨
    (∃ i k : Row, ∃ j : Hole, i ≠ k ∧ B = colAx i k j)) ↔ _
  constructor
  · rintro (hr | ⟨i, k, j, hik, he⟩)
    · exact Or.inl hr
    · exact Or.inr ⟨i, Finset.mem_univ _, k, Finset.mem_univ _, j, Finset.mem_univ _, hik, he⟩
  · rintro (hr | ⟨i, _, k, _, j, _, hik, he⟩)
    · exact Or.inl hr
    · exact Or.inr ⟨i, k, j, hik, he⟩

private theorem indispensableRowModel (i : Row) :
    ∃ a : V → Bool, ¬ ClauseSat a (rowAx i Finset.univ) ∧
      ∀ R ∈ PHP 5 4, R ≠ rowAx i Finset.univ → ClauseSat a R := by
  have hc : ((Finset.univ : Finset Row).erase i).card = (Finset.univ : Finset Hole).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; decide +kernel
  obtain ⟨a, hrow, hmem, hinj⟩ := indispensableMatching hc
  refine ⟨a, ?_, ?_⟩
  · rintro ⟨l, hl, hal⟩
    change l ∈ (Finset.univ : Finset Hole).image (fun j => ((i, j), true)) at hl
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    exact Finset.notMem_erase i Finset.univ (hmem hal).1
  · intro R hR hne
    rcases indispensablePHP.mp hR with ⟨r, rfl⟩ | ⟨r, _, s, _, j, _, hrs, rfl⟩
    · have hri : r ≠ i := fun he => hne (congrArg (fun r => rowAx r Finset.univ) he)
      obtain ⟨j, hj, haj⟩ := hrow r (Finset.mem_erase.mpr ⟨hri, Finset.mem_univ _⟩)
      exact indispensableSatRow hj haj
    · exact indispensableSatCol (fun ⟨hr, hs⟩ => hrs (hinj hr hs))

private theorem indispensableColModel {i k : Row} (j : Hole) (hik : i ≠ k) :
    ∃ a : V → Bool, ¬ ClauseSat a (colAx i k j) ∧
      ∀ R ∈ PHP 5 4, R ≠ colAx i k j → ClauseSat a R := by
  have hkm : k ∈ (Finset.univ : Finset Row).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ _⟩
  have hc : (((Finset.univ : Finset Row).erase i).erase k).card =
      ((Finset.univ : Finset Hole).erase j).card := by
    rw [Finset.card_erase_of_mem hkm, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_erase_of_mem (Finset.mem_univ j)]; decide +kernel
  obtain ⟨b, hbrow, hbmem, hbinj⟩ := indispensableMatching hc
  let a : V → Bool := fun w =>
    if (w.1 = i ∨ w.1 = k) ∧ w.2 = j then true else b w
  have ha (r : Row) (q : Hole) : a (r, q) = true ↔
      ((r = i ∨ r = k) ∧ q = j) ∨ b (r, q) = true := by
    by_cases h : (r = i ∨ r = k) ∧ q = j <;> simp [a, h]
  refine ⟨a, ?_, ?_⟩
  · rintro ⟨l, hl, hal⟩
    simp only [colAx, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · have htrue : a (i, j) = true := (ha i j).2 (Or.inl ⟨Or.inl rfl, rfl⟩)
      have hbad : true = false := htrue.symm.trans hal
      cases hbad
    · have htrue : a (k, j) = true := (ha k j).2 (Or.inl ⟨Or.inr rfl, rfl⟩)
      have hbad : true = false := htrue.symm.trans hal
      cases hbad
  · intro R hR hne
    rcases indispensablePHP.mp hR with ⟨r, rfl⟩ | ⟨r, _, s, _, q, _, hrs, rfl⟩
    · by_cases he : r = i ∨ r = k
      · exact indispensableSatRow (Finset.mem_univ j) ((ha r j).2 (Or.inl ⟨he, rfl⟩))
      · have hr' : r ∈ (Finset.univ.erase i).erase k := Finset.mem_erase.mpr
          ⟨fun h => he (Or.inr h), Finset.mem_erase.mpr ⟨fun h => he (Or.inl h), Finset.mem_univ _⟩⟩
        obtain ⟨q, _, hbr⟩ := hbrow r hr'
        exact indispensableSatRow (Finset.mem_univ q) ((ha r q).2 (Or.inr hbr))
    · apply indispensableSatCol
      intro hboth
      rcases (ha r q).1 hboth.1 with ⟨hr, hq⟩ | hr <;>
        rcases (ha s q).1 hboth.2 with ⟨hs, hq'⟩ | hs
      · apply hne
        rcases hr with hri | hrk <;> rcases hs with hsi | hsk
        · exact (hrs (hri.trans hsi.symm)).elim
        · rw [hri, hsk, hq]
        · simpa only [hrk, hsi, hq, colAx] using
            (Finset.pair_comm ((k, j), false) ((i, j), false))
        · exact (hrs (hrk.trans hsk.symm)).elim
      · exact (Finset.mem_erase.mp (hbmem hs).2).1 hq
      · exact (Finset.mem_erase.mp (hbmem hr).2).1 hq'
      · exact hrs (hbinj hr hs)

theorem critical {B : C} (hB : B ∈ PHP 5 4) :
    ∃ a : V → Bool, ¬ ClauseSat a B ∧ ∀ D ∈ PHP 5 4, D ≠ B → ClauseSat a D := by
  rcases indispensablePHP.mp hB with ⟨i, rfl⟩ | ⟨i, _, k, _, j, _, hik, rfl⟩
  · exact indispensableRowModel i
  · exact indispensableColModel j hik

def collisionBank : Finset C :=
  ((Finset.univ : Finset (Row × Row × Hole)).filter (fun p => p.1 < p.2.1)).image
    (fun p => colAx p.1 p.2.1 p.2.2)

theorem mem_collisionBank (B : C) : B ∈ collisionBank ↔ Collision Finset.univ Finset.univ B := by
  unfold collisionBank
  constructor
  · intro hB
    obtain ⟨⟨i, k, j⟩, hp, he⟩ := Finset.mem_image.mp hB
    exact ⟨i, Finset.mem_univ _, k, Finset.mem_univ _, j, Finset.mem_univ _,
      ne_of_lt (Finset.mem_filter.mp hp).2, he.symm⟩
  · rintro ⟨i, _, k, _, j, _, hik, rfl⟩
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · exact Finset.mem_image.mpr ⟨(i, k, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
    · refine Finset.mem_image.mpr ⟨(k, i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, ?_⟩
      exact Finset.pair_comm ((k, j), false) ((i, j), false)

theorem collisionBank_card : collisionBank.card = 40 := by
  have hinj : Set.InjOn (fun p : Row × Row × Hole => colAx p.1 p.2.1 p.2.2)
      (((Finset.univ : Finset (Row × Row × Hole)).filter (fun p => p.1 < p.2.1)) : Set _) := by
    intro ⟨i1, k1, j1⟩ h1 ⟨i2, k2, j2⟩ h2 heq
    dsimp only at heq
    have hlt1 : i1 < k1 := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
    have hlt2 : i2 < k2 := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
    have m1 : ((i1, j1), false) ∈ colAx i2 k2 j2 := heq ▸ by simp [colAx]
    have m2 : ((k1, j1), false) ∈ colAx i2 k2 j2 := heq ▸ by simp [colAx]
    simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at m1 m2
    rcases m1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases m2 with ⟨h3, _⟩ | ⟨h3, _⟩
    · exact (ne_of_lt hlt1 h3.symm).elim
    · rw [h3]
    · rw [h3] at hlt1; exact (lt_asymm hlt1 hlt2).elim
    · exact (ne_of_lt hlt1 h3.symm).elim
  unfold collisionBank
  rw [Finset.card_image_of_injOn hinj]
  decide +kernel

def axiomBank : Finset C :=
  (Finset.univ.image (fun r : Row => rowAx r Finset.univ)) ∪ collisionBank

theorem mem_axiomBank (B : C) : B ∈ axiomBank ↔ B ∈ PHP 5 4 := by
  rw [indispensablePHP]
  simp only [axiomBank, Finset.mem_union, mem_collisionBank, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro (⟨r, he⟩ | h)
    · exact Or.inl ⟨r, he.symm⟩
    · exact Or.inr h
  · rintro (⟨r, he⟩ | h)
    · exact Or.inl ⟨r, he.symm⟩
    · exact Or.inr h

theorem axiomBank_card : axiomBank.card = 45 := by
  have hdisj : Disjoint (Finset.univ.image (fun r : Row => rowAx r Finset.univ)) collisionBank := by
    rw [Finset.disjoint_left]
    intro B hB1 hB2
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hB1
    have hc : Coll (rowAx r Finset.univ) := (mem_collisionBank _).mp hB2
    exact collisionNoPos hc (r, 0) (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
  have hrow : (Finset.univ.image (fun r : Row => rowAx r Finset.univ)).card = 5 := by
    have hinj : Function.Injective (fun r : Row => rowAx r Finset.univ) := by
      intro r1 r2 heq
      dsimp only at heq
      have hm : ((r1, (0 : Hole)), true) ∈ rowAx r2 Finset.univ :=
        heq ▸ Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
      obtain ⟨_, _, he⟩ := Finset.mem_image.mp hm
      exact (Prod.mk.inj (Prod.mk.inj he).1).1.symm
    rw [Finset.card_image_of_injective _ hinj]
    decide +kernel
  unfold axiomBank
  rw [Finset.card_union_of_disjoint hdisj, hrow, collisionBank_card]

theorem requiredAxioms {π : List C} {A : Finset C} (hs : Absorbs π A)
    (he : (∅ : C) ∈ π) : axiomBank ⊆ A := by
  classical
  intro B hB
  by_contra hm
  obtain ⟨a, _, hrest⟩ := critical ((mem_axiomBank B).mp hB)
  apply emptyUnsat a (hs a ?_ ∅ he)
  intro D hDA hDP
  exact hrest D hDP (fun e => hm (e ▸ hDA))

theorem requiredCollisions {π : List C} {U : Finset C} {S : Finset V}
    (hc : Controls π U S) (he : (∅ : C) ∈ π) :
    ∀ B : C, Coll B → B ∈ U ∧ Hits S B := by
  classical
  intro B hB
  by_contra hm
  obtain ⟨a, _, hrest⟩ := critical (collisionPHP hB)
  have hr : ∀ D ∈ PHP 5 4, ¬ Coll D → ClauseSat a D := by
    intro D hDP hDC
    exact hrest D hDP (fun e => hDC (e.symm ▸ hB))
  have hu : ∀ D ∈ U, Coll D → Hits S D → ClauseSat a D := by
    intro D hDU hDC hDS
    apply hrest D (collisionPHP hDC)
    intro e
    subst D
    exact hm ⟨hDU, hDS⟩
  have hneg : NegsIn S ∅ := by
    intro v hv
    simp at hv
  exact emptyUnsat a (hc U S (fun _ h => h) (fun _ h => h) a hr hu ∅ he
    (fun h => collisionNonempty h rfl) hneg)

theorem refutationLower {π : List C} (hπ : IsRefutation (PHP 5 4) π) :
    101 ≤ π.length := by
  obtain ⟨A, U, S, hsum, ha, hc⟩ := collect hπ.1
  have hab := Finset.card_le_card (requiredAxioms ha hπ.2)
  rw [axiomBank_card] at hab
  have hcov := requiredCollisions hc hπ.2
  have hub : collisionBank ⊆ U := fun B hB => (hcov B ((mem_collisionBank B).mp hB)).1
  have hun := Finset.card_le_card hub
  rw [collisionBank_card] at hun
  have hsn := coverSize S (fun B hB => (hcov B hB).2)
  omega

end PEqualNP.Outside.L_pcx_160_aux

theorem PEqualNP.Outside.L_pcx_160 : ¬ (∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 99) := by
  rintro ⟨π, hπ, hlen⟩
  have := PEqualNP.Outside.L_pcx_160_aux.refutationLower hπ
  omega
