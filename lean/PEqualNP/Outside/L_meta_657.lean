import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L532

namespace PEqualNP.Outside.LMeta657

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.Library.Peel
open PEqualNP.Library.Peel.Scratch

private def targetF (x : Fin 11 → Bool) : Bool :=
  (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 1) ||
  (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) ||
  (x 0 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && x 1)

private def edgePairs : List (Fin 11 × Fin 11) :=
  [(0, 2), (2, 3), (3, 4), (4, 1),
   (0, 5), (5, 6), (6, 7), (7, 1),
   (0, 8), (8, 9), (9, 10), (10, 1)]

private def thetaRel (i j : Fin 11) : Bool :=
  edgePairs.any (fun p => (p.1 == i && p.2 == j) || (p.1 == j && p.2 == i))

private abbrev G : SimpleGraph (Fin 11) :=
  SimpleGraph.fromRel (fun i j => thetaRel i j = true)

private def pt11 (S : Finset (Fin 11)) : Fin 11 → Bool := fun i => decide (i ∈ S)

private lemma targetF_eq_graph (x : Fin 11 → Bool) :
    targetF x = @decide (∃ i j : Fin 11, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _) := by
  apply Bool.eq_iff_iff.mpr
  rw [@decide_eq_true_iff _ (Classical.propDecidable _)]
  constructor
  · intro h
    unfold targetF at h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (((((((((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact ⟨0, 2, by decide, h1, h2⟩
    · exact ⟨2, 3, by decide, h1, h2⟩
    · exact ⟨3, 4, by decide, h1, h2⟩
    · exact ⟨4, 1, by decide, h1, h2⟩
    · exact ⟨0, 5, by decide, h1, h2⟩
    · exact ⟨5, 6, by decide, h1, h2⟩
    · exact ⟨6, 7, by decide, h1, h2⟩
    · exact ⟨7, 1, by decide, h1, h2⟩
    · exact ⟨0, 8, by decide, h1, h2⟩
    · exact ⟨8, 9, by decide, h1, h2⟩
    · exact ⟨9, 10, by decide, h1, h2⟩
    · exact ⟨10, 1, by decide, h1, h2⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    have hmem_all : ∀ a b : Fin 11, G.Adj a b → (a, b) ∈ edgePairs ∨ (b, a) ∈ edgePairs := by decide
    have hmem := hmem_all i j hij
    have hf : targetF x = false → False := by
      intro hf
      unfold targetF at hf
      simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hf
      have hchk : ∀ a b : Fin 11, (a, b) ∈ edgePairs → x a = true → x b = true → False := by
        intro a b hab ha hb
        simp only [edgePairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
      rcases hmem with hm | hm
      · exact hchk i j hm hi hj
      · exact hchk j i hm hj hi
    cases ht : targetF x with
    | true => rfl
    | false => exact (hf ht).elim


private lemma isAcyclic_of_order {n : ℕ} (H : SimpleGraph (Fin n)) (ord : Fin n → ℕ)
    (hinj : Function.Injective ord)
    (hord : ∀ v u1 u2 : Fin n, H.Adj u1 v → H.Adj u2 v → ord u1 < ord v → ord u2 < ord v → u1 = u2) :
    H.IsAcyclic := by
  intro v c hc
  let S : Finset (Fin n) := c.support.toFinset
  have hS : S.Nonempty := ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image S ord hS
  have hm_supp : m ∈ c.support := List.mem_toFinset.mp hmS
  let c' := c.rotate m hm_supp
  have hc' : c'.IsCycle := hc.rotate hm_supp
  have hlen3 : 3 ≤ c'.length := hc'.three_le_length
  have hsupp_sub : ∀ w ∈ c'.support, w ∈ S := by
    intro w hw
    apply List.mem_toFinset.mpr
    by_cases hwm : w = m
    · exact hwm ▸ hm_supp
    · obtain ⟨n1, hn1⟩ := c.support_rotate m hm_supp
      have hw_tail : w ∈ c'.support.tail := by
        cases hc'eq : c' with
        | nil => rw [hc'eq] at hw; simp at hw; exact (hwm hw).elim
        | cons _ p =>
          rw [hc'eq] at hw
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons, List.tail_cons] at hw ⊢
          exact hw.resolve_left hwm
      have hw_rot : w ∈ c.support.tail := by
        rw [← hn1]; exact List.mem_rotate.mpr hw_tail
      exact List.mem_of_mem_tail hw_rot
  cases hc'eq : c' with
  | nil => rw [hc'eq] at hlen3; simp at hlen3
  | cons h1 p1 =>
    rename_i u1
    have hu1_ne : u1 ≠ m := h1.ne.symm
    have hu1_S : u1 ∈ S := hsupp_sub u1 (by rw [hc'eq]; simp)
    have hlt1 : ord u1 < ord m := by
      have hle := hmax u1 hu1_S
      have hne : ord u1 ≠ ord m := fun e => hu1_ne (hinj e)
      omega
    cases hrev : c'.reverse with
    | nil =>
      have : c'.reverse.length = c'.length := SimpleGraph.Walk.length_reverse c'
      rw [hrev] at this; simp at this; omega
    | cons h2 p2 =>
      rename_i u2
      have hu2_ne : u2 ≠ m := h2.ne.symm
      have hu2_S : u2 ∈ S := by
        apply hsupp_sub u2
        have : u2 ∈ c'.reverse.support := by rw [hrev]; simp
        simpa [SimpleGraph.Walk.support_reverse] using this
      have hlt2 : ord u2 < ord m := by
        have hle := hmax u2 hu2_S
        have hne : ord u2 ≠ ord m := fun e => hu2_ne (hinj e)
        omega
      have hu12 : u1 = u2 := hord m u1 u2 h1.symm h2.symm hlt1 hlt2
      have hedg_nodup : c'.edges.Nodup := hc'.edges_nodup
      have hfirst : c'.edges.head? = some s(m, u1) := by rw [hc'eq]; rfl
      have hlast : c'.edges.getLast? = some s(u2, m) := by
        have hr : c'.reverse.edges = c'.edges.reverse := SimpleGraph.Walk.edges_reverse c'
        have hh : c'.reverse.edges.head? = some s(m, u2) := by rw [hrev]; rfl
        rw [hr, List.head?_reverse] at hh
        simpa [Sym2.eq_swap] using hh
      have hlen_e : 3 ≤ c'.edges.length := by simpa [SimpleGraph.Walk.length_edges] using hlen3
      cases he : c'.edges with
      | nil => rw [he] at hlen_e; simp at hlen_e
      | cons e0 es =>
        rw [he] at hedg_nodup hfirst hlast hlen_e
        simp only [List.head?_cons, Option.some.injEq] at hfirst
        cases hes : es with
        | nil => rw [hes] at hlen_e; simp at hlen_e
        | cons e1 es' =>
          rw [hes] at hedg_nodup hlast
          have hmem_last : s(u2, m) ∈ e1 :: es' := by
            have hne_nil : (e1 :: es') ≠ [] := List.cons_ne_nil _ _
            have hgl : (e0 :: e1 :: es').getLast? = (e1 :: es').getLast? := by simp
            rw [hgl] at hlast
            exact List.mem_of_getLast? hlast
          have hnot_mem : e0 ∉ e1 :: es' := (List.nodup_cons.mp hedg_nodup).1
          rw [hfirst, hu12, Sym2.eq_swap] at hnot_mem
          exact hnot_mem hmem_last

private abbrev Gdel0 : SimpleGraph (Fin 11) := delVerts G {0}
private abbrev Gdel2 : SimpleGraph (Fin 11) := delVerts G {2}
private abbrev Gdel23 : SimpleGraph (Fin 11) := delVerts G {2, 3}
private abbrev Gdel234 : SimpleGraph (Fin 11) := delVerts G {2, 3, 4}

private def ordDel0 (v : Fin 11) : ℕ :=
  match v.val with
  | 1 => 0
  | 4 => 1 | 3 => 2 | 2 => 3
  | 7 => 4 | 6 => 5 | 5 => 6
  | 10 => 7 | 9 => 8 | 8 => 9
  | _ => 10

private lemma peelable_Gdel0 : Peelable Gdel0 := by
  apply peelable_of_isAcyclic
  refine isAcyclic_of_order Gdel0 ordDel0 (by decide) ?_
  intro v u1 u2 h1 h2 ho1 ho2
  revert v u1 u2 h1 h2 ho1 ho2
  decide

private def ordDel2C (c : Fin 11) (v : Fin 11) : ℕ :=
  match c.val with
  | 0 =>
    match v.val with
    | 1 => 0 | 4 => 1 | 3 => 2 | 7 => 3 | 6 => 4 | 5 => 5 | 10 => 6 | 9 => 7 | 8 => 8 | 0 => 9 | _ => 10
  | 5 =>
    match v.val with
    | 1 => 0 | 4 => 1 | 3 => 2 | 7 => 3 | 6 => 4 | 10 => 5 | 9 => 6 | 8 => 7 | 0 => 8 | 5 => 9 | _ => 10
  | 6 =>
    match v.val with
    | 1 => 0 | 4 => 1 | 3 => 2 | 7 => 3 | 10 => 4 | 9 => 5 | 8 => 6 | 0 => 7 | 5 => 8 | 6 => 9 | _ => 10
  | 7 =>
    match v.val with
    | 1 => 0 | 4 => 1 | 3 => 2 | 10 => 3 | 9 => 4 | 8 => 5 | 0 => 6 | 5 => 7 | 6 => 8 | 7 => 9 | _ => 10
  | 1 =>
    match v.val with
    | 0 => 0 | 5 => 1 | 6 => 2 | 7 => 3 | 8 => 4 | 9 => 5 | 10 => 6 | 3 => 7 | 4 => 8 | 1 => 9 | _ => 10
  | 10 =>
    match v.val with
    | 1 => 0 | 4 => 1 | 3 => 2 | 7 => 3 | 6 => 4 | 5 => 5 | 0 => 6 | 8 => 7 | 9 => 8 | 10 => 9 | _ => 10
  | 9 =>
    match v.val with
    | 1 => 0 | 4 => 1 | 3 => 2 | 7 => 3 | 6 => 4 | 5 => 5 | 0 => 6 | 8 => 7 | 10 => 8 | 9 => 9 | _ => 10
  | _ =>
    match v.val with
    | 1 => 0 | 4 => 1 | 3 => 2 | 7 => 3 | 6 => 4 | 5 => 5 | 0 => 6 | 10 => 7 | 9 => 8 | 8 => 9 | _ => 10

private def cyc8 : Finset (Fin 11) := {0, 5, 6, 7, 1, 10, 9, 8}

private lemma acyclic_Gdel2_cut (c : Fin 11) (hc : c ∈ cyc8) : (delVerts Gdel2 {c}).IsAcyclic := by
  have hinj : Function.Injective (ordDel2C c) := by
    revert c hc; decide
  refine isAcyclic_of_order (delVerts Gdel2 {c}) (ordDel2C c) hinj ?_
  revert c hc
  decide

private lemma peelable_sub_Gdel2 (H : SimpleGraph (Fin 11))
    (hle : H ≤ Gdel2)
    (hcyc : ∀ i j : Fin 11, i ∈ cyc8 → j ∈ cyc8 → Gdel2.Adj i j → H.Adj i j) :
    Peelable H := by
  intro X hE
  by_cases hhit : ∃ c ∈ cyc8, c ∈ X
  · obtain ⟨c, hc, hcX⟩ := hhit
    left
    have hsub : delVerts H X ≤ delVerts Gdel2 {c} := by
      intro i j hij
      refine ⟨hle hij.1, ?_, ?_⟩
      · intro hi; simp only [Finset.mem_singleton] at hi; exact hij.2.1 (hi ▸ hcX)
      · intro hj; simp only [Finset.mem_singleton] at hj; exact hij.2.2 (hj ▸ hcX)
    exact PEqualNP.MetaComplexity.Helpers.Forest.forest_good_leaf _ ((acyclic_Gdel2_cut c hc).anti hsub) hE
  · right
    push Not at hhit
    have hnot : ∀ c ∈ cyc8, c ∉ X := hhit
    have h0 : (0 : Fin 11) ∉ X := hnot 0 (by decide)
    have h5 : (5 : Fin 11) ∉ X := hnot 5 (by decide)
    have h6 : (6 : Fin 11) ∉ X := hnot 6 (by decide)
    have h7 : (7 : Fin 11) ∉ X := hnot 7 (by decide)
    have h8 : (8 : Fin 11) ∉ X := hnot 8 (by decide)
    have h9 : (9 : Fin 11) ∉ X := hnot 9 (by decide)
    have hH : ∀ i j : Fin 11, i ∈ cyc8 → j ∈ cyc8 → Gdel2.Adj i j → (delVerts H X).Adj i j := by
      intro i j hi hj hadj
      exact ⟨hcyc i j hi hj hadj, hnot i hi, hnot j hj⟩
    refine ⟨7, 6, 5, 0, 8, 9, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w
      constructor
      · intro hw; exact (by decide : ∀ w : Fin 11, Gdel2.Adj 6 w → w = 7 ∨ w = 5) w (hle hw.1)
      · rintro (rfl | rfl)
        · exact hH 6 7 (by decide) (by decide) (by decide)
        · exact hH 6 5 (by decide) (by decide) (by decide)
    · intro w
      constructor
      · intro hw; exact (by decide : ∀ w : Fin 11, Gdel2.Adj 5 w → w = 6 ∨ w = 0) w (hle hw.1)
      · rintro (rfl | rfl)
        · exact hH 5 6 (by decide) (by decide) (by decide)
        · exact hH 5 0 (by decide) (by decide) (by decide)
    · intro w
      constructor
      · intro hw; exact (by decide : ∀ w : Fin 11, Gdel2.Adj 0 w → w = 5 ∨ w = 8) w (hle hw.1)
      · rintro (rfl | rfl)
        · exact hH 0 5 (by decide) (by decide) (by decide)
        · exact hH 0 8 (by decide) (by decide) (by decide)
    · intro w
      constructor
      · intro hw; exact (by decide : ∀ w : Fin 11, Gdel2.Adj 8 w → w = 0 ∨ w = 9) w (hle hw.1)
      · rintro (rfl | rfl)
        · exact hH 8 0 (by decide) (by decide) (by decide)
        · exact hH 8 9 (by decide) (by decide) (by decide)
    · refine ⟨1, fun w hw => ?_⟩
      exact (by decide : ∀ w : Fin 11, Gdel2.Adj 7 w → w = 6 ∨ w = 1) w (hle hw.1)
    · refine ⟨10, fun w hw => ?_⟩
      exact (by decide : ∀ w : Fin 11, Gdel2.Adj 9 w → w = 8 ∨ w = 10) w (hle hw.1)

private lemma peelable_Gdel2 : Peelable Gdel2 :=
  peelable_sub_Gdel2 Gdel2 le_rfl (fun _ _ _ _ h => h)

private lemma peelable_Gdel23 : Peelable Gdel23 :=
  peelable_sub_Gdel2 Gdel23 (by intro i j h; revert i j h; decide) (by intro i j hi hj h; revert i j hi hj h; decide)

private lemma peelable_Gdel234 : Peelable Gdel234 :=
  peelable_sub_Gdel2 Gdel234 (by intro i j h; revert i j h; decide) (by intro i j hi hj h; revert i j hi hj h; decide)

private lemma edgeSet_ncard_eq_card {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (E : Finset (Sym2 (Fin n))) (hE : ∀ e : Sym2 (Fin n), e ∈ H.edgeSet ↔ e ∈ E) :
    H.edgeSet.ncard = E.card := by
  have heq : H.edgeSet = (E : Set (Sym2 (Fin n))) := Set.ext hE
  rw [heq, Set.ncard_coe_finset]

private lemma card_Gdel0 : Gdel0.edgeSet.ncard = 9 := by
  let E : Finset (Sym2 (Fin 11)) :=
    {s(2, 3), s(3, 4), s(4, 1), s(5, 6), s(6, 7), s(7, 1), s(8, 9), s(9, 10), s(10, 1)}
  have h1 : Gdel0.edgeSet.ncard = E.card := by
    apply edgeSet_ncard_eq_card Gdel0 E
    intro e
    rcases e with ⟨a, b⟩
    change Gdel0.Adj a b ↔ s(a, b) ∈ E
    revert a b; decide
  rw [h1]; decide

private lemma card_Gdel2 : Gdel2.edgeSet.ncard = 10 := by
  let E : Finset (Sym2 (Fin 11)) :=
    {s(3, 4), s(4, 1), s(0, 5), s(5, 6), s(6, 7), s(7, 1), s(0, 8), s(8, 9), s(9, 10), s(10, 1)}
  have h1 : Gdel2.edgeSet.ncard = E.card := by
    apply edgeSet_ncard_eq_card Gdel2 E
    intro e
    rcases e with ⟨a, b⟩
    change Gdel2.Adj a b ↔ s(a, b) ∈ E
    revert a b; decide
  rw [h1]; decide

private lemma card_Gdel23 : Gdel23.edgeSet.ncard = 9 := by
  let E : Finset (Sym2 (Fin 11)) :=
    {s(4, 1), s(0, 5), s(5, 6), s(6, 7), s(7, 1), s(0, 8), s(8, 9), s(9, 10), s(10, 1)}
  have h1 : Gdel23.edgeSet.ncard = E.card := by
    apply edgeSet_ncard_eq_card Gdel23 E
    intro e
    rcases e with ⟨a, b⟩
    change Gdel23.Adj a b ↔ s(a, b) ∈ E
    revert a b; decide
  rw [h1]; decide

private lemma card_Gdel234 : Gdel234.edgeSet.ncard = 8 := by
  let E : Finset (Sym2 (Fin 11)) :=
    {s(0, 5), s(5, 6), s(6, 7), s(7, 1), s(0, 8), s(8, 9), s(9, 10), s(10, 1)}
  have h1 : Gdel234.edgeSet.ncard = E.card := by
    apply edgeSet_ncard_eq_card Gdel234 E
    intro e
    rcases e with ⟨a, b⟩
    change Gdel234.Adj a b ↔ s(a, b) ∈ E
    revert a b; decide
  rw [h1]; decide

private lemma cover_ge_of_pairs {n : ℕ} (T : Finset (Fin n)) (ps : List (Fin n × Fin n))
    (hnd : (ps.flatMap fun p => [p.1, p.2]).Nodup)
    (hcov : ∀ p ∈ ps, p.1 ∈ T ∨ p.2 ∈ T) :
    ps.length ≤ T.card := by
  have hpick_nd : (ps.map fun p => if p.1 ∈ T then p.1 else p.2).Nodup := by
    induction ps with
    | nil => simp
    | cons p rest ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, List.mem_flatMap, not_or, not_exists, not_and] at hnd
      simp only [List.map_cons, List.nodup_cons, List.mem_map]
      refine ⟨?_, ih hnd.2.2 (fun q hq => hcov q (List.mem_cons_of_mem _ hq))⟩
      rintro ⟨q, hq, hqeq⟩
      split_ifs at hqeq with h1 h2
      · exact (hnd.1.2 q hq).1 hqeq.symm
      · exact (hnd.2.1 q hq).1 hqeq.symm
      · exact (hnd.1.2 q hq).2.1 hqeq.symm
      · exact (hnd.2.1 q hq).2.1 hqeq.symm
  let picks : List (Fin n) := ps.map fun p => if p.1 ∈ T then p.1 else p.2
  have hlen : picks.length = ps.length := List.length_map _
  have hsub : picks.toFinset ⊆ T := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    split_ifs with h
    · exact h
    · exact (hcov p hp).resolve_left h
  calc ps.length = picks.length := hlen.symm
    _ = picks.toFinset.card := (List.toFinset_card_of_nodup hpick_nd).symm
    _ ≤ T.card := Finset.card_le_card hsub

private lemma cover_ge4_of_matching {n : ℕ} (T : Finset (Fin n)) (a1 b1 a2 b2 a3 b3 a4 b4 : Fin n)
    (hnd : [a1, b1, a2, b2, a3, b3, a4, b4].Nodup)
    (h1 : a1 ∈ T ∨ b1 ∈ T) (h2 : a2 ∈ T ∨ b2 ∈ T) (h3 : a3 ∈ T ∨ b3 ∈ T) (h4 : a4 ∈ T ∨ b4 ∈ T) :
    4 ≤ T.card := by
  have h := cover_ge_of_pairs T [(a1, b1), (a2, b2), (a3, b3), (a4, b4)] (by simpa using hnd) (by
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  simpa using h

private lemma cover_ge5_of_matching {n : ℕ} (T : Finset (Fin n)) (a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 : Fin n)
    (hnd : [a1, b1, a2, b2, a3, b3, a4, b4, a5, b5].Nodup)
    (h1 : a1 ∈ T ∨ b1 ∈ T) (h2 : a2 ∈ T ∨ b2 ∈ T) (h3 : a3 ∈ T ∨ b3 ∈ T)
    (h4 : a4 ∈ T ∨ b4 ∈ T) (h5 : a5 ∈ T ∨ b5 ∈ T) :
    5 ≤ T.card := by
  have h := cover_ge_of_pairs T [(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5)] (by simpa using hnd) (by
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> assumption)
  simpa using h

private lemma bound_0_false (s' : ℕ)
    (h : HasCircuitSize 11 (fun x : Fin 11 → Bool => targetF (Function.update x 0 false)) s') :
    12 ≤ s' := by
  have heq : (fun x : Fin 11 → Bool => targetF (Function.update x 0 false)) =
      (fun x : Fin 11 → Bool => @decide ((∃ a ∈ (∅ : Finset (Fin 11)), x a = true) ∨
        ∃ i j : Fin 11, Gdel0.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) := by
    funext x
    rw [targetF_eq_graph]
    apply Bool.eq_iff_iff.mpr
    rw [@decide_eq_true_iff _ (Classical.propDecidable _), @decide_eq_true_iff _ (Classical.propDecidable _)]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hi0 : i ≠ 0 := by rintro rfl; simp at hi
      have hj0 : j ≠ 0 := by rintro rfl; simp at hj
      rw [Function.update_of_ne hi0] at hi
      rw [Function.update_of_ne hj0] at hj
      exact Or.inr ⟨i, j, ⟨hij, by simpa using hi0, by simpa using hj0⟩, hi, hj⟩
    · rintro (⟨a, ha, _⟩ | ⟨i, j, hij, hi, hj⟩)
      · exact (Finset.notMem_empty a ha).elim
      · have hi0 : i ≠ 0 := by simpa using hij.2.1
        have hj0 : j ≠ 0 := by simpa using hij.2.2
        exact ⟨i, j, hij.1, by rwa [Function.update_of_ne hi0], by rwa [Function.update_of_ne hj0]⟩
  rw [heq] at h
  have hlb := PEqualNP.MetaComplexity.L532 11 4 s' Gdel0 ∅ peelable_Gdel0
    (fun _ _ _ => Finset.notMem_empty _)
    (Or.inr ⟨2, 3, by decide⟩)
    (fun T hT => cover_ge4_of_matching T 2 3 5 6 8 9 4 1 (by decide)
      (hT 2 3 (by decide)) (hT 5 6 (by decide)) (hT 8 9 (by decide)) (hT 4 1 (by decide)))
    h
  rw [Finset.card_empty, card_Gdel0] at hlb
  omega

private lemma bound_2_false (s' : ℕ)
    (h : HasCircuitSize 11 (fun x : Fin 11 → Bool => targetF (Function.update x 2 false)) s') :
    14 ≤ s' := by
  have heq : (fun x : Fin 11 → Bool => targetF (Function.update x 2 false)) =
      (fun x : Fin 11 → Bool => @decide ((∃ a ∈ (∅ : Finset (Fin 11)), x a = true) ∨
        ∃ i j : Fin 11, Gdel2.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) := by
    funext x
    rw [targetF_eq_graph]
    apply Bool.eq_iff_iff.mpr
    rw [@decide_eq_true_iff _ (Classical.propDecidable _), @decide_eq_true_iff _ (Classical.propDecidable _)]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hi2 : i ≠ 2 := by rintro rfl; simp at hi
      have hj2 : j ≠ 2 := by rintro rfl; simp at hj
      rw [Function.update_of_ne hi2] at hi
      rw [Function.update_of_ne hj2] at hj
      exact Or.inr ⟨i, j, ⟨hij, by simpa using hi2, by simpa using hj2⟩, hi, hj⟩
    · rintro (⟨a, ha, _⟩ | ⟨i, j, hij, hi, hj⟩)
      · exact (Finset.notMem_empty a ha).elim
      · have hi2 : i ≠ 2 := by simpa using hij.2.1
        have hj2 : j ≠ 2 := by simpa using hij.2.2
        exact ⟨i, j, hij.1, by rwa [Function.update_of_ne hi2], by rwa [Function.update_of_ne hj2]⟩
  rw [heq] at h
  have hlb := PEqualNP.MetaComplexity.L532 11 5 s' Gdel2 ∅ peelable_Gdel2
    (fun _ _ _ => Finset.notMem_empty _)
    (Or.inr ⟨3, 4, by decide⟩)
    (fun T hT => cover_ge5_of_matching T 3 4 0 5 6 7 8 9 10 1 (by decide)
      (hT 3 4 (by decide)) (hT 0 5 (by decide)) (hT 6 7 (by decide)) (hT 8 9 (by decide)) (hT 10 1 (by decide)))
    h
  rw [Finset.card_empty, card_Gdel2] at hlb
  omega

private lemma bound_23_false (s' : ℕ)
    (h : HasCircuitSize 11 (fun x : Fin 11 → Bool => targetF (Function.update (Function.update x 3 false) 2 false)) s') :
    12 ≤ s' := by
  have heq : (fun x : Fin 11 → Bool => targetF (Function.update (Function.update x 3 false) 2 false)) =
      (fun x : Fin 11 → Bool => @decide ((∃ a ∈ (∅ : Finset (Fin 11)), x a = true) ∨
        ∃ i j : Fin 11, Gdel23.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) := by
    funext x
    rw [targetF_eq_graph]
    apply Bool.eq_iff_iff.mpr
    rw [@decide_eq_true_iff _ (Classical.propDecidable _), @decide_eq_true_iff _ (Classical.propDecidable _)]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hi2 : i ≠ 2 := by rintro rfl; simp at hi
      have hj2 : j ≠ 2 := by rintro rfl; simp at hj
      rw [Function.update_of_ne hi2] at hi
      rw [Function.update_of_ne hj2] at hj
      have hi3 : i ≠ 3 := by rintro rfl; simp at hi
      have hj3 : j ≠ 3 := by rintro rfl; simp at hj
      rw [Function.update_of_ne hi3] at hi
      rw [Function.update_of_ne hj3] at hj
      exact Or.inr ⟨i, j, ⟨hij, by simp [hi2, hi3], by simp [hj2, hj3]⟩, hi, hj⟩
    · rintro (⟨a, ha, _⟩ | ⟨i, j, hij, hi, hj⟩)
      · exact (Finset.notMem_empty a ha).elim
      · have hi2 : i ≠ 2 := fun e => hij.2.1 (by simp [e])
        have hi3 : i ≠ 3 := fun e => hij.2.1 (by simp [e])
        have hj2 : j ≠ 2 := fun e => hij.2.2 (by simp [e])
        have hj3 : j ≠ 3 := fun e => hij.2.2 (by simp [e])
        exact ⟨i, j, hij.1,
          by rw [Function.update_of_ne hi2, Function.update_of_ne hi3]; exact hi,
          by rw [Function.update_of_ne hj2, Function.update_of_ne hj3]; exact hj⟩
  rw [heq] at h
  have hlb := PEqualNP.MetaComplexity.L532 11 4 s' Gdel23 ∅ peelable_Gdel23
    (fun _ _ _ => Finset.notMem_empty _)
    (Or.inr ⟨4, 1, by decide⟩)
    (fun T hT => cover_ge4_of_matching T 0 5 6 7 8 9 4 1 (by decide)
      (hT 0 5 (by decide)) (hT 6 7 (by decide)) (hT 8 9 (by decide)) (hT 4 1 (by decide)))
    h
  rw [Finset.card_empty, card_Gdel23] at hlb
  omega

private lemma bound_3_false (s' : ℕ)
    (h : HasCircuitSize 11 (fun x : Fin 11 → Bool => targetF (Function.update x 3 false)) s') :
    13 ≤ s' := by
  let g3 : (Fin 11 → Bool) → Bool := fun x => targetF (Function.update x 3 false)
  have hgnc : ∃ x y : Fin 11 → Bool, g3 x ≠ g3 y := by
    refine ⟨pt11 ∅, pt11 {0, 2}, ?_⟩; decide
  obtain ⟨gs, o, L, hls⟩ := exists_least 11 g3 s' hgnc h
  have hdep2 : Dep g3 2 := by
    refine ⟨pt11 {0}, ?_⟩; decide
  have hgnc2 : ∀ b : Bool, ∃ x y : Fin 11 → Bool, g3 (Function.update x 2 b) ≠ g3 (Function.update y 2 b) := by
    intro b; refine ⟨pt11 ∅, pt11 {0, 5}, ?_⟩; revert b; decide
  obtain ⟨p, hp⟩ := L.dep_read 2 hdep2 hgnc2
  have hnc2 : ∃ x y : Fin 11 → Bool, g3 (Function.update x 2 false) ≠ g3 (Function.update y 2 false) := by
    refine ⟨pt11 ∅, pt11 {0, 5}, ?_⟩; decide
  obtain ⟨s2, hs2, hc2⟩ := L.save 2 false hnc2 {p} (by
    intro q hq; rw [Finset.mem_singleton.mp hq]; exact rc_input false hp)
  rw [Finset.card_singleton] at hs2
  have h12 : 12 ≤ s2 := bound_23_false s2 hc2
  omega

private lemma bound_3_true (s' : ℕ)
    (h : HasCircuitSize 11 (fun x : Fin 11 → Bool => targetF (Function.update x 3 true)) s') :
    13 ≤ s' := by
  let A : Finset (Fin 11) := {2, 4}
  have heq : (fun x : Fin 11 → Bool => targetF (Function.update x 3 true)) =
      (fun x : Fin 11 → Bool => @decide ((∃ a ∈ A, x a = true) ∨
        ∃ i j : Fin 11, Gdel234.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) := by
    funext x
    rw [targetF_eq_graph]
    apply Bool.eq_iff_iff.mpr
    rw [@decide_eq_true_iff _ (Classical.propDecidable _), @decide_eq_true_iff _ (Classical.propDecidable _)]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      by_cases hi3 : i = 3
      · subst hi3
        have hj3 : j ≠ 3 := hij.ne.symm
        rw [Function.update_of_ne hj3] at hj
        have hjA : j ∈ A := (by decide : ∀ j : Fin 11, G.Adj 3 j → j ∈ ({2, 4} : Finset (Fin 11))) j hij
        exact Or.inl ⟨j, hjA, hj⟩
      by_cases hj3 : j = 3
      · subst hj3
        rw [Function.update_of_ne hi3] at hi
        have hiA : i ∈ A := (by decide : ∀ i : Fin 11, G.Adj i 3 → i ∈ ({2, 4} : Finset (Fin 11))) i hij
        exact Or.inl ⟨i, hiA, hi⟩
      rw [Function.update_of_ne hi3] at hi
      rw [Function.update_of_ne hj3] at hj
      by_cases hiA : i ∈ A
      · exact Or.inl ⟨i, hiA, hi⟩
      by_cases hjA : j ∈ A
      · exact Or.inl ⟨j, hjA, hj⟩
      exact Or.inr ⟨i, j, ⟨hij, by simp [A] at hiA; simp [hi3, hiA], by simp [A] at hjA; simp [hj3, hjA]⟩, hi, hj⟩
    · rintro (⟨a, ha, hxa⟩ | ⟨i, j, hij, hi, hj⟩)
      · have h3a : G.Adj 3 a := (by decide : ∀ a : Fin 11, a ∈ ({2, 4} : Finset (Fin 11)) → G.Adj 3 a) a ha
        have ha3 : a ≠ 3 := h3a.ne.symm
        exact ⟨3, a, h3a, by simp, by rwa [Function.update_of_ne ha3]⟩
      · have hi3 : i ≠ 3 := fun e => hij.2.1 (by simp [e])
        have hj3 : j ≠ 3 := fun e => hij.2.2 (by simp [e])
        exact ⟨i, j, hij.1, by rwa [Function.update_of_ne hi3], by rwa [Function.update_of_ne hj3]⟩
  rw [heq] at h
  have hlb := PEqualNP.MetaComplexity.L532 11 4 s' Gdel234 A peelable_Gdel234
    (by intro i j hij; revert i j hij; decide)
    (Or.inl ⟨2, by simp [A]⟩)
    (fun T hT => cover_ge4_of_matching T 0 5 6 7 1 10 8 9 (by decide)
      (hT 0 5 (by decide)) (hT 6 7 (by decide)) (hT 1 10 (by decide)) (hT 8 9 (by decide)))
    h
  have hAcard : A.card = 2 := by decide
  rw [hAcard, card_Gdel234] at hlb
  omega

private def remapWire (σ : Fin 11 ≃ Fin 11) (w : ℕ) : ℕ :=
  if h : w < 11 then (σ ⟨w, h⟩).val else w

private lemma wiresFrom_remap (σ : Fin 11 ≃ Fin 11) (gs : List Gate) (x : Fin 11 → Bool) :
    ∀ w : ℕ, (wiresFrom (gs.map fun g => ⟨g.op, g.inputs.map (remapWire σ)⟩) (List.ofFn x)).getD (remapWire σ w) false =
      (wiresFrom gs (List.ofFn (x ∘ σ))).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [List.map_nil, wiresFrom, List.foldl_nil]
    by_cases hw : w < 11
    · simp only [remapWire, hw, ↓reduceDIte, List.getD_eq_getElem?_getD, List.getElem?_ofFn, (σ ⟨w, hw⟩).isLt, Function.comp_apply]
    · simp only [remapWire, hw, ↓reduceDIte, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega : (List.ofFn x).length ≤ w),
        List.getElem?_eq_none (by simp; omega : (List.ofFn (x ∘ σ)).length ≤ w)]
  | append_singleton gs g ih =>
    intro w
    simp only [List.map_append, List.map_singleton, wiresFrom_append]
    have hl1 : (wiresFrom (gs.map fun g => ⟨g.op, g.inputs.map (remapWire σ)⟩) (List.ofFn x)).length = 11 + gs.length := by
      rw [length_wiresFrom]; simp
    have hl2 : (wiresFrom gs (List.ofFn (x ∘ σ))).length = 11 + gs.length := by
      rw [length_wiresFrom]; simp
    have hstep : ∀ (v : List Bool) (g0 : Gate), wiresFrom [g0] v = v ++ [g0.op.eval (g0.inputs.map fun i => v.getD i false)] := fun _ _ => rfl
    rw [hstep, hstep]
    have hval : (g.inputs.map (remapWire σ)).map (fun i => (wiresFrom (gs.map fun g => ⟨g.op, g.inputs.map (remapWire σ)⟩) (List.ofFn x)).getD i false) =
        g.inputs.map (fun i => (wiresFrom gs (List.ofFn (x ∘ σ))).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact ih i
    by_cases hlt : w < 11 + gs.length
    · have hlt' : remapWire σ w < 11 + gs.length := by
        dsimp [remapWire]; split_ifs with hw
        · have := (σ ⟨w, hw⟩).isLt; omega
        · omega
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact ih w
    · by_cases heq : w = 11 + gs.length
      · subst heq
        have hrem : remapWire σ (11 + gs.length) = 11 + gs.length := by
          dsimp [remapWire]; split_ifs with h <;> omega
        rw [hrem, getD_snoc_len _ _ _ _ hl1, getD_snoc_len _ _ _ _ hl2, hval]
      · have hgt : 11 + gs.length < w := by omega
        have hrem : remapWire σ w = w := by
          dsimp [remapWire]; split_ifs with h <;> omega
        rw [hrem, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by rw [List.length_append, List.length_singleton, hl1]; omega),
          List.getElem?_eq_none (by rw [List.length_append, List.length_singleton, hl2]; omega)]

private lemma hasCircuitSize_comp (σ : Fin 11 ≃ Fin 11) (g : (Fin 11 → Bool) → Bool) (s : ℕ)
    (h : HasCircuitSize 11 g s) : HasCircuitSize 11 (fun x => g (x ∘ σ)) s := by
  obtain ⟨C, hok, hsz, hev⟩ := h
  refine ⟨⟨C.gates.map fun gt => ⟨gt.op, gt.inputs.map (remapWire σ)⟩, remapWire σ C.output⟩, ?_, ?_, ?_⟩
  · intro gt hgt
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hgt
    have h0 := hok g0 hg0
    exact ⟨h0.1, by simpa using h0.2⟩
  · simpa [Circuit.size] using hsz
  · intro x
    have := wiresFrom_remap σ C.gates x C.output
    change (wiresFrom (C.gates.map fun gt => ⟨gt.op, gt.inputs.map (remapWire σ)⟩) (List.ofFn x)).getD (remapWire σ C.output) false = g (x ∘ σ)
    rw [this]
    exact hev (x ∘ σ)

private def swap01Fun : Fin 11 → Fin 11
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 4 | ⟨4, _⟩ => 2
  | ⟨5, _⟩ => 7 | ⟨7, _⟩ => 5
  | ⟨8, _⟩ => 10 | ⟨10, _⟩ => 8
  | v => v

private def swapP12Fun : Fin 11 → Fin 11
  | ⟨2, _⟩ => 5 | ⟨3, _⟩ => 6 | ⟨4, _⟩ => 7
  | ⟨5, _⟩ => 2 | ⟨6, _⟩ => 3 | ⟨7, _⟩ => 4
  | v => v

private def swapP13Fun : Fin 11 → Fin 11
  | ⟨2, _⟩ => 8 | ⟨3, _⟩ => 9 | ⟨4, _⟩ => 10
  | ⟨8, _⟩ => 2 | ⟨9, _⟩ => 3 | ⟨10, _⟩ => 4
  | v => v

private def swap01 : Fin 11 ≃ Fin 11 :=
  ⟨swap01Fun, swap01Fun, by decide, by decide⟩

private def swapP12 : Fin 11 ≃ Fin 11 :=
  ⟨swapP12Fun, swapP12Fun, by decide, by decide⟩

private def swapP13 : Fin 11 ≃ Fin 11 :=
  ⟨swapP13Fun, swapP13Fun, by decide, by decide⟩

private lemma targetF_equiv (σ : Fin 11 ≃ Fin 11)
    (hG : ∀ i j : Fin 11, G.Adj (σ i) (σ j) ↔ G.Adj i j) (x : Fin 11 → Bool) :
    targetF (x ∘ σ) = targetF x := by
  rw [targetF_eq_graph, targetF_eq_graph]
  classical
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨σ i, σ j, (hG i j).mpr hij, hi, hj⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨σ.symm i, σ.symm j, (hG _ _).mp (by simpa using hij), by simpa using hi, by simpa using hj⟩

private lemma targetF_update_equiv (σ : Fin 11 ≃ Fin 11)
    (hG : ∀ i j : Fin 11, G.Adj (σ i) (σ j) ↔ G.Adj i j) (v : Fin 11) (b : Bool) (x : Fin 11 → Bool) :
    targetF (Function.update x (σ v) b) = targetF (Function.update (x ∘ σ) v b) := by
  rw [← targetF_equiv σ hG (Function.update x (σ v) b)]
  congr 1
  funext i
  by_cases hi : i = v
  · subst hi; simp
  · have hne : σ i ≠ σ v := fun e => hi (σ.injective e)
    simp [hi, hne]

private lemma bound_nbr_false (v : Fin 11) (hv : v ∈ ({2, 4, 5, 7, 8, 10} : Finset (Fin 11))) (s' : ℕ)
    (h : HasCircuitSize 11 (fun x : Fin 11 → Bool => targetF (Function.update x v false)) s') :
    14 ≤ s' := by
  have helper : ∀ (σ : Fin 11 ≃ Fin 11), (∀ i j : Fin 11, G.Adj (σ i) (σ j) ↔ G.Adj i j) →
      σ 2 = v → 14 ≤ s' := by
    intro σ hG hσ
    apply bound_2_false s'
    have hcomp := hasCircuitSize_comp σ.symm _ s' h
    have heq2 : (fun x : Fin 11 → Bool => targetF (Function.update (x ∘ σ.symm) v false)) =
        (fun x : Fin 11 → Bool => targetF (Function.update x 2 false)) := by
      funext x
      rw [← hσ, targetF_update_equiv σ hG 2 false (x ∘ σ.symm)]
      have h4 : (x ∘ σ.symm) ∘ σ = x := by funext i; simp
      rw [h4]
    rw [heq2] at hcomp
    exact hcomp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact bound_2_false s' h
  · exact helper swap01 (by decide) (by decide)
  · exact helper swapP12 (by decide) (by decide)
  · exact helper (swap01.trans swapP12) (by decide) (by decide)
  · exact helper swapP13 (by decide) (by decide)
  · exact helper (swap01.trans swapP13) (by decide) (by decide)

private lemma bound_mid_false (m : Fin 11) (hm : m ∈ ({3, 6, 9} : Finset (Fin 11))) (s' : ℕ)
    (h : HasCircuitSize 11 (fun x : Fin 11 → Bool => targetF (Function.update x m false)) s') :
    13 ≤ s' := by
  have helper : ∀ (σ : Fin 11 ≃ Fin 11), (∀ i j : Fin 11, G.Adj (σ i) (σ j) ↔ G.Adj i j) →
      σ 3 = m → 13 ≤ s' := by
    intro σ hG hσ
    apply bound_3_false s'
    have hcomp := hasCircuitSize_comp σ.symm _ s' h
    have heq2 : (fun x : Fin 11 → Bool => targetF (Function.update (x ∘ σ.symm) m false)) =
        (fun x : Fin 11 → Bool => targetF (Function.update x 3 false)) := by
      funext x
      rw [← hσ, targetF_update_equiv σ hG 3 false (x ∘ σ.symm)]
      have h4 : (x ∘ σ.symm) ∘ σ = x := by funext i; simp
      rw [h4]
    rw [heq2] at hcomp
    exact hcomp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · exact bound_3_false s' h
  · exact helper swapP12 (by decide) (by decide)
  · exact helper swapP13 (by decide) (by decide)

private lemma bound_mid_true (m : Fin 11) (hm : m ∈ ({3, 6, 9} : Finset (Fin 11))) (s' : ℕ)
    (h : HasCircuitSize 11 (fun x : Fin 11 → Bool => targetF (Function.update x m true)) s') :
    13 ≤ s' := by
  have helper : ∀ (σ : Fin 11 ≃ Fin 11), (∀ i j : Fin 11, G.Adj (σ i) (σ j) ↔ G.Adj i j) →
      σ 3 = m → 13 ≤ s' := by
    intro σ hG hσ
    apply bound_3_true s'
    have hcomp := hasCircuitSize_comp σ.symm _ s' h
    have heq2 : (fun x : Fin 11 → Bool => targetF (Function.update (x ∘ σ.symm) m true)) =
        (fun x : Fin 11 → Bool => targetF (Function.update x 3 true)) := by
      funext x
      rw [← hσ, targetF_update_equiv σ hG 3 true (x ∘ σ.symm)]
      have h4 : (x ∘ σ.symm) ∘ σ = x := by funext i; simp
      rw [h4]
    rw [heq2] at hcomp
    exact hcomp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · exact bound_3_true s' h
  · exact helper swapP12 (by decide) (by decide)
  · exact helper swapP13 (by decide) (by decide)

private lemma orSwap_agree {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (p ph l : ℕ) (g : Gate)
    (y : Fin N) (hph : ph < gs.length) (hgp : gs[p]? = some g) (hop : g.op = GateOp.or)
    (hin : g.inputs = [l, N + ph] ∨ g.inputs = [N + ph, l]) (hlne : l ≠ N + ph)
    (hone : ∀ t, Reads gs t (N + ph) → t = p) (x : Fin N → Bool) (hlx : vl gs x l = true) :
    ∀ w, w ≠ N + ph → vl (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y) x w = vl gs x w := by
  have hcl' := PEqualNP.MetaComplexity.EdgeFn.andSwap_clean gs ph y hcl hph
  have hlen := PEqualNP.MetaComplexity.EdgeFn.andSwap_length gs ph y
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwk : w < N
    · rw [vl_input _ x w hwk, vl_input gs x w hwk]
    · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
      have hrp : r ≠ ph := fun e => hw (by rw [e])
      cases hr : gs[r]? with
      | none =>
        have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
        rw [vl_beyond _ x _ (by omega), vl_beyond gs x _ (by omega)]
      | some g' =>
        have hr' : (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y)[r]? = some g' := by
          rw [PEqualNP.MetaComplexity.EdgeFn.andSwap_get_ne gs ph y r hrp]; exact hr
        rw [vl_gate _ hcl' x r g' hr', vl_gate gs hcl x r g' hr]
        by_cases hrp' : r = p
        · subst hrp'
          rw [hgp] at hr
          cases hr
          have hllt : l < N + r := (hcl r g hgp).lt l (by rcases hin with h | h <;> simp [h])
          have hl' : vl (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y) x l = true := by
            rw [ih l hllt hlne]; exact hlx
          rw [hop]
          rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, hl', hlx]
        · congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hrp' (hone r ⟨g', hr, e ▸ ha⟩))

private lemma or_partner_drop3 (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate)
    (o p ph : ℕ) (g : Gate) (y : Fin (n + 1)) (L : Least (n + 1) F gs o)
    (hnc : ∃ x x' : Fin (n + 1) → Bool, F (Function.update x y true) ≠ F (Function.update x' y true))
    (hgp : gs[p]? = some g) (hop : g.op = GateOp.or)
    (hin : g.inputs = [(y : ℕ), n + 1 + ph] ∨ g.inputs = [n + 1 + ph, (y : ℕ)])
    (hph : ph < gs.length) (hone : ∀ t, Reads gs t (n + 1 + ph) → t = p)
    (ho1 : o ≠ n + 1 + p) (ho2 : o ≠ n + 1 + ph) :
    Drop F y true 3 gs.length := by
  have hfnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
    obtain ⟨x, x', h⟩ := hnc; exact ⟨_, _, h⟩
  have hymem : (y : ℕ) ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hhmem : n + 1 + ph ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
  have hphp : n + 1 + ph < n + 1 + p := (L.hcl p g hgp).lt _ hhmem
  have hyne : (y : ℕ) ≠ n + 1 + ph := by have := y.isLt; omega
  have hcl' := PEqualNP.MetaComplexity.EdgeFn.andSwap_clean gs ph y L.hcl hph
  have hgp' : (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y)[p]? = some g := by
    rw [PEqualNP.MetaComplexity.EdgeFn.andSwap_get_ne gs ph y p (by omega)]; exact hgp
  obtain ⟨S, hpS, hSr⟩ := L.live hfnc p hp ho1
  have hSr' : Reads (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y) S (n + 1 + p) := by
    obtain ⟨g', hg', hm⟩ := hSr
    exact ⟨g', by rw [PEqualNP.MetaComplexity.EdgeFn.andSwap_get_ne gs ph y S (by omega)]; exact hg', hm⟩
  have hphR : Reads (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y) ph y :=
    ⟨_, PEqualNP.MetaComplexity.EdgeFn.andSwap_get_eq gs ph y hph, by simp⟩
  have hpR : Reads (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y) p y := ⟨g, hgp', hymem⟩
  have hcp : IsC n (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y) y true (n + 1 + p) :=
    isC_reader hcl' y p g hgp' hymem true (Or.inr (by simp [fixBit, hop]))
  have hag : ∀ x : Fin (n + 1) → Bool,
      vl (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y) (Function.update x y true) o =
        F (Function.update x y true) := by
    intro x
    have hlx : vl gs (Function.update x y true) y = true := by
      rw [vl_input gs _ y y.isLt]; simp
    rw [orSwap_agree gs L.hcl p ph y g y hph hgp hop hin hyne hone _ hlx o ho2, L.hev]
  have hnc' : ∃ x x' : Fin (n + 1) → Bool,
      vl (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y) (Function.update x y true) o ≠
      vl (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y) (Function.update x' y true) o := by
    obtain ⟨x, x', h⟩ := hnc; exact ⟨x, x', by rw [hag, hag]; exact h⟩
  obtain ⟨s', hs', hc⟩ := save n (fun x => vl (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y) x o)
    (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y) o hcl' (fun _ => rfl) y true hnc' {ph, p, S} (by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact rc_input true hphR
      · exact rc_input true hpR
      · exact rc_of_reads hSr' hcp)
  have hcard : ({ph, p, S} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.2 ⟨ph, p, S, by omega, by omega, by omega, rfl⟩
  rw [hcard, PEqualNP.MetaComplexity.EdgeFn.andSwap_length] at hs'
  refine ⟨s', hs', ?_⟩
  have e : (fun x : Fin (n + 1) → Bool => F (Function.update x y true)) =
      fun x => (fun x => vl (PEqualNP.MetaComplexity.EdgeFn.andSwap gs ph y) x o) (Function.update x y true) := by
    funext x; exact (hag x).symm
  rw [e]; exact hc

private def elimOvrStep (ph : ℕ) (c : Bool) (acc : List Stat × List Gate × ℕ) (g : Gate) :
    List Stat × List Gate × ℕ :=
  let st := acc.1
  let outGs := acc.2.1
  let idx := acc.2.2
  if idx = ph then
    (st ++ [Stat.const c], outGs, idx + 1)
  else
    let ins := g.inputs.map (fun i => st.getD i (Stat.const false))
    let r := simplify g.op (11 + outGs.length) ins
    (st ++ [r.2], outGs ++ r.1.toList, idx + 1)

private def elimOvrRun (ph : ℕ) (c : Bool) (gs : List Gate) (acc : List Stat × List Gate × ℕ) :
    List Stat × List Gate × ℕ :=
  gs.foldl (elimOvrStep ph c) acc

private def initSt0 : List Stat :=
  Stat.const false :: (List.range 10).map (fun i => Stat.wire (i + 1))

private lemma initSt0_len : initSt0.length = 11 := by decide

private lemma initSt0_getD (w : ℕ) (hw0 : w ≠ 0) (hw11 : w < 11) :
    initSt0.getD w (Stat.const false) = Stat.wire w := by
  rcases w with _ | w
  · exact (hw0 rfl).elim
  · rcases w with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> first | rfl | omega

private lemma elimOvr_meta (ph : ℕ) (c : Bool) (gs : List Gate) :
    ∀ acc : List Stat × List Gate × ℕ,
      (elimOvrRun ph c gs acc).1.length = acc.1.length + gs.length ∧
      (elimOvrRun ph c gs acc).2.2 = acc.2.2 + gs.length ∧
      (∀ w < acc.1.length, (elimOvrRun ph c gs acc).1.getD w (Stat.const false) = acc.1.getD w (Stat.const false)) := by
  induction gs with
  | nil =>
    intro acc; exact ⟨by simp [elimOvrRun], by simp [elimOvrRun], fun _ _ => rfl⟩
  | cons g gs ih =>
    intro acc
    have hstep := ih (elimOvrStep ph c acc g)
    have h1 : (elimOvrStep ph c acc g).1.length = acc.1.length + 1 := by
      dsimp [elimOvrStep]; split_ifs <;> simp
    have h2 : (elimOvrStep ph c acc g).2.2 = acc.2.2 + 1 := by
      dsimp [elimOvrStep]; split_ifs <;> rfl
    have h3 : ∀ w < acc.1.length, (elimOvrStep ph c acc g).1.getD w (Stat.const false) = acc.1.getD w (Stat.const false) := by
      intro w hw
      dsimp [elimOvrStep]
      split_ifs <;> exact getD_snoc_ne _ _ _ _ (by omega)
    refine ⟨?_, ?_, ?_⟩
    · change (elimOvrRun ph c gs (elimOvrStep ph c acc g)).1.length = acc.1.length + (gs.length + 1)
      rw [hstep.1, h1]; omega
    · change (elimOvrRun ph c gs (elimOvrStep ph c acc g)).2.2 = acc.2.2 + (gs.length + 1)
      rw [hstep.2.1, h2]; omega
    · intro w hw
      change (elimOvrRun ph c gs (elimOvrStep ph c acc g)).1.getD w (Stat.const false) = _
      rw [hstep.2.2 w (by omega), h3 w hw]

private lemma elimOvr_ok (ph : ℕ) (c : Bool) (gs : List Gate) :
    ∀ acc : List Stat × List Gate × ℕ,
      (∀ g ∈ acc.2.1, Ok g) →
      ∀ g ∈ (elimOvrRun ph c gs acc).2.1, Ok g := by
  induction gs with
  | nil => intro acc hok; exact hok
  | cons g gs ih =>
    intro acc hok
    apply ih (elimOvrStep ph c acc g)
    intro g' hg'
    dsimp [elimOvrStep] at hg'
    split_ifs at hg'
    · exact hok g' hg'
    · rcases List.mem_append.mp hg' with hg' | hg'
      · exact hok g' hg'
      · have hsm := simplify_ok g.op (11 + acc.2.1.length) (g.inputs.map fun i => acc.1.getD i (Stat.const false))
        cases hopt : (simplify g.op (11 + acc.2.1.length) (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 with
        | none => rw [hopt] at hg'; simp at hg'
        | some g1 =>
          rw [hopt] at hg' hsm
          simp only [Option.toList_some, List.mem_singleton] at hg'
          subst hg'
          exact hsm g' rfl

private lemma elimOvr_valid (ph : ℕ) (c : Bool) (gs : List Gate)
    (hok_gs : ∀ g ∈ gs, Ok g) :
    ∀ acc : List Stat × List Gate × ℕ,
      (∀ w < acc.1.length, (acc.1.getD w (Stat.const false)).Valid (11 + acc.2.1.length)) →
      ∀ w < (elimOvrRun ph c gs acc).1.length,
        ((elimOvrRun ph c gs acc).1.getD w (Stat.const false)).Valid (11 + (elimOvrRun ph c gs acc).2.1.length) := by
  induction gs with
  | nil => intro acc hv; exact hv
  | cons g gs ih =>
    intro acc hv
    have hgok : Ok g := hok_gs g (by simp)
    apply ih (fun g' hg' => hok_gs g' (by simp [hg'])) (elimOvrStep ph c acc g)
    intro w hw
    dsimp [elimOvrStep] at hw ⊢
    split_ifs at hw ⊢ with heq
    · by_cases hlt : w < acc.1.length
      · rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hv w hlt
      · have hw' : w = acc.1.length := by simp at hw; omega
        rw [hw', getD_snoc_len _ _ _ _ rfl]; trivial
    · have hlen_le : 11 + acc.2.1.length ≤ 11 + (acc.2.1 ++ (simplify g.op (11 + acc.2.1.length) (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length := by
        simp
      by_cases hlt : w < acc.1.length
      · rw [getD_snoc_ne _ _ _ _ (by omega)]
        exact Stat.valid_mono hlen_le _ (hv w hlt)
      · have hw' : w = acc.1.length := by simp at hw; omega
        rw [hw', getD_snoc_len _ _ _ _ rfl]
        let dummy : List Bool := List.replicate (11 + acc.2.1.length) false
        have hdl : dummy.length = 11 + acc.2.1.length := List.length_replicate
        have hss := (simplify_sound g.op hgok.1 dummy (g.inputs.map fun i => acc.1.getD i (Stat.const false))
          (by simpa using hgok.2) (by
            intro s hs
            obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
            rw [hdl]
            by_cases hi : i < acc.1.length
            · exact hv i hi
            · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; trivial)).1
        rw [hdl] at hss
        simpa [List.length_append, Nat.add_assoc] using hss

private lemma elimOvr_sound (ph : ℕ) (c : Bool) (gs : List Gate) (hcl : CleanL 11 gs)
    (hph_val : ∀ x : Fin 11 → Bool, vl gs (Function.update x 0 false) (11 + ph) = c) :
    ∀ (k : ℕ) (x : Fin 11 → Bool), k ≤ gs.length →
      ∀ w < 11 + k, ((elimOvrRun ph c (gs.take k) (initSt0, [], 0)).1.getD w (Stat.const false)).val
          (wiresFrom (elimOvrRun ph c (gs.take k) (initSt0, [], 0)).2.1 (List.ofFn x)) =
        vl gs (Function.update x 0 false) w := by
  intro k
  induction k with
  | zero =>
    intro x _ w hw
    simp only [List.take_zero, elimOvrRun, List.foldl_nil, wiresFrom, List.foldl_nil]
    rw [vl_input gs _ w (by omega)]
    by_cases hw0 : w = 0
    · subst hw0; simp [initSt0, Stat.val]
    · have hst : initSt0.getD w (Stat.const false) = Stat.wire w := initSt0_getD w hw0 (by omega)
      rw [hst, Stat.val, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      have hlt11 : w < 11 := by omega
      simp only [hlt11, ↓reduceDIte, Option.getD_some]
      have hne0 : (⟨w, hlt11⟩ : Fin 11) ≠ 0 := fun e => hw0 (congrArg Fin.val e)
      rw [Function.update_of_ne hne0]
  | succ k ih =>
    intro x hk
    have htake : gs.take (k + 1) = gs.take k ++ [gs[k]'(by omega)] := List.take_succ_eq_append_getElem (by omega)
    have hg : gs[k]? = some (gs[k]'(by omega)) := List.getElem?_eq_getElem (by omega)
    let acc := elimOvrRun ph c (gs.take k) (initSt0, [], 0)
    have hmeta := elimOvr_meta ph c (gs.take k) (initSt0, [], 0)
    have hlen_st : acc.1.length = 11 + k := by
      dsimp [acc]; rw [hmeta.1, initSt0_len, List.length_take]; omega
    have hidx : acc.2.2 = k := by
      dsimp [acc]; rw [hmeta.2.1, List.length_take]; dsimp only; omega
    have hres_eq : elimOvrRun ph c (gs.take (k + 1)) (initSt0, [], 0) =
        elimOvrStep ph c acc (gs[k]'(by omega)) := by
      simp only [elimOvrRun, htake, List.foldl_append, List.foldl_cons, List.foldl_nil, acc]
    have hok_take : ∀ g ∈ gs.take k, Ok g := by
      intro g hg
      obtain ⟨j, hgj⟩ := List.mem_iff_getElem?.mp hg
      have hjlt : j < k := by
        have := (List.getElem?_eq_some_iff.mp hgj).1
        rw [List.length_take] at this; omega
      have hgj' : gs[j]? = some g := by rwa [List.getElem?_take_of_lt hjlt] at hgj
      rcases hcl j g hgj' with ⟨h, _, _, hin⟩ | ⟨h | h, _, _, _, _, hin⟩
      · exact ⟨Or.inr (Or.inr h), by rw [hin]; simp⟩
      · exact ⟨Or.inl h, by rw [hin]; simp⟩
      · exact ⟨Or.inr (Or.inl h), by rw [hin]; simp⟩
    have hvalid_acc : ∀ w < acc.1.length, (acc.1.getD w (Stat.const false)).Valid (11 + acc.2.1.length) := by
      apply elimOvr_valid ph c (gs.take k) hok_take (initSt0, [], 0)
      intro w hw
      rw [initSt0_len] at hw
      by_cases hw0 : w = 0
      · subst hw0; simp [initSt0, Stat.Valid]
      · rw [initSt0_getD w hw0 (by omega)]
        simp only [Stat.Valid]
        omega
    have hih := ih x (by omega)
    intro w hw
    rw [hres_eq]
    dsimp only [elimOvrStep]
    rw [hidx]
    split_ifs with hkph
    · by_cases hlt : w < 11 + k
      · rw [getD_snoc_ne _ _ _ _ (by omega)]
        exact hih w hlt
      · have hw' : w = 11 + k := by omega
        subst hw'
        rw [getD_snoc_len _ _ _ _ hlen_st, Stat.val, hkph, hph_val x]
    · have hwires_len : (wiresFrom acc.2.1 (List.ofFn x)).length = 11 + acc.2.1.length := by
        rw [length_wiresFrom]; simp
      by_cases hlt : w < 11 + k
      · rw [getD_snoc_ne _ _ _ _ (by omega), wiresFrom_append]
        obtain ⟨t, ht, _⟩ := wiresFrom_prefix (simplify (gs[k]'(by omega)).op (11 + acc.2.1.length) ((gs[k]'(by omega)).inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList (wiresFrom acc.2.1 (List.ofFn x))
        rw [ht, Stat.val_append _ _ _ (by rw [hwires_len]; exact hvalid_acc w (by omega))]
        exact hih w hlt
      · have hw' : w = 11 + k := by omega
        subst hw'
        rw [getD_snoc_len _ _ _ _ hlen_st, wiresFrom_append]
        have hop : (gs[k]'(by omega)).op = GateOp.and ∨ (gs[k]'(by omega)).op = GateOp.or ∨ (gs[k]'(by omega)).op = GateOp.not := by
          rcases hcl k _ hg with ⟨h, _⟩ | ⟨h | h, _⟩
          · exact Or.inr (Or.inr h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        have hlen_in : (gs[k]'(by omega)).inputs.length ≤ 2 := by
          rcases hcl k _ hg with ⟨_, _, _, hin⟩ | ⟨_, _, _, _, _, hin⟩ <;> simp [hin]
        have hss := (simplify_sound (gs[k]'(by omega)).op hop (wiresFrom acc.2.1 (List.ofFn x))
          ((gs[k]'(by omega)).inputs.map fun i => acc.1.getD i (Stat.const false))
          (by simpa using hlen_in)
          (by
            intro s hs
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
            have hilt : i < 11 + k := (hcl k _ hg).lt i hi
            rw [hwires_len]; exact hvalid_acc i (by omega))).2
        rw [hwires_len] at hss
        have heq_s : (simplify (gs[k]'(by omega)).op (11 + acc.2.1.length) ((gs[k]'(by omega)).inputs.map fun i => acc.1.getD i (Stat.const false))).2.val
            (wiresFrom (simplify (gs[k]'(by omega)).op (11 + acc.2.1.length) ((gs[k]'(by omega)).inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList (wiresFrom acc.2.1 (List.ofFn x))) =
            (gs[k]'(by omega)).op.eval (((gs[k]'(by omega)).inputs.map fun i => acc.1.getD i (Stat.const false)).map (Stat.val (wiresFrom acc.2.1 (List.ofFn x)))) := hss
        rw [heq_s, vl_gate gs hcl _ k _ hg]
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro i hi
        have hilt : i < 11 + k := (hcl k _ hg).lt i hi
        exact hih i hilt

private lemma elimOvr_count (ph : ℕ) (c : Bool) (gs : List Gate) (hcl : CleanL 11 gs)
    (S : Finset ℕ) (hS_lt : ∀ p ∈ S, p < gs.length)
    (hS_zero : ∀ p ∈ S, p = ph ∨ ∃ g, gs[p]? = some g ∧ (0 ∈ g.inputs ∨ 11 + ph ∈ g.inputs)) :
    (elimOvrRun ph c gs (initSt0, [], 0)).2.1.length + S.card ≤ gs.length := by
  suffices h : ∀ k ≤ gs.length,
      (elimOvrRun ph c (gs.take k) (initSt0, [], 0)).2.1.length + (S.filter (· < k)).card ≤ k by
    have h1 := h gs.length le_rfl
    have h2 : S.filter (· < gs.length) = S := Finset.filter_true_of_mem (fun p hp => hS_lt p hp)
    rw [List.take_length, h2] at h1
    exact h1
  intro k
  induction k with
  | zero =>
    intro _; simp [elimOvrRun]
  | succ k ih =>
    intro hk
    have hih := ih (by omega)
    have htake : gs.take (k + 1) = gs.take k ++ [gs[k]'(by omega)] := List.take_succ_eq_append_getElem (by omega)
    have hg : gs[k]? = some (gs[k]'(by omega)) := List.getElem?_eq_getElem (by omega)
    let acc := elimOvrRun ph c (gs.take k) (initSt0, [], 0)
    have hmeta := elimOvr_meta ph c (gs.take k) (initSt0, [], 0)
    have hidx : acc.2.2 = k := by dsimp [acc]; rw [hmeta.2.1, List.length_take]; dsimp only; omega
    have hres_eq : elimOvrRun ph c (gs.take (k + 1)) (initSt0, [], 0) =
        elimOvrStep ph c acc (gs[k]'(by omega)) := by
      simp only [elimOvrRun, htake, List.foldl_append, List.foldl_cons, List.foldl_nil, acc]
    rw [hres_eq]
    by_cases hkS : k ∈ S
    · have hfilt : S.filter (· < k + 1) = insert k (S.filter (· < k)) := by
        ext p; simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hpS, hplt⟩
          by_cases hpk : p = k
          · exact Or.inl hpk
          · exact Or.inr ⟨hpS, by omega⟩
        · rintro (rfl | ⟨hpS, hplt⟩)
          · exact ⟨hkS, by omega⟩
          · exact ⟨hpS, by omega⟩
      have hnot : k ∉ S.filter (· < k) := by simp
      rw [hfilt, Finset.card_insert_of_notMem hnot]
      have h0len : (elimOvrStep ph c acc (gs[k]'(by omega))).2.1.length = acc.2.1.length := by
        dsimp only [elimOvrStep]
        rw [hidx]
        split_ifs with hkph
        · rfl
        · rcases hS_zero k hkS with rfl | ⟨g0, hg0, h0in⟩
          · exact absurd rfl hkph
          · have heqg : g0 = gs[k]'(by omega) := Option.some.inj (hg0.symm.trans hg)
            subst heqg
            have hconst_in : ∃ c0, Stat.const c0 ∈ (gs[k]'(by omega)).inputs.map (fun i => acc.1.getD i (Stat.const false)) := by
              rcases h0in with h0m | hphm
              · refine ⟨false, List.mem_map.mpr ⟨0, h0m, ?_⟩⟩
                dsimp [acc]
                rw [hmeta.2.2 0 (by rw [initSt0_len]; omega)]
                rfl
              · have hphlt : ph < k := by
                  have := (hcl k _ hg).lt _ hphm; omega
                refine ⟨c, List.mem_map.mpr ⟨11 + ph, hphm, ?_⟩⟩
                have htake_split : gs.take k = gs.take (ph + 1) ++ (gs.take k).drop (ph + 1) :=
                  (List.take_append_drop (ph + 1) (gs.take k)).symm.trans (by rw [List.take_take, Nat.min_eq_left (by omega)])
                have hacc_eq : acc = elimOvrRun ph c ((gs.take k).drop (ph + 1)) (elimOvrRun ph c (gs.take (ph + 1)) (initSt0, [], 0)) := by
                  dsimp only [acc]
                  conv_lhs => rw [htake_split]
                  simp only [elimOvrRun, List.foldl_append]
                have hph_st : (elimOvrRun ph c (gs.take (ph + 1)) (initSt0, [], 0)).1.getD (11 + ph) (Stat.const false) = Stat.const c := by
                  have htk : gs.take (ph + 1) = gs.take ph ++ [gs[ph]'(by omega)] := List.take_succ_eq_append_getElem (by omega)
                  rw [htk]
                  have hstep_eq : elimOvrRun ph c (gs.take ph ++ [gs[ph]'(by omega)]) (initSt0, [], 0) =
                      elimOvrStep ph c (elimOvrRun ph c (gs.take ph) (initSt0, [], 0)) (gs[ph]'(by omega)) := by
                    simp only [elimOvrRun, List.foldl_append, List.foldl_cons, List.foldl_nil]
                  rw [hstep_eq]
                  have hm2 := elimOvr_meta ph c (gs.take ph) (initSt0, [], 0)
                  have hidx2 : (elimOvrRun ph c (gs.take ph) (initSt0, [], 0)).2.2 = ph := by
                    rw [hm2.2.1, List.length_take]; dsimp only; omega
                  have hlen2 : (elimOvrRun ph c (gs.take ph) (initSt0, [], 0)).1.length = 11 + ph := by
                    rw [hm2.1, initSt0_len, List.length_take]; omega
                  dsimp only [elimOvrStep]
                  rw [hidx2]; simp only [↓reduceIte]; exact getD_snoc_len _ _ _ _ hlen2
                have hm3 := elimOvr_meta ph c ((gs.take k).drop (ph + 1)) (elimOvrRun ph c (gs.take (ph + 1)) (initSt0, [], 0))
                have hlen3 : (elimOvrRun ph c (gs.take (ph + 1)) (initSt0, [], 0)).1.length = 11 + (ph + 1) := by
                  have := (elimOvr_meta ph c (gs.take (ph + 1)) (initSt0, [], 0)).1
                  rw [initSt0_len, List.length_take] at this; omega
                rw [hacc_eq, hm3.2.2 (11 + ph) (by omega), hph_st]
            have hnok : NOk (gs[k]'(by omega)) := by
              rcases hcl k _ hg with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j1, j2, _, _, hin⟩
              · exact ⟨⟨Or.inr (Or.inr hop), by rw [hin]; simp⟩, fun _ => by rw [hin]; simp⟩
              · exact ⟨⟨Or.inl hop, by rw [hin]; simp⟩, fun h => by rw [hop] at h; cases h⟩
              · exact ⟨⟨Or.inr (Or.inl hop), by rw [hin]; simp⟩, fun h => by rw [hop] at h; cases h⟩
            have hnone := simplify_count (gs[k]'(by omega)).op (11 + acc.2.1.length)
              ((gs[k]'(by omega)).inputs.map fun i => acc.1.getD i (Stat.const false))
              hnok.1.1 (by simpa using hnok.1.2) (fun h => by simpa using hnok.2 h) hconst_in
            rw [hnone]; simp
      change acc.2.1.length + (S.filter (· < k)).card ≤ k at hih
      rw [h0len]; omega
    · have hfilt : S.filter (· < k + 1) = S.filter (· < k) := by
        ext p; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hpS, hplt⟩
          have hne : p ≠ k := fun e => hkS (e ▸ hpS)
          exact ⟨hpS, by omega⟩
        · rintro ⟨hpS, hplt⟩; exact ⟨hpS, by omega⟩
      rw [hfilt]
      have hle1 : (elimOvrStep ph c acc (gs[k]'(by omega))).2.1.length ≤ acc.2.1.length + 1 := by
        dsimp only [elimOvrStep]
        split_ifs
        · dsimp only; omega
        · simp only [List.length_append]
          have := toList_length_le (simplify (gs[k]'(by omega)).op (11 + acc.2.1.length) ((gs[k]'(by omega)).inputs.map fun i => acc.1.getD i (Stat.const false))).1
          omega
      change acc.2.1.length + (S.filter (· < k)).card ≤ k at hih
      omega

private lemma elimOvr_drop4 (gs : List Gate) (o ph : ℕ) (c : Bool)
    (L : Least 11 targetF gs o)
    (hph_val : ∀ x : Fin 11 → Bool, vl gs (Function.update x 0 false) (11 + ph) = c)
    (p1 p2 p3 p4 : ℕ)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hlt1 : p1 < gs.length) (hlt2 : p2 < gs.length) (hlt3 : p3 < gs.length) (hlt4 : p4 < gs.length)
    (hz1 : p1 = ph ∨ ∃ g, gs[p1]? = some g ∧ (0 ∈ g.inputs ∨ 11 + ph ∈ g.inputs))
    (hz2 : p2 = ph ∨ ∃ g, gs[p2]? = some g ∧ (0 ∈ g.inputs ∨ 11 + ph ∈ g.inputs))
    (hz3 : p3 = ph ∨ ∃ g, gs[p3]? = some g ∧ (0 ∈ g.inputs ∨ 11 + ph ∈ g.inputs))
    (hz4 : p4 = ph ∨ ∃ g, gs[p4]? = some g ∧ (0 ∈ g.inputs ∨ 11 + ph ∈ g.inputs)) :
    ∃ s' : ℕ, s' + 4 ≤ gs.length ∧
      HasCircuitSize 11 (fun x : Fin 11 → Bool => targetF (Function.update x 0 false)) s' := by
  let S : Finset ℕ := {p1, p2, p3, p4}
  have hScard : S.card = 4 := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
        Finset.card_insert_of_notMem (by simp [h23, h24]),
        Finset.card_pair h34]
  have hcnt := elimOvr_count ph c gs L.hcl S
    (fun p hp => by simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl | rfl | rfl <;> assumption)
    (fun p hp => by simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  rw [hScard] at hcnt
  let res := elimOvrRun ph c gs (initSt0, [], 0)
  have hok : ∀ g ∈ res.2.1, Ok g := elimOvr_ok ph c gs (initSt0, [], 0) (by simp)
  have hsound := elimOvr_sound ph c gs L.hcl hph_val gs.length
  simp only [List.take_length] at hsound
  have ho_lt : o < 11 + gs.length := by
    by_contra hge
    have hnc : targetF (pt11 ∅) ≠ targetF (pt11 {0, 2}) := by decide
    apply hnc
    rw [← L.hev, ← L.hev, vl_beyond gs _ o (by omega), vl_beyond gs _ o (by omega)]
  cases hst : res.1.getD o (Stat.const false) with
  | const b =>
    exfalso
    have hnc0 : targetF (Function.update (pt11 ∅) 0 false) ≠ targetF (Function.update (pt11 {5, 6}) 0 false) := by decide
    apply hnc0
    have h1 := hsound (pt11 ∅) le_rfl o ho_lt
    have h2 := hsound (pt11 {5, 6}) le_rfl o ho_lt
    change (res.1.getD o (Stat.const false)).val (wiresFrom res.2.1 (List.ofFn (pt11 ∅))) = vl gs _ o at h1
    change (res.1.getD o (Stat.const false)).val (wiresFrom res.2.1 (List.ofFn (pt11 {5, 6}))) = vl gs _ o at h2
    rw [hst, Stat.val, L.hev] at h1 h2
    exact h1.symm.trans h2
  | wire o' =>
    refine ⟨res.2.1.length, hcnt, ⟨res.2.1, o'⟩, hok, le_rfl, ?_⟩
    intro x
    have h1 := hsound x le_rfl o ho_lt
    change (res.1.getD o (Stat.const false)).val (wiresFrom res.2.1 (List.ofFn x)) = vl gs (Function.update x 0 false) o at h1
    rw [hst, Stat.val, L.hev] at h1
    exact h1

private lemma agree_of_sole_reader (gs : List Gate) (hcl : CleanL 11 gs) (z : Fin 11) (p : ℕ) (g : Gate)
    (hgp : gs[p]? = some g) (huniq : ∀ q, Reads gs q z → q = p)
    (x y : Fin 11 → Bool) (hxy : ∀ i : Fin 11, i ≠ z → x i = y i)
    (hp_eq : vl gs x (11 + p) = vl gs y (11 + p)) :
    ∀ w : ℕ, w ≠ (z : ℕ) → vl gs x w = vl gs y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h11 : w < 11
    · rw [vl_input gs x w h11, vl_input gs y w h11]
      exact hxy ⟨w, h11⟩ (fun e => hw (congrArg Fin.val e))
    · obtain ⟨q, rfl⟩ : ∃ q, w = 11 + q := ⟨w - 11, by omega⟩
      by_cases hqp : q = p
      · subst hqp; exact hp_eq
      · cases hq : gs[q]? with
        | none =>
          have hle := List.getElem?_eq_none_iff.mp hq
          rw [vl_beyond gs x _ (by omega), vl_beyond gs y _ (by omega)]
        | some gq =>
          apply vl_congr gs hcl x y q gq hq
          intro a ha
          have halt : a < 11 + q := (hcl q gq hq).lt a ha
          have haz : a ≠ (z : ℕ) := fun e => hqp (huniq q ⟨gq, hq, e ▸ ha⟩)
          exact ih a halt haz

private lemma indep_of_no_read_before (gs : List Gate) (hcl : CleanL 11 gs) (S : Finset (Fin 11)) (k : ℕ)
    (hno : ∀ r < k, ∀ z ∈ S, ¬ Reads gs r z)
    (x y : Fin 11 → Bool) (hxy : ∀ i : Fin 11, i ∉ S → x i = y i) :
    ∀ w < 11 + k, (∀ z ∈ S, w ≠ (z : ℕ)) → vl gs x w = vl gs y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hnotS
    by_cases h11 : w < 11
    · rw [vl_input gs x w h11, vl_input gs y w h11]
      exact hxy ⟨w, h11⟩ (fun hm => hnotS ⟨w, h11⟩ hm rfl)
    · obtain ⟨r, rfl⟩ : ∃ r, w = 11 + r := ⟨w - 11, by omega⟩
      cases hr : gs[r]? with
      | none =>
        have hle := List.getElem?_eq_none_iff.mp hr
        rw [vl_beyond gs x _ (by omega), vl_beyond gs y _ (by omega)]
      | some gr =>
        apply vl_congr gs hcl x y r gr hr
        intro a ha
        have halt : a < 11 + r := (hcl r gr hr).lt a ha
        have hanS : ∀ z ∈ S, a ≠ (z : ℕ) := fun z hz e => hno r (by omega) z hz ⟨gr, hr, e ▸ ha⟩
        exact ih a (by omega) (by omega) hanS

private lemma not_pair_witness (z u : Fin 11) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (huz : u ≠ z) (b : Bool) :
    ∃ x : Fin 11 → Bool, x u = b ∧ x z = false ∧ targetF x = false ∧ targetF (Function.update x z true) = true := by
  let S : Finset (Fin 11) :=
    if b = false then
      match z.val with
      | 2 => if u.val = 0 then {3} else {0}
      | 3 => if u.val = 2 then {4} else {2}
      | 4 => if u.val = 1 then {3} else {1}
      | 5 => if u.val = 0 then {6} else {0}
      | 6 => if u.val = 5 then {7} else {5}
      | 7 => if u.val = 1 then {6} else {1}
      | 8 => if u.val = 0 then {9} else {0}
      | 9 => if u.val = 8 then {10} else {8}
      | _ => if u.val = 1 then {9} else {1}
    else
      match z.val with
      | 2 => if u.val = 0 then {0} else if u.val = 3 then {3} else if u.val = 4 then {0, 4} else {3, u}
      | 3 => if u.val = 2 then {2} else if u.val = 4 then {4} else if u.val = 0 then {0, 4} else {2, u}
      | 4 => if u.val = 1 then {1} else if u.val = 3 then {3} else if u.val = 2 then {1, 2} else {3, u}
      | 5 => if u.val = 0 then {0} else if u.val = 6 then {6} else if u.val = 7 then {0, 7} else {6, u}
      | 6 => if u.val = 5 then {5} else if u.val = 7 then {7} else if u.val = 0 then {0, 7} else {5, u}
      | 7 => if u.val = 1 then {1} else if u.val = 6 then {6} else if u.val = 5 then {1, 5} else {6, u}
      | 8 => if u.val = 0 then {0} else if u.val = 9 then {9} else if u.val = 10 then {0, 10} else {9, u}
      | 9 => if u.val = 8 then {8} else if u.val = 10 then {10} else if u.val = 0 then {0, 10} else {8, u}
      | _ => if u.val = 1 then {1} else if u.val = 9 then {9} else if u.val = 8 then {1, 8} else {9, u}
  refine ⟨pt11 S, ?_, ?_, ?_, ?_⟩ <;> (dsimp [S]; revert z u hz0 hz1 huz b; decide)

private lemma nbr_four_witnesses (z : Fin 11) (hz : z ∈ ({2, 4, 5, 7, 8, 10} : Finset (Fin 11))) (a b : Bool) :
    ∃ x : Fin 11 → Bool, x 0 = a ∧ x 1 = b ∧ x z = false ∧ targetF x = false ∧ targetF (Function.update x z true) = true := by
  let S : Finset (Fin 11) :=
    match z.val, a, b with
    | 2, false, false => {3}
    | 2, true, false => {0}
    | 2, false, true => {1, 3}
    | 2, true, true => {0, 1}
    | 4, false, false => {3}
    | 4, true, false => {0, 3}
    | 4, false, true => {1}
    | 4, true, true => {0, 1}
    | 5, false, false => {6}
    | 5, true, false => {0}
    | 5, false, true => {1, 6}
    | 5, true, true => {0, 1}
    | 7, false, false => {6}
    | 7, true, false => {0, 6}
    | 7, false, true => {1}
    | 7, true, true => {0, 1}
    | 8, false, false => {9}
    | 8, true, false => {0}
    | 8, false, true => {1, 9}
    | 8, true, true => {0, 1}
    | _, false, false => {9}
    | _, true, false => {0, 9}
    | _, false, true => {1}
    | _, true, true => {0, 1}
  refine ⟨pt11 S, ?_, ?_, ?_, ?_, ?_⟩ <;> (dsimp [S]; revert z hz a b; decide)

private lemma mid_three_witnesses (z : Fin 11) (hz : z ∈ ({3, 6, 9} : Finset (Fin 11))) (a b : Bool)
    (hnot11 : ¬ (a = true ∧ b = true)) :
    ∃ x : Fin 11 → Bool, x 0 = a ∧ x 1 = b ∧ x z = false ∧ targetF x = false ∧ targetF (Function.update x z true) = true := by
  let S : Finset (Fin 11) :=
    match z.val, a, b with
    | 3, false, false => {2}
    | 3, true, false => {0, 4}
    | 3, false, true => {1, 2}
    | 6, false, false => {5}
    | 6, true, false => {0, 7}
    | 6, false, true => {1, 5}
    | 9, false, false => {8}
    | 9, true, false => {0, 10}
    | 9, false, true => {1, 8}
    | _, _, _ => ∅
  refine ⟨pt11 S, ?_, ?_, ?_, ?_, ?_⟩ <;> (dsimp [S]; revert z hz a b hnot11; decide)

private lemma dep_all (v : Fin 11) : Dep targetF v := by
  have h : ∃ u : Fin 11, G.Adj u v := by revert v; decide
  obtain ⟨u, huv⟩ := h
  refine ⟨pt11 {u}, ?_⟩
  have h1 : targetF (pt11 {u}) = false := by
    rw [targetF_eq_graph, decide_eq_false_iff_not]
    rintro ⟨i, j, hij, hi, hj⟩
    simp only [pt11, decide_eq_true_eq, Finset.mem_singleton] at hi hj
    subst hi; subst hj; exact G.loopless.irrefl _ hij
  have h2 : targetF (Function.update (pt11 {u}) v (!pt11 {u} v)) = true := by
    have hvu : v ≠ u := huv.ne.symm
    have hptv : pt11 {u} v = false := by simp [pt11, hvu]
    rw [hptv, Bool.not_false, targetF_eq_graph, @decide_eq_true_eq _ (Classical.propDecidable _)]
    exact ⟨u, v, huv, by rw [Function.update_of_ne hvu.symm]; simp [pt11], by simp⟩
  rw [h1, h2]; decide

private lemma restr_nc_all (v : Fin 11) (b : Bool) :
    ∃ x y : Fin 11 → Bool, targetF (Function.update x v b) ≠ targetF (Function.update y v b) := by
  refine ⟨pt11 ∅, pt11 {0, 2, 5, 6}, ?_⟩
  revert v b; decide

set_option maxHeartbeats 2000000 in
private lemma main_lower (s : ℕ) (h : HasCircuitSize 11 targetF s) : 16 ≤ s := by
  classical
  by_contra hlt
  have hs15 : s ≤ 15 := by omega
  have hfnc : ∃ x y : Fin 11 → Bool, targetF x ≠ targetF y := ⟨pt11 ∅, pt11 {0, 2}, by decide⟩
  obtain ⟨gs, o, L, hls⟩ := exists_least 11 targetF s hfnc h
  have hglen : gs.length ≤ 15 := by omega
  let Nbr : Finset (Fin 11) := {2, 4, 5, 7, 8, 10}
  let Mid : Finset (Fin 11) := {3, 6, 9}
  let IntV : Finset (Fin 11) := {2, 3, 4, 5, 6, 7, 8, 9, 10}
  have hStep1 : ∀ v ∈ Nbr, ∃ p g, gs[p]? = some g ∧ g.op = GateOp.or ∧ (v : ℕ) ∈ g.inputs ∧
      (∀ q, Reads gs q v → q = p) := by
    intro v hv
    obtain ⟨p, hp⟩ := L.dep_read v (dep_all v) (restr_nc_all v)
    have huniq : ∀ q, Reads gs q v → q = p := by
      intro q hq
      by_contra hne
      obtain ⟨s', hs', hc'⟩ := L.save2 v false (restr_nc_all v false) p q (Ne.symm hne)
        (rc_input false hp) (rc_input false hq)
      have := bound_nbr_false v hv s' hc'
      omega
    obtain ⟨g, hgp, hvin⟩ := hp
    have hop_or : g.op = GateOp.or := by
      rcases gate_cases gs L.hcl p g hgp v hvin with ⟨hnot, _, _⟩ | ⟨_, _, ⟨hand, _⟩ | ⟨hor, _⟩⟩
      · exfalso
        have hc := isC_reader L.hcl v p g hgp hvin false (Or.inl hnot)
        obtain ⟨q, hpq, _, hqrc⟩ := L.next v false (restr_nc_all v false) p (reads_len ⟨g, hgp, hvin⟩) hc
        obtain ⟨s', hs', hc'⟩ := L.save2 v false (restr_nc_all v false) p q (by omega)
          (rc_input false ⟨g, hgp, hvin⟩) hqrc
        have := bound_nbr_false v hv s' hc'
        omega
      · exfalso
        have hc := isC_reader L.hcl v p g hgp hvin false (Or.inr (by simp [fixBit, hand]))
        obtain ⟨q, hpq, _, hqrc⟩ := L.next v false (restr_nc_all v false) p (reads_len ⟨g, hgp, hvin⟩) hc
        obtain ⟨s', hs', hc'⟩ := L.save2 v false (restr_nc_all v false) p q (by omega)
          (rc_input false ⟨g, hgp, hvin⟩) hqrc
        have := bound_nbr_false v hv s' hc'
        omega
      · exact hor
    exact ⟨p, g, hgp, hop_or, hvin, huniq⟩
  have hStep2 : ∀ m ∈ Mid, ∃ p g h, gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      (g.inputs = [(m : ℕ), h] ∨ g.inputs = [h, (m : ℕ)]) ∧
      (∀ q, Reads gs q m → q = p) ∧
      (∀ ph, h = 11 + ph → ∃ r, r ≠ p ∧ Reads gs r h) := by
    intro m hm
    obtain ⟨p, hp⟩ := L.dep_read m (dep_all m) (restr_nc_all m)
    have huniq : ∀ q, Reads gs q m → q = p := by
      intro q hq
      by_contra hne
      have hpays := L.two_readers m (restr_nc_all m) p q (Ne.symm hne) hp hq
      rcases hpays with ⟨⟨s', hs', hc'⟩, _⟩ | ⟨⟨s', hs', hc'⟩, _⟩ | ⟨_, ⟨s', hs', hc'⟩⟩
      · have := bound_mid_false m hm s' hc'; omega
      · have := bound_mid_false m hm s' hc'; omega
      · have := bound_mid_true m hm s' hc'; omega
    obtain ⟨g, hgp, hmin⟩ := hp
    rcases gate_cases gs L.hcl p g hgp m hmin with ⟨hnot, hin_not, hval_not⟩ | ⟨h, hin_bin, hor_and⟩
    · exfalso
      have hcp_f := isC_reader L.hcl m p g hgp hmin false (Or.inl hnot)
      have hcp_t := isC_reader L.hcl m p g hgp hmin true (Or.inl hnot)
      obtain ⟨q, hpq, hqr, hqrc_f⟩ := L.next m false (restr_nc_all m false) p (reads_len ⟨g, hgp, hmin⟩) hcp_f
      by_cases hex2 : ∃ q2, q2 ≠ q ∧ Reads gs q2 (11 + p)
      · obtain ⟨q2, hq2ne, hq2r⟩ := hex2
        obtain ⟨⟨s', hs', hc'⟩, _⟩ := L.not_two_readers m (restr_nc_all m) p g hgp hnot hmin q q2 (Ne.symm hq2ne) hqr hq2r
        have := bound_mid_false m hm s' hc'; omega
      · obtain ⟨gq, hgq, hqpin⟩ := hqr
        rcases gate_cases gs L.hcl q gq hgq (11 + p) hqpin with ⟨hqnot, _, hqval⟩ | ⟨_, _, ⟨hqand, _⟩ | ⟨hqor, _⟩⟩
        · exact L.no_alias hfnc q (List.getElem?_eq_some_iff.mp hgq).1 m (by have := m.isLt; omega)
            (fun u => by rw [hqval u, hval_not u, Bool.not_not])
        · obtain ⟨c1, hc1⟩ := hcp_t
          have hc1v : c1 = false := by
            have h1 := st_val_const 10 gs L.hcl m true (11 + p) c1 hc1 (fun _ => false)
            rw [hval_not, vl_input gs _ m m.isLt] at h1
            simp [ins] at h1; exact h1
          subst hc1v
          have hcq : IsC 10 gs m true (11 + q) :=
            const_read 10 gs L.hcl m true q gq hgq (11 + p) hqpin (by simp [hc1, fixBit, hqand])
          obtain ⟨r, hqr_lt, _, hrrc⟩ := L.next m true (restr_nc_all m true) q (List.getElem?_eq_some_iff.mp hgq).1 hcq
          obtain ⟨s', hs', hc'⟩ := L.save3 m true (restr_nc_all m true) p q r (by omega) (by omega) (by omega)
            (rc_input true ⟨g, hgp, hmin⟩) (rc_of_reads ⟨gq, hgq, hqpin⟩ ⟨false, hc1⟩) hrrc
          have := bound_mid_true m hm s' hc'; omega
        · obtain ⟨c0, hc0⟩ := hcp_f
          have hc0v : c0 = true := by
            have h1 := st_val_const 10 gs L.hcl m false (11 + p) c0 hc0 (fun _ => false)
            rw [hval_not, vl_input gs _ m m.isLt] at h1
            simp [ins] at h1; exact h1
          subst hc0v
          have hcq : IsC 10 gs m false (11 + q) :=
            const_read 10 gs L.hcl m false q gq hgq (11 + p) hqpin (by simp [hc0, fixBit, hqor])
          obtain ⟨r, hqr_lt, _, hrrc⟩ := L.next m false (restr_nc_all m false) q (List.getElem?_eq_some_iff.mp hgq).1 hcq
          obtain ⟨s', hs', hc'⟩ := L.save3 m false (restr_nc_all m false) p q r (by omega) (by omega) (by omega)
            (rc_input false ⟨g, hgp, hmin⟩) (rc_of_reads ⟨gq, hgq, hqpin⟩ ⟨true, hc0⟩) hrrc
          have := bound_mid_false m hm s' hc'; omega
    · refine ⟨p, g, h, hgp, ?_, hin_bin, huniq, ?_⟩
      · rcases hor_and with ⟨hand, _⟩ | ⟨hor, _⟩
        · exact Or.inl hand
        · exact Or.inr hor
      · intro ph hheq
        subst hheq
        by_contra hno
        push Not at hno
        have hone : ∀ t, Reads gs t (11 + ph) → t = p := fun t ht => by
          by_contra hne; exact hno t hne ht
        have hphlt : ph < gs.length := by
          have := (L.hcl p g hgp).lt (11 + ph) (by rcases hin_bin with h | h <;> simp [h])
          have hpl := (List.getElem?_eq_some_iff.mp hgp).1
          omega
        have ho2 : o ≠ 11 + ph := by
          intro ho_eq
          obtain ⟨x, hx⟩ := dep_all m
          apply hx
          rw [← L.hev, ← L.hev, ho_eq]
          have hph_p : 11 + ph < 11 + p := (L.hcl p g hgp).lt (11 + ph) (by rcases hin_bin with h | h <;> simp [h])
          exact indep_of_no_read_before gs L.hcl {m} p
            (fun r hr z hz hrz => by
              rw [Finset.mem_singleton.mp hz] at hrz
              have := huniq r hrz; omega)
            (Function.update x m (!x m)) x
            (fun i hi => Function.update_of_ne (fun e => hi (by simp [e])) _ _)
            (11 + ph) hph_p (fun z _ => by have := z.isLt; omega)
        rcases hor_and with ⟨hand, _⟩ | ⟨hor, _⟩
        · have ho1 : o ≠ 11 + p := by
            intro ho_eq
            have hcp := isC_reader L.hcl m p g hgp hmin false (Or.inr (by simp [fixBit, hand]))
            obtain ⟨c, hc⟩ := hcp
            obtain ⟨x, y, hxy⟩ := restr_nc_all m false
            rw [← ho_eq] at hc
            exact hxy ((restr_const L.hcl L.hev m false c hc x).trans (restr_const L.hcl L.hev m false c hc y).symm)
          have h3 := (PEqualNP.MetaComplexity.EdgeFn.stmtAnd 10 targetF gs o p ph m g m L
            (restr_nc_all m) (dep_all m) hgp hand hin_bin (Or.inl rfl) hphlt hone ho1 ho2).1 rfl
          obtain ⟨s', hs', hc'⟩ := h3
          have := bound_mid_false m hm s' hc'; omega
        · have ho1 : o ≠ 11 + p := by
            intro ho_eq
            have hcp := isC_reader L.hcl m p g hgp hmin true (Or.inr (by simp [fixBit, hor]))
            obtain ⟨c, hc⟩ := hcp
            obtain ⟨x, y, hxy⟩ := restr_nc_all m true
            rw [← ho_eq] at hc
            exact hxy ((restr_const L.hcl L.hev m true c hc x).trans (restr_const L.hcl L.hev m true c hc y).symm)
          obtain ⟨s', hs', hc'⟩ := or_partner_drop3 10 targetF gs o p ph g m L
            (restr_nc_all m true) hgp hor hin_bin hphlt hone ho1 ho2
          have := bound_mid_true m hm s' hc'; omega
  have hexInt : ∃ k, ∃ z ∈ IntV, Reads gs k z := by
    obtain ⟨p, hp⟩ := L.dep_read 2 (dep_all 2) (restr_nc_all 2)
    exact ⟨p, 2, by decide, hp⟩
  let k := Nat.find hexInt
  have hk_spec : ∃ z ∈ IntV, Reads gs k z := Nat.find_spec hexInt
  have hk_min : ∀ r < k, ∀ z ∈ IntV, ¬ Reads gs r z := by
    intro r hr z hz hrz
    exact Nat.find_min hexInt hr ⟨z, hz, hrz⟩
  obtain ⟨z, hzInt, hkz⟩ := hk_spec
  have hz0 : z ≠ 0 := (by decide : ∀ z : Fin 11, z ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset (Fin 11)) → z ≠ 0) z hzInt
  have hz1 : z ≠ 1 := (by decide : ∀ z : Fin 11, z ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset (Fin 11)) → z ≠ 1) z hzInt
  have hsplit_z : z ∈ Nbr ∨ z ∈ Mid := (by decide : ∀ z : Fin 11, z ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset (Fin 11)) → z ∈ ({2, 4, 5, 7, 8, 10} : Finset (Fin 11)) ∨ z ∈ ({3, 6, 9} : Finset (Fin 11))) z hzInt
  have hk_bin : ∃ g h, gs[k]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      (g.inputs = [(z : ℕ), h] ∨ g.inputs = [h, (z : ℕ)]) ∧
      (∀ q, Reads gs q z → q = k) ∧
      (z ∈ Nbr → g.op = GateOp.or) ∧
      (z ∈ Mid → ∀ ph, h = 11 + ph → ∃ r, r ≠ k ∧ Reads gs r h) := by
    rcases hsplit_z with hzN | hzM
    · obtain ⟨p, g, hgp, hor, hzin, huniq⟩ := hStep1 z hzN
      have hkp : k = p := huniq k hkz
      subst hkp
      rcases gate_cases gs L.hcl k g hgp z hzin with ⟨hnot, _, _⟩ | ⟨h, hin, _⟩
      · rw [hor] at hnot; cases hnot
      · exact ⟨g, h, hgp, Or.inr hor, hin, huniq, fun _ => hor, fun hzM => ((by decide : ∀ z : Fin 11, z ∈ ({2, 4, 5, 7, 8, 10} : Finset (Fin 11)) → z ∉ ({3, 6, 9} : Finset (Fin 11))) z hzN hzM).elim⟩
    · obtain ⟨p, g, h, hgp, hop, hin, huniq, hsh⟩ := hStep2 z hzM
      have hkp : k = p := huniq k hkz
      subst hkp
      exact ⟨g, h, hgp, hop, hin, huniq, fun hzN => ((by decide : ∀ z : Fin 11, z ∈ ({2, 4, 5, 7, 8, 10} : Finset (Fin 11)) → z ∉ ({3, 6, 9} : Finset (Fin 11))) z hzN hzM).elim, fun _ => hsh⟩
  obtain ⟨gk, h, hgk, hkop, hkin, hkuniq, hknbr, hkmid⟩ := hk_bin
  have hlt_h : h < 11 + k := (L.hcl k gk hgk).lt h (by rcases hkin with e | e <;> simp [e])
  have hklen : k < gs.length := (List.getElem?_eq_some_iff.mp hgk).1
  have hblock : ∀ x : Fin 11 → Bool, vl gs x h = fixBit gk → x z = false →
      targetF x = targetF (Function.update x z true) := by
    intro x hxh hxz
    have hh_eq : vl gs (Function.update x z true) h = vl gs x h := by
      have hz_ne_h : h ≠ (z : ℕ) := by
        intro e
        subst e
        apply L.no_alias hfnc k hklen z (by have := z.isLt; omega)
        intro u
        rw [vl_gate gs L.hcl u k gk hgk]
        rcases hkin with e1 | e1 <;> rw [e1] <;> rcases hkop with ho | ho <;> rw [ho] <;> simp [GateOp.eval]
      exact agree_of_sole_reader gs L.hcl z k gk hgk hkuniq (Function.update x z true) x
        (fun i hi => Function.update_of_ne hi _ _)
        (by
          rw [vl_gate gs L.hcl _ k gk hgk, vl_gate gs L.hcl _ k gk hgk]
          have hh1 : vl gs (Function.update x z true) h = fixBit gk := by
            have := indep_of_no_read_before gs L.hcl {z} k
              (fun r hr z' hz' hrz => by rw [Finset.mem_singleton.mp hz'] at hrz; have := hkuniq r hrz; omega)
              (Function.update x z true) x (fun i hi => Function.update_of_ne (fun e => hi (by simp [e])) _ _)
              h hlt_h (fun z' hz' => by rw [Finset.mem_singleton.mp hz']; exact hz_ne_h)
            rw [this, hxh]
          have hh2 : vl gs x h = fixBit gk := hxh
          rcases hkin with e1 | e1 <;> rw [e1] <;> rcases hkop with ho | ho <;> rw [ho] <;> simp [fixBit, ho] at hh1 hh2 <;> simp [GateOp.eval, hh1, hh2])
        h hz_ne_h
    have hkeq : vl gs x (11 + k) = vl gs (Function.update x z true) (11 + k) := by
      rw [vl_gate gs L.hcl _ k gk hgk, vl_gate gs L.hcl _ k gk hgk]
      have hh1 : vl gs (Function.update x z true) h = fixBit gk := by rw [hh_eq, hxh]
      rcases hkin with e1 | e1 <;> rw [e1] <;> rcases hkop with ho | ho <;> rw [ho] <;> simp [fixBit, ho] at hxh hh1 <;> simp [GateOp.eval, hxh, hh1]
    rw [← L.hev, ← L.hev]
    exact agree_of_sole_reader gs L.hcl z k gk hgk hkuniq x (Function.update x z true)
      (fun i hi => (Function.update_of_ne hi _ _).symm) hkeq o (by
        intro hoz
        obtain ⟨u, hu⟩ := not_pair_witness z (if z = 2 then 3 else 2) hz0 hz1 (by split_ifs <;> intro e <;> simp_all) false
        have h1 : targetF u = u z := by rw [← L.hev, hoz, vl_input gs u z z.isLt]
        have h2 : targetF (Function.update u z true) = true := by rw [← L.hev, hoz, vl_input gs _ z z.isLt]; simp
        have h3 : targetF (pt11 {z}) = true := by rw [← L.hev, hoz, vl_input gs _ z z.isLt]; simp [pt11]
        have h4 : targetF (pt11 {z}) = false := by
          rw [targetF_eq_graph, decide_eq_false_iff_not]
          rintro ⟨i, j, hij, hi, hj⟩
          simp only [pt11, decide_eq_true_eq, Finset.mem_singleton] at hi hj
          subst hi; subst hj; exact G.loopless.irrefl _ hij
        rw [h4] at h3; cases h3)
  have hge11 : 11 ≤ h := by
    by_contra hlt11
    let u : Fin 11 := ⟨h, by omega⟩
    have huz : u ≠ z := by
      intro e
      have he : h = (z : ℕ) := congrArg Fin.val e
      apply L.no_alias hfnc k hklen z (by have := z.isLt; omega)
      intro x
      rw [vl_gate gs L.hcl x k gk hgk]
      rcases hkin with e1 | e1 <;> rw [e1, he] <;> rcases hkop with ho | ho <;> rw [ho] <;> simp [GateOp.eval]
    obtain ⟨x, hxu, hxz, hfx0, hfx1⟩ := not_pair_witness z u hz0 hz1 huz (fixBit gk)
    have hxh : vl gs x h = fixBit gk := by rw [vl_input gs x h (by omega)]; exact hxu
    have heq := hblock x hxh hxz
    rw [hfx0, hfx1] at heq; cases heq
  obtain ⟨ph, rfl⟩ : ∃ ph, h = 11 + ph := ⟨h - 11, by omega⟩
  have hph_k : ph < k := by omega
  have hph_len : ph < gs.length := by omega
  have hdep01 : ∀ x y : Fin 11 → Bool, x 0 = y 0 → x 1 = y 1 → vl gs x (11 + ph) = vl gs y (11 + ph) := by
    intro x y h0 h1
    exact indep_of_no_read_before gs L.hcl IntV k hk_min x y
      (fun i hi => by
        have : i = 0 ∨ i = 1 := by revert i hi; decide
        rcases this with rfl | rfl <;> assumption)
      (11 + ph) (by omega) (fun z' _ => by have := z'.isLt; omega)
  rcases hsplit_z with hzN | hzM
  · have hor := hknbr hzN
    have hfb : fixBit gk = true := by simp [fixBit, hor]
    apply L.no_const hfnc ph hph_len false
    intro x
    obtain ⟨w, hw0, hw1, hwz, hfw0, hfw1⟩ := nbr_four_witnesses z hzN (x 0) (x 1)
    rw [hdep01 x w hw0.symm hw1.symm]
    cases hv : vl gs w (11 + ph) with
    | false => rfl
    | true =>
      have heq := hblock w (by rw [hv, hfb]) hwz
      rw [hfw0, hfw1] at heq; cases heq
  · have hnot11_val : ∀ x : Fin 11 → Bool, ¬ (x 0 = true ∧ x 1 = true) → vl gs x (11 + ph) = !fixBit gk := by
      intro x hnot11
      obtain ⟨w, hw0, hw1, hwz, hfw0, hfw1⟩ := mid_three_witnesses z hzM (x 0) (x 1) hnot11
      rw [hdep01 x w hw0.symm hw1.symm]
      by_contra hne
      have hvf : vl gs w (11 + ph) = fixBit gk := by
        revert hne; cases vl gs w (11 + ph) <;> cases fixBit gk <;> simp
      have heq := hblock w hvf hwz
      rw [hfw0, hfw1] at heq; cases heq
    have hval_0false : ∀ x : Fin 11 → Bool, vl gs (Function.update x 0 false) (11 + ph) = !fixBit gk := by
      intro x
      exact hnot11_val _ (by simp)
    have h11_val : vl gs (pt11 {0, 1}) (11 + ph) = fixBit gk := by
      by_contra hne
      have h11f : vl gs (pt11 {0, 1}) (11 + ph) = !fixBit gk := by
        revert hne; cases vl gs (pt11 {0, 1}) (11 + ph) <;> cases fixBit gk <;> simp
      apply L.no_const hfnc ph hph_len (!fixBit gk)
      intro x
      by_cases h11 : x 0 = true ∧ x 1 = true
      · rw [hdep01 x (pt11 {0, 1}) (by rw [h11.1]; decide) (by rw [h11.2]; decide), h11f]
      · exact hnot11_val x h11
    obtain ⟨r, hrk, hrr⟩ := hkmid hzM ph rfl
    have hphr : ph < r := by
      have := reads_lt L.hcl hrr; omega
    have hrlen : r < gs.length := reads_len hrr
    have hkr_ne : k ≠ r := Ne.symm hrk
    have hphk_ne : ph ≠ k := by omega
    have hphr_ne : ph ≠ r := by omega
    have hkm : ∃ g, gs[k]? = some g ∧ (0 ∈ g.inputs ∨ 11 + ph ∈ g.inputs) :=
      ⟨gk, hgk, Or.inr (by rcases hkin with e | e <;> simp [e])⟩
    have hrm : ∃ g, gs[r]? = some g ∧ (0 ∈ g.inputs ∨ 11 + ph ∈ g.inputs) := by
      obtain ⟨gr, hgr, hrin⟩ := hrr
      exact ⟨gr, hgr, Or.inr hrin⟩
    by_cases hph0 : Reads gs ph 0
    · have hex_t : ∃ t, t ≠ ph ∧ Reads gs t 0 := by
        by_contra hno
        push Not at hno
        have huniq0 : ∀ q, Reads gs q 0 → q = ph := fun q hq => by
          by_contra hne; exact hno q hne hq
        obtain ⟨gph, hgph, _⟩ := hph0
        have heq_ph : vl gs (pt11 {2}) (11 + ph) = vl gs (pt11 {0, 2}) (11 + ph) := by
          rw [hnot11_val (pt11 {2}) (by decide), hnot11_val (pt11 {0, 2}) (by decide)]
        have heq_o : vl gs (pt11 {2}) o = vl gs (pt11 {0, 2}) o := by
          refine agree_of_sole_reader gs L.hcl 0 ph gph hgph huniq0 (pt11 {2}) (pt11 {0, 2}) ?_ heq_ph o ?_
          · intro i hi
            simp only [pt11, Finset.mem_insert, Finset.mem_singleton]
            by_cases hi2 : i = 2
            · subst hi2; decide
            · simp [hi, hi2]
          · intro ho0
            have h1 : targetF (pt11 {0}) = true := by rw [← L.hev, ho0]; change vl gs (pt11 {0}) 0 = true; rw [vl_input gs _ 0 (by omega)]; simp [pt11]
            have h2 : targetF (pt11 {0}) = false := by decide
            rw [h2] at h1; cases h1
        rw [L.hev, L.hev] at heq_o
        have h1 : targetF (pt11 {2}) = false := by decide
        have h2 : targetF (pt11 {0, 2}) = true := by decide
        rw [h1, h2] at heq_o; cases heq_o
      obtain ⟨t, htph, ht0⟩ := hex_t
      have htk : t ≠ k := by
        rintro rfl
        obtain ⟨g0, hg0, h0in⟩ := ht0
        rw [hgk] at hg0; cases hg0
        rcases hkin with e | e <;> rw [e] at h0in <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h0in
        · rcases h0in with h0z | h0ph
          · exact hz0 (Fin.ext h0z.symm)
          · omega
        · rcases h0in with h0ph | h0z
          · omega
          · exact hz0 (Fin.ext h0z.symm)
      have htr : t ≠ r := fun e => L.no_tri hfnc ph r 0 hph0 (e ▸ ht0) hrr
      have htlen : t < gs.length := reads_len ht0
      obtain ⟨gt, hgt, ht0in⟩ := ht0
      obtain ⟨s', hs', hc'⟩ := elimOvr_drop4 gs o ph (!fixBit gk) L hval_0false ph k r t
        hphk_ne hphr_ne (Ne.symm htph) hkr_ne (Ne.symm htk) (Ne.symm htr)
        hph_len hklen hrlen htlen (Or.inl rfl) (Or.inr hkm) (Or.inr hrm) (Or.inr ⟨gt, hgt, Or.inl ht0in⟩)
      have := bound_0_false s' hc'
      omega
    · have hex_a : ∃ a < ph, Reads gs a 0 := by
        by_contra hno
        push Not at hno
        have heq_ph : vl gs (pt11 {1}) (11 + ph) = vl gs (pt11 {0, 1}) (11 + ph) := by
          exact indep_of_no_read_before gs L.hcl {0} (ph + 1)
            (fun r hr z' hz' hrz => by
              rw [Finset.mem_singleton.mp hz'] at hrz
              by_cases hrph : r = ph
              · subst hrph; exact hph0 hrz
              · exact hno r (by omega) hrz)
            (pt11 {1}) (pt11 {0, 1})
            (fun i hi => by
              have hi0 : i ≠ 0 := by simpa using hi
              simp only [pt11, Finset.mem_insert, Finset.mem_singleton, hi0, false_or])
            (11 + ph) (by omega) (fun z' hz' => by rw [Finset.mem_singleton.mp hz']; omega)
        rw [hnot11_val (pt11 {1}) (by decide), h11_val] at heq_ph
        cases hfb : fixBit gk <;> rw [hfb] at heq_ph <;> cases heq_ph
      obtain ⟨a, haph, ha0⟩ := hex_a
      have halen : a < gs.length := by omega
      obtain ⟨ga, hga, ha0in⟩ := ha0
      obtain ⟨s', hs', hc'⟩ := elimOvr_drop4 gs o ph (!fixBit gk) L hval_0false a ph k r
        (by omega) (by omega) (by omega) hphk_ne hphr_ne hkr_ne
        halen hph_len hklen hrlen (Or.inr ⟨ga, hga, Or.inl ha0in⟩) (Or.inl rfl) (Or.inr hkm) (Or.inr hrm)
      have := bound_0_false s' hc'
      omega

end PEqualNP.Outside.LMeta657

theorem PEqualNP.Outside.L_meta_657 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 11 (fun x : Fin 11 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) || (x 0 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && x 1)) s → 16 ≤ s :=
  PEqualNP.Outside.LMeta657.main_lower
