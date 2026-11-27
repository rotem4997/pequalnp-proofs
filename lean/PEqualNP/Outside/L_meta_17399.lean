import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17399

private abbrev V := Fin 13
private abbrev Adj (a b : V) : Prop :=
  a = b ∨ a = b+1 ∨ a = b+3 ∨ a = b+9

private def neigh (rev : Bool) (i : V) : List V :=
  if rev then [i,i-1,i-3,i-9] else [i,i+1,i+3,i+9]

set_option maxRecDepth 10000 in
private theorem neigh_spec : ∀ i j : V,
    (j ∈ neigh false i ↔ Adj j i) ∧ (j ∈ neigh true i ↔ Adj i j) := by
  decide +kernel

private theorem neigh_nodup : ∀ (rev : Bool) (i : V), (neigh rev i).Nodup := by
  decide +kernel

private def clear (rev : Bool) (m : ℕ) (i : V) : Bool :=
  !(neigh rev i).any (fun p => m.testBit p.val)

private def arcCode (rev : Bool) (m : ℕ) : Bool :=
  (List.finRange 13).all fun i =>
    (neigh rev i).countP (fun p => m.testBit p.val) ≤ 2

private def certified (m : ℕ) : Bool :=
  (!arcCode false m || ((List.finRange 13).all fun p =>
    (List.finRange 13).any fun l => clear false m l && !(neigh true p |>.contains l))) &&
  (!arcCode true m || ((List.finRange 13).all fun l =>
    (List.finRange 13).any fun p => clear true m p && !(neigh false l |>.contains p)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk0 : ∀ j : Fin 256, certified (0*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk1 : ∀ j : Fin 256, certified (1*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk2 : ∀ j : Fin 256, certified (2*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk3 : ∀ j : Fin 256, certified (3*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk4 : ∀ j : Fin 256, certified (4*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk5 : ∀ j : Fin 256, certified (5*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk6 : ∀ j : Fin 256, certified (6*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk7 : ∀ j : Fin 256, certified (7*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk8 : ∀ j : Fin 256, certified (8*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk9 : ∀ j : Fin 256, certified (9*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk10 : ∀ j : Fin 256, certified (10*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk11 : ∀ j : Fin 256, certified (11*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk12 : ∀ j : Fin 256, certified (12*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk13 : ∀ j : Fin 256, certified (13*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk14 : ∀ j : Fin 256, certified (14*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk15 : ∀ j : Fin 256, certified (15*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk16 : ∀ j : Fin 256, certified (16*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk17 : ∀ j : Fin 256, certified (17*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk18 : ∀ j : Fin 256, certified (18*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk19 : ∀ j : Fin 256, certified (19*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk20 : ∀ j : Fin 256, certified (20*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk21 : ∀ j : Fin 256, certified (21*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk22 : ∀ j : Fin 256, certified (22*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk23 : ∀ j : Fin 256, certified (23*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk24 : ∀ j : Fin 256, certified (24*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk25 : ∀ j : Fin 256, certified (25*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk26 : ∀ j : Fin 256, certified (26*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk27 : ∀ j : Fin 256, certified (27*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk28 : ∀ j : Fin 256, certified (28*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk29 : ∀ j : Fin 256, certified (29*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk30 : ∀ j : Fin 256, certified (30*256+j.val) = true := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem chunk31 : ∀ j : Fin 256, certified (31*256+j.val) = true := by
  decide +kernel
private theorem certified_all (m : ℕ) (hm : m < 8192) : certified m = true := by
  have hq : m / 256 < 32 := by omega
  let q : Fin 32 := ⟨m/256,hq⟩
  let r : Fin 256 := ⟨m%256,by omega⟩
  have hc : ∀ q : Fin 32, certified (q.val*256+r.val) = true := by
    intro q
    fin_cases q
    · exact chunk0 r
    · exact chunk1 r
    · exact chunk2 r
    · exact chunk3 r
    · exact chunk4 r
    · exact chunk5 r
    · exact chunk6 r
    · exact chunk7 r
    · exact chunk8 r
    · exact chunk9 r
    · exact chunk10 r
    · exact chunk11 r
    · exact chunk12 r
    · exact chunk13 r
    · exact chunk14 r
    · exact chunk15 r
    · exact chunk16 r
    · exact chunk17 r
    · exact chunk18 r
    · exact chunk19 r
    · exact chunk20 r
    · exact chunk21 r
    · exact chunk22 r
    · exact chunk23 r
    · exact chunk24 r
    · exact chunk25 r
    · exact chunk26 r
    · exact chunk27 r
    · exact chunk28 r
    · exact chunk29 r
    · exact chunk30 r
    · exact chunk31 r
  have h := hc q
  have he : q.val*256+r.val = m := by dsimp [q,r]; omega
  rwa [he] at h


private def avoiding (E : V → V → Prop) [DecidableRel E] (S : Finset V) : Finset V :=
  Finset.univ.filter (fun b => ∀ a ∈ S, ¬ E a b)

private def arc (E : V → V → Prop) [DecidableRel E] (S : Finset V) : Prop :=
  ∀ b, (S.filter (fun a => E a b)).card ≤ 2

private def noPencil (E : V → V → Prop) (S : Finset V) : Prop :=
  ∀ b, ∃ a ∈ S, ¬ E a b

private theorem card_filter_neigh (rev : Bool) (S : Finset V) (i : V) :
    ((neigh rev i).countP (fun p => decide (p ∈ S))) =
      (S.filter (fun p => p ∈ neigh rev i)).card := by
  let l := (neigh rev i).filter (fun p => decide (p ∈ S))
  have hl : l.toFinset = S.filter (fun p => p ∈ neigh rev i) := by
    ext x
    simp [l, and_comm]
  rw [← hl, List.toFinset_card_of_nodup ((neigh_nodup rev i).filter _)]
  exact List.countP_eq_length_filter

private theorem mask_for (S : Finset V) : ∃ m < 8192, ∀ i : V, m.testBit i.val = decide (i ∈ S) := by
  let l := List.ofFn (fun i : V => decide (i ∈ S))
  let x := BitVec.ofBoolListLE l
  refine ⟨x.toNat, by simpa [x,l] using x.isLt, ?_⟩
  intro i
  change x.getLsbD i.val = _
  rw [BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD]
  change (List.ofFn (fun j : V => decide (j ∈ S)))[i.val]?.getD false = _
  rw [List.getElem?_ofFn, dite_eq_left i.isLt]
  rfl

private theorem no_pencil_both (S : Finset V) :
    (arc Adj S → noPencil (fun l p => Adj p l) (avoiding Adj S)) ∧
    (arc (fun l p => Adj p l) S → noPencil Adj (avoiding (fun l p => Adj p l) S)) := by
  obtain ⟨m, hm, hbit⟩ := mask_for S
  have hcheck := certified_all m hm
  simp only [certified, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.all_eq_true, List.any_eq_true] at hcheck
  constructor
  · intro ha p
    have hc : arcCode false m = true := by
      apply List.all_eq_true.mpr
      intro l _
      simp only [decide_eq_true_eq, hbit, card_filter_neigh]
      have he : S.filter (fun q => q ∈ neigh false l) = S.filter (fun q => Adj q l) := by
        ext q
        simp only [Finset.mem_filter, (neigh_spec l q).1]
      rw [he]
      exact ha l
    have hp := hcheck.1.resolve_left (by simp [hc]) p (by simp)
    obtain ⟨l, _, hh⟩ := hp
    have hcl := hh.1
    have hnl := hh.2
    refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · intro q hq h
      have hmem := (neigh_spec l q).1.mpr h
      have he : (neigh false l).any (fun q => m.testBit q.val) = true :=
        List.any_eq_true.mpr ⟨q, hmem, (hbit q).trans (decide_eq_true hq)⟩
      simp [clear, he] at hcl
    · simpa only [List.contains_eq_mem, decide_eq_false_iff_not,
        (neigh_spec p l).2] using hnl
  · intro ha l
    have hc : arcCode true m = true := by
      apply List.all_eq_true.mpr
      intro p _
      simp only [decide_eq_true_eq, hbit, card_filter_neigh]
      have he : S.filter (fun q => q ∈ neigh true p) = S.filter (fun q => Adj p q) := by
        ext q
        simp only [Finset.mem_filter, (neigh_spec p q).2]
      rw [he]
      exact ha p
    have hl := hcheck.2.resolve_left (by simp [hc]) l (by simp)
    obtain ⟨p, _, hh⟩ := hl
    have hcp := hh.1
    have hnp := hh.2
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · intro q hq h
      have hmem := (neigh_spec p q).2.mpr h
      have he : (neigh true p).any (fun q => m.testBit q.val) = true :=
        List.any_eq_true.mpr ⟨q, hmem, (hbit q).trans (decide_eq_true hq)⟩
      simp [clear, he] at hcp
    · simpa only [List.contains_eq_mem, decide_eq_false_iff_not,
        (neigh_spec l p).1] using hnp

private theorem common_line : ∀ a b : V, ∃ l : V, Adj a l ∧ Adj b l := by decide +kernel

set_option maxRecDepth 10000 in
private theorem unique_line : ∀ a b : V, a ≠ b →
    ((Finset.univ : Finset V).filter (fun l => Adj a l ∧ Adj b l)).card ≤ 1 := by decide +kernel

private theorem extend_arc (S Y : Finset V) (hS : arc Adj S) (hSY : S ⊆ Y)
    (hY : noPencil Adj Y) : ∃ X, S ⊆ X ∧ X ⊆ Y ∧ arc Adj X ∧ 3 ≤ X.card := by
  classical
  let T := Y.powerset.filter fun X => S ⊆ X ∧ arc Adj X
  have hh : S ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSY,Finset.Subset.refl _,hS⟩
  obtain ⟨X,hX,hmax⟩ := Finset.exists_max_image T Finset.card ⟨S,hh⟩
  have h := Finset.mem_filter.mp hX
  have hXY := Finset.mem_powerset.mp h.1
  have hcontain := h.2.1
  have hArc := h.2.2
  refine ⟨X,hcontain,hXY,hArc,?_⟩
  by_contra! hsmall
  have grow (p : V) (hp : p ∈ Y) (hn : p ∉ X) (ha : arc Adj (insert p X)) : False := by
    have ht : insert p X ∈ T := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr (Finset.insert_subset_iff.mpr ⟨hp,hXY⟩),
        hcontain.trans (Finset.subset_insert _ _),ha⟩
    have he := hmax _ ht
    rw [Finset.card_insert_of_notMem hn] at he
    omega
  by_cases hh : X.card ≤ 1
  · obtain ⟨a,ha⟩ := Finset.card_le_one_iff_subset_singleton.mp hh
    obtain ⟨l,hl,_⟩ := common_line a a
    obtain ⟨p,hp,hn⟩ := hY l
    have hnot : p ∉ X := by
      intro hx
      have he : p = a := Finset.mem_singleton.mp (ha hx)
      exact hn (he ▸ hl)
    exact grow p hp hnot fun l =>
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (by
        rw [Finset.card_insert_of_notMem hnot]
        omega)
  · obtain ⟨a,b,hab,hXeq⟩ := Finset.card_eq_two.mp (by omega : X.card=2)
    obtain ⟨l,hal,hbl⟩ := common_line a b
    obtain ⟨p,hp,hn⟩ := hY l
    have hnot : p ∉ X := by
      simp only [hXeq,Finset.mem_insert,Finset.mem_singleton]
      rintro (rfl | rfl) <;> contradiction
    apply grow p hp hnot
    intro k
    by_cases he : Adj p k
    · have hnab : ¬(Adj a k ∧ Adj b k) := by
        intro hb
        have hm := Finset.card_le_one.mp (unique_line a b hab) k
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩) l
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hal,hbl⟩)
        exact hn (hm ▸ he)
      rw [hXeq,Finset.filter_insert]
      simp only [ite_eq_left he]
      by_cases ha : Adj a k <;> by_cases hb : Adj b k
      · exact (hnab ⟨ha,hb⟩).elim
      · exact (Finset.card_insert_le _ _).trans (by simp [Finset.filter_insert,Finset.filter_singleton,ha,hb])
      · exact (Finset.card_insert_le _ _).trans (by simp [Finset.filter_insert,Finset.filter_singleton,ha,hb])
      · exact (Finset.card_insert_le _ _).trans (by simp [Finset.filter_insert,Finset.filter_singleton,ha,hb])
    · simpa [Finset.filter_insert,he] using hArc k

end PEqualNP.Outside.L_meta_17399

open PEqualNP.Outside.L_meta_17399

theorem PEqualNP.Outside.L_meta_17399 : (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; ∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∈ x3, ∀ x7 ∈ x4, ¬x1 x5 x7) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x1 x7 x6}.card ≤ (2 : ℕ)) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x1 x7 x8}.card ≤ (2 : ℕ)) → ∃ (x8 : Finset (Fin (13 : ℕ))), x3 ⊆ x8 ∧ x4 ⊆ x2 x8 ∧ (∀ x9 ∉ x8, ∃ x11 ∈ x2 x8, x1 x9 x11) ∧ (¬∃ (x9 : Fin (13 : ℕ)), ∀ x10 ∈ x8, x1 x10 x9) ∧ ¬∃ (x9 : Fin (13 : ℕ)), ∀ x10 ∈ x2 x8, x1 x9 x10) := by
  dsimp only
  intro U W H hU hW
  have hsub : U ⊆ avoiding (fun l p => Adj p l) W := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun l hl => H p hp l hl⟩
  obtain ⟨S,hUS,hSW,hS,hScard⟩ := extend_arc U _ hU hsub ((no_pencil_both W).2 hW)
  let R := avoiding Adj S
  let X := avoiding (fun l p => Adj p l) R
  have hSX : S ⊆ X := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun l hl => (Finset.mem_filter.mp hl).2 p hp⟩
  have hX : avoiding Adj X = R := by
    ext l
    constructor
    · intro hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => (Finset.mem_filter.mp hl).2 p (hSX hp)⟩
    · intro hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => (Finset.mem_filter.mp hp).2 l hl⟩
  have hWR : W ⊆ R := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp => (Finset.mem_filter.mp (hSW hp)).2 l hl⟩
  change ∃ X, U ⊆ X ∧ W ⊆ avoiding Adj X ∧
    (∀ p ∉ X, ∃ l ∈ avoiding Adj X, Adj p l) ∧
    (¬∃ l, ∀ p ∈ X, Adj p l) ∧ ¬∃ p, ∀ l ∈ avoiding Adj X, Adj p l
  refine ⟨X,hUS.trans hSX,by simpa only [hX] using hWR,?_,?_,?_⟩
  · rw [hX]
    intro p hp
    by_contra hh
    exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun l hl h => hh ⟨l,hl,h⟩⟩)
  · rintro ⟨l,hl⟩
    have he : S.filter (fun p => Adj p l) = S :=
      Finset.filter_eq_self.mpr (fun p hp => hl p (hSX hp))
    have ht := hS l
    rw [he] at ht
    omega
  · rw [hX]
    rintro ⟨p,hp⟩
    obtain ⟨l,hl,h⟩ := (no_pencil_both S).1 hS p
    exact h (hp l hl)

