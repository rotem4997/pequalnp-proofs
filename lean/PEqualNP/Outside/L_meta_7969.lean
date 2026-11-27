import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7969

open PEqualNP.HeptadCover

private abbrev Index := Fin 13
private abbrev Indices := Finset Index

-- An explicit form of the thirteen Singer lines for the finite checks.
private def line (l : Index) : Indices :=
  match l.val with
  | 0 => {0, 1, 3, 9}
  | 1 => {1, 2, 4, 10}
  | 2 => {2, 3, 5, 11}
  | 3 => {3, 4, 6, 12}
  | 4 => {0, 4, 5, 7}
  | 5 => {1, 5, 6, 8}
  | 6 => {2, 6, 7, 9}
  | 7 => {3, 7, 8, 10}
  | 8 => {4, 8, 9, 11}
  | 9 => {5, 9, 10, 12}
  | 10 => {0, 6, 10, 11}
  | 11 => {1, 7, 11, 12}
  | _ => {0, 2, 8, 12}

private lemma line_eq (l : Index) : line l = singerLines3 l := by
  fin_cases l <;> decide +kernel

private abbrev PointsOk (P : Indices) : Prop :=
  ∀ l : Index, (P ∩ line l).card ≤ 2

private abbrev LinesOk (L : Indices) : Prop :=
  ∀ p : Index, (L.filter fun l => p ∈ line l).card ≤ 2

private abbrev Bounds (P L : Indices) : Prop :=
  L.card ≤ 3 ∧ PointsOk P ∧ LinesOk L

private def offLines (P : Indices) : Indices :=
  Finset.univ.filter fun l => Disjoint (line l) P

private lemma offLines_eq (P : Indices) : offLines P = missLines singerLines3 P := by
  simp only [offLines, missLines, line_eq]

-- Entries pair a quadrangle with a bit mask of its missing lines.
-- Row a covers the eligible pairs whose point set is {0, a, b}.
-- For a = 0 only the singleton point set is needed.
private def pointRow (a : Index) : List (List Index × ℕ) :=
  match a.val with
  | 0 => [([0, 1, 2, 5], 392),
      ([0, 1, 4, 8], 580),
      ([0, 2, 3, 4], 2592),
      ([0, 3, 5, 6], 2306),
      ([0, 3, 10, 12], 352),
      ([0, 4, 6, 9], 2180),
      ([0, 5, 8, 10], 2120),
      ([0, 5, 11, 12], 194),
      ([0, 7, 8, 9], 14),
      ([0, 1, 2, 6], 896),
      ([0, 2, 7, 11], 552),
      ([0, 3, 7, 11], 546),
      ([0, 4, 9, 12], 164),
      ([0, 1, 6, 7], 772),
      ([0, 1, 2, 7], 776),
      ([0, 1, 2, 11], 648),
      ([0, 1, 4, 6], 644),
      ([0, 1, 4, 11], 704),
      ([0, 1, 4, 12], 196),
      ([0, 1, 5, 10], 328),
      ([0, 1, 5, 11], 200),
      ([0, 1, 5, 12], 448),
      ([0, 1, 6, 12], 388),
      ([0, 1, 7, 8], 524),
      ([0, 1, 7, 10], 268),
      ([0, 1, 8, 10], 76),
      ([0, 1, 8, 11], 584),
      ([0, 1, 10, 12], 324),
      ([0, 2, 3, 6], 2816),
      ([0, 2, 3, 7], 800),
      ([0, 2, 3, 10], 2336),
      ([0, 2, 4, 6], 2688),
      ([0, 2, 4, 9], 2208),
      ([0, 2, 4, 11], 672),
      ([0, 2, 5, 6], 2432),
      ([0, 2, 5, 9], 2184),
      ([0, 2, 5, 10], 2312),
      ([0, 2, 7, 10], 296),
      ([0, 2, 9, 10], 2088),
      ([0, 2, 9, 11], 168),
      ([0, 3, 4, 8], 2624),
      ([0, 3, 4, 10], 2144),
      ([0, 3, 4, 11], 608),
      ([0, 3, 5, 8], 2114),
      ([0, 3, 5, 10], 2368),
      ([0, 3, 5, 12], 322),
      ([0, 3, 6, 7], 770),
      ([0, 3, 6, 8], 2562),
      ([0, 3, 7, 12], 290),
      ([0, 3, 8, 11], 578),
      ([0, 3, 11, 12], 98),
      ([0, 4, 6, 8], 2564),
      ([0, 4, 8, 10], 2116),
      ([0, 4, 9, 10], 2084),
      ([0, 4, 10, 12], 100),
      ([0, 4, 11, 12], 224),
      ([0, 5, 6, 9], 2178),
      ([0, 5, 6, 12], 386),
      ([0, 5, 8, 9], 2058),
      ([0, 5, 8, 11], 74),
      ([0, 5, 9, 11], 138),
      ([0, 6, 7, 8], 518),
      ([0, 6, 7, 12], 262),
      ([0, 6, 8, 9], 2054),
      ([0, 6, 9, 12], 134),
      ([0, 7, 8, 11], 522),
      ([0, 7, 9, 10], 44),
      ([0, 7, 9, 11], 42),
      ([0, 7, 9, 12], 38),
      ([0, 7, 10, 12], 292),
      ([0, 8, 9, 10], 2060),
      ([0, 9, 11, 12], 162)]
  | 1 => [([0, 1, 2, 5], 392),
      ([0, 1, 4, 8], 580),
      ([0, 1, 6, 7], 772),
      ([0, 1, 10, 12], 324),
      ([0, 1, 2, 11], 648),
      ([0, 1, 4, 12], 196),
      ([0, 1, 8, 10], 76),
      ([0, 1, 5, 11], 200),
      ([0, 1, 2, 6], 896),
      ([0, 1, 2, 7], 776)]
  | 2 => [([0, 2, 3, 4], 2592),
      ([0, 2, 5, 6], 2432),
      ([0, 2, 7, 10], 296),
      ([0, 2, 9, 11], 168),
      ([0, 1, 2, 6], 896),
      ([0, 2, 5, 9], 2184),
      ([0, 2, 7, 11], 552),
      ([0, 2, 3, 10], 2336),
      ([0, 2, 4, 6], 2688)]
  | 3 => [([0, 3, 4, 8], 2624),
      ([0, 3, 7, 12], 290),
      ([0, 3, 5, 6], 2306),
      ([0, 3, 4, 10], 2144),
      ([0, 3, 7, 11], 546),
      ([0, 3, 5, 12], 322),
      ([0, 2, 3, 6], 2816),
      ([0, 3, 8, 11], 578),
      ([0, 2, 3, 10], 2336)]
  | 4 => [([0, 4, 6, 8], 2564),
      ([0, 4, 11, 12], 224),
      ([0, 4, 9, 10], 2084),
      ([0, 4, 6, 9], 2180),
      ([0, 4, 8, 10], 2116),
      ([0, 1, 4, 11], 704),
      ([0, 1, 4, 12], 196),
      ([0, 2, 3, 4], 2592)]
  | 5 => [([0, 5, 6, 9], 2178),
      ([0, 5, 8, 10], 2120),
      ([0, 5, 11, 12], 194),
      ([0, 5, 6, 12], 386),
      ([0, 5, 9, 11], 138),
      ([0, 1, 5, 10], 328),
      ([0, 2, 5, 6], 2432),
      ([0, 3, 5, 8], 2114)]
  | 6 => [([0, 6, 7, 8], 518),
      ([0, 6, 9, 12], 134),
      ([0, 2, 3, 6], 2816),
      ([0, 6, 7, 12], 262),
      ([0, 6, 8, 9], 2054),
      ([0, 1, 2, 6], 896),
      ([0, 2, 4, 6], 2688)]
  | _ => []

private lemma mem_offLines (P : Indices) (l : Index) :
    l ∈ offLines P ↔ ∀ p ∈ P, p ∉ line l := by
  simp only [offLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
  exact ⟨fun h p hp hpl => h hpl hp, fun h p hpl hp => h p hp hpl⟩

private def decode (mask : ℕ) : Indices :=
  Finset.univ.filter fun l => mask.testBit l.val = true

private lemma mem_decode (mask : ℕ) (l : Index) :
    l ∈ decode mask ↔ mask.testBit l.val = true := by
  simp [decode]

private def listMask : List Index → ℕ
  | [] => 0
  | p :: ps => (2 ^ p.val) ||| listMask ps

private lemma listMask_bit (ps : List Index) (n : ℕ) :
    (listMask ps).testBit n = true ↔ ∃ p ∈ ps, p.val = n := by
  induction ps with
  | nil => simp [listMask]
  | cons p ps ih =>
    simp only [listMask, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
      decide_eq_true_eq, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨q, hq, h⟩)
      · exact ⟨p, Or.inl rfl, h⟩
      · exact ⟨q, Or.inr hq, h⟩
    · rintro ⟨q, rfl | hq, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, hq, h⟩

private def encode (P : Indices) : ℕ :=
  listMask ((List.finRange 13).filter fun p => decide (p ∈ P))

private lemma encode_bit (P : Indices) (n : ℕ) :
    (encode P).testBit n = true ↔ ∃ p ∈ P, p.val = n := by
  simp [encode, listMask_bit]

private lemma encode_inter (P Q : Indices) : encode (P ∩ Q) = encode P &&& encode Q := by
  apply Nat.eq_of_testBit_eq
  intro n
  apply Bool.eq_iff_iff.mpr
  simp only [Nat.testBit_and, Bool.and_eq_true, encode_bit, Finset.mem_inter]
  constructor
  · rintro ⟨p, ⟨hp, hq⟩, hn⟩
    exact ⟨⟨p, hp, hn⟩, ⟨p, hq, hn⟩⟩
  · rintro ⟨⟨p, hp, hpn⟩, ⟨q, hq, hqn⟩⟩
    have h : p = q := Fin.ext (hpn.trans hqn.symm)
    exact ⟨p, ⟨hp, h ▸ hq⟩, hpn⟩

private lemma encode_zero (P : Indices) : encode P = 0 ↔ P = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hb := (encode_bit P p.val).mpr ⟨p, hp, rfl⟩
    rw [h, Nat.zero_testBit] at hb
    cases hb
  · rintro rfl
    decide +kernel

private def lineMask (l : Index) : ℕ :=
  match l.val with
  | 0 => 523
  | 1 => 1046
  | 2 => 2092
  | 3 => 4184
  | 4 => 177
  | 5 => 354
  | 6 => 708
  | 7 => 1416
  | 8 => 2832
  | 9 => 5664
  | 10 => 3137
  | 11 => 6274
  | _ => 4357

private lemma lineMask_eq (l : Index) : lineMask l = encode (line l) := by
  fin_cases l <;> decide +kernel

private lemma mask_disjoint (l : Index) (P : Indices) :
    lineMask l &&& encode P = 0 ↔ Disjoint (line l) P := by
  rw [lineMask_eq, ← encode_inter, encode_zero, Finset.disjoint_iff_inter_eq_empty]

private lemma mask_triple (a b c : Index) :
    lineMask a &&& lineMask b &&& lineMask c = 0 ↔
      Disjoint (line a ∩ line b) (line c) := by
  rw [lineMask_eq, lineMask_eq, lineMask_eq, ← encode_inter, ← encode_inter,
    encode_zero, Finset.disjoint_iff_inter_eq_empty]

private lemma encode_toFinset (ps : List Index) : encode ps.toFinset = listMask ps := by
  apply Nat.eq_of_testBit_eq
  intro n
  apply Bool.eq_iff_iff.mpr
  simp only [encode_bit, listMask_bit, List.mem_toFinset]

private lemma listMask_subset {ps : List Index} {mask : ℕ}
    (h : listMask ps &&& mask = listMask ps) : ps.toFinset ⊆ decode mask := by
  intro l hl
  have hp := (listMask_bit ps l.val).mpr ⟨l, List.mem_toFinset.mp hl, rfl⟩
  have hm := congrArg (fun n : ℕ => n.testBit l.val) h
  simp only [Nat.testBit_and, hp, Bool.true_and] at hm
  exact (mem_decode mask l).mpr hm

private lemma decode_encode (P : Indices) : decode (encode P) = P := by
  ext l
  rw [mem_decode, encode_bit]
  exact ⟨fun ⟨p, hp, hv⟩ => (Fin.ext hv : p = l) ▸ hp, fun hl => ⟨l, hl, rfl⟩⟩

private lemma lineMask_bit (l p : Index) : (lineMask l).testBit p.val = true ↔ p ∈ line l := by
  rw [← mem_decode, lineMask_eq, decode_encode]

private def checkPoints (ps : List Index) : Bool :=
  let pts := ps.dedup
  decide (pts.length ≤ 2) ||
    (List.finRange 13).all fun l =>
      decide (pts.countP (fun p => (lineMask l).testBit p.val) ≤ 2)

private lemma checkPoints_spec (ps : List Index) : checkPoints ps = true ↔ PointsOk ps.toFinset := by
  have hc : ps.dedup.length = ps.toFinset.card := by
    rw [← List.toFinset_card_of_nodup (List.nodup_dedup ps), List.toFinset_dedup]
  have hf (l : Index) :
      (ps.dedup.countP fun p => (lineMask l).testBit p.val) =
        (ps.toFinset ∩ line l).card := by
    rw [List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup ((List.nodup_dedup ps).filter _)]
    congr 1
    ext p
    simp [lineMask_bit]
  simp only [checkPoints, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies, hc, hf]
  exact ⟨fun h l => h.elim
    (fun h => (Finset.card_le_card Finset.inter_subset_left).trans h) (fun h => h l), Or.inr⟩

private def verified (row : List (List Index × ℕ)) : Bool :=
  row.all fun (ps, mask) =>
    let bits := listMask ps
    decide (ps.dedup.length = 4) && checkPoints ps &&
      (List.finRange 13).all fun l => !mask.testBit l.val || decide (lineMask l &&& bits = 0)

private lemma row_sound {row : List (List Index × ℕ)} (h : verified row = true)
    {ps : List Index} {mask : ℕ} (hm : (ps, mask) ∈ row) :
    IsQuadrangle singerLines3 ps.toFinset ∧ decode mask ⊆ offLines ps.toFinset := by
  have hv := List.all_eq_true.mp h (ps, mask) hm
  change (decide (ps.dedup.length = 4) && checkPoints ps &&
    (List.finRange 13).all (fun l => !mask.testBit l.val ||
      decide (lineMask l &&& listMask ps = 0))) = true at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq, checkPoints_spec, List.all_eq_true,
    List.mem_finRange, true_implies] at hv
  have hc : ps.toFinset.card = 4 := by
    rw [← List.toFinset_dedup, List.toFinset_card_of_nodup (List.nodup_dedup ps)]
    exact hv.1.1
  refine ⟨⟨hc, by simpa only [PointsOk, line_eq] using hv.1.2⟩, ?_⟩
  intro l hl
  have hd := hv.2 l
  rw [(mem_decode mask l).mp hl, ← encode_toFinset] at hd
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hd
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mask_disjoint l ps.toFinset).mp hd⟩

private def available (ps : List Index) : List Index :=
  let bits := listMask ps
  (List.finRange 13).filter fun l => decide (lineMask l &&& bits = 0)

private lemma mem_available (ps : List Index) (l : Index) :
    l ∈ available ps ↔ l ∈ offLines ps.toFinset := by
  simp [available, offLines, ← encode_toFinset, mask_disjoint]

private lemma nodup_available (ps : List Index) : (available ps).Nodup := by
  unfold available
  exact (List.nodup_finRange 13).filter _

private def checkTriple (ls : List Index) : Bool :=
  match ls with
  | [a, b, c] => decide (lineMask a &&& lineMask b &&& lineMask c = 0)
  | _ => true

private lemma checkTriple_true {ls : List Index} (hn : ls.Nodup) (h : LinesOk ls.toFinset) :
    checkTriple ls = true := by
  match ls with
  | [a, b, c] =>
    apply decide_eq_true
    apply (mask_triple a b c).mpr
    refine Finset.disjoint_left.mpr ?_
    intro p hp hc
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hp
    have hall : [a, b, c].toFinset ⊆ [a, b, c].toFinset.filter (fun l => p ∈ line l) := by
      intro l hl
      refine Finset.mem_filter.mpr ⟨hl, ?_⟩
      simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    have hh := (Finset.card_le_card hall).trans (h p)
    rw [List.toFinset_card_of_nodup hn] at hh
    exact (by decide : ¬ 3 ≤ 2) hh
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => rfl

private lemma linesOk_of_checkTriple (ls : List Index) (hlen : ls.length ≤ 3)
    (h : checkTriple ls = true) : LinesOk ls.toFinset := by
  have small (xs : List Index) (hxs : xs.length ≤ 2) : LinesOk xs.toFinset :=
    fun p => (Finset.card_le_card (Finset.filter_subset _ _)).trans
      ((List.toFinset_card_le (l := xs)).trans hxs)
  match ls with
  | [] => exact small [] (by decide)
  | [a] => exact small [a] (by simp)
  | [a, b] => exact small [a, b] (by simp)
  | [a, b, c] =>
    have hd : Disjoint (line a ∩ line b) (line c) := (mask_triple a b c).mp (of_decide_eq_true h)
    intro p
    by_contra! hbig
    let L := [a, b, c].toFinset
    have hEq : L.filter (fun l => p ∈ line l) = L :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        ((List.toFinset_card_le (l := [a, b, c])).trans (show 3 ≤ (L.filter fun l => p ∈ line l).card from hbig))
    have hp (l : Index) (hl : l ∈ [a, b, c]) : p ∈ line l := by
      have hl' : l ∈ L := List.mem_toFinset.mpr hl
      rw [← hEq] at hl'
      exact (Finset.mem_filter.mp hl').2
    exact Finset.disjoint_left.mp hd (Finset.mem_inter.mpr ⟨hp a (by simp), hp b (by simp)⟩)
      (hp c (by simp))
  | _ :: _ :: _ :: _ :: _ => simp at hlen; omega

private lemma available_toFinset (ps : List Index) :
    (available ps).toFinset = offLines ps.toFinset := by
  ext l
  simp [mem_available]

private def covers (row : List (List Index × ℕ)) (ps : List Index) : Bool :=
  if checkPoints ps then
    let bits := listMask ps
    let witnesses := row.filter fun QL => decide (bits &&& listMask QL.1 = bits)
    let others := available ps
    (List.range (min 3 (4 - ps.dedup.length) + 1)).all fun n =>
      (others.sublistsLen n).all fun ls =>
        !checkTriple ls || witnesses.any (fun QL => ls.all fun l => QL.2.testBit l.val)
  else true

private abbrev Extends (P L : Indices) : Prop :=
  ∃ Q, IsQuadrangle singerLines3 Q ∧ P ⊆ Q ∧ L ⊆ offLines Q

private lemma covered {row : List (List Index × ℕ)} {L : Indices} {ps : List Index}
    (hrow : verified row = true) (hcover : covers row ps = true)
    (hPL : ps.toFinset.card + L.card ≤ 4) (hL : L ⊆ offLines ps.toFinset)
    (hb : Bounds ps.toFinset L) : Extends ps.toFinset L := by
  unfold covers at hcover
  rw [ite_eq_left ((checkPoints_spec ps).mpr hb.2.1)] at hcover
  let ls := (available ps).filter fun l => decide (l ∈ L)
  have hsub : List.Sublist ls (available ps) := List.filter_sublist
  have hln : ls.Nodup := (nodup_available ps).sublist hsub
  have hs : ls.toFinset = L := by
    ext l
    simp only [ls, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_available]
    exact ⟨And.right, fun h => ⟨hL h, h⟩⟩
  have hr : ls.length ∈ List.range (min 3 (4 - ps.dedup.length) + 1) := by
    rw [← List.toFinset_card_of_nodup (List.nodup_dedup ps), List.toFinset_dedup,
      List.mem_range, ← List.toFinset_card_of_nodup hln, hs, Nat.lt_succ_iff]
    exact le_min hb.1 (by omega)
  have hm := List.mem_sublistsLen_self hsub
  have ht := List.all_eq_true.mp (List.all_eq_true.mp hcover _ hr) ls hm
  rw [checkTriple_true hln (hs.symm ▸ hb.2.2)] at ht
  simp only [Bool.not_true, Bool.false_or] at ht
  obtain ⟨⟨qs, mask⟩, hQ, hbits⟩ := List.any_eq_true.mp ht
  have hf := List.mem_filter.mp hQ
  obtain ⟨hq, he⟩ := row_sound hrow hf.1
  have hp := listMask_subset (of_decide_eq_true hf.2)
  rw [← encode_toFinset, decode_encode] at hp
  exact ⟨qs.toFinset, hq, hp, fun l hl => he
    ((mem_decode mask l).mpr (List.all_eq_true.mp hbits l (List.mem_toFinset.mp (hs.symm ▸ hl))))⟩

private def pointChecks (a : Index) : Bool :=
  (List.finRange 13).all fun b =>
    if (a = 0 ∧ b = 0) ∨ (a ≠ 0 ∧ (b = 0 ∨ a < b)) then
      covers (pointRow a) [0, a, b]
    else true

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private lemma point_checked (a : Index) :
    a.val ≤ 6 → verified (pointRow a) = true ∧ pointChecks a = true := by
  fin_cases a <;> decide +kernel

private lemma pointCase {P : Indices} (h0 : 0 ∈ P) (hc : P.card ≤ 3) :
    ∃ a b : Index, P = {0, a, b} ∧
      ((a = 0 ∧ b = 0) ∨ (a ≠ 0 ∧ (b = 0 ∨ a < b))) := by
  have he : (P.erase 0).card ≤ 2 := by
    rw [Finset.card_erase_of_mem h0]
    omega
  have hP := Finset.insert_erase h0
  by_cases hempty : P.erase 0 = ∅
  · exact ⟨0, 0, by simpa [hempty] using hP.symm, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
  have hsingle := Finset.insert_erase ha
  have he' : ((P.erase 0).erase a).card ≤ 1 := by
    rw [Finset.card_erase_of_mem ha]
    omega
  by_cases hrest : (P.erase 0).erase a = ∅
  · refine ⟨a, 0, ?_, Or.inr ⟨ha0, Or.inl rfl⟩⟩
    rw [hrest] at hsingle
    rw [← hP, ← hsingle]
    simpa using (Finset.pair_comm (0 : Index) a)
  obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hrest
  have hb' := Finset.mem_erase.mp hb
  have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb'.2).1
  have hh : (P.erase 0).erase a = {b} :=
    (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hb)
      (by simpa using he')).symm
  rw [hh] at hsingle
  have heq : P = {0, a, b} := by rw [← hP, ← hsingle]
  rcases lt_or_gt_of_ne hb'.1 with h | h
  · exact ⟨b, a, by rw [heq, Finset.pair_comm a b], Or.inr ⟨hb0, Or.inr h⟩⟩
  · exact ⟨a, b, heq, Or.inr ⟨ha0, Or.inr h⟩⟩

private def shift (c : Index) : Equiv.Perm Index where
  toFun p := ⟨(p.val + 13 - c.val) % 13, Nat.mod_lt _ (by decide)⟩
  invFun p := ⟨(p.val + c.val) % 13, Nat.mod_lt _ (by decide)⟩
  left_inv p := by
    apply Fin.ext
    change ((p.val + 13 - c.val) % 13 + c.val) % 13 = p.val
    omega
  right_inv p := by
    apply Fin.ext
    change ((p.val + c.val) % 13 + 13 - c.val) % 13 = p.val
    omega

private lemma shift_self (c : Index) : shift c c = 0 := by
  apply Fin.ext
  change (c.val + 13 - c.val) % 13 = 0
  omega

private lemma shift_mem (c p l : Index) : shift c p ∈ line (shift c l) ↔ p ∈ line l := by
  have hmod :
      ((shift c p).val + 13 - (shift c l).val) % 13 = (p.val + 13 - l.val) % 13 := by
    change ((p.val + 13 - c.val) % 13 + 13 - (l.val + 13 - c.val) % 13) % 13 =
      (p.val + 13 - l.val) % 13
    omega
  simp only [line_eq, singerLines3, Finset.mem_filter, Finset.mem_univ, true_and, hmod]

private def move (c : Index) (P : Indices) : Indices :=
  P.map (shift c).toEmbedding

private lemma mem_move (c p : Index) (P : Indices) : shift c p ∈ move c P ↔ p ∈ P :=
  by simp [move]

private lemma card_move (c : Index) (P : Indices) : (move c P).card = P.card :=
  Finset.card_map _

private lemma move_filter (c : Index) (P : Indices) {f g : Index → Prop}
    [DecidablePred f] [DecidablePred g] (h : ∀ x, f x ↔ g (shift c x)) :
    move c (P.filter f) = (move c P).filter g := by
  ext y
  obtain ⟨x, rfl⟩ := (shift c).surjective y
  simp only [mem_move, Finset.mem_filter, h]

private lemma point_bound_move (c : Index) (P : Indices) :
    PointsOk (move c P) ↔ PointsOk P := by
  have h (l : Index) : ((move c P) ∩ line (shift c l)).card = (P ∩ line l).card := by
    rw [← Finset.filter_mem_eq_inter, ← Finset.filter_mem_eq_inter]
    rw [← move_filter c P (fun p => (shift_mem c p l).symm), card_move]
  constructor
  · intro hb l
    rw [← h l]
    exact hb (shift c l)
  · intro hb l
    obtain ⟨l, rfl⟩ := (shift c).surjective l
    rw [h]
    exact hb l

private lemma line_bound_move (c : Index) (L : Indices) :
    LinesOk (move c L) ↔ LinesOk L := by
  have h (p : Index) :
      ((move c L).filter fun l => shift c p ∈ line l).card =
        (L.filter fun l => p ∈ line l).card := by
    rw [← move_filter c L (fun l => (shift_mem c p l).symm), card_move]
  constructor
  · intro hb p
    rw [← h p]
    exact hb (shift c p)
  · intro hb p
    obtain ⟨p, rfl⟩ := (shift c).surjective p
    rw [h]
    exact hb p

private lemma offLines_move (c : Index) (P : Indices) :
    offLines (move c P) = move c (offLines P) := by
  ext l
  obtain ⟨l, rfl⟩ := (shift c).surjective l
  rw [mem_move, mem_offLines, mem_offLines]
  constructor
  · intro h p hp hpl
    exact h _ ((mem_move c p P).mpr hp) ((shift_mem c p l).mpr hpl)
  · intro h p hp hpl
    obtain ⟨p, rfl⟩ := (shift c).surjective p
    exact h _ ((mem_move c p P).mp hp) ((shift_mem c p l).mp hpl)

private lemma bounds_move (c : Index) (P L : Indices) :
    Bounds (move c P) (move c L) ↔ Bounds P L := by
  simp only [Bounds, card_move, point_bound_move, line_bound_move]

private lemma quad_move (c : Index) (P : Indices) :
    IsQuadrangle singerLines3 (move c P) ↔ IsQuadrangle singerLines3 P := by
  have h (Q : Indices) : IsQuadrangle singerLines3 Q ↔ Q.card = 4 ∧ PointsOk Q := by
    simp only [IsQuadrangle, PointsOk, line_eq]
  simp only [h, card_move, point_bound_move]

private lemma extends_unshift (c : Index) {P L : Indices}
    (h : Extends (move c P) (move c L)) : Extends P L := by
  obtain ⟨Q, hq, hp, hl⟩ := h
  let R := Q.map (shift c).symm.toEmbedding
  have hR : move c R = Q := by
    ext p
    obtain ⟨p, rfl⟩ := (shift c).surjective p
    simp [R, mem_move, Finset.mem_map_equiv]
  refine ⟨R, (quad_move c R).mp (hR.symm ▸ hq), ?_, ?_⟩
  · intro p hm
    exact (mem_move c p R).mp (hR.symm ▸ hp ((mem_move c p P).mpr hm))
  · intro l hm
    have he : offLines Q = move c (offLines R) := hR ▸ offLines_move c R
    exact (mem_move c l (offLines R)).mp (he ▸ hl ((mem_move c l L).mpr hm))

private abbrev Anchored (P : Indices) : Prop :=
  0 ∈ P ∧ (P = {0} ∨ ∃ r ∈ P, r ≠ 0 ∧ r.val ≤ 6)

private lemma extend_normal (P L : Indices)
    (ht : P.card + L.card ≤ 4) (hi : L ⊆ offLines P) (hb : Bounds P L)
    (h0 : Anchored P) : Extends P L := by
  obtain ⟨h0, hshort⟩ := h0
  by_cases h4 : P.card = 4
  · exact ⟨P, ⟨h4, by simpa only [PointsOk, line_eq] using hb.2.1⟩, le_rfl, hi⟩
  obtain ⟨a, b, rfl, hab⟩ := pointCase h0 (by omega)
  have ha : a.val ≤ 6 := by
    rcases hshort with he | ⟨r, hr, hr0, hr6⟩
    · have ham : a ∈ ({0, a, b} : Indices) := by simp
      rw [he, Finset.mem_singleton] at ham
      simp [ham]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hr0 rfl).elim
      · exact hr6
      · rcases hab with ⟨ha0, _⟩ | ⟨_, hb0 | hab⟩
        · simp [ha0]
        · exact (hr0 hb0).elim
        · have : a.val < r.val := hab
          omega
  have hc := List.all_eq_true.mp (point_checked a ha).2 b (by simp)
  rw [ite_eq_left hab] at hc
  have hs : ([0, a, b] : List Index).toFinset = {0, a, b} := by simp
  rw [← hs] at ht hi hb ⊢
  exact covered (point_checked a ha).1 hc ht hi hb

private lemma short_direction (p q : Index) (hne : p ≠ q) :
    (shift p q).val ≤ 6 ∨ (shift q p).val ≤ 6 := by
  have hv : p.val ≠ q.val := fun h => hne (Fin.ext h)
  change (q.val + 13 - p.val) % 13 ≤ 6 ∨ (p.val + 13 - q.val) % 13 ≤ 6
  omega

private lemma extend_nonempty (P L : Indices) (hP : P.Nonempty)
    (ht : P.card + L.card ≤ 4) (hi : L ⊆ offLines P) (hb : Bounds P L) : Extends P L := by
  have hmove (c : Index) (h0 : Anchored (move c P)) : Extends P L := by
    apply extends_unshift c
    refine extend_normal _ _ (by simpa only [card_move] using ht) ?_
      ((bounds_move c P L).mpr hb) h0
    rw [offLines_move]
    exact Finset.map_subset_map.mpr hi
  obtain ⟨p, hp⟩ := hP
  have hzero {c : Index} (hc : c ∈ P) : 0 ∈ move c P :=
    shift_self c ▸ (mem_move c c P).mpr hc
  by_cases hs : P = {p}
  · exact hmove p ⟨hzero hp, Or.inl (by simp [hs, move, shift_self])⟩
  obtain ⟨q, hq, hqp⟩ : ∃ q ∈ P, q ≠ p := by
    by_contra! h
    apply hs
    exact Finset.Subset.antisymm (fun q hq => Finset.mem_singleton.mpr (h q hq))
      (Finset.singleton_subset_iff.mpr hp)
  have hshort {c r : Index} (hc : c ∈ P) (hr : r ∈ P) (hne : r ≠ c)
      (hd : (shift c r).val ≤ 6) : Extends P L := by
    apply hmove c
    refine ⟨hzero hc, Or.inr ⟨shift c r, (mem_move c r P).mpr hr, ?_, hd⟩⟩
    exact fun h => hne ((shift c).injective (h.trans (shift_self c).symm))
  exact (short_direction p q hqp.symm).elim (hshort hp hq hqp) (hshort hq hp hqp.symm)

private lemma line_card (l : Index) : (line l).card = 4 := by
  fin_cases l <;> decide +kernel

-- At most three four-point lines leave at least one of the thirteen points free.
private lemma extend (P L : Indices)
    (ht : P.card + L.card ≤ 4) (hi : L ⊆ offLines P) (hb : Bounds P L) : Extends P L := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · have hc : (L.biUnion line).card ≤ L.card * 4 :=
      (Finset.card_biUnion_le (s := L) (t := line)).trans_eq (Finset.sum_const_nat (fun l _ => line_card l))
    obtain ⟨p, hp⟩ : ∃ p : Index, p ∉ L.biUnion line := by
      by_contra! h
      have hu : (Finset.univ : Indices) ⊆ L.biUnion line := fun p _ => h p
      have hn := Finset.card_le_card hu
      simp only [Finset.card_univ, Fintype.card_fin] at hn
      have hL := hb.1
      omega
    have hfree : L ⊆ offLines ({p} : Indices) := by
      intro l hl
      rw [mem_offLines]
      intro q hq hql
      rw [Finset.mem_singleton.mp hq] at hql
      exact hp (Finset.mem_biUnion.mpr ⟨l, hl, hql⟩)
    have hsingle : PointsOk ({p} : Indices) := fun l =>
      (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    obtain ⟨Q, hq, _, hl⟩ :=
      extend_nonempty {p} L (by simp) (by simp; have := hb.1; omega)
        hfree ⟨hb.1, hsingle, hb.2.2⟩
    exact ⟨Q, hq, Finset.empty_subset _, hl⟩
  · exact extend_nonempty P L hP ht hi hb

private def larger (a : Index) : List Index :=
  (List.finRange 13).filter fun b => decide (a < b)

private def checkQuad (a : Index) : Bool :=
  ((larger a).sublistsLen 2).all fun R =>
    let qs := 0 :: a :: R
    let L := available qs
    !checkPoints qs || (decide (L.length ≤ 3) && checkTriple L)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private lemma quad_checked (a : Index) (ha : a ≠ 0) : checkQuad a = true := by
  fin_cases a
  · exact (ha rfl).elim
  all_goals decide +kernel

private lemma bounds_quad {Q : Indices} (hq : IsQuadrangle singerLines3 Q) :
    Bounds Q (offLines Q) := by
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (show 0 < Q.card by rw [hq.1]; decide)
  have hQ := (quad_move c Q).mpr hq
  rw [← bounds_move c Q, ← offLines_move]
  let V := move c Q
  change Bounds V (offLines V)
  have h0 : 0 ∈ V := shift_self c ▸ (mem_move c c Q).mpr hc
  have hn : (V.erase 0).card = 3 := by rw [Finset.card_erase_of_mem h0, hQ.1]
  have hne : (V.erase 0).Nonempty := Finset.card_pos.mp (by rw [hn]; decide)
  let a := (V.erase 0).min' hne
  have ha : a ∈ V.erase 0 := Finset.min'_mem _ _
  let R := (larger a).filter fun b => decide (b ∈ (V.erase 0).erase a)
  have hsub : List.Sublist R (larger a) := List.filter_sublist
  have hr : R.toFinset = (V.erase 0).erase a := by
    ext b
    simp only [R, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    intro hb
    have hba := Finset.mem_erase.mp hb
    have hlt : a < b := lt_of_le_of_ne (Finset.min'_le _ _ hba.2) hba.1.symm
    simp [larger, hlt]
  have hlen : R.length = 2 := by
    rw [← List.toFinset_card_of_nodup
      (((List.nodup_finRange 13).filter _).sublist hsub),
      hr, Finset.card_erase_of_mem ha, hn]
  have hm : R ∈ (larger a).sublistsLen 2 := List.mem_sublistsLen.mpr ⟨hsub, hlen⟩
  have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
  have hb := List.all_eq_true.mp (quad_checked a ha0) R hm
  dsimp only at hb
  have hset : (0 :: a :: R).toFinset = V := by
    rw [List.toFinset_cons, List.toFinset_cons, hr, Finset.insert_erase ha, Finset.insert_erase h0]
  have hp : PointsOk V := by simpa only [PointsOk, line_eq] using hQ.2
  have hcheck : checkPoints (0 :: a :: R) = true := (checkPoints_spec _).mpr (hset.symm ▸ hp)
  rw [hcheck] at hb
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hb
  have he : (available (0 :: a :: R)).toFinset = offLines V := by rw [available_toFinset, hset]
  rw [← he]
  exact ⟨(List.toFinset_card_le (l := available (0 :: a :: R))).trans hb.1, hp,
    linesOk_of_checkTriple _ hb.1 hb.2⟩

private lemma free_iff (V : Finset (Index ⊕ Index)) :
    IsFree (incidences singerLines3) V ↔ V.toRight ⊆ offLines V.toLeft := by
  constructor
  · intro hf l hl
    rw [mem_offLines]
    intro p hp hpl
    have hi : (p, l) ∈ incidences singerLines3 := by
      simpa [incidences, line_eq] using hpl
    exact hf (p, l) hi ⟨Finset.mem_toLeft.mp hp, Finset.mem_toRight.mp hl⟩
  · intro hf pl hpl hv
    have hi : pl.1 ∈ line pl.2 := by simpa [incidences, line_eq] using hpl
    exact (mem_offLines _ _).mp (hf (Finset.mem_toRight.mpr hv.2)) _
      (Finset.mem_toLeft.mpr hv.1) hi

private lemma bounds_subset {P P' L L' : Indices}
    (hp : P ⊆ P') (hl : L ⊆ L') (hb : Bounds P' L') : Bounds P L := by
  exact ⟨(Finset.card_le_card hl).trans hb.1,
    fun l => (Finset.card_le_card (Finset.inter_subset_inter_right hp)).trans (hb.2.1 l),
    fun p => (Finset.card_le_card (Finset.filter_subset_filter _ hl)).trans (hb.2.2 p)⟩

end PEqualNP.Outside.L_meta_7969

open PEqualNP.HeptadCover PEqualNP.Outside.L_meta_7969

theorem PEqualNP.Outside.L_meta_7969 :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences x1) x2 ∧ x2.toRight.card ≤ (3 : ℕ) ∧ (∀ (x3 : Fin (13 : ℕ)), (x2.toLeft ∩ x1 x3).card ≤ (2 : ℕ)) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2.toRight | x3 ∈ x1 x4}.card ≤ (2 : ℕ); ∀ (x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x3.card ≤ (4 : ℕ) → (x2 x3 ↔ ∃ (x5 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x5 ∧ x3 ⊆ PEqualNP.HeptadCover.supp x1 x5) := by
  intro S admissible V hV
  change (IsFree (incidences singerLines3) V ∧ V.toRight.card ≤ 3 ∧
    (∀ l : Index, (V.toLeft ∩ singerLines3 l).card ≤ 2) ∧
    (∀ p : Index, (V.toRight.filter fun l => p ∈ singerLines3 l).card ≤ 2)) ↔ _
  simp only [← line_eq]
  constructor
  · rintro ⟨hf, hb⟩
    obtain ⟨Q, hq, hp, hl⟩ := extend V.toLeft V.toRight
      (Finset.card_toLeft_add_card_toRight.trans_le hV) ((free_iff V).mp hf) hb
    rw [offLines_eq] at hl
    exact ⟨Q, hq, by
      rw [supp, Finset.subset_disjSum]
      exact ⟨hp, hl⟩⟩
  · rintro ⟨Q, hq, hsub⟩
    have hp : V.toLeft ⊆ Q := by simpa [supp] using Finset.toLeft_subset_toLeft hsub
    have hl : V.toRight ⊆ offLines Q := by
      simpa [supp, offLines_eq] using Finset.toRight_subset_toRight hsub
    refine ⟨(free_iff V).mpr ?_, bounds_subset hp hl (bounds_quad hq)⟩
    intro l hm
    rw [mem_offLines]
    exact fun p hpm => (mem_offLines _ _).mp (hl hm) p (hp hpm)
