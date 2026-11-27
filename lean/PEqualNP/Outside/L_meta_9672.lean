import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import PEqualNP.Defs
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Cast.Order

namespace PEqualNP.Outside.L_meta_9672_aux.Sol9668ParityWitness

abbrev Word := BitVec 3
abbrev Row := Word × Word × Word

def eval (f : Row) (t : Word) : Word :=
  (if t.getLsbD 0 then f.1 else 0) ^^^ (if t.getLsbD 1 then f.2.1 else 0) ^^^
    (if t.getLsbD 2 then f.2.2 else 0)

def strong : Finset Word := {3, 5, 6, 7}
def even : Finset Word := {3, 5, 6}
def support (f : Row) : Finset Word := strong.image (eval f)
def full : Finset Word := {0, 1, 2, 3, 4, 5, 6, 7}
abbrev high (f : Row) : Prop := 3 ≤ (support f).card
def plane (u v : Word) : Finset Word := {0, u, v, u ^^^ v}
def xorSum (P Q : Finset Word) : Finset Word := (P ×ˢ Q).image fun ab => ab.1 ^^^ ab.2

def sums (rows : List Row) : Finset Word := rows.foldr (fun r s => xorSum (support r) s) {0}
def total (t : Word) (rows : List Row) : Word := rows.foldr (fun r a => eval r t ^^^ a) 0

def Good (rows : List Row) : Prop := 0 ∈ sums rows ∨
  ∃ r ∈ rows, ∃ t ∈ even, total t (rows.erase r) = 0

structure RankFacts : Prop where
  lowFull (f : Row) : ¬ high f → support f = full.image (eval f)
  highPlane (f : Row) (u v : Word) : high f → u ≠ 0 → v ≠ 0 → u ≠ v →
    (support f ∩ plane u v).Nonempty
  disjointHigh (f g : Row) : high f → high g → support f ∩ support g = ∅ →
    xorSum (support f) (support g) = full.erase 0 ∧
      (∃ t ∈ even, eval f t = 0 ∨ eval g t = 0)

theorem full_mem (x : Word) : x ∈ full := by revert x; decide +kernel

@[local simp] theorem eval_zero (f : Row) : eval f 0 = 0 := by simp [eval]

theorem xor_left_comm (a b c : Word) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

theorem eval_six (f : Row) : eval f 6 = eval f 3 ^^^ eval f 5 := by
  simp [eval]
  rw [BitVec.xor_assoc, xor_left_comm f.1 f.2.1, ← BitVec.xor_assoc f.1 f.1,
    BitVec.xor_self, BitVec.zero_xor]

@[local simp] theorem mem_xorSum {x : Word} {P Q : Finset Word} :
    x ∈ xorSum P Q ↔ ∃ a ∈ P, ∃ b ∈ Q, a ^^^ b = x := by
  simp [xorSum, Prod.exists, and_assoc]

theorem xorSum_comm (P Q : Finset Word) : xorSum P Q = xorSum Q P := by
  ext x
  simp only [mem_xorSum]
  exact ⟨fun ⟨a, ha, b, hb, h⟩ => ⟨b, hb, a, ha, BitVec.xor_comm b a ▸ h⟩,
    fun ⟨a, ha, b, hb, h⟩ => ⟨b, hb, a, ha, BitVec.xor_comm b a ▸ h⟩⟩

theorem xorSum_assoc (P Q R : Finset Word) :
    xorSum (xorSum P Q) R = xorSum P (xorSum Q R) := by
  ext x
  constructor
  · rintro hx
    obtain ⟨u, hu, c, hc, rfl⟩ := mem_xorSum.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_xorSum.mp hu
    exact mem_xorSum.mpr ⟨a, ha, b ^^^ c, mem_xorSum.mpr ⟨b, hb, c, hc, rfl⟩,
      (BitVec.xor_assoc a b c).symm⟩
  · rintro hx
    obtain ⟨a, ha, u, hu, rfl⟩ := mem_xorSum.mp hx
    obtain ⟨b, hb, c, hc, rfl⟩ := mem_xorSum.mp hu
    exact mem_xorSum.mpr ⟨a ^^^ b, mem_xorSum.mpr ⟨a, ha, b, hb, rfl⟩, c, hc,
      BitVec.xor_assoc a b c⟩

@[local simp] theorem xorSum_zero (P : Finset Word) : xorSum P {0} = P := by
  ext x
  simp

theorem sums_perm {rows rows' : List Row} (h : rows.Perm rows') : sums rows = sums rows' := by
  induction h with
  | nil => rfl
  | cons x h ih => change xorSum (support x) (sums _) = xorSum (support x) (sums _); rw [ih]
  | swap x y xs =>
    change xorSum (support y) (xorSum (support x) (sums xs)) = _
    rw [← xorSum_assoc, xorSum_comm (support y) (support x), xorSum_assoc]
    rfl
  | trans hab hbc ihab ihbc => exact ihab.trans ihbc

theorem total_perm (t : Word) {rows rows' : List Row} (h : rows.Perm rows') :
    total t rows = total t rows' := by
  induction h with
  | nil => rfl
  | cons x h ih => change eval x t ^^^ total t _ = eval x t ^^^ total t _; rw [ih]
  | swap x y xs =>
    change eval y t ^^^ (eval x t ^^^ total t xs) = eval x t ^^^ (eval y t ^^^ total t xs)
    rw [← BitVec.xor_assoc, BitVec.xor_comm (eval y t) (eval x t), BitVec.xor_assoc]
  | trans hab hbc ihab ihbc => exact ihab.trans ihbc

theorem good_of_perm {rows rows' : List Row} (h : rows.Perm rows') (p : Good rows) :
    Good rows' := by
  rcases p with p | ⟨r, hr, t, ht, hz⟩
  · left; rwa [← sums_perm h]
  · right
    exact ⟨r, h.mem_iff.mp hr, t, ht, (total_perm t (h.erase r)).symm.trans hz⟩

theorem support_nonempty (r : Row) : (support r).Nonempty :=
  ⟨eval r 3, Finset.mem_image.mpr ⟨3, by simp [strong], rfl⟩⟩

theorem mem_support_of_low (R : RankFacts) {r : Row} (hl : ¬ high r) (t : Word) :
    eval r t ∈ support r := by
  rw [R.lowFull r hl]
  exact Finset.mem_image.mpr ⟨t, full_mem t, rfl⟩

theorem zero_mem_low (R : RankFacts) {r : Row} (hl : ¬ high r) : 0 ∈ support r :=
  eval_zero r ▸ mem_support_of_low R hl 0

theorem support_nontrivial_of_high {r : Row} (h : high r) : (support r).Nontrivial :=
  Finset.one_lt_card_iff_nontrivial.mp (show 1 < (support r).card from Nat.lt_of_lt_of_le (by decide) h)

theorem xorSum_full (P : Finset Word) (h : P.Nonempty) : xorSum full P = full := by
  ext x; constructor
  · intro _; exact full_mem x
  · intro _
    obtain ⟨y, hy⟩ := h
    exact mem_xorSum.mpr ⟨x ^^^ y, full_mem _, y, hy, by simp [BitVec.xor_assoc]⟩

theorem xorSum_nonzero (P : Finset Word) (h : P.Nontrivial) :
    xorSum (full.erase 0) P = full := by
  ext x; constructor
  · intro _; exact full_mem x
  · intro _
    obtain ⟨y, hy, hxy⟩ := h.exists_ne x
    refine mem_xorSum.mpr ⟨x ^^^ y, Finset.mem_erase.mpr ⟨?_, full_mem _⟩, y, hy, ?_⟩
    · exact fun hz => hxy (BitVec.xor_eq_zero_iff.mp hz).symm
    · simp [BitVec.xor_assoc]

theorem avoid_pair (P : Finset Word) (h : 3 ≤ P.card) (a b : Word) :
    ∃ x ∈ P, x ≠ a ∧ x ≠ b := by
  by_contra! hn
  have hsub : P ⊆ {a, b} := by
    intro x hx
    simpa using (show x = a ∨ x = b from or_iff_not_imp_left.mpr (hn x hx))
  have hcard := Finset.card_le_card hsub
  have hpair := Finset.card_pair_eq_one_or_two (a := a) (b := b)
  omega

theorem plane_in_xorSum (P Q : Finset Word) (hP : 3 ≤ P.card) (hQ : 3 ≤ Q.card)
    (h : (P ∩ Q).Nonempty) : ∃ a b : Word, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      plane a b ⊆ xorSum P Q := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨hsP, hsQ⟩ := Finset.mem_inter.mp hs
  obtain ⟨p, hp, hps, _⟩ := avoid_pair P hP s s
  obtain ⟨q, hq, hqs, hqp⟩ := avoid_pair Q hQ s p
  refine ⟨p ^^^ s, q ^^^ s, ?_, ?_, ?_, ?_⟩
  · exact fun hz => hps (BitVec.xor_eq_zero_iff.mp hz)
  · exact fun hz => hqs (BitVec.xor_eq_zero_iff.mp hz)
  · intro hsame
    have hsame' := congrArg (fun x => x ^^^ s) hsame
    exact hqp (by simpa [BitVec.xor_assoc] using hsame'.symm)
  · intro x hx
    simp only [plane, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mem_xorSum.mpr ⟨s, hsP, s, hsQ, by simp⟩
    · exact mem_xorSum.mpr ⟨p, hp, s, hsQ, rfl⟩
    · exact mem_xorSum.mpr ⟨s, hsP, q, hq, BitVec.xor_comm _ _⟩
    · exact mem_xorSum.mpr ⟨p, hp, q, hq, by
        rw [BitVec.xor_assoc p s, BitVec.xor_comm q s, ← BitVec.xor_assoc s, BitVec.xor_self,
          BitVec.zero_xor]⟩

theorem sums_four (a b c d : Row) : sums [a, b, c, d] =
    xorSum (xorSum (support a) (support b)) (xorSum (support c) (support d)) := by
  simp only [sums, List.foldr_cons, List.foldr_nil, xorSum_zero, xorSum_assoc]

theorem sums_four_right (a b c d : Row) : sums [a, b, c, d] =
    xorSum (support a) (xorSum (support b) (xorSum (support c) (support d))) := by
  simp only [sums, List.foldr_cons, List.foldr_nil, xorSum_zero]

theorem sums_four_mid (a b c d : Row) : sums [a, b, c, d] =
    xorSum (xorSum (xorSum (support a) (support b)) (support c)) (support d) := by
  simp only [sums, List.foldr_cons, List.foldr_nil, xorSum_zero, xorSum_assoc]

theorem sum_zero (P Q : Finset Word) (p : 0 ∈ P) (q : 0 ∈ Q) : 0 ∈ xorSum P Q :=
  mem_xorSum.mpr ⟨0, p, 0, q, by simp⟩

theorem sum_zero_of_inter (P Q : Finset Word) (h : (P ∩ Q).Nonempty) : 0 ∈ xorSum P Q := by
  obtain ⟨x, hx⟩ := h
  exact mem_xorSum.mpr ⟨x, (Finset.mem_inter.mp hx).1, x, (Finset.mem_inter.mp hx).2, by simp⟩

theorem good_disjoint_three (R : RankFacts) {a b c d : Row} (ha : high a) (hb : high b)
    (hc : (support c).Nontrivial) (hab : support a ∩ support b = ∅) : Good [a, b, c, d] := by
  left
  rw [sums_four_mid, (R.disjointHigh a b ha hb hab).1, xorSum_nonzero _ hc,
    xorSum_full _ (support_nonempty d)]
  exact full_mem _

theorem good_no_high (R : RankFacts) {a b c d : Row} (ha : ¬ high a) (hb : ¬ high b)
    (hc : ¬ high c) (hd : ¬ high d) : Good [a, b, c, d] := by
  left; rw [sums_four]
  apply sum_zero
  · exact sum_zero _ _ (zero_mem_low R ha) (zero_mem_low R hb)
  · exact sum_zero _ _ (zero_mem_low R hc) (zero_mem_low R hd)

theorem total_six (rows : List Row) : total 6 rows = total 3 rows ^^^ total 5 rows := by
  induction rows with
  | nil => decide
  | cons r rs ih =>
    change eval r 6 ^^^ total 6 rs = (eval r 3 ^^^ total 3 rs) ^^^ (eval r 5 ^^^ total 5 rs)
    rw [eval_six, ih]
    simp only [BitVec.xor_assoc]
    rw [xor_left_comm (total 3 rs) (eval r 5)]

theorem total_mem_three (R : RankFacts) {b c d : Row} (hb : ¬ high b) (hc : ¬ high c)
    (hd : ¬ high d) (t : Word) :
    total t [b, c, d] ∈ xorSum (support b) (xorSum (support c) (support d)) := by
  refine mem_xorSum.mpr ⟨eval b t, mem_support_of_low R hb t, _,
    mem_xorSum.mpr ⟨eval c t, mem_support_of_low R hc t, eval d t,
      mem_support_of_low R hd t, rfl⟩, ?_⟩
  simp [total]

theorem special_first {a b c d : Row} {t : Word} (ht : t ∈ even)
    (h : total t [b, c, d] = 0) : Good [a, b, c, d] := by
  right
  exact ⟨a, by simp, t, ht, by simpa using h⟩

theorem good_one_high (R : RankFacts) {a b c d : Row} (ha : high a) (hb : ¬ high b)
    (hc : ¬ high c) (hd : ¬ high d) : Good [a, b, c, d] := by
  let u := total 3 [b, c, d]
  let v := total 5 [b, c, d]
  by_cases hu : u = 0
  · exact special_first (t := 3) (by simp [even]) hu
  by_cases hv : v = 0
  · exact special_first (t := 5) (by simp [even]) hv
  by_cases huv : u = v
  · apply special_first (t := 6) (by simp [even])
    rw [total_six]
    exact BitVec.xor_eq_zero_iff.mpr huv
  left; rw [sums_four_right]
  apply sum_zero_of_inter
  obtain ⟨x, hx⟩ := R.highPlane a u v ha hu hv huv
  obtain ⟨hxa, hplane⟩ := Finset.mem_inter.mp hx
  refine ⟨x, Finset.mem_inter.mpr ⟨hxa, ?_⟩⟩
  simp only [plane, Finset.mem_insert, Finset.mem_singleton] at hplane
  rcases hplane with rfl | rfl | rfl | rfl
  · exact sum_zero _ _ (zero_mem_low R hb) (sum_zero _ _ (zero_mem_low R hc) (zero_mem_low R hd))
  · exact total_mem_three R hb hc hd 3
  · exact total_mem_three R hb hc hd 5
  · rw [← total_six]
    exact total_mem_three R hb hc hd 6

theorem many_of_zero_ne_singleton (P : Finset Word) (h0 : 0 ∈ P) (h : P ≠ {0}) :
    P.Nontrivial := by
  apply Finset.one_lt_card_iff_nontrivial.mp
  by_contra! hc
  apply h
  ext x
  exact ⟨fun hx => Finset.mem_singleton.mpr (Finset.card_le_one.mp hc x hx 0 h0),
    fun hx => Finset.mem_singleton.mp hx ▸ h0⟩

theorem no_eval_of_support_zero (R : RankFacts) {r : Row} (h : ¬ high r)
    (hs : support r = {0}) (t : Word) : eval r t = 0 := by
  exact Finset.mem_singleton.mp (hs ▸ mem_support_of_low R h t)

theorem good_two_high (R : RankFacts) {a b c d : Row} (ha : high a) (hb : high b)
    (hc : ¬ high c) (hd : ¬ high d) : Good [a, b, c, d] := by
  by_cases hab : support a ∩ support b = ∅
  · by_cases hz : support c = {0}
    · by_cases hw : support d = {0}
      · obtain ⟨t, ht, h | h⟩ := (R.disjointHigh a b ha hb hab).2
        · right
          refine ⟨b, by simp, t, ht, ?_⟩
          by_cases heq : a = b
          · subst b
            simp [total, h, no_eval_of_support_zero R hc hz t, no_eval_of_support_zero R hd hw t]
          · simp [total, heq, h, no_eval_of_support_zero R hc hz t, no_eval_of_support_zero R hd hw t]
        · exact special_first ht (by simp [total, h, no_eval_of_support_zero R hc hz t,
            no_eval_of_support_zero R hd hw t])
      · left; rw [sums_four, (R.disjointHigh a b ha hb hab).1, hz]
        have he : xorSum {0} (support d) = support d := by rw [xorSum_comm, xorSum_zero]
        rw [he, xorSum_nonzero _ (many_of_zero_ne_singleton _ (zero_mem_low R hd) hw)]
        exact full_mem _
    · exact good_disjoint_three R ha hb (many_of_zero_ne_singleton _ (zero_mem_low R hc) hz) hab
  · left; rw [sums_four]
    exact sum_zero _ _ (sum_zero_of_inter _ _ (Finset.nonempty_iff_ne_empty.mpr hab))
      (sum_zero _ _ (zero_mem_low R hc) (zero_mem_low R hd))

theorem good_three_high (R : RankFacts) {a b c d : Row} (ha : high a) (hb : high b)
    (hc : high c) (hd : ¬ high d) : Good [a, b, c, d] := by
  by_cases hab : support a ∩ support b = ∅
  · exact good_disjoint_three R ha hb (support_nontrivial_of_high hc) hab
  · left; rw [sums_four_mid]
    apply sum_zero _ _ _ (zero_mem_low R hd)
    obtain ⟨u, v, hu, hv, huv, hp⟩ := plane_in_xorSum _ _ ha hb (Finset.nonempty_iff_ne_empty.mpr hab)
    obtain ⟨x, hx⟩ := R.highPlane c u v hc hu hv huv
    exact mem_xorSum.mpr ⟨x, hp (Finset.mem_inter.mp hx).2, x, (Finset.mem_inter.mp hx).1, by simp⟩

theorem good_four_high (R : RankFacts) {a b c d : Row} (ha : high a) (hb : high b)
    (hc : high c) (hd : high d) : Good [a, b, c, d] := by
  by_cases hab : support a ∩ support b = ∅
  · exact good_disjoint_three R ha hb (support_nontrivial_of_high hc) hab
  by_cases hcd : support c ∩ support d = ∅
  · have h : [c, d, a, b].Perm [a, b, c, d] := List.perm_append_comm (l₁ := [c, d]) (l₂ := [a, b])
    exact good_of_perm h (good_disjoint_three R hc hd (support_nontrivial_of_high ha) hcd)
  left; rw [sums_four]
  exact sum_zero _ _ (sum_zero_of_inter _ _ (Finset.nonempty_iff_ne_empty.mpr hab))
    (sum_zero_of_inter _ _ (Finset.nonempty_iff_ne_empty.mpr hcd))

theorem sortedGood (R : RankFacts) (hi lo : List Row) (hlen : (hi ++ lo).length = 4)
    (hhi : ∀ r ∈ hi, high r) (hlo : ∀ r ∈ lo, ¬ high r) : Good (hi ++ lo) := by
  have hclass : hi.length = 0 ∨ hi.length = 1 ∨ hi.length = 2 ∨
      hi.length = 3 ∨ hi.length = 4 := by simp only [List.length_append] at hlen; omega
  rcases hclass with h | h | h | h | h
  · have hl : lo.length = 4 := by simp only [List.length_append] at hlen; omega
    obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp hl
    obtain rfl := List.eq_nil_of_length_eq_zero h
    apply good_no_high R <;> apply hlo <;> simp
  · have hl : lo.length = 3 := by simp only [List.length_append] at hlen; omega
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h
    obtain ⟨b, c, d, rfl⟩ := List.length_eq_three.mp hl
    apply good_one_high R <;> first | (apply hhi; simp) | (apply hlo; simp)
  · have hl : lo.length = 2 := by simp only [List.length_append] at hlen; omega
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp h
    obtain ⟨c, d, rfl⟩ := List.length_eq_two.mp hl
    apply good_two_high R <;> first | (apply hhi; simp) | (apply hlo; simp)
  · have hl : lo.length = 1 := by simp only [List.length_append] at hlen; omega
    obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp h
    obtain ⟨d, rfl⟩ := List.length_eq_one_iff.mp hl
    apply good_three_high R <;> first | (apply hhi; simp) | (apply hlo; simp)
  · have hl : lo.length = 0 := by simp only [List.length_append] at hlen; omega
    obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp h
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    apply good_four_high R <;> apply hhi <;> simp

theorem good_four_of_rankFacts (R : RankFacts) (rows : List Row) (hlen : rows.length = 4) :
    Good rows := by
  let p : Row → Bool := fun r => decide (high r)
  have hperm := List.filter_append_perm p rows
  apply good_of_perm hperm
  apply sortedGood R _ _ (hperm.length_eq.trans hlen)
  · intro r hr
    have h := (List.mem_filter.mp hr).2
    exact of_decide_eq_true h
  · intro r hr
    have h := (List.mem_filter.mp hr).2
    simpa [p] using h

def words : List Word := [0, 1, 2, 3, 4, 5, 6, 7]
def rowWords : List Row := words.flatMap fun a => words.flatMap fun b => words.map fun c => (a, b, c)
def highShapes : List (Finset Word) := ((rowWords.map support).eraseDups).filter fun p => decide (3 ≤ p.card)

theorem words_mem (x : Word) : x ∈ words := by revert x; decide +kernel

theorem rowWords_mem (r : Row) : r ∈ rowWords := by
  rcases r with ⟨a, b, c⟩
  unfold rowWords
  exact List.mem_flatMap.mpr ⟨a, words_mem a, List.mem_flatMap.mpr ⟨b, words_mem b,
    List.mem_map.mpr ⟨c, words_mem c, rfl⟩⟩⟩

theorem highShapes_mem (r : Row) (hr : high r) : support r ∈ highShapes := by
  apply List.mem_filter.mpr
  exact ⟨List.mem_eraseDups.mpr (List.mem_map.mpr ⟨r, rowWords_mem r, rfl⟩), decide_eq_true hr⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowCheck : rowWords.all (fun f => decide (¬ high f → support f = full.image (eval f))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem planeCheck : highShapes.all (fun p => words.all fun u => words.all fun v =>
    decide (u ≠ 0 → v ≠ 0 → u ≠ v → (p ∩ plane u v).Nonempty)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pairCheck : highShapes.all (fun p => highShapes.all fun q =>
    decide (p ∩ q = ∅ → xorSum p q = full.erase 0 ∧
      ((p.card = 3 ∧ 0 ∈ p) ∨ (q.card = 3 ∧ 0 ∈ q)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem evenCheck : rowWords.all (fun f => decide ((support f).card = 3 → 0 ∈ support f →
    ∃ t ∈ even, eval f t = 0)) = true := by
  decide +kernel

theorem rankFacts : RankFacts := by
  constructor
  · intro f hf
    exact of_decide_eq_true (List.all_eq_true.mp lowCheck f (rowWords_mem f)) hf
  · intro f u v hf hu hv huv
    exact of_decide_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp (List.all_eq_true.mp planeCheck _ (highShapes_mem f hf)) u (words_mem u))
      v (words_mem v)) hu hv huv
  · intro f g hf hg hd
    have h := of_decide_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp pairCheck _ (highShapes_mem f hf)) _ (highShapes_mem g hg)) hd
    refine ⟨h.1, ?_⟩
    rcases h.2 with h | h
    · obtain ⟨t, ht, hz⟩ := of_decide_eq_true (List.all_eq_true.mp evenCheck f (rowWords_mem f)) h.1 h.2
      exact ⟨t, ht, Or.inl hz⟩
    · obtain ⟨t, ht, hz⟩ := of_decide_eq_true (List.all_eq_true.mp evenCheck g (rowWords_mem g)) h.1 h.2
      exact ⟨t, ht, Or.inr hz⟩

theorem good_four (rows : List Row) (hlen : rows.length = 4) : Good rows :=
  good_four_of_rankFacts rankFacts rows hlen

def evalMasks (rows : List Row) (masks : List Word) : Word :=
  (rows.zipWith (fun r t => eval r t) masks).foldr (fun x a => x ^^^ a) 0

theorem masks_of_sums {rows : List Row} {x : Word} (h : x ∈ sums rows) :
    ∃ masks : List Word, masks.length = rows.length ∧ (∀ t ∈ masks, t ∈ strong) ∧
      evalMasks rows masks = x := by
  induction rows generalizing x with
  | nil =>
    refine ⟨[], rfl, by simp, ?_⟩
    change x ∈ ({0} : Finset Word) at h
    exact (Finset.mem_singleton.mp h).symm
  | cons r rs ih =>
    change x ∈ xorSum (support r) (sums rs) at h
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_xorSum.mp h
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨masks, hl, hm, hv⟩ := ih hb
    refine ⟨t :: masks, by simp [hl], by simpa [ht] using hm, ?_⟩
    change eval r t ^^^ evalMasks rs masks = eval r t ^^^ b
    rw [hv]

theorem split_of_erase {r : Row} {rows : List Row} (hr : r ∈ rows) :
    ∃ before after : List Row, rows = before ++ r :: after ∧ rows.erase r = before ++ after := by
  induction rows with
  | nil => simp at hr
  | cons a as ih =>
    by_cases har : a = r
    · subst a
      exact ⟨[], as, rfl, by simp⟩
    · have hra : r ≠ a := Ne.symm har
      have has : r ∈ as := by simpa [hra] using hr
      obtain ⟨before, after, h1, h2⟩ := ih has
      refine ⟨a :: before, after, ?_, ?_⟩
      · simpa using congrArg (List.cons a) h1
      · rw [List.erase_cons_tail (show ¬ (a == r) from by simpa using har)]
        exact congrArg (List.cons a) h2

theorem evalMasks_append (rs₁ rs₂ : List Row) (ms₁ ms₂ : List Word)
    (h : rs₁.length = ms₁.length) : evalMasks (rs₁ ++ rs₂) (ms₁ ++ ms₂) =
      evalMasks rs₁ ms₁ ^^^ evalMasks rs₂ ms₂ := by
  induction rs₁ generalizing ms₁ with
  | nil =>
    have hnil : ms₁ = [] := List.eq_nil_of_length_eq_zero h.symm
    subst ms₁
    simp [evalMasks]
  | cons r rs ih =>
    cases ms₁ with
    | nil => simp at h
    | cons m ms =>
      have heq : rs.length = ms.length := by simpa using h
      change eval r m ^^^ evalMasks (rs ++ rs₂) (ms ++ ms₂) =
        (eval r m ^^^ evalMasks rs ms) ^^^ evalMasks rs₂ ms₂
      rw [ih ms heq, BitVec.xor_assoc]

theorem total_append (t : Word) (rs₁ rs₂ : List Row) :
    total t (rs₁ ++ rs₂) = total t rs₁ ^^^ total t rs₂ := by
  induction rs₁ with
  | nil => simp [total]
  | cons r rs ih =>
    change eval r t ^^^ total t (rs ++ rs₂) = (eval r t ^^^ total t rs) ^^^ total t rs₂
    rw [ih, BitVec.xor_assoc]

theorem evalMasks_uniform (t : Word) (rows : List Row) :
    evalMasks rows (rows.map fun _ => t) = total t rows := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    change eval r t ^^^ evalMasks rs (rs.map fun _ => t) = eval r t ^^^ total t rs
    rw [ih]

theorem four_masks (rows : List Row) (h : rows.length = 4) :
    ∃ masks : List Word, masks.length = rows.length ∧ evalMasks rows masks = 0 ∧
      ((∀ t ∈ masks, t ∈ strong) ∨
        ∃ left right : List Word, ∃ t ∈ even, masks = left ++ 0 :: right ∧
          (∀ i ∈ left, i = t) ∧ (∀ i ∈ right, i = t)) := by
  rcases good_four rows h with hsum | ⟨r, hr, t, ht, hsum⟩
  · obtain ⟨masks, hlen, hm, hz⟩ := masks_of_sums hsum
    exact ⟨masks, hlen, hz, Or.inl hm⟩
  · obtain ⟨before, after, h1, h2⟩ := split_of_erase hr
    rw [h2, total_append] at hsum
    rw [h1]
    refine ⟨(before.map fun _ => t) ++ 0 :: (after.map fun _ => t), by simp, ?_, Or.inr ?_⟩
    · rw [evalMasks_append _ _ _ _ (by simp), evalMasks_uniform]
      change total t before ^^^ (eval r 0 ^^^ evalMasks after (after.map fun _ => t)) = 0
      rw [eval_zero, evalMasks_uniform]
      change total t before ^^^ (0#3 ^^^ total t after) = 0
      rwa [BitVec.zero_xor]
    · exact ⟨_, _, t, ht, rfl, by simp, by simp⟩

end PEqualNP.Outside.L_meta_9672_aux.Sol9668ParityWitness

namespace PEqualNP.Outside.L_meta_9672_aux.Sol9668HalfBridge

open Sol9668ParityWitness
open scoped BigOperators

abbrev Positions := Fin 4 × Fin 3

def parity (z : ℤ) : Bool := decide (z % 2 = 1)
def asInt (b : Bool) : ℤ := if b then 1 else 0

theorem parity_add (x y : ℤ) : parity (x + y) = (parity x ^^ parity y) := by
  unfold parity
  by_cases hx : x % 2 = 1 <;> by_cases hy : y % 2 = 1 <;> simp [hx, hy] <;> omega

theorem parity_mul (x y : ℤ) : parity (x * y) = (parity x && parity y) := by
  unfold parity
  rw [Int.mul_emod]
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy]

@[local simp] theorem parity_asInt (b : Bool) : parity (asInt b) = b := by cases b <;> decide

theorem asInt_bounds (b : Bool) : 0 ≤ asInt b ∧ asInt b ≤ 1 := by cases b <;> decide

def pack (p : Fin 3 → ℤ) : Word :=
  (if parity (p 0) then 1 else 0) ^^^ (if parity (p 1) then 2 else 0) ^^^
    (if parity (p 2) then 4 else 0)

theorem get_pack (p : Fin 3 → ℤ) (k : Fin 3) : (pack p).getLsbD k.val = parity (p k) := by
  unfold pack
  fin_cases k <;> cases h0 : parity (p 0) <;> cases h1 : parity (p 1) <;>
    cases h2 : parity (p 2) <;> simp [h0, h1, h2]

def packRow (f : Fin 3 → Positions → ℤ) (i : Fin 4) : Row :=
  (pack (fun k => f k (i, 0)), pack (fun k => f k (i, 1)), pack (fun k => f k (i, 2)))

theorem get_cond_pack (p : Fin 3 → ℤ) (k : Fin 3) (b : Bool) :
    (if b then pack p else 0).getLsbD k.val = (parity (p k) && b) := by
  cases b
  · exact BitVec.getLsbD_zero.trans (Bool.and_false _).symm
  · exact (get_pack p k).trans (Bool.and_true _).symm

theorem row_parity (f : Fin 3 → Positions → ℤ) (i : Fin 4) (k : Fin 3) (t : Word)
    (a : Positions → ℤ) (ha : ∀ j, parity (a (i, j)) = t.getLsbD j.val) :
    (eval (packRow f i) t).getLsbD k.val = parity (∑ j : Fin 3, f k (i, j) * a (i, j)) := by
  simp only [eval, BitVec.getLsbD_xor, packRow, get_cond_pack,
    Fin.sum_univ_three, parity_add, parity_mul, ha]
  rfl

theorem zip_ofFn (f : Fin 4 → Row) (m : Fin 4 → Word) :
    (List.ofFn f).zipWith eval (List.ofFn m) = List.ofFn (fun i => eval (f i) (m i)) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp

def xorFour (g : Fin 4 → Word) : Word := g 0 ^^^ (g 1 ^^^ (g 2 ^^^ g 3))

theorem evalMasks_ofFn (f : Fin 4 → Row) (m : Fin 4 → Word) :
    evalMasks (List.ofFn f) (List.ofFn m) = xorFour (fun i => eval (f i) (m i)) := by
  unfold evalMasks
  rw [zip_ofFn]
  simp [List.ofFn_succ, xorFour, Fin.succ]

theorem get_uniform_special (l r : List Word) (t : Word)
    (hl : ∀ x ∈ l, x = t) (hr : ∀ x ∈ r, x = t) (j : Nat)
    (hj : j < (l ++ 0 :: r).length) :
    (l ++ 0 :: r)[j] = if j = l.length then 0 else t := by
  induction l generalizing j with
  | nil =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj' : j < r.length := by simpa using hj
      simpa using hr r[j] (List.getElem_mem hj')
  | cons x l ih =>
    cases j with
    | zero => simpa using hl x (by simp)
    | succ j =>
      have hj' : j < (l ++ 0 :: r).length := by simpa using hj
      simpa using ih (fun y hy => hl y (by simp [hy])) j hj'

theorem four_masks_fin (f : Fin 4 → Row) :
    ∃ m : Fin 4 → Word, xorFour (fun i => eval (f i) (m i)) = 0 ∧
      ((∀ i, m i ∈ strong) ∨ ∃ i : Fin 4, ∃ t ∈ even, ∀ j, m j = if j = i then 0 else t) := by
  obtain ⟨xs, hlen, hz, hs⟩ := four_masks (List.ofFn f) (by simp)
  have hn : xs.length = 4 := by simpa using hlen
  let m : Fin 4 → Word := fun i => xs[i.val]'(by simp [hn])
  have hxs : List.ofFn m = xs := by
    apply List.ext_getElem (by simp [hn])
    intro n h₁ h₂
    rw [List.getElem_ofFn]
  refine ⟨m, ?_, ?_⟩
  · rw [← evalMasks_ofFn, hxs]
    exact hz
  · rcases hs with hs | ⟨l, r, t, ht, heq, hl, hr⟩
    · left; intro i; exact hs _ (List.getElem_mem _)
    · have hi : l.length < 4 := by rw [heq] at hn; simp at hn; omega
      let i : Fin 4 := ⟨l.length, hi⟩
      right; refine ⟨i, t, ht, ?_⟩
      intro j
      have hj : j.val < (l ++ 0 :: r).length := by rw [← heq, hn]; exact j.isLt
      have hm : m j = (l ++ 0 :: r)[j.val] := by
        exact List.getElem_of_eq heq _
      rw [hm, get_uniform_special l r t hl hr]
      by_cases hji : j = i
      · subst j; simp [i]
      · have hji' : j.val ≠ l.length := fun x => hji (Fin.ext x)
        simp [hji, hji']

theorem zero_get (k : Nat) : (0 : Word).getLsbD k = false := BitVec.getLsbD_zero

theorem summed_parity (f : Fin 3 → Positions → ℤ) (a : Positions → ℤ) (m : Fin 4 → Word)
    (ha : ∀ i j, parity (a (i, j)) = (m i).getLsbD j.val)
    (hz : xorFour (fun i => eval (packRow f i) (m i)) = 0) (k : Fin 3) :
    (2 : ℤ) ∣ ∑ v : Positions, f k v * a v := by
  have h := congrArg (fun w : Word => w.getLsbD k.val) hz
  simp only [xorFour, BitVec.getLsbD_xor, zero_get, row_parity f _ k _ a (ha _)] at h
  have hmod : parity (∑ v : Positions, f k v * a v) = false := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_four]
    simp only [parity_add, Bool.xor_assoc]
    exact h
  unfold parity at hmod
  have : (∑ v : Positions, f k v * a v) % 2 ≠ 1 := of_decide_eq_false hmod
  omega

theorem strong_row (t : Word) : t ∈ strong → 2 ≤ ∑ j : Fin 3, asInt (t.getLsbD j.val) := by
  revert t
  decide +kernel

theorem even_strong (t : Word) : t ∈ even → t ∈ strong := by revert t; decide +kernel

theorem even_missing (t : Word) : t ∈ even → ∃ j : Fin 3, t.getLsbD j.val = false := by
  revert t
  decide +kernel

theorem half_point (f : Fin 3 → Positions → ℤ) :
    ∃ a : Positions → ℤ,
      (∀ v, 0 ≤ a v ∧ a v ≤ 2) ∧
      (∀ i : Fin 4, 2 ≤ ∑ j : Fin 3, a (i, j)) ∧
      (∀ (i i' : Fin 4) (j : Fin 3), i ≠ i' → a (i, j) + a (i', j) ≤ 2) ∧
      (∀ k : Fin 3, (2 : ℤ) ∣ ∑ v : Positions, f k v * a v) := by
  obtain ⟨m, hz, hs⟩ := four_masks_fin (packRow f)
  rcases hs with hs | ⟨i₀, t, ht, hm⟩
  · let a : Positions → ℤ := fun v => asInt ((m v.1).getLsbD v.2.val)
    refine ⟨a, ?_, ?_, ?_, summed_parity f a m (by intro i j; exact parity_asInt _) hz⟩
    · intro v
      have h := asInt_bounds ((m v.1).getLsbD v.2.val)
      exact ⟨h.1, h.2.trans (by decide)⟩
    · intro i; exact strong_row _ (hs i)
    · intro i i' j _
      have h := (asInt_bounds ((m i).getLsbD j.val)).2
      have h' := (asInt_bounds ((m i').getLsbD j.val)).2
      change asInt ((m i).getLsbD j.val) + asInt ((m i').getLsbD j.val) ≤ 2
      omega
  · obtain ⟨j₀, hj₀⟩ := even_missing t ht
    let a : Positions → ℤ := fun v =>
      if v.1 = i₀ then if v.2 = j₀ then 2 else 0 else asInt (t.getLsbD v.2.val)
    have ha0 (j : Fin 3) : a (i₀, j) = (if j = j₀ then 2 else 0) := by simp [a]
    have ha1 (i : Fin 4) (hi : i ≠ i₀) (j : Fin 3) : a (i, j) = asInt (t.getLsbD j.val) := by simp [a, hi]
    refine ⟨a, ?_, ?_, ?_, summed_parity f a m ?_ hz⟩
    · intro ⟨i, j⟩
      by_cases hi : i = i₀
      · subst i; rw [ha0]; split <;> decide
      · rw [ha1 i hi]
        exact ⟨(asInt_bounds _).1, (asInt_bounds _).2.trans (by decide)⟩
    · intro i
      by_cases hi : i = i₀
      · subst i; simp [ha0]
      · simpa only [ha1 i hi] using strong_row t (even_strong t ht)
    · intro i i' j hne
      have hu := (asInt_bounds (t.getLsbD j.val)).2
      by_cases hi : i = i₀
      · subst i
        rw [ha0, ha1 _ hne.symm]
        by_cases hj : j = j₀
        · subst j; rw [ite_eq_left rfl, hj₀]; decide
        · simp only [ite_eq_right hj]; omega
      · by_cases hi' : i' = i₀
        · subst i'; rw [ha0, ha1 _ hi]
          by_cases hj : j = j₀
          · subst j; rw [ite_eq_left rfl, hj₀]; decide
          · simp only [ite_eq_right hj]; omega
        · rw [ha1 _ hi, ha1 _ hi']; omega
    · intro i j
      rw [hm i]
      by_cases hi : i = i₀
      · subst i; rw [ha0, ite_eq_left rfl, zero_get]; split <;> decide
      · rw [ha1 _ hi, ite_eq_right hi, parity_asInt]

end PEqualNP.Outside.L_meta_9672_aux.Sol9668HalfBridge

namespace PEqualNP.Outside.L_meta_9672_aux.Gemini9668Path

def closedUnder (incoming : ℕ → List ℕ) (live : Finset ℕ) : Prop :=
  ∀ i ∈ live, ∀ j ∈ incoming i, j ∈ live

def uses (incoming : ℕ → List ℕ) (live : Finset ℕ) (i : ℕ) : ℕ :=
  ∑ j ∈ live, (incoming j).count i

def step (incoming : ℕ → List ℕ) (live : Finset ℕ) (i j : ℕ) : Prop :=
  j ∈ live ∧ i ∈ incoming j

def Reach (incoming : ℕ → List ℕ) (live : Finset ℕ) (start x : ℕ) : Prop :=
  Relation.ReflTransGen (step incoming live) start x

noncomputable def affected (incoming : ℕ → List ℕ) (live : Finset ℕ) (start : ℕ) : Finset ℕ := by
  classical
  exact live.filter (fun x => Reach incoming live start x)

theorem mem_affected_iff {incoming : ℕ → List ℕ} {live : Finset ℕ} {start x : ℕ} :
    x ∈ affected incoming live start ↔ x ∈ live ∧ Reach incoming live start x := by
  classical
  simp [affected]

theorem reach_mem_live {incoming : ℕ → List ℕ} {live : Finset ℕ} {start x : ℕ}
    (hstart : start ∈ live) (h : Reach incoming live start x) : x ∈ live := by
  induction h with
  | refl => exact hstart
  | tail _ hstep _ => exact hstep.1

theorem mem_affected_of_reach {incoming : ℕ → List ℕ} {live : Finset ℕ} {start x : ℕ}
    (hstart : start ∈ live) (h : Reach incoming live start x) :
    x ∈ affected incoming live start :=
  mem_affected_iff.mpr ⟨reach_mem_live hstart h, h⟩

theorem reach_of_mem_affected {incoming : ℕ → List ℕ} {live : Finset ℕ} {start x : ℕ}
    (hx : x ∈ affected incoming live start) : Reach incoming live start x :=
  (mem_affected_iff.mp hx).2

theorem reach_le {incoming : ℕ → List ℕ} {live : Finset ℕ}
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    {start x : ℕ} (h : Reach incoming live start x) : start ≤ x := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    have hlt := horder _ hstep.1 _ hstep.2
    omega

theorem reaches_output_from_live {incoming : ℕ → List ℕ} {live : Finset ℕ} {root : ℕ}
    (hsub : live ⊆ Finset.range (root + 1))
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ incoming j) :
    ∀ x ∈ live, Reach incoming live x root := by
  suffices h : ∀ n x : ℕ, root - x = n → x ∈ live → Reach incoming live x root from
    fun x hx => h (root - x) x rfl hx
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro x hn hx
    by_cases hxr : x = root
    · subst hxr
      exact Relation.ReflTransGen.refl
    · obtain ⟨y, hy, hxy⟩ := hused x hx hxr
      have hxr_lt : x < root := by
        have := Finset.mem_range.mp (hsub hx)
        omega
      have hyr_le : y ≤ root := by
        have := Finset.mem_range.mp (hsub hy)
        omega
      have hlt : x < y := horder y hy x hxy
      have hdrop : root - y < n := by omega
      exact Relation.ReflTransGen.head ⟨hy, hxy⟩ (ih (root - y) hdrop y rfl hy)

theorem root_mem_affected {incoming : ℕ → List ℕ} {live : Finset ℕ} {root start : ℕ}
    (hroot : root ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ incoming j)
    (hstart : start ∈ live) :
    root ∈ affected incoming live start :=
  mem_affected_iff.mpr ⟨hroot, reaches_output_from_live hsub horder hused start hstart⟩

theorem complement_closed {incoming : ℕ → List ℕ} {live : Finset ℕ} {start : ℕ}
    (hclosed : closedUnder incoming live) :
    closedUnder incoming (live \ affected incoming live start) := by
  intro j hj i hij
  rw [Finset.mem_sdiff] at hj ⊢
  refine ⟨hclosed j hj.1 i hij, fun hi => hj.2 ?_⟩
  exact mem_affected_iff.mpr ⟨hj.1,
    Relation.ReflTransGen.tail (reach_of_mem_affected hi) ⟨hj.1, hij⟩⟩

theorem start_no_affected_input {incoming : ℕ → List ℕ} {live : Finset ℕ} {start : ℕ}
    (hstart : start ∈ live)
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i) :
    ∀ i ∈ incoming start, ¬ Reach incoming live start i := by
  intro i hi hreach
  have hle := reach_le horder hreach
  have hlt := horder start hstart i hi
  omega

theorem start_not_mem_affected_input {incoming : ℕ → List ℕ} {live : Finset ℕ} {start : ℕ}
    (hstart : start ∈ live)
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i) :
    ∀ i ∈ incoming start, i ∉ affected incoming live start := by
  intro i hi hmem
  exact start_no_affected_input hstart horder i hi (reach_of_mem_affected hmem)

theorem uses_one_unique_occ {incoming : ℕ → List ℕ} {live : Finset ℕ} {i j : ℕ}
    (hcount : uses incoming live i = 1) (hj : j ∈ live) (hij : i ∈ incoming j) :
    (incoming j).count i = 1 ∧ ∀ k ∈ live, i ∈ incoming k → k = j := by
  have hpos : 0 < (incoming j).count i := List.count_pos_iff.mpr hij
  have hle : (incoming j).count i ≤ uses incoming live i :=
    Finset.single_le_sum (f := fun x => (incoming x).count i) (fun _ _ => Nat.zero_le _) hj
  refine ⟨by omega, fun k hk hik => ?_⟩
  by_contra hne
  have hkpos : 0 < (incoming k).count i := List.count_pos_iff.mpr hik
  have hkmem : k ∈ live.erase j := Finset.mem_erase.mpr ⟨hne, hk⟩
  have hbound : (incoming k).count i ≤ ∑ x ∈ live.erase j, (incoming x).count i :=
    Finset.single_le_sum (f := fun x => (incoming x).count i) (fun _ _ => Nat.zero_le _) hkmem
  have hsum : (∑ x ∈ live.erase j, (incoming x).count i) + (incoming j).count i =
      uses incoming live i := Finset.sum_erase_add _ (fun x => (incoming x).count i) hj
  omega

theorem reach_comparable {incoming : ℕ → List ℕ} {live : Finset ℕ} {root start : ℕ}
    (hsub : live ⊆ Finset.range (root + 1))
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (huses1 : ∀ i, Reach incoming live start i → i ≠ root → uses incoming live i = 1) :
    ∀ {x y : ℕ}, Reach incoming live start x → Reach incoming live start y →
      Reach incoming live x y ∨ Reach incoming live y x := by
  intro x y hx
  induction hx generalizing y with
  | refl =>
    intro hy
    exact Or.inl hy
  | @tail a b ha hstep ih =>
    intro hy
    rcases ih hy with hay | hya
    · rcases Relation.ReflTransGen.cases_head hay with rfl | ⟨c, hac, hcy⟩
      · exact Or.inr (Relation.ReflTransGen.single hstep)
      · have hne : a ≠ root := by
          have hb_le : b ≤ root := by
            have := Finset.mem_range.mp (hsub hstep.1)
            omega
          have hlt := horder b hstep.1 a hstep.2
          omega
        have huniq := (uses_one_unique_occ (huses1 a ha hne) hstep.1 hstep.2).2 c hac.1 hac.2
        subst huniq
        exact Or.inl hcy
    · exact Or.inr (Relation.ReflTransGen.tail hya hstep)

theorem affected_unique_input {incoming : ℕ → List ℕ} {live : Finset ℕ} {root start : ℕ}
    (hsub : live ⊆ Finset.range (root + 1))
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (huses1 : ∀ i, Reach incoming live start i → i ≠ root → uses incoming live i = 1)
    {j : ℕ} (hj : Reach incoming live start j) (hne : j ≠ start) :
    ∃ i, Reach incoming live start i ∧ (incoming j).count i = 1 ∧
      ∀ i' ∈ incoming j, Reach incoming live start i' → i' = i := by
  rcases Relation.ReflTransGen.cases_tail hj with rfl | ⟨i, hi, hij⟩
  · exact absurd rfl hne
  · have hjl : j ∈ live := hij.1
    have hij_mem : i ∈ incoming j := hij.2
    have hjr : j ≤ root := by
      have := Finset.mem_range.mp (hsub hjl)
      omega
    have hir : i ≠ root := by
      have := horder j hjl i hij_mem
      omega
    have hcount := (uses_one_unique_occ (huses1 i hi hir) hjl hij_mem).1
    refine ⟨i, hi, hcount, fun i' hi'mem hi'reach => ?_⟩
    by_contra hi'ne
    rcases reach_comparable hsub horder huses1 hi'reach hi with hi'i | hii'
    · rcases Relation.ReflTransGen.cases_head hi'i with rfl | ⟨c, hi'c, hci⟩
      · exact hi'ne rfl
      · have hi'r : i' ≠ root := by
          have := horder j hjl i' hi'mem
          omega
        have hcj : c = j :=
          (uses_one_unique_occ (huses1 i' hi'reach hi'r) hjl hi'mem).2 c hi'c.1 hi'c.2
        rw [hcj] at hci
        have hjle := reach_le horder hci
        have hilt := horder j hjl i hij_mem
        omega
    · rcases Relation.ReflTransGen.cases_head hii' with rfl | ⟨c, hic, hci'⟩
      · exact hi'ne rfl
      · have hcj : c = j :=
          (uses_one_unique_occ (huses1 i hi hir) hjl hij_mem).2 c hic.1 hic.2
        rw [hcj] at hci'
        have hjle := reach_le horder hci'
        have hi'lt := horder j hjl i' hi'mem
        omega

private lemma length_filter_eq_countP (xs : List ℕ) (p : ℕ → Bool) :
    (xs.filter p).length = xs.countP p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hpx : p x <;> simp [hpx, ih]

private lemma sum_count_eq_countP (xs : List ℕ) (s : Finset ℕ) (p : ℕ → Bool)
    (hp : ∀ x, p x = true ↔ x ∈ s) :
    (∑ i ∈ s, xs.count i) = xs.countP p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, ih, List.countP_cons]
    by_cases hx : x ∈ s
    · have hpx : p x = true := (hp x).mpr hx
      have hsum : (∑ i ∈ s, if x = i then (1 : ℕ) else 0) = 1 := by
        rw [← Finset.sum_erase_add _ _ hx]
        have hz : (∑ i ∈ s.erase x, if x = i then (1 : ℕ) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [Finset.mem_erase] at hi
          simp [Ne.symm hi.1]
        simp [hz]
      rw [hsum, hpx]
      simp
    · have hpx : p x = false := Bool.eq_false_iff.mpr fun h => hx ((hp x).mp h)
      have hsum : (∑ i ∈ s, if x = i then (1 : ℕ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hne : x ≠ i := fun heq => hx (heq ▸ hi)
        simp [hne]
      rw [hsum, hpx]
      simp

theorem start_countP_affected_eq_zero {incoming : ℕ → List ℕ} {live : Finset ℕ} {start : ℕ}
    (hstart : start ∈ live)
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i) :
    (incoming start).countP (fun i => decide (i ∈ affected incoming live start)) = 0 := by
  rw [List.countP_eq_zero]
  intro i hi hdec
  have hmem : i ∈ affected incoming live start := of_decide_eq_true hdec
  exact start_not_mem_affected_input hstart horder i hi hmem

theorem start_sum_affected_counts_eq_zero {incoming : ℕ → List ℕ} {live : Finset ℕ} {start : ℕ}
    (hstart : start ∈ live)
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i) :
    (∑ i ∈ affected incoming live start, (incoming start).count i) = 0 := by
  rw [sum_count_eq_countP _ _ (fun i => decide (i ∈ affected incoming live start))
    (fun _ => decide_eq_true_iff)]
  exact start_countP_affected_eq_zero hstart horder

theorem affected_unique_input_counts {incoming : ℕ → List ℕ} {live : Finset ℕ} {root start : ℕ}
    (hsub : live ⊆ Finset.range (root + 1))
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (hstart : start ∈ live)
    (huses1 : ∀ i, Reach incoming live start i → i ≠ root → uses incoming live i = 1)
    {j : ℕ} (hj : j ∈ affected incoming live start) (hne : j ≠ start) :
    (∑ i ∈ affected incoming live start, (incoming j).count i) = 1 ∧
      ∃! p : Fin (incoming j).length, (incoming j)[p] ∈ affected incoming live start := by
  obtain ⟨i, hi, hcount, huniq⟩ :=
    affected_unique_input hsub horder huses1 (reach_of_mem_affected hj) hne
  have hia : i ∈ affected incoming live start := mem_affected_of_reach hstart hi
  have hsum : (∑ x ∈ affected incoming live start, (incoming j).count x) = 1 := by
    rw [← Finset.sum_erase_add _ _ hia, hcount]
    have hzero : (∑ x ∈ (affected incoming live start).erase i, (incoming j).count x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finset.mem_erase] at hx
      apply List.count_eq_zero.mpr
      intro hmem
      exact hx.1 (huniq x hmem (reach_of_mem_affected hx.2))
    omega
  refine ⟨hsum, ?_⟩
  have himem : i ∈ incoming j := List.count_pos_iff.mp (by omega)
  obtain ⟨p, hp, heq⟩ := List.getElem_of_mem himem
  refine ⟨⟨p, hp⟩, by simpa [heq] using hia, ?_⟩
  intro q hq
  have hqmem : (incoming j)[q] ∈ incoming j := List.getElem_mem _
  have hqi : (incoming j)[q] = i := huniq _ hqmem (reach_of_mem_affected hq)
  by_contra hne_q
  have hne_val : q.val ≠ p := fun h => hne_q (Fin.ext h)
  have hcount_ge2 : 2 ≤ (incoming j).count i := by
    have hlist :
        ∀ (xs : List ℕ) (a b : Fin xs.length), a ≠ b → xs[a] = i → xs[b] = i → 2 ≤ xs.count i := by
      intro xs a b hab ha hb
      induction xs with
      | nil => exact Fin.elim0 a
      | cons x xs ih =>
        rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩ <;>
          rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
        · exact absurd rfl hab
        · change x = i at ha
          change xs[b'] = i at hb
          have hpos : 0 < xs.count i := List.count_pos_iff.mpr (hb ▸ List.getElem_mem _)
          rw [ha, List.count_cons_self]
          omega
        · change xs[a'] = i at ha
          change x = i at hb
          have hpos : 0 < xs.count i := List.count_pos_iff.mpr (ha ▸ List.getElem_mem _)
          rw [hb, List.count_cons_self]
          omega
        · have hab' : a' ≠ b' := fun h => hab (congrArg Fin.succ h)
          change xs[a'] = i at ha
          change xs[b'] = i at hb
          have h1 := ih a' b' hab' ha hb
          rw [List.count_cons]
          omega
    exact hlist (incoming j) q ⟨p, hp⟩ (fun h => hne_val (congrArg Fin.val h)) hqi heq
  omega

theorem affected_countP_eq_one {incoming : ℕ → List ℕ} {live : Finset ℕ} {root start : ℕ}
    (hsub : live ⊆ Finset.range (root + 1))
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (hstart : start ∈ live)
    (huses1 : ∀ i, Reach incoming live start i → i ≠ root → uses incoming live i = 1)
    {j : ℕ} (hj : j ∈ affected incoming live start) (hne : j ≠ start) :
    (incoming j).countP (fun i => decide (i ∈ affected incoming live start)) = 1 := by
  have hsum := (affected_unique_input_counts hsub horder hstart huses1 hj hne).1
  rw [← sum_count_eq_countP _ _ _ (fun _ => decide_eq_true_iff)]
  exact hsum

theorem affected_filter_length_eq_one {incoming : ℕ → List ℕ} {live : Finset ℕ} {root start : ℕ}
    (hsub : live ⊆ Finset.range (root + 1))
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (hstart : start ∈ live)
    (huses1 : ∀ i, Reach incoming live start i → i ≠ root → uses incoming live i = 1)
    {j : ℕ} (hj : j ∈ affected incoming live start) (hne : j ≠ start) :
    ((incoming j).filter (fun i => decide (i ∈ affected incoming live start))).length = 1 := by
  rw [length_filter_eq_countP]
  exact affected_countP_eq_one hsub horder hstart huses1 hj hne

noncomputable def upChain (next : ℕ → ℕ) (root x : ℕ) : List ℕ :=
  if _ : x < next x ∧ next x ≤ root then x :: upChain next root (next x) else [x]
termination_by root - x
decreasing_by omega

theorem upChain_ne_nil (next : ℕ → ℕ) (root x : ℕ) : upChain next root x ≠ [] := by
  rw [upChain]
  split_ifs <;> simp

theorem upChain_head? (next : ℕ → ℕ) (root x : ℕ) : (upChain next root x).head? = some x := by
  rw [upChain]
  split_ifs <;> rfl

theorem exists_unique_upward_path {incoming : ℕ → List ℕ} {live : Finset ℕ} {root start : ℕ}
    (hroot : root ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ incoming j)
    (hstart : start ∈ live)
    (huses1 : ∀ i, Reach incoming live start i → i ≠ root → uses incoming live i = 1) :
    ∃ path : List ℕ,
      path ≠ [] ∧
      path.head? = some start ∧
      path.getLast? = some root ∧
      path.Pairwise (· < ·) ∧
      (∀ x, x ∈ path ↔ x ∈ affected incoming live start) ∧
      path.IsChain (fun a b => b ∈ live ∧ (incoming b).count a = 1 ∧
        ∀ i ∈ incoming b, i ∈ affected incoming live start → i = a) := by
  classical
  let next (x : ℕ) : ℕ :=
    if hx : x ∈ live.erase root then
      Classical.choose (hused x (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1)
    else root
  have hnext_spec : ∀ {x : ℕ}, Reach incoming live start x → x ≠ root →
      next x ∈ live ∧ x ∈ incoming (next x) ∧ x < next x ∧ next x ≤ root ∧
        Reach incoming live start (next x) := by
    intro x hx hne
    have hxl : x ∈ live := reach_mem_live hstart hx
    have hxer : x ∈ live.erase root := Finset.mem_erase.mpr ⟨hne, hxl⟩
    have hs := Classical.choose_spec (hused x hxl hne)
    have hnx : next x = Classical.choose (hused x hxl hne) := by
      simp [next, hne, hxl]
    rw [hnx]
    have hlt := horder _ hs.1 _ hs.2
    have hle : Classical.choose (hused x hxl hne) ≤ root := by
      have := Finset.mem_range.mp (hsub hs.1)
      omega
    exact ⟨hs.1, hs.2, hlt, hle, Relation.ReflTransGen.tail hx ⟨hs.1, hs.2⟩⟩
  have hnext_root : next root = root := by
    simp only [next, Finset.notMem_erase, ↓reduceDIte]
  have hstep_eq : ∀ {x y : ℕ}, Reach incoming live start x → step incoming live x y → y = next x := by
    intro x y hx hxy
    have hxr : x ≠ root := by
      have hyr : y ≤ root := by
        have := Finset.mem_range.mp (hsub hxy.1)
        omega
      have hlt := horder y hxy.1 x hxy.2
      omega
    obtain ⟨hnxl, hxnx, _, _, _⟩ := hnext_spec hx hxr
    exact (uses_one_unique_occ (huses1 x hx hxr) hnxl hxnx).2 y hxy.1 hxy.2
  have hprops : ∀ n x : ℕ, root - x = n → Reach incoming live start x →
      (upChain next root x).getLast? = some root ∧
      (∀ z ∈ upChain next root x, x ≤ z) ∧
      (upChain next root x).Pairwise (· < ·) ∧
      (∀ z, z ∈ upChain next root x ↔ Reach incoming live x z) ∧
      (upChain next root x).IsChain (fun a b => b ∈ live ∧ (incoming b).count a = 1 ∧
        ∀ i ∈ incoming b, i ∈ affected incoming live start → i = a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro x hn hx
      by_cases hxr : x = root
      · subst x
        have huc : upChain next root root = [root] := by
          rw [upChain, hnext_root]
          simp
        rw [huc]
        refine ⟨rfl, ?_, List.pairwise_singleton _ _, ?_, List.isChain_singleton root⟩
        · intro z hz
          rw [List.mem_singleton.mp hz]
        · intro z
          rw [List.mem_singleton]
          constructor
          · rintro rfl
            exact Relation.ReflTransGen.refl
          · intro hrz
            have hle := reach_le horder hrz
            have hzl := reach_mem_live hroot hrz
            have hzr : z ≤ root := by
              have := Finset.mem_range.mp (hsub hzl)
              omega
            omega
      · obtain ⟨hnxl, hxnx, hlt, hle, hnx_reach⟩ := hnext_spec hx hxr
        have hdrop : root - next x < n := by omega
        obtain ⟨hlast, hge, hpw, hmem, hchain⟩ := ih (root - next x) hdrop (next x) rfl hnx_reach
        have huc : upChain next root x = x :: upChain next root (next x) := by
          rw [upChain]
          simp [hlt, hle]
        rw [huc]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [List.getLast?_cons_of_ne_nil (upChain_ne_nil next root (next x))]
          exact hlast
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact le_rfl
          · exact le_trans hlt.le (hge z hz')
        · rw [List.pairwise_cons]
          exact ⟨fun z hz => lt_of_lt_of_le hlt (hge z hz), hpw⟩
        · intro z
          rw [List.mem_cons, hmem z]
          constructor
          · rintro (rfl | hnz)
            · exact Relation.ReflTransGen.refl
            · exact Relation.ReflTransGen.head ⟨hnxl, hxnx⟩ hnz
          · intro hxz
            rcases Relation.ReflTransGen.cases_head hxz with rfl | ⟨y, hxy, hyz⟩
            · exact Or.inl rfl
            · have hy_eq := hstep_eq hx hxy
              subst hy_eq
              exact Or.inr hyz
        · have hne_start : next x ≠ start := by
            have hx_le := reach_le horder hx
            omega
          obtain ⟨i, hi_reach, hicount, hiuniq⟩ :=
            affected_unique_input hsub horder huses1 hnx_reach hne_start
          have hx_eq_i : x = i := hiuniq x hxnx hx
          subst x
          have hrel : next i ∈ live ∧ (incoming (next i)).count i = 1 ∧
              ∀ i' ∈ incoming (next i), i' ∈ affected incoming live start → i' = i :=
            ⟨hnxl, hicount, fun i' hi'mem hi'aff =>
              hiuniq i' hi'mem (reach_of_mem_affected hi'aff)⟩
          cases htail_eq : upChain next root (next i) with
          | nil => exact absurd htail_eq (upChain_ne_nil next root (next i))
          | cons hd tl =>
            have hhd : (upChain next root (next i)).head? = some (next i) :=
              upChain_head? next root (next i)
            rw [htail_eq, List.head?_cons] at hhd
            injection hhd with hhd_eq
            subst hhd_eq
            rw [htail_eq] at hchain
            exact List.isChain_cons_cons.mpr ⟨hrel, hchain⟩
  obtain ⟨hlast, _, hpw, hmem, hchain⟩ :=
    hprops (root - start) start rfl Relation.ReflTransGen.refl
  refine ⟨upChain next root start, upChain_ne_nil next root start,
    upChain_head? next root start, hlast, hpw, ?_, hchain⟩
  intro x
  rw [hmem x, mem_affected_iff]
  exact ⟨fun hx => ⟨reach_mem_live hstart hx, hx⟩, fun hx => hx.2⟩

theorem affected_dag_summary {incoming : ℕ → List ℕ} {live : Finset ℕ} {root start : ℕ}
    (hroot : root ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (hclosed : closedUnder incoming live)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ incoming j)
    (hstart : start ∈ live)
    (huses1 : ∀ i, Reach incoming live start i → i ≠ root → uses incoming live i = 1) :
    root ∈ affected incoming live start ∧
    closedUnder incoming (live \ affected incoming live start) ∧
    (∀ i ∈ incoming start, i ∉ affected incoming live start) ∧
    (∀ j ∈ affected incoming live start, j ≠ start →
      (∑ i ∈ affected incoming live start, (incoming j).count i) = 1 ∧
      ((incoming j).filter (fun i => decide (i ∈ affected incoming live start))).length = 1 ∧
      ∃ i ∈ affected incoming live start, (incoming j).count i = 1 ∧
        ∀ i' ∈ incoming j, i' ∈ affected incoming live start → i' = i) ∧
    (∃ path : List ℕ,
      path ≠ [] ∧
      path.head? = some start ∧
      path.getLast? = some root ∧
      path.Pairwise (· < ·) ∧
      (∀ x, x ∈ path ↔ x ∈ affected incoming live start) ∧
      path.IsChain (fun a b => b ∈ live ∧ (incoming b).count a = 1 ∧
        ∀ i ∈ incoming b, i ∈ affected incoming live start → i = a)) := by
  refine ⟨root_mem_affected hroot hsub horder hused hstart,
    complement_closed hclosed,
    start_not_mem_affected_input hstart horder, ?_,
    exists_unique_upward_path hroot hsub horder hused hstart huses1⟩
  intro j hj hne
  obtain ⟨i, hi, hcount, huniq⟩ :=
    affected_unique_input hsub horder huses1 (reach_of_mem_affected hj) hne
  exact ⟨(affected_unique_input_counts hsub horder hstart huses1 hj hne).1,
    affected_filter_length_eq_one hsub horder hstart huses1 hj hne,
    i, mem_affected_of_reach hstart hi, hcount,
    fun i' hi'mem hi'aff => huniq i' hi'mem (reach_of_mem_affected hi'aff)⟩

end PEqualNP.Outside.L_meta_9672_aux.Gemini9668Path

namespace PEqualNP.Outside.L_meta_9672_aux.Sol9668Cones

open Gemini9668Path
open scoped BigOperators

noncomputable def cone (incoming : ℕ → List ℕ) (live : Finset ℕ) (p : ℕ) : Finset ℕ := by
  classical
  exact live.filter (fun i => Reach incoming live i p)

noncomputable def outer (incoming : ℕ → List ℕ) (live : Finset ℕ) (p : ℕ) : Finset ℕ :=
  live \ (cone incoming live p).erase p

def cutIncoming (incoming : ℕ → List ℕ) (p i : ℕ) : List ℕ :=
  if i = p then [] else incoming i

def leaves (incoming : ℕ → List ℕ) (live : Finset ℕ) : Finset ℕ :=
  live.filter (fun i => incoming i = [])

@[local simp] theorem mem_cone {incoming : ℕ → List ℕ} {live : Finset ℕ} {p i : ℕ} :
    i ∈ cone incoming live p ↔ i ∈ live ∧ Reach incoming live i p := by
  classical
  simp [cone]

@[local simp] theorem mem_outer {incoming : ℕ → List ℕ} {live : Finset ℕ} {p i : ℕ} :
    i ∈ outer incoming live p ↔ i ∈ live ∧ (i ≠ p → i ∉ cone incoming live p) := by
  simp [outer, Finset.mem_erase]

@[local simp] theorem mem_leaves {incoming : ℕ → List ℕ} {live : Finset ℕ} {i : ℕ} :
    i ∈ leaves incoming live ↔ i ∈ live ∧ incoming i = [] := by
  simp [leaves]

theorem cone_subset {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ} :
    cone incoming live p ⊆ live := fun _ h => (mem_cone.mp h).1

theorem outer_subset {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ} :
    outer incoming live p ⊆ live := fun _ h => (mem_outer.mp h).1

theorem pivot_mem_cone {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ} (hp : p ∈ live) :
    p ∈ cone incoming live p := mem_cone.mpr ⟨hp, Relation.ReflTransGen.refl⟩

theorem pivot_mem_outer {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ} (hp : p ∈ live) :
    p ∈ outer incoming live p := mem_outer.mpr ⟨hp, fun h => (h rfl).elim⟩

theorem cone_bound {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ}
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i) :
    cone incoming live p ⊆ Finset.range (p + 1) := by
  intro i hi
  have hle := reach_le horder (mem_cone.mp hi).2
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)

theorem cone_order {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ}
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i) :
    ∀ i ∈ cone incoming live p, ∀ j ∈ incoming i, j < i :=
  fun i hi => horder i (cone_subset hi)

theorem cone_closed {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ}
    (hclosed : closedUnder incoming live) : closedUnder incoming (cone incoming live p) := by
  intro j hj i hij
  obtain ⟨hjl, hjp⟩ := mem_cone.mp hj
  exact mem_cone.mpr ⟨hclosed j hjl i hij, Relation.ReflTransGen.head ⟨hjl, hij⟩ hjp⟩

theorem cone_used {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ} :
    ∀ i ∈ cone incoming live p, i ≠ p → ∃ j ∈ cone incoming live p, i ∈ incoming j := by
  intro i hi hne
  rcases Relation.ReflTransGen.cases_head (mem_cone.mp hi).2 with he | ⟨j, hstep, hjp⟩
  · exact (hne he).elim
  · exact ⟨j, mem_cone.mpr ⟨hstep.1, hjp⟩, hstep.2⟩

theorem pos_uses_of_reader {incoming : ℕ → List ℕ} {live : Finset ℕ} {i j : ℕ}
    (hj : j ∈ live) (hij : i ∈ incoming j) : 0 < uses incoming live i := by
  have hpos : 0 < (incoming j).count i := List.count_pos_iff.mpr hij
  exact hpos.trans_le (Finset.single_le_sum (f := fun k => (incoming k).count i)
    (fun _ _ => Nat.zero_le _) hj)

theorem cone_uses_one_of_local_unique {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ}
    (huniq : ∀ i ∈ cone incoming live p, i ≠ p → uses incoming live i = 1) :
    ∀ i ∈ cone incoming live p, i ≠ p → uses incoming (cone incoming live p) i = 1 := by
  intro i hi hne
  obtain ⟨j, hj, hij⟩ := cone_used i hi hne
  have hpos := pos_uses_of_reader hj hij
  have hle : uses incoming (cone incoming live p) i ≤ uses incoming live i :=
    Finset.sum_le_sum_of_subset_of_nonneg cone_subset (fun _ _ _ => Nat.zero_le _)
  have hg := huniq i hi hne
  omega

theorem local_unique_of_global_unique {incoming : ℕ → List ℕ} {live : Finset ℕ} {root p : ℕ}
    (hp : p ∈ live) (hbound : live ⊆ Finset.range (root + 1))
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (huniq : ∀ i ∈ live, i ≠ root → i ≠ p → uses incoming live i = 1) :
    ∀ i ∈ cone incoming live p, i ≠ p → uses incoming live i = 1 := by
  intro i hi hne
  have hip := reach_le horder (mem_cone.mp hi).2
  have hpr := Finset.mem_range.mp (hbound hp)
  exact huniq i (cone_subset hi) (by omega) hne

theorem cone_uses_one {incoming : ℕ → List ℕ} {live : Finset ℕ} {root p : ℕ}
    (hp : p ∈ live) (hbound : live ⊆ Finset.range (root + 1))
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (huniq : ∀ i ∈ live, i ≠ root → i ≠ p → uses incoming live i = 1) :
    ∀ i ∈ cone incoming live p, i ≠ p → uses incoming (cone incoming live p) i = 1 :=
  cone_uses_one_of_local_unique (local_unique_of_global_unique hp hbound horder huniq)

theorem root_mem_outer {incoming : ℕ → List ℕ} {live : Finset ℕ} {root p : ℕ}
    (hroot : root ∈ live) (hp : p ∈ live) (hbound : live ⊆ Finset.range (root + 1))
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i) : root ∈ outer incoming live p := by
  refine mem_outer.mpr ⟨hroot, fun hne hcone => ?_⟩
  have hrp := reach_le horder (mem_cone.mp hcone).2
  have hpr := Finset.mem_range.mp (hbound hp)
  omega

theorem outer_bound {incoming : ℕ → List ℕ} {live : Finset ℕ} {root p : ℕ}
    (hbound : live ⊆ Finset.range (root + 1)) :
    outer incoming live p ⊆ Finset.range (root + 1) := fun _ h => hbound (outer_subset h)

theorem outer_order {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ}
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i) :
    ∀ i ∈ outer incoming live p, ∀ j ∈ cutIncoming incoming p i, j < i := by
  intro i hi j hj
  by_cases he : i = p
  · simp [cutIncoming, he] at hj
  · exact horder i (outer_subset hi) j (by simpa [cutIncoming, he] using hj)

theorem outer_original_reader {incoming : ℕ → List ℕ} {live : Finset ℕ} {p i j : ℕ}
    (hp : p ∈ live) (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (hclosed : closedUnder incoming live) (hi : i ∈ outer incoming live p)
    (hj : j ∈ live) (hij : i ∈ incoming j) : j ∈ outer incoming live p ∧ j ≠ p := by
  have hn : j ∉ cone incoming live p := by
    intro hc
    have hlt := horder j hj i hij
    have hjp := reach_le horder (mem_cone.mp hc).2
    have hic := cone_closed hclosed j hc i hij
    exact (mem_outer.mp hi).2 (by omega) hic
  refine ⟨mem_outer.mpr ⟨hj, fun _ => hn⟩, ?_⟩
  intro he
  subst j
  exact hn (pivot_mem_cone hp)

theorem outer_closed {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ}
    (hclosed : closedUnder incoming live)
    (huniq : ∀ i ∈ cone incoming live p, i ≠ p → uses incoming live i = 1) :
    closedUnder (cutIncoming incoming p) (outer incoming live p) := by
  intro j hj i hij
  by_cases hne : j = p
  · simp [cutIncoming, hne] at hij
  have hjl := outer_subset hj
  have hij' : i ∈ incoming j := by simpa [cutIncoming, hne] using hij
  refine mem_outer.mpr ⟨hclosed j hjl i hij', fun hip hic => ?_⟩
  obtain ⟨k, hk, hik⟩ := cone_used i hic hip
  have eq := (uses_one_unique_occ (huniq i hic hip) (cone_subset hk) hik).2 j hjl hij'
  exact (mem_outer.mp hj).2 hne (eq.symm ▸ hk)

theorem outer_closed_of_global_unique {incoming : ℕ → List ℕ} {live : Finset ℕ} {root p : ℕ}
    (hp : p ∈ live) (hbound : live ⊆ Finset.range (root + 1))
    (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i) (hclosed : closedUnder incoming live)
    (huniq : ∀ i ∈ live, i ≠ root → i ≠ p → uses incoming live i = 1) :
    closedUnder (cutIncoming incoming p) (outer incoming live p) :=
  outer_closed hclosed (local_unique_of_global_unique hp hbound horder huniq)

theorem outer_uses_eq {incoming : ℕ → List ℕ} {live : Finset ℕ} {p i : ℕ}
    (hp : p ∈ live) (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (hclosed : closedUnder incoming live) (hi : i ∈ outer incoming live p) :
    uses (cutIncoming incoming p) (outer incoming live p) i = uses incoming live i := by
  unfold uses
  calc
    (∑ j ∈ outer incoming live p, (cutIncoming incoming p j).count i) =
        ∑ j ∈ outer incoming live p, (incoming j).count i := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hne : j = p
      · subst j
        have hn : i ∉ incoming p := fun h =>
          (outer_original_reader hp horder hclosed hi hp h).2 rfl
        simp [cutIncoming, List.count_eq_zero_of_not_mem hn]
      · simp [cutIncoming, hne]
    _ = ∑ j ∈ live, (incoming j).count i := by
      apply Finset.sum_subset outer_subset
      intro j hj hnj
      exact List.count_eq_zero_of_not_mem fun hij =>
        hnj (outer_original_reader hp horder hclosed hi hj hij).1

theorem outer_used {incoming : ℕ → List ℕ} {live : Finset ℕ} {root p : ℕ}
    (hp : p ∈ live) (horder : ∀ i ∈ live, ∀ j ∈ incoming i, j < i)
    (hclosed : closedUnder incoming live)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ incoming j) :
    ∀ i ∈ outer incoming live p, i ≠ root →
      ∃ j ∈ outer incoming live p, i ∈ cutIncoming incoming p j := by
  intro i hi hn
  obtain ⟨j, hj, hij⟩ := hused i (outer_subset hi) hn
  obtain ⟨hjo, hjp⟩ := outer_original_reader hp horder hclosed hi hj hij
  exact ⟨j, hjo, by simpa [cutIncoming, hjp] using hij⟩

theorem partition {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ} :
    cone incoming live p ∪ (outer incoming live p).erase p = live := by
  classical
  ext i
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact cone_subset h
    · exact outer_subset (Finset.mem_erase.mp h).2
  · intro hi
    by_cases hc : i ∈ cone incoming live p
    · exact Finset.mem_union_left _ hc
    · refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, mem_outer.mpr ⟨hi, fun _ => hc⟩⟩)
      exact fun he => hc (he ▸ pivot_mem_cone (he.symm ▸ hi))

theorem partition_disjoint {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ} :
    Disjoint (cone incoming live p) ((outer incoming live p).erase p) := by
  apply Finset.disjoint_left.mpr
  intro i hi hio
  obtain ⟨hne, houter⟩ := Finset.mem_erase.mp hio
  exact (mem_outer.mp houter).2 hne hi

theorem leaves_partition {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ} :
    leaves incoming live = leaves incoming (cone incoming live p) ∪
      leaves incoming ((outer incoming live p).erase p) := by
  calc
    leaves incoming live = leaves incoming (cone incoming live p ∪ (outer incoming live p).erase p) :=
      congrArg (leaves incoming) (partition (incoming := incoming) (live := live) (p := p)).symm
    _ = leaves incoming (cone incoming live p) ∪
        leaves incoming ((outer incoming live p).erase p) := by
      simp only [leaves, Finset.filter_union]

theorem leaves_partition_disjoint {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ} :
    Disjoint (leaves incoming (cone incoming live p))
      (leaves incoming ((outer incoming live p).erase p)) := by
  exact partition_disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem outer_cut_leaves {incoming : ℕ → List ℕ} {live : Finset ℕ} {p : ℕ} (hp : p ∈ live) :
    leaves (cutIncoming incoming p) (outer incoming live p) =
      insert p (leaves incoming ((outer incoming live p).erase p)) := by
  ext i
  by_cases he : i = p
  · subst i
    exact iff_of_true (mem_leaves.mpr ⟨pivot_mem_outer hp, by simp [cutIncoming]⟩) (by simp)
  · constructor
    · intro h
      obtain ⟨hi, hcut⟩ := mem_leaves.mp h
      exact Finset.mem_insert_of_mem (mem_leaves.mpr
        ⟨Finset.mem_erase.mpr ⟨he, hi⟩, by simpa [cutIncoming, he] using hcut⟩)
    · intro h
      obtain ⟨hi, hin⟩ := mem_leaves.mp ((Finset.mem_insert.mp h).resolve_left he)
      exact mem_leaves.mpr ⟨(Finset.mem_erase.mp hi).2, by simpa [cutIncoming, he] using hin⟩

end PEqualNP.Outside.L_meta_9672_aux.Sol9668Cones

namespace PEqualNP.Outside.L_meta_9672_aux.CPGraphScratch

open PEqualNP.Search PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

abbrev AxiomRule (V : Type) [DecidableEq V] := Clause V ⊕ (V ⊕ V)

abbrev DerivedRule := (ℕ × ℕ) ⊕ ((ℕ × ℕ) ⊕ (ℕ × ℕ))

abbrev Rule (V : Type) [DecidableEq V] := AxiomRule V ⊕ DerivedRule

def earlier (previous : List (CPLine V)) (i : ℕ) : CPLine V :=
  previous.reverse.getD i (0, 0)

def legalRule (F : Set (Clause V)) (size : ℕ) (read : ℕ → CPLine V)
    (line : CPLine V) : Rule V → Prop
  | .inl (.inl C) => C ∈ F ∧ line = clauseCP C
  | .inl (.inr (.inl v)) => line = (fun u => if u = v then 1 else 0, 0)
  | .inl (.inr (.inr v)) => line = (fun u => if u = v then -1 else 0, -1)
  | .inr (.inl (a, b)) => a < size ∧ b < size ∧
      line = ((read a).1 + (read b).1, (read a).2 + (read b).2)
  | .inr (.inr (.inl (a, d))) => a < size ∧
      line = (((d : ℤ) • (read a).1), (d : ℤ) * (read a).2)
  | .inr (.inr (.inr (a, d))) => a < size ∧ 0 < d ∧
      (∀ v, (d : ℤ) ∣ (read a).1 v) ∧
      line = (fun v => (read a).1 v / (d : ℤ), -((-(read a).2) / (d : ℤ)))

def validRule (F : Set (Clause V)) (previous : List (CPLine V))
    (line : CPLine V) : Rule V → Prop :=
  legalRule F previous.length (earlier previous) line

def traced (F : Set (Clause V)) : List (CPLine V) → List (Rule V) → Prop
  | [], [] => True
  | e :: previous, r :: rs => traced F previous rs ∧ validRule F previous e r
  | _, _ => False

def parents : Rule V → List ℕ
  | .inl _ => []
  | .inr (.inl (a, b)) => [a, b]
  | .inr (.inr (.inl (a, _))) => [a]
  | .inr (.inr (.inr (a, _))) => [a]

omit [DecidableEq V] in
theorem find_earlier {previous : List (CPLine V)} {e : CPLine V} (h : e ∈ previous) :
    ∃ j < previous.length, earlier previous j = e := by
  obtain ⟨j, hj, eq⟩ := List.getElem_of_mem (List.mem_reverse.mpr h)
  refine ⟨j, by simpa using hj, ?_⟩
  rwa [earlier, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem extract {F : Set (Clause V)} {π : List (CPLine V)}
    (h : IsCPDerivation F π) : ∃ r : List (Rule V), traced F π r := by
  induction h with
  | nil =>
    exact ⟨[], trivial⟩
  | ax C _ hC ih =>
    obtain ⟨rs, hrs⟩ := ih
    exact ⟨.inl (.inl C) :: rs, hrs, hC, rfl⟩
  | boolLo v _ ih =>
    obtain ⟨rs, hrs⟩ := ih
    exact ⟨.inl (.inr (.inl v)) :: rs, hrs, rfl⟩
  | boolHi v _ ih =>
    obtain ⟨rs, hrs⟩ := ih
    exact ⟨.inl (.inr (.inr v)) :: rs, hrs, rfl⟩
  | add _ he he' ih =>
    obtain ⟨rs, hrs⟩ := ih
    obtain ⟨a, ha, ea⟩ := find_earlier he
    obtain ⟨b, hb, eb⟩ := find_earlier he'
    exact ⟨.inr (.inl (a, b)) :: rs, hrs, ha, hb, by rw [ea, eb]⟩
  | mul d _ he ih =>
    obtain ⟨rs, hrs⟩ := ih
    obtain ⟨a, ha, ea⟩ := find_earlier he
    exact ⟨.inr (.inr (.inl (a, d))) :: rs, hrs, ha, by rw [ea]⟩
  | div d _ he hd hdvd ih =>
    obtain ⟨rs, hrs⟩ := ih
    obtain ⟨a, ha, ea⟩ := find_earlier he
    exact ⟨.inr (.inr (.inr (a, d))) :: rs, hrs, ha, hd,
      by simpa only [ea] using hdvd, by rw [ea]⟩

theorem trace_length {F : Set (Clause V)} {π : List (CPLine V)} {rs : List (Rule V)}
    (h : traced F π rs) : rs.length = π.length := by
  induction π generalizing rs with
  | nil => cases rs <;> simp_all [traced]
  | cons e previous ih =>
    cases rs with
    | nil => exact False.elim h
    | cons r rs => simpa only [List.length_cons] using congrArg Nat.succ (ih h.1)

theorem parent_lt {F : Set (Clause V)} {size : ℕ} {read : ℕ → CPLine V}
    {r : Rule V} {e : CPLine V} (h : legalRule F size read e r) :
    ∀ i ∈ parents r, i < size := by
  intro i hi
  rcases r with ax | r
  · exact False.elim (List.not_mem_nil hi)
  · rcases r with ab | sub
    · rcases ab with ⟨a, b⟩
      rcases List.mem_pair.mp hi with rfl | rfl
      · exact h.1
      · exact h.2.1
    · rcases sub with ad | ad <;> rcases ad with ⟨a, d⟩
      all_goals
        have hi' : i = a := List.mem_singleton.mp hi
        exact hi'.symm ▸ h.1

theorem legalRule_congr {F : Set (Clause V)} {size : ℕ} {read new : ℕ → CPLine V}
    {r : Rule V} {e : CPLine V} (h : legalRule F size read e r)
    (agree : ∀ i < size, new i = read i) : legalRule F size new e r := by
  rcases r with ax | r
  · rcases ax with C | v
    · exact h
    · cases v <;> exact h
  · rcases r with ⟨a, b⟩ | (⟨a, k⟩ | ⟨a, d⟩)
    · obtain ⟨ha, hb, he⟩ := h
      exact ⟨ha, hb, by simpa only [agree a ha, agree b hb] using he⟩
    · obtain ⟨ha, he⟩ := h
      exact ⟨ha, by simpa only [agree a ha] using he⟩
    · obtain ⟨ha, hd, hdiv, he⟩ := h
      exact ⟨ha, hd, by simpa only [agree a ha] using hdiv,
        by simpa only [agree a ha] using he⟩

omit [DecidableEq V] in
theorem earlier_cons_lt (π : List (CPLine V)) (e : CPLine V)
    {i : ℕ} (hi : i < π.length) : earlier (e :: π) i = earlier π i := by
  have h : i < π.reverse.length := by simpa using hi
  simp only [earlier, List.reverse_cons, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

omit [DecidableEq V] in
theorem earlier_cons_last (π : List (CPLine V)) (e : CPLine V) :
    earlier (e :: π) π.length = e := by
  simp [earlier, List.getD_eq_getElem?_getD]

theorem rule_at {F : Set (Clause V)} {π : List (CPLine V)} {rs : List (Rule V)}
    (h : traced F π rs) {i : ℕ} {r : Rule V} (hi : rs.reverse[i]? = some r) :
    legalRule F i (earlier π) (earlier π i) r := by
  induction π generalizing rs i r with
  | nil =>
    cases rs <;> simp_all [traced]
  | cons e π ih =>
    cases rs with
    | nil => exact False.elim h
    | cons top rs =>
      have htail : traced F π rs := h.1
      have hlen := trace_length htail
      by_cases hlt : i < π.length
      · have inrules : i < rs.reverse.length := by simpa [hlen] using hlt
        have hi' : rs.reverse[i]? = some r := by
          simpa only [List.reverse_cons, List.getElem?_append_left inrules] using hi
        rw [earlier_cons_lt π e hlt]
        exact legalRule_congr (ih htail hi') (fun j hj =>
          earlier_cons_lt π e (hj.trans hlt))
      · obtain ⟨ilen, _⟩ := List.getElem?_eq_some_iff.mp hi
        simp only [List.length_reverse, List.length_cons, hlen] at ilen
        have eq : i = π.length := by omega
        subst i
        have he : rs.reverse.length ≤ π.length := by simp [hlen]
        have hr : top = r := by
          simpa [List.reverse_cons, List.getElem?_append_right he, hlen] using hi
        rw [← hr, earlier_cons_last]
        exact legalRule_congr h.2 (fun j hj => earlier_cons_lt π e hj)

def closedUnder (incoming : ℕ → List ℕ) (live : Finset ℕ) : Prop :=
  ∀ i ∈ live, ∀ j ∈ incoming i, j ∈ live

theorem find_live (incoming : ℕ → List ℕ) (root : ℕ)
    (horder : ∀ i j, j ∈ incoming i → j < i) :
    ∃ live : Finset ℕ, root ∈ live ∧ live ⊆ Finset.range (root + 1) ∧
      closedUnder incoming live ∧
      ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ incoming j := by
  classical
  let eligible : ℕ → Prop := fun n =>
    ∃ live : Finset ℕ, root ∈ live ∧ live ⊆ Finset.range (root + 1) ∧
      closedUnder incoming live ∧ live.card = n
  have hrange : closedUnder incoming (Finset.range (root + 1)) := by
    intro i hi j hj
    exact Finset.mem_range.mpr ((horder i j hj).trans (Finset.mem_range.mp hi))
  have h : ∃ n, eligible n :=
    ⟨root + 1, Finset.range (root + 1), by simp, Finset.Subset.refl _, hrange, by simp⟩
  obtain ⟨live, hroot, hsub, hc, hmin⟩ := Nat.find_spec h
  refine ⟨live, hroot, hsub, hc, ?_⟩
  intro i hi hne
  by_contra! hnone
  have herase : (live.erase i).card < live.card := Finset.card_erase_lt_of_mem hi
  have heraseMin : eligible (live.erase i).card := by
    refine ⟨live.erase i, Finset.mem_erase.mpr ⟨Ne.symm hne, hroot⟩,
      (Finset.erase_subset _ _).trans hsub, ?_, rfl⟩
    intro j hj k hk
    have hj' : j ∈ live := Finset.mem_of_mem_erase hj
    exact Finset.mem_erase.mpr ⟨fun eq => hnone j hj' (eq ▸ hk), hc j hj' k hk⟩
  exact (not_lt_of_ge (Nat.find_min' h heraseMin)) (hmin ▸ herase)

def uses (incoming : ℕ → List ℕ) (live : Finset ℕ) (i : ℕ) : ℕ :=
  ∑ j ∈ live, (incoming j).count i

theorem sum_occurrences {xs : List ℕ} {s : Finset ℕ} (hs : ∀ x ∈ xs, x ∈ s) :
    (∑ i ∈ s, xs.count i) = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x ∈ s := hs x (List.mem_cons_self)
    have rest : (∑ i ∈ s, xs.count i) = xs.length :=
      ih (fun i hi => hs i (List.mem_cons_of_mem _ hi))
    simp only [List.count_cons, beq_iff_eq, List.length_cons]
    rw [Finset.sum_add_distrib, rest]
    simp [hx]

theorem total_uses {incoming : ℕ → List ℕ} {live : Finset ℕ}
    (hclosed : closedUnder incoming live) :
    (∑ i ∈ live, uses incoming live i) = ∑ j ∈ live, (incoming j).length := by
  unfold uses
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j hj => sum_occurrences (hclosed j hj)

theorem root_uses_zero {incoming : ℕ → List ℕ} {live : Finset ℕ} {root : ℕ}
    (hsub : live ⊆ Finset.range (root + 1))
    (horder : ∀ i j, j ∈ incoming i → j < i) : uses incoming live root = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply List.count_eq_zero.mpr
  intro hmem
  have hjr := Finset.mem_range.mp (hsub hj)
  have := horder j root hmem
  omega

theorem uses_pos {incoming : ℕ → List ℕ} {live : Finset ℕ} {i : ℕ}
    (h : ∃ j ∈ live, i ∈ incoming j) : 0 < uses incoming live i := by
  obtain ⟨j, hj, hmem⟩ := h
  calc
    0 < (incoming j).count i := List.count_pos_iff.mpr hmem
    _ ≤ uses incoming live i :=
      Finset.single_le_sum (f := fun j => (incoming j).count i) (fun _ _ => Nat.zero_le _) hj

theorem count_budget {incoming : ℕ → List ℕ} {live : Finset ℕ} {root : ℕ}
    (hroot : root ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (hclosed : closedUnder incoming live)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ incoming j)
    (horder : ∀ i j, j ∈ incoming i → j < i)
    (hfanin : ∀ i ∈ live, (incoming i).length ≤ 2) :
    live.card + 1 = 2 * (live.filter (fun i => (incoming i).length = 0)).card +
      (live.filter (fun i => (incoming i).length = 1)).card +
      ∑ i ∈ live.erase root, (uses incoming live i - 1) := by
  let leaves := (live.filter (fun i => (incoming i).length = 0)).card
  let unary := (live.filter (fun i => (incoming i).length = 1)).card
  let excess := ∑ i ∈ live.erase root, (uses incoming live i - 1)
  have hE := total_uses hclosed
  have hroot0 := root_uses_zero hsub horder
  have hbefore : (∑ i ∈ live, uses incoming live i) = (live.erase root).card + excess := by
    rw [← Finset.sum_erase_add _ _ hroot, hroot0, Nat.add_zero]
    change (∑ i ∈ live.erase root, uses incoming live i) =
      (live.erase root).card + ∑ i ∈ live.erase root, (uses incoming live i - 1)
    have hones : (∑ _ ∈ live.erase root, (1 : ℕ)) = (live.erase root).card := by simp
    rw [← hones, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => by
      obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hi
      have hp := uses_pos (hused i hm hne)
      omega
  have hcard : (live.erase root).card + 1 = live.card := Finset.card_erase_add_one hroot
  have hc : (∑ i ∈ live, (incoming i).length) + 2 * leaves + unary = 2 * live.card := by
    have hleaves : (∑ i ∈ live, if (incoming i).length = 0 then (1 : ℕ) else 0) = leaves :=
      Finset.sum_boole _ _
    have hunary : (∑ i ∈ live, if (incoming i).length = 1 then (1 : ℕ) else 0) = unary :=
      Finset.sum_boole _ _
    rw [← hleaves, ← hunary, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have hd : (∑ i ∈ live, ((incoming i).length + 2 * (if (incoming i).length = 0 then 1 else 0) +
        (if (incoming i).length = 1 then 1 else 0))) = ∑ _ ∈ live, 2 := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hh := hfanin i hi
      interval_cases h : (incoming i).length <;> simp
    simpa [Nat.mul_comm] using hd
  change live.card + 1 = 2 * leaves + unary + excess
  omega

theorem sum_weighted_occurrences {A : Type} [AddCommMonoid A] (f : ℕ → A)
    {xs : List ℕ} {s : Finset ℕ} (hs : ∀ x ∈ xs, x ∈ s) :
    (∑ i ∈ s, xs.count i • f i) = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x ∈ s := hs x (List.mem_cons_self)
    have rest : (∑ i ∈ s, xs.count i • f i) = (xs.map f).sum :=
      ih (fun i hi => hs i (List.mem_cons_of_mem _ hi))
    simp only [List.count_cons, beq_iff_eq, add_nsmul, List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, rest]
    have hone : (∑ i ∈ s, (if x = i then 1 else 0) • f i) = f x := by
      simp [ite_smul, hx]
    rw [hone, add_comm]

theorem sum_children_values {A : Type} [AddCommMonoid A] (f : ℕ → A)
    {incoming : ℕ → List ℕ} {live : Finset ℕ} (hclosed : closedUnder incoming live) :
    (∑ i ∈ live, uses incoming live i • f i) =
      ∑ j ∈ live, ((incoming j).map f).sum := by
  unfold uses
  simp only [← Finset.sum_nsmul_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j hj => sum_weighted_occurrences f (hclosed j hj)

theorem value_from_leaves {A : Type} [AddCommGroup A] (f : ℕ → A)
    {incoming : ℕ → List ℕ} {live : Finset ℕ} {root : ℕ}
    (hroot : root ∈ live) (hroot0 : uses incoming live root = 0)
    (hclosed : closedUnder incoming live)
    (hused : ∀ j ∈ live, j ≠ root → 0 < uses incoming live j)
    (hadd : ∀ j ∈ live, incoming j ≠ [] → f j = ((incoming j).map f).sum) :
    f root = (∑ i ∈ live.filter (fun j => incoming j = []), f i) +
      ∑ i ∈ live.erase root, (uses incoming live i - 1) • f i := by
  let leaves := live.filter (fun j => incoming j = [])
  let extra := ∑ i ∈ live.erase root, (uses incoming live i - 1) • f i
  have hbreak : (∑ i ∈ live, f i) =
      (∑ j ∈ leaves, f j) + ∑ j ∈ live, ((incoming j).map f).sum := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : incoming i = []
    · simp [h]
    · simp only [ite_eq_right h, zero_add]
      exact hadd i hi h
  have hweights := sum_children_values f hclosed
  have huses : (∑ i ∈ live, uses incoming live i • f i) =
      (∑ i ∈ live.erase root, f i) + extra := by
    rw [← Finset.sum_erase_add _ _ hroot, hroot0, zero_nsmul, add_zero]
    change (∑ i ∈ live.erase root, uses incoming live i • f i) =
      _ + ∑ i ∈ live.erase root, (uses incoming live i - 1) • f i
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hi
    have hsplit : uses incoming live i = 1 + (uses incoming live i - 1) := by
      have := hused i hm hne
      omega
    nth_rw 1 [hsplit]
    rw [add_nsmul, one_nsmul]
  rw [← hweights, huses] at hbreak
  change f root = (∑ i ∈ leaves, f i) + extra
  let rest := ∑ i ∈ live.erase root, f i
  apply add_right_cancel (b := rest)
  calc
    f root + rest = ∑ i ∈ live, f i := by
      rw [add_comm]
      exact Finset.sum_erase_add _ _ hroot
    _ = (∑ i ∈ leaves, f i) + (rest + extra) := hbreak
    _ = ((∑ i ∈ leaves, f i) + extra) + rest := by abel

theorem uses_one_unique {incoming : ℕ → List ℕ} {live : Finset ℕ} {i j k : ℕ}
    (hcount : uses incoming live i = 1) (hj : j ∈ live) (hk : k ∈ live)
    (hij : i ∈ incoming j) (hik : i ∈ incoming k) : j = k := by
  by_contra! hne
  have hjs := List.count_pos_iff.mpr hij
  have hks := List.count_pos_iff.mpr hik
  have hk' : k ∈ live.erase j := Finset.mem_erase.mpr ⟨Ne.symm hne, hk⟩
  have hbound : (incoming k).count i ≤ ∑ x ∈ live.erase j, (incoming x).count i :=
    Finset.single_le_sum (f := fun x => (incoming x).count i) (fun _ _ => Nat.zero_le _) hk'
  unfold uses at hcount
  rw [← Finset.sum_erase_add _ _ hj] at hcount
  omega

def weightsFrom (next : ℕ → ℕ) (factor : ℕ → ℚ) (root : ℕ) (i : ℕ) : ℚ :=
  if _h : i < next i ∧ next i ≤ root then
    weightsFrom next factor root (next i) * factor (next i)
  else 1
termination_by root - i
decreasing_by omega

theorem weightsFrom_range (next : ℕ → ℕ) (factor : ℕ → ℚ) (root : ℕ)
    (hf : ∀ i, 0 < factor i ∧ factor i ≤ 1) (i : ℕ) :
    0 < weightsFrom next factor root i ∧ weightsFrom next factor root i ≤ 1 := by
  suffices h : ∀ n i : ℕ, root - i = n → 0 < weightsFrom next factor root i ∧
      weightsFrom next factor root i ≤ 1 by exact h _ i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro i hi
    rw [weightsFrom]
    split_ifs with hx
    · have hlt : root - next i < n := by omega
      have hnext := ih _ hlt (next i) rfl
      have hp := hf (next i)
      refine ⟨mul_pos hnext.1 hp.1, ?_⟩
      simpa using mul_le_mul hnext.2 hp.2 hp.1.le (by norm_num : (0 : ℚ) ≤ 1)
    · norm_num

theorem find_weights {incoming : ℕ → List ℕ} {live : Finset ℕ} {root : ℕ}
    (hsub : live ⊆ Finset.range (root + 1))
    (hafter : ∀ i j, i ∈ incoming j → i < j)
    (hclosed : closedUnder incoming live)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ incoming j)
    (honce : ∀ i ∈ live, i ≠ root → uses incoming live i = 1)
    (factor : ℕ → ℚ) (hf : ∀ i, 0 < factor i ∧ factor i ≤ 1) :
    ∃ w : ℕ → ℚ, w root = 1 ∧ (∀ i, 0 < w i ∧ w i ≤ 1) ∧
      ∀ j ∈ live, ∀ i ∈ incoming j, w i = w j * factor j := by
  classical
  let parentsExist (i : ℕ) (hi : i ∈ live.erase root) :=
    hused i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1
  let next (i : ℕ) : ℕ := if hi : i ∈ live.erase root then
      Classical.choose (parentsExist i hi) else root
  let w := weightsFrom next factor root
  refine ⟨w, ?_, weightsFrom_range next factor root hf, ?_⟩
  · have hnext : next root = root := by simp [next]
    change weightsFrom next factor root root = 1
    rw [weightsFrom, hnext]
    simp
  · intro j hj i hij
    have hil := hclosed j hj i hij
    have hlt := hafter i j hij
    have hjr := Finset.mem_range.mp (hsub hj)
    have hne : i ≠ root := by omega
    have himself : i ∈ live.erase root := Finset.mem_erase.mpr ⟨hne, hil⟩
    have hspec := Classical.choose_spec (parentsExist i himself)
    have he : Classical.choose (parentsExist i himself) = j :=
      uses_one_unique (honce i hil hne) hspec.1 hj hspec.2 hij
    have hn : next i = j := by
      unfold next
      rw [dite_eq_left himself]
      exact he
    change weightsFrom next factor root i = _
    rw [weightsFrom]
    simp [hn, hlt, show j ≤ root by omega, w]

end PEqualNP.Outside.L_meta_9672_aux.CPGraphScratch

namespace PEqualNP.Outside.L_meta_9672_aux.CPHalfScratch

open PEqualNP.Search

variable {V : Type} [Fintype V]

def value (a : V → ℤ) (e : CPLine V) : ℤ :=
  ∑ v, e.1 v * a v

def holds (a : V → ℤ) (e : CPLine V) : Prop :=
  2 * e.2 ≤ value a e

def sumLine (e e' : CPLine V) : CPLine V :=
  (e.1 + e'.1, e.2 + e'.2)

def mulLine (d : ℕ) (e : CPLine V) : CPLine V :=
  ((d : ℤ) • e.1, (d : ℤ) * e.2)

def divLine (d : ℕ) (e : CPLine V) : CPLine V :=
  (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ)))

theorem holds_add {a : V → ℤ} {e e' : CPLine V}
    (h : holds a e) (h' : holds a e') : holds a (sumLine e e') := by
  unfold holds value sumLine at *
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  linarith

theorem holds_mul {a : V → ℤ} {e : CPLine V}
    (d : ℕ) (h : holds a e) : holds a (mulLine d e) := by
  unfold holds value mulLine at *
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  calc
    2 * ((d : ℤ) * e.2) = (d : ℤ) * (2 * e.2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Int.natCast_nonneg d)

theorem holds_div {a : V → ℤ} {e : CPLine V} {d : ℕ}
    (hd : 0 < d) (hdvd : ∀ v, (d : ℤ) ∣ e.1 v) (h : holds a e)
    (heven : (2 : ℤ) ∣ value a (divLine d e)) : holds a (divLine d e) := by
  have hd' : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hscale : (d : ℤ) * value a (divLine d e) = value a e := by
    unfold value divLine
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← mul_assoc, Int.mul_ediv_cancel' (hdvd v)]
  obtain ⟨k, hk⟩ := heven
  have hleft : (d : ℤ) * (2 * k) = value a e := by rwa [← hk]
  unfold holds at h ⊢
  have hk' : e.2 ≤ (d : ℤ) * k := by
    linarith
  have hn : -k ≤ (-e.2) / (d : ℤ) := by
    apply (Int.le_ediv_iff_mul_le hd').mpr
    linarith
  rw [hk]
  change 2 * (-((-e.2) / (d : ℤ))) ≤ 2 * k
  linarith

def roundUp (n d : ℤ) : ℤ := -((-n) / d)

theorem roundUp_shift (n d k : ℤ) (hd : 0 < d) :
    roundUp (n + d * k) d = roundUp n d + k := by
  unfold roundUp
  rw [show -(n + d * k) = -n + (-k) * d by ring]
  rw [Int.add_mul_ediv_right _ _ (ne_of_gt hd)]
  ring

theorem roundUp_comp (n d d' : ℤ) (hd : 0 < d) :
    roundUp (roundUp n d) d' = roundUp n (d * d') := by
  unfold roundUp
  rw [neg_neg, Int.ediv_ediv_of_nonneg (le_of_lt hd)]

def cleared (a : V → ℤ) (e : CPLine V) (den num : ℤ) : Prop :=
  0 < den ∧ e.2 = roundUp num den ∧ 2 * num ≤ den * value a e

theorem clear_start {a : V → ℤ} {e : CPLine V} (h : holds a e) :
    cleared a e 1 e.2 := by
  refine ⟨by decide, by simp [roundUp], ?_⟩
  simpa [holds] using h

theorem clear_add {a : V → ℤ} {e f : CPLine V} {den num : ℤ}
    (h : cleared a e den num) (hf : holds a f) :
    cleared a (sumLine e f) den (num + den * f.2) := by
  obtain ⟨hd, hr, hle⟩ := h
  refine ⟨hd, ?_, ?_⟩
  · simp only [sumLine, roundUp_shift _ _ _ hd]
    rw [hr]
  · unfold holds at hf
    have hm := mul_le_mul_of_nonneg_left hf (le_of_lt hd)
    have heval : value a (sumLine e f) = value a e + value a f := by
      simp only [value, sumLine, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [heval]
    linarith

theorem clear_div {a : V → ℤ} {e : CPLine V} {den num : ℤ} {d : ℕ}
    (h : cleared a e den num) (hd : 0 < d) (hdvd : ∀ v, (d : ℤ) ∣ e.1 v) :
    cleared a (divLine d e) (den * (d : ℤ)) num := by
  obtain ⟨hden, hr, hle⟩ := h
  have hd' : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  refine ⟨mul_pos hden hd', ?_, ?_⟩
  · change roundUp e.2 (d : ℤ) = _
    rw [hr, roundUp_comp _ _ _ hden]
  · have hscale : (d : ℤ) * value a (divLine d e) = value a e := by
      unfold value divLine
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← mul_assoc, Int.mul_ediv_cancel' (hdvd v)]
    rw [mul_assoc, hscale]
    exact hle

theorem no_cleared_contradiction (a : V → ℤ) (den num : ℤ) :
    ¬ cleared a ((0 : V → ℤ), 1) den num := by
  rintro ⟨hd, hr, hval⟩
  have hn : num ≤ 0 := by
    simp [value] at hval
    omega
  have hnonneg : 0 ≤ (-num) / den := Int.ediv_nonneg (by omega) (le_of_lt hd)
  unfold roundUp at hr
  omega

end PEqualNP.Outside.L_meta_9672_aux.CPHalfScratch

namespace PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch

open PEqualNP.Search PEqualNP.ProofComplexity

abbrev V := Fin (3 + 1) × Fin 3

def pigeon (i : Fin 4) : Clause V :=
  Finset.univ.image (fun j : Fin 3 => ((i, j), true))

def collision (i i' : Fin 4) (j : Fin 3) : Clause V :=
  {((i, j), false), ((i', j), false)}

def pairs : List (Fin 4 × Fin 4) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

def clauses : List (Clause V) :=
  (List.finRange 4).map pigeon ++
    (List.finRange 3).flatMap (fun j => pairs.map (fun e => collision e.1 e.2 j))

def given (i : Fin 22) : Clause V := clauses.getD i.val ∅

def positions : List (List (Option (Fin 3))) :=
  [[none, some 0, some 1, some 2], [some 0, none, some 1, some 2],
   [some 0, some 1, none, some 2], [some 0, some 1, some 2, none],
   [some 0, some 0, some 1, some 2], [some 0, some 1, some 0, some 2],
   [some 0, some 1, some 2, some 0], [some 1, some 0, some 0, some 2],
   [some 1, some 0, some 2, some 0], [some 1, some 2, some 0, some 0],
   [some 1, some 1, some 0, some 2], [some 1, some 0, some 1, some 2],
   [some 1, some 0, some 2, some 1], [some 0, some 1, some 1, some 2],
   [some 0, some 1, some 2, some 1], [some 0, some 2, some 1, some 1],
   [some 2, some 2, some 0, some 1], [some 2, some 0, some 2, some 1],
   [some 2, some 0, some 1, some 2], [some 0, some 2, some 2, some 1],
   [some 0, some 2, some 1, some 2], [some 0, some 1, some 2, some 2]]

def point (k : Fin 22) (v : V) : Bool :=
  decide ((positions.getD k.val []).getD v.1.val none = some v.2)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem unique_failure : ∀ (k c : Fin 22),
    CPLine.Holds (point k) (clauseCP (given c)) ↔ k ≠ c := by
  unfold CPLine.Holds
  decide +kernel

theorem pigeon_present : ∀ (i : Fin 4), ∃ k : Fin 22, given k = pigeon i := by
  decide +kernel

set_option maxRecDepth 12000 in
theorem collision_present : ∀ (i i' : Fin 4) (j : Fin 3),
    i ≠ i' → ∃ k : Fin 22, given k = collision i i' j := by
  decide +kernel

theorem full {C : Clause V} (h : C ∈ PHP (3 + 1) 3) :
    ∃ k : Fin 22, given k = C := by
  rcases h with ⟨i, hi⟩ | ⟨i, i', j, hne, heq⟩
  · rw [hi]
    exact pigeon_present i
  · rw [heq]
    exact collision_present i i' j hne

theorem given_injective : Function.Injective given := by
  intro a b h
  by_contra! hne
  have hab := (unique_failure a b).mpr hne
  rw [← h] at hab
  exact (unique_failure a a).mp hab rfl

theorem coefficient_separates (k : Fin 22) {C : Clause V}
    (h : C ∈ PHP (3 + 1) 3) (hne : C ≠ given k) :
    CPLine.Holds (point k) (clauseCP C) := by
  obtain ⟨j, rfl⟩ := full h
  exact (unique_failure k j).mpr (fun eq => hne (congrArg given eq.symm))

end PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch

namespace PEqualNP.Outside.L_meta_9672_aux.CPRankOneScratch

def edges : List (Fin 4 × Fin 4) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

def selected (mask : Fin 64) : List (Fin 4 × Fin 4) :=
  (List.finRange 6).filterMap fun i =>
    if mask.val.testBit i.val then edges[i.val]? else none

def degree (mask : Fin 64) (i : Fin 4) : ℤ :=
  ((selected mask).filter (fun e => e.1 == i || e.2 == i)).length

def present (mask : Fin 16) (i : Fin 4) : ℤ :=
  if mask.val.testBit i.val then 1 else 0

def rowCount (mask : Fin 16) : ℕ :=
  ((List.finRange 4).filter (fun i => mask.val.testBit i.val)).length

def edgeCount (mask : Fin 64) : ℕ := (selected mask).length

def allowedTwo (p e : ℕ) : Prop :=
  (p = 0 ∧ (e = 0 ∨ e = 3 ∨ e = 4)) ∨
  (p = 2 ∧ 1 ≤ e ∧ e ≤ 5) ∨ (p = 4 ∧ (e = 2 ∨ e = 3 ∨ e = 6))

def allowedThree (p e : ℕ) : Prop :=
  (p = 0 ∧ (e = 0 ∨ e = 6)) ∨ (p = 2 ∧ e = 1) ∨
  (p = 3 ∧ e = 3) ∨ (p = 4 ∧ e = 2)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem column_two : ∀ (p : Fin 16) (e : Fin 64),
    (∀ i : Fin 4, (2 : ℤ) ∣ present p i - degree e i) →
    allowedTwo (rowCount p) (edgeCount e) := by
  unfold allowedTwo
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem column_three : ∀ (p : Fin 16) (e : Fin 64),
    (∀ i : Fin 4, (3 : ℤ) ∣ present p i - degree e i) →
    allowedThree (rowCount p) (edgeCount e) := by
  unfold allowedThree
  decide +kernel

def holdsAfterRound (d : ℤ) (p a b c : ℕ) : Prop :=
  let total : ℤ := (a : ℤ) + (b : ℤ) + (c : ℤ)
  let rhs := (p : ℤ) - total
  let sumCoeff := 3 * (p : ℤ) - 2 * total
  3 * (-((-rhs) / d)) ≤ sumCoeff / d

set_option maxRecDepth 8000 in
theorem counts_two : ∀ (p : Fin 5) (a b c : Fin 7),
    allowedTwo p.val a.val → allowedTwo p.val b.val → allowedTwo p.val c.val →
    holdsAfterRound 2 p.val a.val b.val c.val := by
  intro p a b c ha hb hc
  unfold allowedTwo at ha hb hc
  unfold holdsAfterRound
  omega

set_option maxRecDepth 8000 in
theorem counts_three : ∀ (p : Fin 5) (a b c : Fin 7),
    allowedThree p.val a.val → allowedThree p.val b.val → allowedThree p.val c.val →
    holdsAfterRound 3 p.val a.val b.val c.val := by
  unfold allowedThree holdsAfterRound
  decide +kernel

theorem rowCount_bound : ∀ p : Fin 16, rowCount p < 5 := by decide

theorem edgeCount_bound : ∀ e : Fin 64, edgeCount e < 7 := by decide

theorem cut_two (p : Fin 16) (a b c : Fin 64)
    (ha : ∀ i : Fin 4, (2 : ℤ) ∣ present p i - degree a i)
    (hb : ∀ i : Fin 4, (2 : ℤ) ∣ present p i - degree b i)
    (hc : ∀ i : Fin 4, (2 : ℤ) ∣ present p i - degree c i) :
    holdsAfterRound 2 (rowCount p) (edgeCount a) (edgeCount b) (edgeCount c) :=
  counts_two ⟨_, rowCount_bound p⟩ ⟨_, edgeCount_bound a⟩
    ⟨_, edgeCount_bound b⟩ ⟨_, edgeCount_bound c⟩
    (column_two p a ha) (column_two p b hb) (column_two p c hc)

theorem cut_three (p : Fin 16) (a b c : Fin 64)
    (ha : ∀ i : Fin 4, (3 : ℤ) ∣ present p i - degree a i)
    (hb : ∀ i : Fin 4, (3 : ℤ) ∣ present p i - degree b i)
    (hc : ∀ i : Fin 4, (3 : ℤ) ∣ present p i - degree c i) :
    holdsAfterRound 3 (rowCount p) (edgeCount a) (edgeCount b) (edgeCount c) :=
  counts_three ⟨_, rowCount_bound p⟩ ⟨_, edgeCount_bound a⟩
    ⟨_, edgeCount_bound b⟩ ⟨_, edgeCount_bound c⟩
    (column_three p a ha) (column_three p b hb) (column_three p c hc)

end PEqualNP.Outside.L_meta_9672_aux.CPRankOneScratch

namespace PEqualNP.Outside.L_meta_9672_aux.Gemini9668Scale

structure SplitPHP43 where
  rowB : Fin 4 → Bool
  adjB : Fin 3 → Fin 4 → Fin 4 → Bool
  adj_irrefl : ∀ j i, adjB j i i = false
  adj_symm : ∀ j u v, adjB j u v = adjB j v u

namespace SplitPHP43

def degB (S : SplitPHP43) (j : Fin 3) (i : Fin 4) : ℕ :=
  (Finset.univ.filter fun i' : Fin 4 => S.adjB j i i').card

def edgesColB (S : SplitPHP43) (j : Fin 3) : ℕ :=
  (Finset.univ.filter fun p : Fin 4 × Fin 4 => p.1 < p.2 ∧ S.adjB j p.1 p.2).card

def edgesB (S : SplitPHP43) : ℕ :=
  ∑ j : Fin 3, S.edgesColB j

def numRowB (S : SplitPHP43) : ℤ :=
  ∑ i : Fin 4, if S.rowB i then (1 : ℤ) else 0

def cB (S : SplitPHP43) (i : Fin 4) (j : Fin 3) : ℤ :=
  (if S.rowB i then (1 : ℤ) else 0) - (S.degB j i : ℤ)

theorem degB_le_three (S : SplitPHP43) (j : Fin 3) (i : Fin 4) :
    S.degB j i ≤ 3 := by
  unfold degB
  have hsub : (Finset.univ.filter fun i' : Fin 4 => S.adjB j i i') ⊆ Finset.univ.erase i := by
    intro i' hi'
    rw [Finset.mem_filter] at hi'
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i'⟩
    intro h
    subst h
    rw [S.adj_irrefl] at hi'
    simp at hi'
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin] at hcard
  exact hcard

theorem exists_edgeA_of_degB_lt_three (S : SplitPHP43) {j : Fin 3} {i : Fin 4}
    (h : S.degB j i < 3) : ∃ i' : Fin 4, i' ≠ i ∧ S.adjB j i i' = false := by
  by_contra! hall
  have hsub : Finset.univ.erase i ⊆ Finset.univ.filter fun i' : Fin 4 => S.adjB j i i' := by
    intro i' hi'
    rw [Finset.mem_erase] at hi'
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ i', ?_⟩
    cases hval : S.adjB j i i'
    · exact False.elim (by simpa [hval] using hall i' hi'.1)
    · rfl
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin] at hcard
  change 3 ≤ S.degB j i at hcard
  omega

theorem two_mul_edgesColB (S : SplitPHP43) (j : Fin 3) :
    2 * S.edgesColB j = ∑ i : Fin 4, S.degB j i := by
  unfold edgesColB degB
  simp only [Finset.card_filter]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four]
  have h00 : S.adjB j 0 0 = false := S.adj_irrefl j 0
  have h11 : S.adjB j 1 1 = false := S.adj_irrefl j 1
  have h22 : S.adjB j 2 2 = false := S.adj_irrefl j 2
  have h33 : S.adjB j 3 3 = false := S.adj_irrefl j 3
  have h10 : S.adjB j 1 0 = S.adjB j 0 1 := S.adj_symm j 1 0
  have h20 : S.adjB j 2 0 = S.adjB j 0 2 := S.adj_symm j 2 0
  have h30 : S.adjB j 3 0 = S.adjB j 0 3 := S.adj_symm j 3 0
  have h21 : S.adjB j 2 1 = S.adjB j 1 2 := S.adj_symm j 2 1
  have h31 : S.adjB j 3 1 = S.adjB j 1 3 := S.adj_symm j 3 1
  have h32 : S.adjB j 3 2 = S.adjB j 2 3 := S.adj_symm j 3 2
  simp [h00, h11, h22, h33, h10, h20, h30, h21, h31, h32]
  ring

theorem edgesColB_eq_zero_of_degB_zero (S : SplitPHP43) (j : Fin 3)
    (h : ∀ i : Fin 4, S.degB j i = 0) : S.edgesColB j = 0 := by
  have hsum : ∑ i : Fin 4, S.degB j i = 0 := Finset.sum_eq_zero fun i _ => h i
  have h2 := S.two_mul_edgesColB j
  omega

theorem edgesColB_eq_zero_or_six_of_degB_zero_or_three (S : SplitPHP43) (j : Fin 3)
    (h : ∀ i : Fin 4, S.degB j i = 0 ∨ S.degB j i = 3) :
    S.edgesColB j = 0 ∨ S.edgesColB j = 6 := by
  by_cases hzero : ∀ i : Fin 4, S.degB j i = 0
  · left
    exact S.edgesColB_eq_zero_of_degB_zero j hzero
  · right
    push Not at hzero
    obtain ⟨i₀, hi₀⟩ := hzero
    have hdeg0 : S.degB j i₀ = 3 := (h i₀).resolve_left hi₀
    let F₀ : Finset (Fin 4) := Finset.univ.filter fun i' : Fin 4 => S.adjB j i₀ i'
    have hsub : F₀ ⊆ Finset.univ.erase i₀ := by
      intro i' hi'
      rw [Finset.mem_filter] at hi'
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i'⟩
      intro heq
      subst heq
      rw [S.adj_irrefl] at hi'
      simp at hi'
    have hcard_eq : F₀ = Finset.univ.erase i₀ := by
      refine Finset.eq_of_subset_of_card_le hsub ?_
      rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_fin]
      exact le_of_eq hdeg0.symm
    have hall3 : ∀ i : Fin 4, S.degB j i = 3 := by
      intro i
      by_cases heq : i = i₀
      · subst heq; exact hdeg0
      · have hmem : i ∈ F₀ := by
          rw [hcard_eq]
          exact Finset.mem_erase.mpr ⟨heq, Finset.mem_univ i⟩
        have hadj : S.adjB j i i₀ = true := by
          rw [Finset.mem_filter] at hmem
          rw [S.adj_symm]
          exact hmem.2
        have hpos : 0 < S.degB j i := by
          unfold degB
          exact Finset.card_pos.mpr ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hadj⟩⟩
        exact (h i).resolve_left (by omega)
    have hsum : ∑ i : Fin 4, S.degB j i = 12 := by
      simp [hall3]
    have h2 := S.two_mul_edgesColB j
    omega

end SplitPHP43

section ArithmeticCore

theorem all_rows_in_A (S : SplitPHP43) (k : ℤ) (hk : 2 ≤ k)
    (cA : Fin 4 → Fin 3 → ℤ)
    (hcoeff : ∀ i j, k * cA i j + S.cB i j = 0)
    (hB_nonpos : ∀ i j, S.rowB i = true → cA i j ≤ 0)
    (hB_neg_of_deg1 : ∀ i j, S.rowB i = true → S.degB j i = 1 → cA i j < 0) :
    ∀ i : Fin 4, S.rowB i = false := by
  intro i
  by_contra hB
  have hiB : S.rowB i = true := Bool.eq_true_of_not_eq_false hB
  have hcA_le : cA i 0 ≤ 0 := hB_nonpos i 0 hiB
  have h0 := hcoeff i 0
  unfold SplitPHP43.cB at h0
  rw [hiB] at h0
  simp only [↓reduceIte] at h0
  have hdeg_le : S.degB 0 i ≤ 3 := S.degB_le_three 0 i
  have hcA_zero : cA i 0 = 0 := by nlinarith
  have hdeg1 : S.degB 0 i = 1 := by nlinarith
  have hcA_lt : cA i 0 < 0 := hB_neg_of_deg1 i 0 hiB hdeg1
  omega

theorem k_two_edgesB_zero (S : SplitPHP43)
    (cA : Fin 4 → Fin 3 → ℤ)
    (hrowA : ∀ i : Fin 4, S.rowB i = false)
    (hcoeff : ∀ i j, 2 * cA i j + S.cB i j = 0)
    (hA_lt_one_of_deg2 : ∀ i j, S.rowB i = false → S.degB j i = 2 → cA i j < 1) :
    S.edgesB = 0 := by
  have hdeg0 : ∀ j i, S.degB j i = 0 := by
    intro j i
    have h0 := hcoeff i j
    unfold SplitPHP43.cB at h0
    rw [hrowA i] at h0
    simp only [Bool.false_eq_true, ↓reduceIte] at h0
    have hdeg_le : S.degB j i ≤ 3 := S.degB_le_three j i
    by_cases h2 : S.degB j i = 2
    · have hlt := hA_lt_one_of_deg2 i j (hrowA i) h2
      omega
    · omega
  unfold SplitPHP43.edgesB
  exact Finset.sum_eq_zero fun j _ => S.edgesColB_eq_zero_of_degB_zero j (hdeg0 j)

theorem k_three_six_dvd_edgesB (S : SplitPHP43)
    (cA : Fin 4 → Fin 3 → ℤ)
    (hrowA : ∀ i : Fin 4, S.rowB i = false)
    (hcoeff : ∀ i j, 3 * cA i j + S.cB i j = 0) :
    6 ∣ S.edgesB := by
  have hcol : ∀ j : Fin 3, 6 ∣ S.edgesColB j := by
    intro j
    have hdeg : ∀ i : Fin 4, S.degB j i = 0 ∨ S.degB j i = 3 := by
      intro i
      have h0 := hcoeff i j
      unfold SplitPHP43.cB at h0
      rw [hrowA i] at h0
      simp only [Bool.false_eq_true, ↓reduceIte] at h0
      have hdeg_le : S.degB j i ≤ 3 := S.degB_le_three j i
      omega
    rcases S.edgesColB_eq_zero_or_six_of_degB_zero_or_three j hdeg with h0 | h6
    · rw [h0]; exact dvd_zero 6
    · rw [h6]
  unfold SplitPHP43.edgesB
  exact Finset.dvd_sum fun j _ => hcol j

theorem k_ge_four_edgesB_zero (S : SplitPHP43) (k : ℤ) (hk : 4 ≤ k)
    (cA : Fin 4 → Fin 3 → ℤ)
    (hrowA : ∀ i : Fin 4, S.rowB i = false)
    (hcoeff : ∀ i j, k * cA i j + S.cB i j = 0) :
    S.edgesB = 0 := by
  have hdeg0 : ∀ j i, S.degB j i = 0 := by
    intro j i
    have h0 := hcoeff i j
    unfold SplitPHP43.cB at h0
    rw [hrowA i] at h0
    simp only [Bool.false_eq_true, ↓reduceIte] at h0
    have hdeg_le : S.degB j i ≤ 3 := S.degB_le_three j i
    have hcA0 : cA i j = 0 := by nlinarith
    nlinarith
  unfold SplitPHP43.edgesB
  exact Finset.sum_eq_zero fun j _ => S.edgesColB_eq_zero_of_degB_zero j (hdeg0 j)

theorem scale_impossible_of_helpers (S : SplitPHP43) (k : ℤ) (hk : 2 ≤ k)
    (cA : Fin 4 → Fin 3 → ℤ) (rA : ℤ)
    (hcoeff : ∀ i j, k * cA i j + S.cB i j = 0)
    (hrhs : k * rA + (S.numRowB - (S.edgesB : ℤ)) = 1)
    (hB_nonpos : ∀ i j, S.rowB i = true → cA i j ≤ 0)
    (hB_neg_of_deg1 : ∀ i j, S.rowB i = true → S.degB j i = 1 → cA i j < 0)
    (hA_lt_one_of_deg2 : ∀ i j, S.rowB i = false → S.degB j i = 2 → cA i j < 1) :
    False := by
  have hrowA : ∀ i : Fin 4, S.rowB i = false :=
    all_rows_in_A S k hk cA hcoeff hB_nonpos hB_neg_of_deg1
  have hnumRowB : S.numRowB = 0 := by
    unfold SplitPHP43.numRowB
    exact Finset.sum_eq_zero fun i _ => by simp [hrowA i]
  rw [hnumRowB] at hrhs
  by_cases hk2 : k = 2
  · subst hk2
    have he : S.edgesB = 0 := k_two_edgesB_zero S cA hrowA hcoeff hA_lt_one_of_deg2
    rw [he] at hrhs
    omega
  · by_cases hk3 : k = 3
    · subst hk3
      obtain ⟨m, hm⟩ := k_three_six_dvd_edgesB S cA hrowA hcoeff
      have hmZ : (S.edgesB : ℤ) = 6 * (m : ℤ) := by exact_mod_cast hm
      rw [hmZ] at hrhs
      omega
    · have hk4 : 4 ≤ k := by omega
      have he : S.edgesB = 0 := k_ge_four_edgesB_zero S k hk4 cA hrowA hcoeff
      rw [he] at hrhs
      simp only [Nat.cast_zero, sub_zero, add_zero] at hrhs
      rcases le_or_gt rA 0 with hr | hr <;> nlinarith

end ArithmeticCore

section LeafWeightBridge

structure LeafWeights (S : SplitPHP43) where
  wRow : Fin 4 → ℚ
  wEdge : Fin 3 → Fin 4 → Fin 4 → ℚ
  wRow_pos : ∀ i, S.rowB i = false → 0 < wRow i
  wRow_le_one : ∀ i, S.rowB i = false → wRow i ≤ 1
  wEdge_pos : ∀ j u v, u ≠ v → S.adjB j u v = false → 0 < wEdge j u v
  wEdge_le_one : ∀ j u v, u ≠ v → S.adjB j u v = false → wEdge j u v ≤ 1

def cAQ (S : SplitPHP43) (W : LeafWeights S) (i : Fin 4) (j : Fin 3) : ℚ :=
  (if S.rowB i then 0 else W.wRow i) -
    ∑ i' : Fin 4, if i' ≠ i ∧ S.adjB j i i' = false then W.wEdge j i i' else 0

private theorem edgeSum_nonneg (S : SplitPHP43) (W : LeafWeights S) (i : Fin 4) (j : Fin 3) :
    0 ≤ ∑ i' : Fin 4, if i' ≠ i ∧ S.adjB j i i' = false then W.wEdge j i i' else 0 := by
  refine Finset.sum_nonneg fun i' _ => ?_
  split_ifs with h
  · exact le_of_lt (W.wEdge_pos j i i' h.1.symm h.2)
  · exact le_rfl

private theorem edgeSum_pos_of_degB_lt_three (S : SplitPHP43) (W : LeafWeights S)
    {i : Fin 4} {j : Fin 3} (hdeg : S.degB j i < 3) :
    0 < ∑ i' : Fin 4, if i' ≠ i ∧ S.adjB j i i' = false then W.wEdge j i i' else 0 := by
  obtain ⟨i₀, hne, hadj⟩ := S.exists_edgeA_of_degB_lt_three hdeg
  let f : Fin 4 → ℚ := fun i' => if i' ≠ i ∧ S.adjB j i i' = false then W.wEdge j i i' else 0
  have hnonneg : ∀ i' ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ f i' := by
    intro i' _
    dsimp [f]
    split_ifs with h
    · exact le_of_lt (W.wEdge_pos j i i' (Ne.symm h.1) h.2)
    · exact le_rfl
  have hsingle : f i₀ ≤ ∑ i' : Fin 4, f i' :=
    Finset.single_le_sum hnonneg (Finset.mem_univ i₀)
  have hf0 : 0 < f i₀ := by
    dsimp [f]
    simp only [hne, hadj, not_false_eq_true, and_self, ↓reduceIte]
    exact W.wEdge_pos j i i₀ (Ne.symm hne) hadj
  exact lt_of_lt_of_le hf0 hsingle

theorem helper_B_nonpos (S : SplitPHP43) (W : LeafWeights S) (cA : Fin 4 → Fin 3 → ℤ)
    (hcA : ∀ i j, (cA i j : ℚ) = cAQ S W i j) :
    ∀ i j, S.rowB i = true → cA i j ≤ 0 := by
  intro i j hi
  have hq : (cA i j : ℚ) ≤ 0 := by
    rw [hcA i j]
    unfold cAQ
    rw [hi]
    simp only [↓reduceIte, zero_sub, neg_nonpos]
    exact edgeSum_nonneg S W i j
  exact_mod_cast hq

theorem helper_B_neg_of_degB_lt_three (S : SplitPHP43) (W : LeafWeights S)
    (cA : Fin 4 → Fin 3 → ℤ) (hcA : ∀ i j, (cA i j : ℚ) = cAQ S W i j) :
    ∀ i j, S.rowB i = true → S.degB j i < 3 → cA i j < 0 := by
  intro i j hi hdeg
  have hq : (cA i j : ℚ) < 0 := by
    rw [hcA i j]
    unfold cAQ
    rw [hi]
    simp only [↓reduceIte, zero_sub, neg_lt_zero]
    exact edgeSum_pos_of_degB_lt_three S W hdeg
  exact_mod_cast hq

theorem helper_A_lt_one_of_degB_lt_three (S : SplitPHP43) (W : LeafWeights S)
    (cA : Fin 4 → Fin 3 → ℤ) (hcA : ∀ i j, (cA i j : ℚ) = cAQ S W i j) :
    ∀ i j, S.rowB i = false → S.degB j i < 3 → cA i j < 1 := by
  intro i j hi hdeg
  have hq : (cA i j : ℚ) < 1 := by
    rw [hcA i j]
    unfold cAQ
    rw [hi]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hrow : W.wRow i ≤ 1 := W.wRow_le_one i hi
    have hedge : 0 < ∑ i' : Fin 4, if i' ≠ i ∧ S.adjB j i i' = false then W.wEdge j i i' else 0 :=
      edgeSum_pos_of_degB_lt_three S W hdeg
    linarith
  exact_mod_cast hq

theorem scale_impossible (S : SplitPHP43) (W : LeafWeights S) (k : ℤ) (hk : 2 ≤ k)
    (cA : Fin 4 → Fin 3 → ℤ) (rA : ℤ)
    (hcA : ∀ i j, (cA i j : ℚ) = cAQ S W i j)
    (hcoeff : ∀ i j, k * cA i j + S.cB i j = 0)
    (hrhs : k * rA + (S.numRowB - (S.edgesB : ℤ)) = 1) :
    False :=
  scale_impossible_of_helpers S k hk cA rA hcoeff hrhs
    (helper_B_nonpos S W cA hcA)
    (fun i j hi hdeg => helper_B_neg_of_degB_lt_three S W cA hcA i j hi (by omega))
    (fun i j hi hdeg => helper_A_lt_one_of_degB_lt_three S W cA hcA i j hi (by omega))

end LeafWeightBridge

end PEqualNP.Outside.L_meta_9672_aux.Gemini9668Scale

namespace PEqualNP.Outside.L_meta_9672_aux.Gemini9668Raw

open PEqualNP.Search PEqualNP.ProofComplexity
open PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch
open PEqualNP.Outside.L_meta_9672_aux.CPRankOneScratch
open PEqualNP.Outside.L_meta_9672_aux.Gemini9668Scale

def clauseSum (S : Finset (Fin 22)) : CPLine V :=
  (fun v => ∑ k ∈ S, (clauseCP (given k)).1 v, ∑ k ∈ S, (clauseCP (given k)).2)

def rowIdx (i : Fin 4) : Fin 22 := ⟨i.val, by omega⟩

def edgeIdx (j : Fin 3) (m : Fin 6) : Fin 22 := ⟨4 + 6 * j.val + m.val, by omega⟩

theorem rowIdx_injective : Function.Injective rowIdx := by
  intro a b h
  have hv : (rowIdx a).val = (rowIdx b).val := congrArg Fin.val h
  change a.val = b.val at hv
  exact Fin.ext hv

theorem edgeIdx_injective : Function.Injective (fun p : Fin 3 × Fin 6 => edgeIdx p.1 p.2) := by
  intro p₁ p₂ h
  have hv : 4 + 6 * p₁.1.val + p₁.2.val = 4 + 6 * p₂.1.val + p₂.2.val := congrArg Fin.val h
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem rowIdx_ne_edgeIdx (i : Fin 4) (j : Fin 3) (m : Fin 6) : rowIdx i ≠ edgeIdx j m := by
  intro h
  have hv : (rowIdx i).val = (edgeIdx j m).val := congrArg Fin.val h
  change i.val = 4 + 6 * j.val + m.val at hv
  omega

def splitEquiv : Fin 4 ⊕ (Fin 3 × Fin 6) ≃ Fin 22 where
  toFun
    | .inl i => rowIdx i
    | .inr (j, m) => edgeIdx j m
  invFun k :=
    if h : k.val < 4 then .inl ⟨k.val, h⟩
    else .inr (⟨(k.val - 4) / 6, by omega⟩, ⟨(k.val - 4) % 6, by omega⟩)
  left_inv x := by
    rcases x with i | ⟨j, m⟩
    · fin_cases i <;> rfl
    · fin_cases j <;> fin_cases m <;> rfl
  right_inv k := by
    fin_cases k <;> rfl

theorem sum_fin22_split {A : Type*} [AddCommMonoid A] (S : Finset (Fin 22)) (f : Fin 22 → A) :
    ∑ k ∈ S, f k =
      (∑ i : Fin 4, if rowIdx i ∈ S then f (rowIdx i) else 0) +
      ∑ j : Fin 3, ∑ m : Fin 6, if edgeIdx j m ∈ S then f (edgeIdx j m) else 0 := by
  have h1 : ∑ k ∈ S, f k = ∑ k : Fin 22, if k ∈ S then f k else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp
  rw [h1, ← Equiv.sum_comp splitEquiv (fun k => if k ∈ S then f k else 0)]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  rfl

theorem clauseCP_rowIdx_fst : ∀ (i : Fin 4) (v : V),
    (clauseCP (given (rowIdx i))).1 v = if v.1 = i then 1 else 0 := by
  decide +kernel

theorem clauseCP_rowIdx_snd : ∀ (i : Fin 4),
    (clauseCP (given (rowIdx i))).2 = 1 := by
  decide +kernel

theorem clauseCP_edgeIdx_fst : ∀ (j : Fin 3) (m : Fin 6) (v : V),
    (clauseCP (given (edgeIdx j m))).1 v =
      if v.2 = j ∧ (v.1 = (edges[m.val]).1 ∨ v.1 = (edges[m.val]).2) then -1 else 0 := by
  decide +kernel

theorem clauseCP_edgeIdx_snd : ∀ (j : Fin 3) (m : Fin 6),
    (clauseCP (given (edgeIdx j m))).2 = -1 := by
  decide +kernel

def bitMaskVal : ∀ {n : ℕ}, (Fin n → Bool) → ℕ
  | 0, _ => 0
  | _ + 1, f => (if f 0 then 1 else 0) + 2 * bitMaskVal (fun k => f k.succ)

theorem bitMaskVal_lt : ∀ {n : ℕ} (f : Fin n → Bool), bitMaskVal f < 2 ^ n
  | 0, _ => by simp [bitMaskVal]
  | n + 1, f => by
    have ih := bitMaskVal_lt (fun k : Fin n => f k.succ)
    simp only [bitMaskVal, Nat.pow_succ]
    split_ifs <;> omega

theorem testBit_bitMaskVal : ∀ {n : ℕ} (f : Fin n → Bool) (k : Fin n),
    (bitMaskVal f).testBit k.val = f k
  | 0, _, k => Fin.elim0 k
  | n + 1, f, k => by
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
    · simp only [bitMaskVal, Fin.val_zero, Nat.testBit_zero]
      cases f 0 <;> simp
    · simp only [bitMaskVal, Fin.val_succ]
      rw [Nat.testBit_succ]
      have hdiv : ((if f 0 then 1 else 0) + 2 * bitMaskVal (fun j : Fin n => f j.succ)) / 2 =
          bitMaskVal (fun j : Fin n => f j.succ) := by
        cases f 0
        · simp
        · simp; omega
      rw [hdiv]
      exact testBit_bitMaskVal (fun j : Fin n => f j.succ) k'

def rowMask (S : Finset (Fin 22)) : Fin 16 :=
  ⟨bitMaskVal (fun i : Fin 4 => decide (rowIdx i ∈ S)),
    bitMaskVal_lt (fun i : Fin 4 => decide (rowIdx i ∈ S))⟩

def edgeMask (S : Finset (Fin 22)) (j : Fin 3) : Fin 64 :=
  ⟨bitMaskVal (fun m : Fin 6 => decide (edgeIdx j m ∈ S)),
    bitMaskVal_lt (fun m : Fin 6 => decide (edgeIdx j m ∈ S))⟩

theorem testBit_rowMask (S : Finset (Fin 22)) (i : Fin 4) :
    (rowMask S).val.testBit i.val = decide (rowIdx i ∈ S) := by
  change (bitMaskVal (fun i' : Fin 4 => decide (rowIdx i' ∈ S))).testBit i.val =
    decide (rowIdx i ∈ S)
  exact testBit_bitMaskVal (fun i' : Fin 4 => decide (rowIdx i' ∈ S)) i

theorem testBit_edgeMask (S : Finset (Fin 22)) (j : Fin 3) (m : Fin 6) :
    (edgeMask S j).val.testBit m.val = decide (edgeIdx j m ∈ S) := by
  change (bitMaskVal (fun m' : Fin 6 => decide (edgeIdx j m' ∈ S))).testBit m.val =
    decide (edgeIdx j m ∈ S)
  exact testBit_bitMaskVal (fun m' : Fin 6 => decide (edgeIdx j m' ∈ S)) m

private theorem length_filter_filterMap {α β : Type*} (l : List α)
    (f : α → Option β) (p : β → Bool) :
    ((l.filterMap f).filter p).length =
      (l.map fun x => match f x with | some y => if p y then 1 else 0 | none => 0).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases hx : f x
    · simp [hx, ih]
    · rename_i y
      by_cases hp : p y <;> simp [hx, hp, ih, Nat.add_comm]

theorem rowCount_eq_sum (p : Fin 16) :
    (rowCount p : ℤ) = ∑ i : Fin 4, present p i := by
  unfold rowCount present
  rw [Fin.sum_univ_four]
  have hlen : ((List.finRange 4).filter fun i => p.val.testBit i.val).length =
      (if p.val.testBit 0 then 1 else 0) + (if p.val.testBit 1 then 1 else 0) +
        (if p.val.testBit 2 then 1 else 0) + (if p.val.testBit 3 then 1 else 0) := by
    have h := length_filter_filterMap (List.finRange 4) some (fun i => p.val.testBit i.val)
    simpa [List.finRange_succ, Nat.add_assoc] using h
  rw [hlen]
  push_cast
  simp

private theorem finRange6_sum_eq (g : Fin 6 → ℕ) :
    (((List.finRange 6).map g).sum : ℤ) = ∑ m : Fin 6, (g m : ℤ) := by
  have hr : List.finRange 6 = [0, 1, 2, 3, 4, 5] := by decide
  rw [hr, Fin.sum_univ_six]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.cast_add]
  ring

theorem degree_eq_sum (e : Fin 64) (i : Fin 4) :
    degree e i = ∑ m : Fin 6,
      if e.val.testBit m.val && ((edges[m.val]).1 == i || (edges[m.val]).2 == i) then 1 else 0 := by
  unfold degree selected
  have h := length_filter_filterMap (List.finRange 6)
    (fun m => if e.val.testBit m.val then edges[m.val]? else none)
    (fun p => p.1 == i || p.2 == i)
  rw [h, finRange6_sum_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hlen : edges.length = 6 := rfl
  have hm : edges[m.val]? = some (edges[m.val]) := List.getElem?_eq_getElem (by omega)
  rw [hm]
  cases e.val.testBit m.val <;> simp

theorem edgeCount_eq_sum (e : Fin 64) :
    (edgeCount e : ℤ) = ∑ m : Fin 6, if e.val.testBit m.val then 1 else 0 := by
  unfold edgeCount selected
  have h := length_filter_filterMap (List.finRange 6)
    (fun m => if e.val.testBit m.val then edges[m.val]? else none) (fun _ => true)
  simp only [List.filter_true] at h
  rw [h, finRange6_sum_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hlen : edges.length = 6 := rfl
  have hm : edges[m.val]? = some (edges[m.val]) := List.getElem?_eq_getElem (by omega)
  rw [hm]
  cases e.val.testBit m.val <;> simp

theorem sum_degree_eq_two_mul_edgeCount (e : Fin 64) :
    ∑ i : Fin 4, degree e i = 2 * (edgeCount e : ℤ) := by
  simp_rw [degree_eq_sum]
  rw [Finset.sum_comm, edgeCount_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Fin.sum_univ_four]
  cases hbit : e.val.testBit m.val
  · simp
  · fin_cases m <;> decide

theorem present_bounds : ∀ (p : Fin 16) (i : Fin 4),
    0 ≤ present p i ∧ present p i ≤ 1 := by
  intro p i
  unfold present
  split_ifs <;> omega

theorem degree_bounds (e : Fin 64) (i : Fin 4) :
    0 ≤ degree e i ∧ degree e i ≤ 3 := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  rw [degree_eq_sum]
  have hle : ∑ m : Fin 6,
      (if e.val.testBit m.val && ((edges[m.val]).1 == i || (edges[m.val]).2 == i) then (1 : ℤ) else 0) ≤
      ∑ m : Fin 6, if (edges[m.val]).1 == i || (edges[m.val]).2 == i then (1 : ℤ) else 0 := by
    refine Finset.sum_le_sum fun m _ => ?_
    cases e.val.testBit m.val <;> cases ((edges[m.val]).1 == i || (edges[m.val]).2 == i) <;> simp
  have hthree : (∑ m : Fin 6, if (edges[m.val]).1 == i || (edges[m.val]).2 == i then (1 : ℤ) else 0) = 3 := by
    fin_cases i <;> decide +kernel
  omega

theorem clauseSum_fst_eq_mask (S : Finset (Fin 22)) (i : Fin 4) (j : Fin 3) :
    (clauseSum S).1 (i, j) = present (rowMask S) i - degree (edgeMask S j) i := by
  unfold clauseSum
  dsimp only
  rw [sum_fin22_split]
  have hrow : (∑ i' : Fin 4, if rowIdx i' ∈ S then (clauseCP (given (rowIdx i'))).1 (i, j) else 0) =
      present (rowMask S) i := by
    have hcongr : (∑ i' : Fin 4, if rowIdx i' ∈ S then (clauseCP (given (rowIdx i'))).1 (i, j) else 0) =
        ∑ i' : Fin 4, if i = i' then (if rowIdx i' ∈ S then (1 : ℤ) else 0) else 0 := by
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [clauseCP_rowIdx_fst]
      split_ifs <;> simp_all
    rw [hcongr, Finset.sum_ite_eq Finset.univ i]
    simp only [Finset.mem_univ, ↓reduceIte, present, testBit_rowMask]
    split_ifs <;> simp_all
  have hedge : (∑ j' : Fin 3, ∑ m : Fin 6,
      if edgeIdx j' m ∈ S then (clauseCP (given (edgeIdx j' m))).1 (i, j) else 0) =
      -degree (edgeMask S j) i := by
    have hcongr : ∀ j' : Fin 3, (∑ m : Fin 6,
        if edgeIdx j' m ∈ S then (clauseCP (given (edgeIdx j' m))).1 (i, j) else 0) =
        if j = j' then -degree (edgeMask S j) i else 0 := by
      intro j'
      by_cases hjj : j = j'
      · subst hjj
        simp only [↓reduceIte, degree_eq_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [clauseCP_edgeIdx_fst, testBit_edgeMask]
        by_cases hm : edgeIdx j m ∈ S <;>
          by_cases h1 : (edges[m.val]).1 = i <;>
          by_cases h2 : (edges[m.val]).2 = i
        all_goals simp [hm, h1, h2, Ne.symm]
      · simp only [hjj, ↓reduceIte]
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [clauseCP_edgeIdx_fst]
        simp [hjj]
    rw [Finset.sum_congr rfl (fun j' _ => hcongr j'), Finset.sum_ite_eq Finset.univ j]
    simp
  rw [hrow, hedge, sub_eq_add_neg]

theorem clauseSum_snd_eq_mask (S : Finset (Fin 22)) :
    (clauseSum S).2 = (rowCount (rowMask S) : ℤ) -
      ((edgeCount (edgeMask S 0) : ℤ) + (edgeCount (edgeMask S 1) : ℤ) +
        (edgeCount (edgeMask S 2) : ℤ)) := by
  unfold clauseSum
  dsimp only
  rw [sum_fin22_split]
  have hrow : (∑ i : Fin 4, if rowIdx i ∈ S then (clauseCP (given (rowIdx i))).2 else 0) =
      (rowCount (rowMask S) : ℤ) := by
    rw [rowCount_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [clauseCP_rowIdx_snd]
    simp [present, testBit_rowMask]
  have hedge : ∀ j : Fin 3, (∑ m : Fin 6,
      if edgeIdx j m ∈ S then (clauseCP (given (edgeIdx j m))).2 else 0) =
      -(edgeCount (edgeMask S j) : ℤ) := by
    intro j
    rw [edgeCount_eq_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [clauseCP_edgeIdx_snd, testBit_edgeMask]
    by_cases hm : edgeIdx j m ∈ S <;> simp [hm]
  rw [hrow]
  simp only [hedge, Fin.sum_univ_three]
  ring

theorem sum_clauseSum_fst_eq_mask (S : Finset (Fin 22)) :
    ∑ v : V, (clauseSum S).1 v =
      3 * (rowCount (rowMask S) : ℤ) -
        2 * ((edgeCount (edgeMask S 0) : ℤ) + (edgeCount (edgeMask S 1) : ℤ) +
          (edgeCount (edgeMask S 2) : ℤ)) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hcol : ∀ j : Fin 3, ∑ i : Fin 4, (clauseSum S).1 (i, j) =
      (rowCount (rowMask S) : ℤ) - 2 * (edgeCount (edgeMask S j) : ℤ) := by
    intro j
    have hsub : ∑ i : Fin 4, (clauseSum S).1 (i, j) =
        ∑ i : Fin 4, (present (rowMask S) i - degree (edgeMask S j) i) :=
      Finset.sum_congr rfl fun i _ => clauseSum_fst_eq_mask S i j
    rw [hsub, Finset.sum_sub_distrib, ← rowCount_eq_sum, sum_degree_eq_two_mul_edgeCount]
  simp only [hcol, Fin.sum_univ_three]
  ring

theorem sum_div_eq_ediv_sum {α : Type*} [Fintype α] (f : α → ℤ) {d : ℕ}
    (hd : 0 < d) (hdvd : ∀ x, (d : ℤ) ∣ f x) :
    ∑ x, f x / (d : ℤ) = (∑ x, f x) / (d : ℤ) := by
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hmul : (d : ℤ) * (∑ x, f x / (d : ℤ)) = ∑ x, f x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Int.mul_ediv_cancel' (hdvd x)
  rw [← hmul, Int.mul_ediv_cancel_left _ hd0]

theorem raw_thirds_clauseSum (S : Finset (Fin 22)) :
    3 * (clauseSum S).2 ≤ ∑ v : V, (clauseSum S).1 v := by
  rw [clauseSum_snd_eq_mask, sum_clauseSum_fst_eq_mask]
  omega

theorem clauseSum_fst_bounds (S : Finset (Fin 22)) (v : V) :
    -3 ≤ (clauseSum S).1 v ∧ (clauseSum S).1 v ≤ 1 := by
  rcases v with ⟨i, j⟩
  rw [clauseSum_fst_eq_mask]
  have hp := present_bounds (rowMask S) i
  have hd := degree_bounds (edgeMask S j) i
  omega

theorem all_thirds_div_clauseSum (S : Finset (Fin 22)) {d : ℕ}
    (hd : 0 < d) (hdvd : ∀ v : V, (d : ℤ) ∣ (clauseSum S).1 v) :
    3 * (-((-(clauseSum S).2) / (d : ℤ))) ≤ ∑ v : V, (clauseSum S).1 v / (d : ℤ) := by
  rw [sum_div_eq_ediv_sum _ hd hdvd]
  by_cases hd1 : d = 1
  · subst hd1
    simpa using raw_thirds_clauseSum S
  · by_cases hd2 : d = 2
    · subst hd2
      have hdiv : ∀ j : Fin 3, ∀ i : Fin 4,
          (2 : ℤ) ∣ present (rowMask S) i - degree (edgeMask S j) i := fun j i => by
        simpa [clauseSum_fst_eq_mask] using hdvd (i, j)
      have hcut := cut_two (rowMask S) (edgeMask S 0) (edgeMask S 1) (edgeMask S 2)
        (hdiv 0) (hdiv 1) (hdiv 2)
      unfold holdsAfterRound at hcut
      simpa [clauseSum_snd_eq_mask, sum_clauseSum_fst_eq_mask] using hcut
    · by_cases hd3 : d = 3
      · subst hd3
        have hdiv : ∀ j : Fin 3, ∀ i : Fin 4,
            (3 : ℤ) ∣ present (rowMask S) i - degree (edgeMask S j) i := fun j i => by
          simpa [clauseSum_fst_eq_mask] using hdvd (i, j)
        have hcut := cut_three (rowMask S) (edgeMask S 0) (edgeMask S 1) (edgeMask S 2)
          (hdiv 0) (hdiv 1) (hdiv 2)
        unfold holdsAfterRound at hcut
        simpa [clauseSum_snd_eq_mask, sum_clauseSum_fst_eq_mask] using hcut
      · have hd4 : (4 : ℤ) ≤ (d : ℤ) := by omega
        have hzero : ∀ v : V, (clauseSum S).1 v = 0 := by
          intro v
          obtain ⟨q, hq⟩ := hdvd v
          have hb := clauseSum_fst_bounds S v
          have hq0 : q = 0 := by nlinarith
          simp [hq, hq0]
        have hsum0 : ∑ v : V, (clauseSum S).1 v = 0 :=
          Finset.sum_eq_zero fun v _ => hzero v
        have hrhs_le : (clauseSum S).2 ≤ 0 := by
          have hraw := raw_thirds_clauseSum S
          rw [hsum0] at hraw
          omega
        have hdiv_nonneg : 0 ≤ (-(clauseSum S).2) / (d : ℤ) :=
          Int.ediv_nonneg (by omega) (by exact_mod_cast Nat.zero_le d)
        rw [hsum0, Int.zero_ediv]
        omega

theorem all_thirds_exact_divide (S : Finset (Fin 22)) (d : ℕ) (hd : 0 < d)
    (e : CPLine V)
    (he1 : ∀ v, e.1 v = ∑ k ∈ S, (clauseCP (given k)).1 v)
    (he2 : e.2 = ∑ k ∈ S, (clauseCP (given k)).2)
    (hdvd : ∀ v, (d : ℤ) ∣ e.1 v) :
    3 * (-((-e.2) / (d : ℤ))) ≤ ∑ v, e.1 v / (d : ℤ) := by
  have heq1 : e.1 = (clauseSum S).1 := funext he1
  have heq2 : e.2 = (clauseSum S).2 := he2
  rw [heq1, heq2]
  exact all_thirds_div_clauseSum S hd (fun v => by simpa [heq1] using hdvd v)

def pairEdge? (u v : Fin 4) : Option (Fin 6) :=
  let a := min u v
  let b := max u v
  match a.val, b.val with
  | 0, 1 => some 0
  | 0, 2 => some 1
  | 0, 3 => some 2
  | 1, 2 => some 3
  | 1, 3 => some 4
  | 2, 3 => some 5
  | _, _ => none

theorem pairEdge?_self (i : Fin 4) : pairEdge? i i = none := by
  fin_cases i <;> rfl

theorem pairEdge?_comm (u v : Fin 4) : pairEdge? u v = pairEdge? v u := by
  simp only [pairEdge?, min_comm u v, max_comm u v]

theorem pairEdge?_edges (m : Fin 6) :
    pairEdge? (edges[m.val]).1 (edges[m.val]).2 = some m := by
  fin_cases m <;> rfl

theorem edges_pairEdge?_lt {u v : Fin 4} {m : Fin 6} (huv : u < v)
    (hm : pairEdge? u v = some m) :
    (edges[m.val]).1 = u ∧ (edges[m.val]).2 = v := by
  revert huv hm
  fin_cases u <;> fin_cases v <;> fin_cases m <;> decide

def splitOfSubset (S : Finset (Fin 22)) : SplitPHP43 where
  rowB i := decide (rowIdx i ∈ S)
  adjB j u v :=
    match pairEdge? u v with
    | some m => decide (edgeIdx j m ∈ S)
    | none => false
  adj_irrefl j i := by simp [pairEdge?_self]
  adj_symm j u v := by simp [pairEdge?_comm]

def subsetOfSplit (P : SplitPHP43) : Finset (Fin 22) :=
  Finset.univ.filter fun k =>
    (match splitEquiv.symm k with
      | .inl i => P.rowB i
      | .inr (j, m) => P.adjB j (edges[m.val]).1 (edges[m.val]).2) = true

theorem rowIdx_mem_subsetOfSplit (P : SplitPHP43) (i : Fin 4) :
    rowIdx i ∈ subsetOfSplit P ↔ P.rowB i = true := by
  unfold subsetOfSplit
  have hsym : splitEquiv.symm (rowIdx i) = .inl i := splitEquiv.symm_apply_apply (.inl i)
  simp [hsym]

theorem edgeIdx_mem_subsetOfSplit (P : SplitPHP43) (j : Fin 3) (m : Fin 6) :
    edgeIdx j m ∈ subsetOfSplit P ↔ P.adjB j (edges[m.val]).1 (edges[m.val]).2 = true := by
  unfold subsetOfSplit
  have hsym : splitEquiv.symm (edgeIdx j m) = .inr (j, m) :=
    splitEquiv.symm_apply_apply (.inr (j, m))
  simp [hsym]

theorem subsetOfSplit_splitOfSubset (S : Finset (Fin 22)) :
    subsetOfSplit (splitOfSubset S) = S := by
  ext k
  obtain ⟨x, rfl⟩ := splitEquiv.surjective k
  rcases x with i | ⟨j, m⟩
  · change rowIdx i ∈ subsetOfSplit (splitOfSubset S) ↔ rowIdx i ∈ S
    rw [rowIdx_mem_subsetOfSplit]
    simp [splitOfSubset]
  · change edgeIdx j m ∈ subsetOfSplit (splitOfSubset S) ↔ edgeIdx j m ∈ S
    rw [edgeIdx_mem_subsetOfSplit]
    simp [splitOfSubset, pairEdge?_edges]

theorem splitOfSubset_subsetOfSplit (P : SplitPHP43) :
    splitOfSubset (subsetOfSplit P) = P := by
  cases P with
  | mk rowB adjB irrefl symm =>
    simp only [splitOfSubset]
    congr 1
    · funext i
      cases h : rowB i <;> simp [rowIdx_mem_subsetOfSplit, h]
    · funext j u v
      rcases lt_trichotomy u v with huv | rfl | hvu
      · obtain ⟨m, hm⟩ : ∃ m : Fin 6, pairEdge? u v = some m := by
          revert huv
          fin_cases u <;> fin_cases v <;> decide
        obtain ⟨h1, h2⟩ := edges_pairEdge?_lt huv hm
        cases h : adjB j u v <;> simp [hm, edgeIdx_mem_subsetOfSplit, h1, h2, h]
      · simp [pairEdge?_self, irrefl]
      · obtain ⟨m, hm⟩ : ∃ m : Fin 6, pairEdge? v u = some m := by
          revert hvu
          fin_cases u <;> fin_cases v <;> decide
        obtain ⟨h1, h2⟩ := edges_pairEdge?_lt hvu hm
        rw [pairEdge?_comm]
        cases h : adjB j v u <;> simp [hm, edgeIdx_mem_subsetOfSplit, h1, h2, h, symm j u v]

theorem splitOfSubset_adjB (S : Finset (Fin 22)) (j : Fin 3) (u v : Fin 4) :
    (splitOfSubset S).adjB j u v =
      match pairEdge? u v with
      | some m => (edgeMask S j).val.testBit m.val
      | none => false := by
  unfold splitOfSubset
  cases hpe : pairEdge? u v with
  | none => simp [hpe]
  | some m => simp [hpe, testBit_edgeMask]

private theorem deg_match_sum (i : Fin 4) (p : Fin 64) :
    (∑ i' : Fin 4,
      match pairEdge? i i' with
      | some m => if p.val.testBit m.val then (1 : ℤ) else 0
      | none => 0) =
    ∑ m : Fin 6,
      if p.val.testBit m.val && ((edges[m.val]).1 == i || (edges[m.val]).2 == i)
      then 1 else 0 := by
  rw [Fin.sum_univ_four, Fin.sum_univ_six]
  fin_cases i <;> simp [edges, pairEdge?]

theorem splitOfSubset_numRowB (S : Finset (Fin 22)) :
    (splitOfSubset S).numRowB = (rowCount (rowMask S) : ℤ) := by
  unfold SplitPHP43.numRowB
  rw [rowCount_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [splitOfSubset, present, testBit_rowMask]

theorem splitOfSubset_degB (S : Finset (Fin 22)) (j : Fin 3) (i : Fin 4) :
    ((splitOfSubset S).degB j i : ℤ) = degree (edgeMask S j) i := by
  unfold SplitPHP43.degB
  rw [degree_eq_sum, Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have h1 : (∑ i' : Fin 4, if (splitOfSubset S).adjB j i i' = true then (1 : ℤ) else 0) =
      ∑ i' : Fin 4,
        match pairEdge? i i' with
        | some m => if (edgeMask S j).val.testBit m.val then (1 : ℤ) else 0
        | none => 0 := by
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [splitOfSubset_adjB]
    cases pairEdge? i i' <;> simp
  rw [h1]
  exact deg_match_sum i (edgeMask S j)

theorem splitOfSubset_edgesColB (S : Finset (Fin 22)) (j : Fin 3) :
    (splitOfSubset S).edgesColB j = edgeCount (edgeMask S j) := by
  have h2 := (splitOfSubset S).two_mul_edgesColB j
  have hdeg : (∑ i : Fin 4, ((splitOfSubset S).degB j i : ℤ)) =
      ∑ i : Fin 4, degree (edgeMask S j) i :=
    Finset.sum_congr rfl fun i _ => splitOfSubset_degB S j i
  have h2' : (2 * ((splitOfSubset S).edgesColB j : ℤ)) =
      ∑ i : Fin 4, ((splitOfSubset S).degB j i : ℤ) := by
    exact_mod_cast h2
  rw [hdeg, sum_degree_eq_two_mul_edgeCount] at h2'
  omega

theorem splitOfSubset_edgesB (S : Finset (Fin 22)) :
    (splitOfSubset S).edgesB =
      edgeCount (edgeMask S 0) + edgeCount (edgeMask S 1) + edgeCount (edgeMask S 2) := by
  unfold SplitPHP43.edgesB
  simp only [splitOfSubset_edgesColB, Fin.sum_univ_three]

theorem clauseSum_fst_eq_cB (S : Finset (Fin 22)) (i : Fin 4) (j : Fin 3) :
    (clauseSum S).1 (i, j) = (splitOfSubset S).cB i j := by
  rw [clauseSum_fst_eq_mask, SplitPHP43.cB, splitOfSubset_degB]
  simp [splitOfSubset, present, testBit_rowMask]

theorem clauseSum_snd_eq_split_rhs (S : Finset (Fin 22)) :
    (clauseSum S).2 = (splitOfSubset S).numRowB - ((splitOfSubset S).edgesB : ℤ) := by
  rw [clauseSum_snd_eq_mask, splitOfSubset_numRowB, splitOfSubset_edgesB]
  push_cast
  ring

theorem sum_clauseSum_fst_eq_split (S : Finset (Fin 22)) :
    ∑ v : V, (clauseSum S).1 v =
      3 * (splitOfSubset S).numRowB - 2 * ((splitOfSubset S).edgesB : ℤ) := by
  rw [sum_clauseSum_fst_eq_mask, splitOfSubset_numRowB, splitOfSubset_edgesB]
  push_cast
  ring

theorem subsetOfSplit_clauseSum_fst (P : SplitPHP43) (i : Fin 4) (j : Fin 3) :
    (clauseSum (subsetOfSplit P)).1 (i, j) = P.cB i j := by
  rw [clauseSum_fst_eq_cB, splitOfSubset_subsetOfSplit]

theorem subsetOfSplit_clauseSum_snd (P : SplitPHP43) :
    (clauseSum (subsetOfSplit P)).2 = P.numRowB - (P.edgesB : ℤ) := by
  rw [clauseSum_snd_eq_split_rhs, splitOfSubset_subsetOfSplit]

theorem all_thirds_div_split (P : SplitPHP43) {d : ℕ} (hd : 0 < d)
    (hdvd : ∀ i j, (d : ℤ) ∣ P.cB i j) :
    3 * (-((-(P.numRowB - (P.edgesB : ℤ))) / (d : ℤ))) ≤
      ∑ i : Fin 4, ∑ j : Fin 3, P.cB i j / (d : ℤ) := by
  have hc := all_thirds_div_clauseSum (subsetOfSplit P) hd (fun ⟨i, j⟩ => by
    simpa [subsetOfSplit_clauseSum_fst] using hdvd i j)
  rw [subsetOfSplit_clauseSum_snd] at hc
  have hsum : ∑ v : V, (clauseSum (subsetOfSplit P)).1 v / (d : ℤ) =
      ∑ i : Fin 4, ∑ j : Fin 3, P.cB i j / (d : ℤ) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [subsetOfSplit_clauseSum_fst]
  rwa [hsum] at hc

def leafWeightsOfSubset (S : Finset (Fin 22)) (w : Fin 22 → ℚ)
    (hw : ∀ k ∉ S, 0 < w k ∧ w k ≤ 1) : LeafWeights (splitOfSubset S) where
  wRow i := w (rowIdx i)
  wEdge j u v :=
    match pairEdge? u v with
    | some m => w (edgeIdx j m)
    | none => 1
  wRow_pos i hi := by
    have hnot : rowIdx i ∉ S := by simpa [splitOfSubset] using hi
    exact (hw _ hnot).1
  wRow_le_one i hi := by
    have hnot : rowIdx i ∉ S := by simpa [splitOfSubset] using hi
    exact (hw _ hnot).2
  wEdge_pos j u v huv hadj := by
    obtain ⟨m, hm⟩ : ∃ m : Fin 6, pairEdge? u v = some m := by
      revert huv
      fin_cases u <;> fin_cases v <;> decide
    have hnot : edgeIdx j m ∉ S := by
      have : (splitOfSubset S).adjB j u v = false := hadj
      simpa [splitOfSubset, hm] using this
    simpa [hm] using (hw _ hnot).1
  wEdge_le_one j u v huv hadj := by
    obtain ⟨m, hm⟩ : ∃ m : Fin 6, pairEdge? u v = some m := by
      revert huv
      fin_cases u <;> fin_cases v <;> decide
    have hnot : edgeIdx j m ∉ S := by
      have : (splitOfSubset S).adjB j u v = false := hadj
      simpa [splitOfSubset, hm] using this
    simpa [hm] using (hw _ hnot).2

private theorem sum_edges_match_pairEdge (i : Fin 4) (f : Fin 6 → ℚ) :
    (∑ m : Fin 6, if (edges[m.val]).1 = i ∨ (edges[m.val]).2 = i then f m else 0) =
    ∑ i' : Fin 4, match pairEdge? i i' with | some m => f m | none => 0 := by
  fin_cases i <;>
    simp [Fin.sum_univ_four, Fin.sum_univ_six, edges, pairEdge?]

theorem weighted_compl_eq_cAQ (S : Finset (Fin 22)) (w : Fin 22 → ℚ)
    (hw : ∀ k ∉ S, 0 < w k ∧ w k ≤ 1) (i : Fin 4) (j : Fin 3) :
    (∑ k ∈ Finset.univ \ S, w k * ((clauseCP (given k)).1 (i, j) : ℚ)) =
      cAQ (splitOfSubset S) (leafWeightsOfSubset S w hw) i j := by
  rw [sum_fin22_split]
  have hrow : (∑ i' : Fin 4,
      if rowIdx i' ∈ Finset.univ \ S then
        w (rowIdx i') * ((clauseCP (given (rowIdx i'))).1 (i, j) : ℚ)
      else 0) =
      if (splitOfSubset S).rowB i then 0 else (leafWeightsOfSubset S w hw).wRow i := by
    have hcongr : (∑ i' : Fin 4,
        if rowIdx i' ∈ Finset.univ \ S then
          w (rowIdx i') * ((clauseCP (given (rowIdx i'))).1 (i, j) : ℚ)
        else 0) =
        ∑ i' : Fin 4,
          if i = i' then (if rowIdx i' ∉ S then w (rowIdx i') else 0) else 0 := by
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [clauseCP_rowIdx_fst]
      by_cases hi' : rowIdx i' ∈ S <;> by_cases heq : i = i' <;>
        simp [hi', heq, Finset.mem_sdiff]
    rw [hcongr, Finset.sum_ite_eq Finset.univ i]
    by_cases hi : rowIdx i ∈ S <;> simp [hi, splitOfSubset, leafWeightsOfSubset]
  have hedge : (∑ j' : Fin 3, ∑ m : Fin 6,
      if edgeIdx j' m ∈ Finset.univ \ S then
        w (edgeIdx j' m) * ((clauseCP (given (edgeIdx j' m))).1 (i, j) : ℚ)
      else 0) =
      -(∑ i' : Fin 4,
        if i' ≠ i ∧ (splitOfSubset S).adjB j i i' = false
        then (leafWeightsOfSubset S w hw).wEdge j i i' else 0) := by
    have hcol : ∀ j' : Fin 3,
        (∑ m : Fin 6,
          if edgeIdx j' m ∈ Finset.univ \ S then
            w (edgeIdx j' m) * ((clauseCP (given (edgeIdx j' m))).1 (i, j) : ℚ)
          else 0) =
        if j = j' then
          -(∑ m : Fin 6,
            if edgeIdx j m ∉ S ∧ ((edges[m.val]).1 = i ∨ (edges[m.val]).2 = i)
            then w (edgeIdx j m) else 0)
        else 0 := by
      intro j'
      by_cases hjj : j = j'
      · subst hjj
        simp only [↓reduceIte, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [clauseCP_edgeIdx_fst]
        by_cases hm : edgeIdx j m ∈ S <;>
          by_cases h1 : (edges[m.val]).1 = i <;>
          by_cases h2 : (edges[m.val]).2 = i
        all_goals simp [hm, h1, h2, Ne.symm, Finset.mem_sdiff]
      · simp only [hjj, ↓reduceIte]
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [clauseCP_edgeIdx_fst]
        simp [hjj]
    rw [Finset.sum_congr rfl (fun j' _ => hcol j'), Finset.sum_ite_eq Finset.univ j]
    simp only [Finset.mem_univ, ↓reduceIte]
    congr 1
    let valM (m : Fin 6) : ℚ := if edgeIdx j m ∉ S then w (edgeIdx j m) else 0
    have hl : (∑ m : Fin 6,
        if edgeIdx j m ∉ S ∧ ((edges[m.val]).1 = i ∨ (edges[m.val]).2 = i)
        then w (edgeIdx j m) else 0) =
        ∑ m : Fin 6, if (edges[m.val]).1 = i ∨ (edges[m.val]).2 = i then valM m else 0 := by
      refine Finset.sum_congr rfl fun m _ => ?_
      dsimp [valM]
      by_cases hm : edgeIdx j m ∉ S <;>
        by_cases hinc : (edges[m.val]).1 = i ∨ (edges[m.val]).2 = i <;>
        simp [hm, hinc]
    have hr : (∑ i' : Fin 4,
        if i' ≠ i ∧ (splitOfSubset S).adjB j i i' = false
        then (leafWeightsOfSubset S w hw).wEdge j i i' else 0) =
        ∑ i' : Fin 4, match pairEdge? i i' with | some m => valM m | none => 0 := by
      refine Finset.sum_congr rfl fun i' _ => ?_
      dsimp [valM, splitOfSubset, leafWeightsOfSubset]
      by_cases hne : i' = i
      · subst hne
        simp [pairEdge?_self]
      · obtain ⟨m, hm⟩ : ∃ m : Fin 6, pairEdge? i i' = some m := by
          revert hne
          fin_cases i <;> fin_cases i' <;> decide
        by_cases hmem : edgeIdx j m ∈ S <;> simp [hne, hm, hmem]
    rw [hl, hr, sum_edges_match_pairEdge]
  rw [hrow, hedge]
  unfold cAQ
  ring

theorem weighted_compl_rhs_eq (S : Finset (Fin 22)) (w : Fin 22 → ℚ) :
    (∑ k ∈ Finset.univ \ S, w k * ((clauseCP (given k)).2 : ℚ)) =
      (∑ i : Fin 4, if rowIdx i ∉ S then w (rowIdx i) else 0) -
        ∑ j : Fin 3, ∑ m : Fin 6, if edgeIdx j m ∉ S then w (edgeIdx j m) else 0 := by
  rw [sum_fin22_split]
  have hrow : (∑ i : Fin 4,
      if rowIdx i ∈ Finset.univ \ S then w (rowIdx i) * ((clauseCP (given (rowIdx i))).2 : ℚ)
      else 0) =
      ∑ i : Fin 4, if rowIdx i ∉ S then w (rowIdx i) else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [clauseCP_rowIdx_snd]
    simp [Finset.mem_sdiff]
  have hedge : (∑ j : Fin 3, ∑ m : Fin 6,
      if edgeIdx j m ∈ Finset.univ \ S then
        w (edgeIdx j m) * ((clauseCP (given (edgeIdx j m))).2 : ℚ)
      else 0) =
      -(∑ j : Fin 3, ∑ m : Fin 6, if edgeIdx j m ∉ S then w (edgeIdx j m) else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [clauseCP_edgeIdx_snd]
    by_cases hm : edgeIdx j m ∈ S <;> simp [Finset.mem_sdiff, hm]
  rw [hrow, hedge, sub_eq_add_neg]

end PEqualNP.Outside.L_meta_9672_aux.Gemini9668Raw

namespace PEqualNP.Outside.L_meta_9672_aux.CPIntegrationScratch

open PEqualNP.Search PEqualNP.ProofComplexity
open PEqualNP.Outside.L_meta_9672_aux.CPGraphScratch PEqualNP.Outside.L_meta_9672_aux.CPHalfScratch

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem exists_live_trace [Nonempty V] {F : Set (Clause V)} {π : List (CPLine V)}
    (h : IsCPRefutation F π) :
    ∃ (read : ℕ → CPLine V) (rule : ℕ → Rule V) (live : Finset ℕ) (root : ℕ),
      root ∈ live ∧ live ⊆ Finset.range (root + 1) ∧ live.card ≤ π.length ∧
      read root = ((0 : V → ℤ), 1) ∧
      (∀ i ∈ live, legalRule F i read (read i) (rule i)) ∧
      closedUnder (fun i => parents (rule i)) live ∧
      (∀ i j, j ∈ parents (rule i) → j < i) ∧
      ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j) := by
  obtain ⟨r, ht⟩ := extract h.1
  obtain ⟨root, hroot, hread⟩ := find_earlier h.2
  let rule (i : ℕ) : Rule V := if i < π.length then r.reverse.getD i (.inr (.inl (0, 0)))
    else .inl (.inr (.inl (Classical.choice (inferInstance : Nonempty V))))
  have hwhen : ∀ i < π.length, legalRule F i (earlier π) (earlier π i) (rule i) := by
    intro i hi
    have hir : i < r.reverse.length := by simpa [trace_length ht] using hi
    have hlookup : r.reverse[i]? = some (rule i) := by
      simp [rule, hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hir]
    exact rule_at ht hlookup
  have hp : ∀ i j, j ∈ parents (rule i) → j < i := by
    intro i j hj
    by_cases hi : i < π.length
    · exact parent_lt (hwhen i hi) j hj
    · simp [rule, hi, parents] at hj
  obtain ⟨live, hr, hsub, hclosed, hused⟩ := find_live (fun i => parents (rule i)) root hp
  refine ⟨earlier π, rule, live, root, hr, hsub, ?_, hread, ?_, hclosed, hp, hused⟩
  · have hc := Finset.card_le_card hsub
    simp only [Finset.card_range] at hc
    omega
  · intro i hi
    have hir := Finset.mem_range.mp (hsub hi)
    exact hwhen i (by omega)

theorem boolLo_holds (point : V → ℤ) (h : ∀ v, 0 ≤ point v) (v : V) :
    holds point (fun u => if u = v then 1 else 0, 0) := by
  unfold holds value
  simp [ite_mul, Finset.sum_ite_eq', h]

theorem boolHi_holds (point : V → ℤ) (h : ∀ v, point v ≤ 2) (v : V) :
    holds point (fun u => if u = v then -1 else 0, -1) := by
  unfold holds value
  simp [ite_mul, Finset.sum_ite_eq']
  exact h v

theorem sound_closed {F : Set (Clause V)} {read : ℕ → CPLine V} {rule : ℕ → Rule V}
    {live : Finset ℕ} (a : V → ℤ)
    (hlo : ∀ v, 0 ≤ a v) (hhi : ∀ v, a v ≤ 2)
    (hl : ∀ i ∈ live, legalRule F i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (hax : ∀ i ∈ live, ∀ C, rule i = .inl (.inl C) → C ∈ F → holds a (clauseCP C))
    (hev : ∀ i ∈ live, ∀ p d, rule i = .inr (.inr (.inr (p, d))) →
      (2 : ℤ) ∣ value a (read i)) :
    ∀ i ∈ live, holds a (read i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    have h := hl i hi
    have prior (p : ℕ) (hp : p ∈ parents (rule i)) : holds a (read p) :=
      ih p (parent_lt h p hp) (hc i hi p hp)
    rcases hr : rule i with ax | st
    · rw [hr] at h
      rcases ax with C | v
      · obtain ⟨hm, he⟩ := h
        rw [he]
        exact hax i hi C hr hm
      · rcases v with v | v
        · rw [show read i = _ from h]
          exact boolLo_holds a hlo v
        · rw [show read i = _ from h]
          exact boolHi_holds a hhi v
    · rw [hr] at h
      rcases st with ⟨p, q⟩ | (⟨p, k⟩ | ⟨p, d⟩)
      · obtain ⟨_, _, eq⟩ := h
        rw [eq]
        exact holds_add (prior p (by simp [hr, parents])) (prior q (by simp [hr, parents]))
      · obtain ⟨_, eq⟩ := h
        rw [eq]
        exact holds_mul k (prior p (by simp [hr, parents]))
      · obtain ⟨_, hd, hdiv, eq⟩ := h
        have he := hev i hi p d hr
        rw [eq] at he ⊢
        exact holds_div hd hdiv (prior p (by simp [hr, parents])) he

def twiceBool (a : V → Bool) (v : V) : ℤ := if a v then 2 else 0

omit [DecidableEq V] in
theorem twiceBool_value (a : V → Bool) (e : CPLine V) :
    value (twiceBool a) e = 2 * ∑ v, e.1 v * (if a v then 1 else 0) := by
  unfold value
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  cases hv : a v <;> simp [twiceBool, hv, mul_comm]

open PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch in
theorem all_clauses_used {read : ℕ → CPLine PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch.V}
    {rule : ℕ → Rule PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch.V}
    {live : Finset ℕ} {root : ℕ} (hroot : root ∈ live)
    (hr : read root = (0, 1))
    (hl : ∀ i ∈ live, legalRule (PHP (3 + 1) 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live) :
    ∀ k : Fin 22, ∃ i ∈ live, rule i = .inl (.inl (given k)) := by
  intro k
  by_contra! hn
  let a := twiceBool (point k)
  have hlo : ∀ v, 0 ≤ a v := by intro v; cases h : point k v <;> simp [a, twiceBool, h]
  have hhi : ∀ v, a v ≤ 2 := by intro v; cases h : point k v <;> simp [a, twiceBool, h]
  have hax (i : ℕ) (hi : i ∈ live) (C : Clause PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch.V)
      (hrule : rule i = .inl (.inl C)) (hF : C ∈ PHP (3 + 1) 3) : holds a (clauseCP C) := by
    have hne : C ≠ given k := fun eq => hn i hi (eq ▸ hrule)
    have he := coefficient_separates k hF hne
    unfold CPLine.Holds at he
    unfold holds a
    rw [twiceBool_value]
    omega
  have hev (i : ℕ) : (2 : ℤ) ∣ value a (read i) := by
    unfold a
    rw [twiceBool_value]
    exact dvd_mul_right _ _
  have hh := sound_closed a hlo hhi hl hc hax (fun i _ _ _ _ => hev i) root hroot
  rw [hr] at hh
  simp [holds, value] at hh

theorem at_least_22_leaves {read : ℕ → CPLine PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch.V}
    {rule : ℕ → Rule PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch.V}
    {live : Finset ℕ} {root : ℕ} (hroot : root ∈ live)
    (hr : read root = (0, 1))
    (hl : ∀ i ∈ live, legalRule (PHP (3 + 1) 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live) :
    22 ≤ (live.filter (fun i => (parents (rule i)).length = 0)).card := by
  classical
  have every := all_clauses_used hroot hr hl hc
  let pick := fun k : Fin 22 => Classical.choose (every k)
  have spec (k : Fin 22) : pick k ∈ live ∧
      rule (pick k) = .inl (.inl (PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch.given k)) :=
    Classical.choose_spec (every k)
  have hcard := Finset.card_le_card_of_injOn (s := Finset.univ)
    (t := live.filter (fun i => (parents (rule i)).length = 0)) pick (fun k _ =>
    Finset.mem_filter.mpr ⟨(spec k).1, by rw [(spec k).2]; rfl⟩) (by
      intro a _ b _ hab
      have hrule := (spec a).2.symm.trans (congrArg rule hab)
      rw [(spec b).2] at hrule
      exact PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch.given_injective
        (Sum.inl.inj (Sum.inl.inj hrule)))
  simpa using hcard

section Pigeon

open PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch

abbrev Vars := Fin 4 × Fin 3

theorem pigeon_coeff : ∀ (i : Fin 4) (v : Vars),
    (clauseCP (pigeon i)).1 v = if v.1 = i then 1 else 0 := by
  decide +kernel

theorem pigeon_rhs : ∀ i : Fin 4, (clauseCP (pigeon i)).2 = 1 := by
  decide +kernel

theorem collision_coeff : ∀ (i i' : Fin 4) (j : Fin 3) (v : Vars), i ≠ i' →
    (clauseCP (collision i i' j)).1 v =
      (if v = (i, j) then -1 else 0) + (if v = (i', j) then -1 else 0) := by
  decide +kernel

theorem collision_rhs : ∀ (i i' : Fin 4) (j : Fin 3), i ≠ i' →
    (clauseCP (collision i i' j)).2 = -1 := by
  decide +kernel

theorem holds_php (a : Vars → ℤ)
    (hrow : ∀ i : Fin 4, 2 ≤ ∑ j : Fin 3, a (i, j))
    (hpair : ∀ (i i' : Fin 4) (j : Fin 3), i ≠ i' → a (i, j) + a (i', j) ≤ 2)
    {C : Clause Vars} (hc : C ∈ PHP (3 + 1) 3) : holds a (clauseCP C) := by
  rcases hc with ⟨i, rfl⟩ | ⟨i, i', j, hn, rfl⟩
  · change holds a (clauseCP (pigeon i))
    unfold holds value
    simp only [pigeon_rhs, pigeon_coeff, mul_one]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i]
    · simpa using hrow i
    · intro k _ hk
      simp [hk]
    · simp
  · change holds a (clauseCP (collision i i' j))
    unfold holds value
    simp only [collision_rhs _ _ _ hn, collision_coeff _ _ _ _ hn, add_mul,
      Finset.sum_add_distrib, ite_mul, neg_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have := hpair i i' j hn
    linarith

def ParitySource : Prop :=
  ∀ f : Fin 3 → Vars → ℤ, ∃ a : Vars → ℤ, (∀ v, 0 ≤ a v ∧ a v ≤ 2) ∧
    (∀ i : Fin 4, 2 ≤ ∑ j : Fin 3, a (i, j)) ∧
    (∀ (i i' : Fin 4) (j : Fin 3), i ≠ i' → a (i, j) + a (i', j) ≤ 2) ∧
    ∀ k, (2 : ℤ) ∣ ∑ v, f k v * a v

theorem half_for_lines (source : ParitySource) (read : ℕ → CPLine Vars)
    {lines : Finset ℕ} (hsize : lines.card ≤ 3) :
    ∃ a : Vars → ℤ, (∀ v, 0 ≤ a v ∧ a v ≤ 2) ∧
      (∀ C ∈ PHP (3 + 1) 3, holds a (clauseCP C)) ∧
      ∀ i ∈ lines, (2 : ℤ) ∣ value a (read i) := by
  let f (k : Fin 3) (v : Vars) := (read (lines.toList.getD k.val 0)).1 v
  obtain ⟨a, hbox, hrow, hpair, he⟩ := source f
  refine ⟨a, hbox, fun _ hC => holds_php a hrow hpair hC, ?_⟩
  intro i hi
  obtain ⟨j, hj, hji⟩ := List.getElem_of_mem (Finset.mem_toList.mpr hi)
  have hj3 : j < 3 := by
    have := Finset.length_toList lines
    omega
  have hf : lines.toList.getD j 0 = i := by
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have h := he ⟨j, hj3⟩
  change (2 : ℤ) ∣ ∑ v, (read (lines.toList.getD j 0)).1 v * a v at h
  rw [hf] at h
  exact h

def isDivision (r : Rule Vars) : Bool :=
  match r with
  | .inr (.inr (.inr _)) => true
  | _ => false

theorem at_least_four_divisions (source : ParitySource) {read : ℕ → CPLine Vars}
    {rule : ℕ → Rule Vars} {live : Finset ℕ} {root : ℕ}
    (hroot : root ∈ live) (hr : read root = (0, 1))
    (hl : ∀ i ∈ live, legalRule (PHP (3 + 1) 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live) :
    4 ≤ (live.filter (fun i => isDivision (rule i) = true)).card := by
  by_contra! hn
  have hsize : (live.filter (fun i => isDivision (rule i) = true)).card ≤ 3 := by omega
  obtain ⟨a, hbox, hax, he⟩ := half_for_lines source read hsize
  have hdiv (i : ℕ) (hi : i ∈ live) (p d : ℕ)
      (hp : rule i = .inr (.inr (.inr (p, d)))) :
      (2 : ℤ) ∣ value a (read i) :=
    he i (Finset.mem_filter.mpr ⟨hi, by simp [hp, isDivision]⟩)
  have h := sound_closed a (fun v => (hbox v).1) (fun v => (hbox v).2) hl hc
    (fun _ _ C _ => hax C) hdiv root hroot
  rw [hr] at h
  simp [holds, value] at h

def isMultiply (r : Rule Vars) : Bool :=
  match r with
  | .inr (.inr (.inl _)) => true
  | _ => false

theorem parent_count (r : Rule Vars) : (parents r).length ≤ 2 := by
  rcases r with ax | (ab | (m | d)) <;> simp [parents]

theorem unary_kind (r : Rule Vars) :
    (parents r).length = 1 ↔ isDivision r = true ∨ isMultiply r = true := by
  rcases r with ax | (ab | (m | d)) <;> simp [parents, isDivision, isMultiply]

theorem unary_kinds_disjoint (r : Rule Vars) :
    ¬ (isDivision r = true ∧ isMultiply r = true) := by
  rcases r with ax | (ab | (m | d)) <;> simp [isDivision, isMultiply]

theorem live_budget (source : ParitySource) {read : ℕ → CPLine Vars}
    {rule : ℕ → Rule Vars} {live : Finset ℕ} {root : ℕ}
    (hroot : root ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (hsize : live.card ≤ 48) (hr : read root = (0, 1))
    (hl : ∀ i ∈ live, legalRule (PHP (3 + 1) 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (horder : ∀ i j, j ∈ parents (rule i) → j < i)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j)) :
    (live.filter (fun i => (parents (rule i)).length = 0)).card = 22 ∧
      4 ≤ (live.filter (fun i => isDivision (rule i) = true)).card ∧
      (live.filter (fun i => isDivision (rule i) = true)).card +
      (live.filter (fun i => isMultiply (rule i) = true)).card +
      ∑ i ∈ live.erase root, (uses (fun n => parents (rule n)) live i - 1) ≤ 5 := by
  have hL := at_least_22_leaves hroot hr hl hc
  have hD := at_least_four_divisions source hroot hr hl hc
  have hcount := count_budget hroot hsub hc hused horder (fun i _ => parent_count (rule i))
  have hdis : Disjoint (live.filter (fun i => isDivision (rule i) = true))
      (live.filter (fun i => isMultiply (rule i) = true)) := by
    refine Finset.disjoint_left.mpr fun i hi hj => ?_
    exact unary_kinds_disjoint (rule i) ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩
  have hunion : live.filter (fun i => (parents (rule i)).length = 1) =
      (live.filter (fun i => isDivision (rule i) = true)) ∪
      (live.filter (fun i => isMultiply (rule i) = true)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, unary_kind]
    tauto
  rw [hunion, Finset.card_union_of_disjoint hdis] at hcount
  omega

theorem lower_47 (source : ParitySource) (π : List (CPLine Vars))
    (hπ : IsCPRefutation (PHP (3 + 1) 3) π) : 47 ≤ π.length := by
  obtain ⟨read, rule, live, root, hr, hsub, hlen, hroot, hl, hc, horder, hused⟩ :=
    exists_live_trace hπ
  have hL := at_least_22_leaves hr hroot hl hc
  have hD := at_least_four_divisions source hr hroot hl hc
  have hcount := count_budget hr hsub hc hused horder (fun i _ => parent_count (rule i))
  have hdu : (live.filter (fun i => isDivision (rule i) = true)) ⊆
      live.filter (fun i => (parents (rule i)).length = 1) := by
    intro i hi
    obtain ⟨hm, hdiv⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hm, (unary_kind (rule i)).mpr (Or.inl hdiv)⟩
  have hcd := Finset.card_le_card hdu
  omega

theorem checked_lower_47 (π : List (CPLine Vars))
    (hπ : IsCPRefutation (PHP (3 + 1) 3) π) : 47 ≤ π.length :=
  lower_47 PEqualNP.Outside.L_meta_9672_aux.Sol9668HalfBridge.half_point π hπ

theorem no_cleared_region {read : ℕ → CPLine Vars} {rule : ℕ → Rule Vars}
    {live region : Finset ℕ} {root start p d : ℕ}
    (hreg : region ⊆ live) (hroot : root ∈ region) (hresult : read root = (0, 1))
    (hstart : rule start = .inr (.inr (.inr (p, d)))) (hpoff : p ∉ region)
    (hl : ∀ i ∈ live, legalRule (PHP (3 + 1) 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (hcoff : closedUnder (fun i => parents (rule i)) (live \ region))
    (hsmallMul : ∀ i ∈ region, ∀ p m, rule i = .inr (.inr (.inl (p, m))) → m ≤ 1)
    (hcount : ∀ i ∈ region, i ≠ start →
      ((parents (rule i)).filter (fun j => decide (j ∈ region))).length = 1)
    (hdivs : ((live \ region).filter (fun i => isDivision (rule i) = true)).card ≤ 3) :
    False := by
  obtain ⟨a, hbox, hax, heven⟩ :=
    half_for_lines PEqualNP.Outside.L_meta_9672_aux.Sol9668HalfBridge.half_point read hdivs
  have hoff : ∀ i ∈ live, i ∉ region → holds a (read i) := by
    intro i hi hno
    refine sound_closed a (fun v => (hbox v).1) (fun v => (hbox v).2)
      (fun j hj => hl j (Finset.mem_sdiff.mp hj).1) hcoff (fun _ _ C _ => hax C)
      (fun j hj p d hrd => heven j (Finset.mem_filter.mpr ⟨hj, by simp [hrd, isDivision]⟩))
      i (Finset.mem_sdiff.mpr ⟨hi, hno⟩)
  have hclear : ∀ i ∈ region, ∃ den num : ℤ, cleared a (read i) den num := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi
      have hil := hreg hi
      have law := hl i hil
      have earlier_mem (j : ℕ) (hm : j ∈ parents (rule i)) : j ∈ live :=
        hc i hil j hm
      by_cases hsame : i = start
      · subst i
        rw [hstart] at law
        obtain ⟨_, hd, hcoef, eq⟩ := law
        have hpl := earlier_mem p (by simp [hstart, parents])
        rw [eq]
        exact ⟨1 * (d : ℤ), (read p).2, clear_div (clear_start (hoff p hpl hpoff)) hd hcoef⟩
      · have one := hcount i hi hsame
        rcases hr : rule i with ax | (⟨j, k⟩ | (⟨j, m⟩ | ⟨j, l⟩))
        · simp [hr, parents] at one
        · rw [hr] at law
          obtain ⟨hj, hk, eq⟩ := law
          by_cases hjx : j ∈ region <;> by_cases hkx : k ∈ region
          · simp [hr, parents, hjx, hkx] at one
          · obtain ⟨den, num, hv⟩ := ih j hj hjx
            have hk' := earlier_mem k (by simp [hr, parents])
            rw [eq]
            exact ⟨den, num + den * (read k).2, clear_add hv (hoff k hk' hkx)⟩
          · obtain ⟨den, num, hv⟩ := ih k hk hkx
            have hj' := earlier_mem j (by simp [hr, parents])
            have eq' : read i = sumLine (read k) (read j) := by
              rw [eq]
              simp [sumLine, add_comm]
            rw [eq']
            exact ⟨den, num + den * (read j).2, clear_add hv (hoff j hj' hjx)⟩
          · simp [hr, parents, hjx, hkx] at one
        · have hm := hsmallMul i hi j m hr
          rw [hr] at law
          obtain ⟨hj, eq⟩ := law
          interval_cases m
          · have eq0 : read i = (0, 0) := by rw [eq]; simp
            rw [eq0]
            exact ⟨1, 0, clear_start (by simp [holds, value])⟩
          · have eq1 : read i = read j := by rw [eq]; simp
            have hjx : j ∈ region := by
              by_contra hno
              simp [hr, parents, hno] at one
            rw [eq1]
            exact ih j hj hjx
        · rw [hr] at law
          obtain ⟨hj, hl, hcoef, eq⟩ := law
          have hjx : j ∈ region := by
            by_contra hno
            simp [hr, parents, hno] at one
          obtain ⟨den, num, hv⟩ := ih j hj hjx
          rw [eq]
          exact ⟨den * (l : ℤ), num, clear_div hv hl hcoef⟩
  obtain ⟨den, num, h⟩ := hclear root hroot
  rw [hresult] at h
  exact no_cleared_contradiction a den num h

open PEqualNP.Outside.L_meta_9672_aux.Gemini9668Path hiding uses closedUnder in
theorem no_clearable_division {read : ℕ → CPLine Vars} {rule : ℕ → Rule Vars}
    {live : Finset ℕ} {root start : ℕ}
    (hr : root ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (hs : start ∈ live) (hdiv : isDivision (rule start) = true)
    (hresult : read root = (0, 1))
    (hl : ∀ i ∈ live, legalRule (PHP (3 + 1) 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (horder : ∀ i j, j ∈ parents (rule i) → j < i)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j))
    (honce : ∀ i, Reach (fun j => parents (rule j)) live start i →
      i ≠ root → uses (fun j => parents (rule j)) live i = 1)
    (hsmallMul : ∀ i, Reach (fun j => parents (rule j)) live start i →
      ∀ p m, rule i = .inr (.inr (.inl (p, m))) → m ≤ 1)
    (hdivs : ((live \ affected (fun i => parents (rule i)) live start).filter
      (fun i => isDivision (rule i) = true)).card ≤ 3) : False := by
  have hpair : ∃ p d, rule start = .inr (.inr (.inr (p, d))) := by
    rcases heq : rule start with ax | (ab | (m | ⟨p, d⟩))
    all_goals simp [heq, isDivision] at hdiv
    exact ⟨p, d, rfl⟩
  obtain ⟨p, d, hp⟩ := hpair
  let incoming := fun i => parents (rule i)
  have order : ∀ i ∈ live, ∀ j ∈ incoming i, j < i := fun i _ j => horder i j
  have hrootX := root_mem_affected hr hsub order hused hs
  have hpoff := start_not_mem_affected_input hs order p (by simp [incoming, hp, parents])
  exact no_cleared_region (fun _ hi => (mem_affected_iff.mp hi).1) hrootX hresult hp hpoff hl hc
    (complement_closed hc) (fun _ hi => hsmallMul _ (reach_of_mem_affected hi))
    (fun _ hi hne => affected_filter_length_eq_one hsub order hs honce hi hne) hdivs

def forks (incoming : ℕ → List ℕ) (live : Finset ℕ) (root : ℕ) : Finset ℕ :=
  (live.erase root).filter (fun i => 1 < uses incoming live i)

theorem forks_count (incoming : ℕ → List ℕ) (live : Finset ℕ) (root : ℕ) :
    (forks incoming live root).card ≤ ∑ i ∈ live.erase root, (uses incoming live i - 1) := by
  have sumBoole : (∑ i ∈ live.erase root, if 1 < uses incoming live i then (1 : ℕ) else 0) =
      (forks incoming live root).card := Finset.sum_boole _ _
  rw [← sumBoole]
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> omega

def divs (rule : ℕ → Rule Vars) (live : Finset ℕ) : Finset ℕ :=
  live.filter (fun i => isDivision (rule i) = true)

def mults (rule : ℕ → Rule Vars) (live : Finset ℕ) : Finset ℕ :=
  live.filter (fun i => isMultiply (rule i) = true)

def isLargeMultiply (r : Rule Vars) : Bool :=
  match r with
  | .inr (.inr (.inl (_, k))) => decide (2 ≤ k)
  | _ => false

def obstructions (rule : ℕ → Rule Vars) (live : Finset ℕ) (root : ℕ) : Finset ℕ :=
  live.filter (fun i => isLargeMultiply (rule i) = true) ∪
    forks (fun j => parents (rule j)) live root

open PEqualNP.Outside.L_meta_9672_aux.Gemini9668Path hiding uses closedUnder in
theorem clear_if_disjoint {read : ℕ → CPLine Vars} {rule : ℕ → Rule Vars}
    {live : Finset ℕ} {root start : ℕ}
    (hr : root ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (hs : start ∈ divs rule live) (hresult : read root = (0, 1))
    (hl : ∀ i ∈ live, legalRule (PHP (3 + 1) 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (horder : ∀ i j, j ∈ parents (rule i) → j < i)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j))
    (hnone : ∀ i ∈ obstructions rule live root,
      ¬ Reach (fun j => parents (rule j)) live start i)
    (hsmall : (divs rule (live \ affected (fun j => parents (rule j)) live start)).card ≤ 3) :
    False := by
  obtain ⟨hsl, hsd⟩ := Finset.mem_filter.mp hs
  apply no_clearable_division hr hsub hsl hsd hresult hl hc horder hused _ _ hsmall
  · intro i hreach hne
    have hi := reach_mem_live hsl hreach
    have hp := uses_pos (hused i hi hne)
    by_contra! hbad
    have hg : i ∈ forks (fun j => parents (rule j)) live root :=
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hi⟩, by omega⟩
    exact hnone i (Finset.mem_union_right _ hg) hreach
  · intro i hreach p m horig
    have hi := reach_mem_live hsl hreach
    by_contra! hlarge
    have hg : i ∈ live.filter (fun i => isLargeMultiply (rule i) = true) :=
      Finset.mem_filter.mpr ⟨hi, by simp [horig, isLargeMultiply, show 2 ≤ m by omega]⟩
    exact hnone i (Finset.mem_union_left _ hg) hreach

open PEqualNP.Outside.L_meta_9672_aux.Gemini9668Path hiding uses closedUnder in
theorem four_divisions_reach_obstruction {read : ℕ → CPLine Vars} {rule : ℕ → Rule Vars}
    {live : Finset ℕ} {root start : ℕ}
    (hr : root ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (hD : (divs rule live).card = 4) (hs : start ∈ divs rule live)
    (hresult : read root = (0, 1))
    (hl : ∀ i ∈ live, legalRule (PHP (3 + 1) 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (horder : ∀ i j, j ∈ parents (rule i) → j < i)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j)) :
    ∃ i ∈ obstructions rule live root, Reach (fun j => parents (rule j)) live start i := by
  classical
  by_contra! hnone
  let region := affected (fun j => parents (rule j)) live start
  have hx : start ∈ region := mem_affected_of_reach (Finset.mem_filter.mp hs).1
    Relation.ReflTransGen.refl
  have hle : divs rule (live \ region) ⊆ (divs rule live).erase start := by
    intro i hi
    obtain ⟨hm, hd⟩ := Finset.mem_filter.mp hi
    obtain ⟨hil, hn⟩ := Finset.mem_sdiff.mp hm
    exact Finset.mem_erase.mpr ⟨fun eq => hn (eq.symm ▸ hx), Finset.mem_filter.mpr ⟨hil, hd⟩⟩
  have herr := Finset.card_le_card hle
  have hdel := Finset.card_erase_add_one hs
  have hsmall : (divs rule (live \ region)).card ≤ 3 := by omega
  exact clear_if_disjoint hr hsub hs hresult hl hc horder hused hnone hsmall

open PEqualNP.Outside.L_meta_9672_aux.Gemini9668Path hiding uses closedUnder in
theorem five_divisions_incomparable {read : ℕ → CPLine Vars} {rule : ℕ → Rule Vars}
    {live : Finset ℕ} {root start other : ℕ}
    (hr : root ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (hD : (divs rule live).card = 5) (hs : start ∈ divs rule live)
    (ht : other ∈ divs rule live) (hne : start ≠ other)
    (hno : obstructions rule live root = ∅)
    (hresult : read root = (0, 1))
    (hl : ∀ i ∈ live, legalRule (PHP (3 + 1) 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (horder : ∀ i j, j ∈ parents (rule i) → j < i)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j)) :
    ¬ Reach (fun j => parents (rule j)) live start other := by
  classical
  intro hreach
  let region := affected (fun j => parents (rule j)) live start
  have hsl := (Finset.mem_filter.mp hs).1
  have hx : start ∈ region := mem_affected_of_reach hsl Relation.ReflTransGen.refl
  have hy : other ∈ region := mem_affected_of_reach hsl hreach
  have hle : divs rule (live \ region) ⊆ ((divs rule live).erase start).erase other := by
    intro i hi
    obtain ⟨hm, hd⟩ := Finset.mem_filter.mp hi
    obtain ⟨hil, hn⟩ := Finset.mem_sdiff.mp hm
    exact Finset.mem_erase.mpr ⟨fun eq => hn (eq.symm ▸ hy), Finset.mem_erase.mpr
      ⟨fun eq => hn (eq.symm ▸ hx), Finset.mem_filter.mpr ⟨hil, hd⟩⟩⟩
  have herr := Finset.card_le_card hle
  have hsdel := Finset.card_erase_add_one hs
  have htdel := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨Ne.symm hne, ht⟩)
  have hsmall : (divs rule (live \ region)).card ≤ 3 := by omega
  exact clear_if_disjoint hr hsub hs hresult hl hc horder hused (by simp [hno]) hsmall

theorem obstructions_card_le (rule : ℕ → Rule Vars) (live : Finset ℕ) (root : ℕ) :
    (obstructions rule live root).card ≤ (mults rule live).card +
      ∑ i ∈ live.erase root, (uses (fun j => parents (rule j)) live i - 1) := by
  have hM : live.filter (fun i => isLargeMultiply (rule i) = true) ⊆ mults rule live := by
    intro i hi
    obtain ⟨hm, hb⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hm, ?_⟩
    rcases hv : rule i with ax | (ab | (⟨p,k⟩ | d))
    all_goals simp [hv, isLargeMultiply, isMultiply] at hb ⊢
  unfold obstructions
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_le_card hM)
    (forks_count _ _ _))

open PEqualNP.Outside.L_meta_9672_aux.Gemini9668Path hiding uses closedUnder in
theorem four_div_cut {read : ℕ → CPLine Vars} {rule : ℕ → Rule Vars}
    {live : Finset ℕ} {root : ℕ}
    (hr : root ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (hD : (divs rule live).card = 4) (hbudget : (mults rule live).card +
      ∑ i ∈ live.erase root, (uses (fun j => parents (rule j)) live i - 1) ≤ 1)
    (hresult : read root = (0, 1))
    (hl : ∀ i ∈ live, legalRule (PHP (3 + 1) 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (horder : ∀ i j, j ∈ parents (rule i) → j < i)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j)) :
    ∃ pivot ∈ live,
      (∀ i ∈ divs rule live, Reach (fun j => parents (rule j)) live i pivot) ∧
      (((∃ p k, 2 ≤ k ∧ rule pivot = .inr (.inr (.inl (p, k)))) ∧
          (∀ i ∈ mults rule live, i = pivot) ∧
          (∀ i ∈ live, i ≠ root → uses (fun j => parents (rule j)) live i = 1)) ∨
       (mults rule live = ∅ ∧ pivot ≠ root ∧ uses (fun j => parents (rule j)) live pivot = 2 ∧
          ∀ i ∈ live, i ≠ root → i ≠ pivot → uses (fun j => parents (rule j)) live i = 1)) := by
  classical
  let O := obstructions rule live root
  have hO : O.card ≤ 1 := (obstructions_card_le rule live root).trans hbudget
  have hDne : (divs rule live).Nonempty := Finset.card_pos.mp (by omega)
  have reach (i : ℕ) (hi : i ∈ divs rule live) :=
    four_divisions_reach_obstruction hr hsub hD hi hresult hl hc horder hused
  obtain ⟨d, hd⟩ := hDne
  obtain ⟨pivot, hp, _⟩ := reach d hd
  have hunique (i : ℕ) (hi : i ∈ O) : i = pivot := Finset.card_le_one.mp hO i hi pivot hp
  have reachall (i : ℕ) (hi : i ∈ divs rule live) :
      Reach (fun j => parents (rule j)) live i pivot := by
    obtain ⟨q, hq, hreach⟩ := reach i hi
    rw [hunique q hq] at hreach
    exact hreach
  have excess_le (i : ℕ) (hi : i ∈ live) (hne : i ≠ root) :
      uses (fun j => parents (rule j)) live i - 1 ≤
        ∑ j ∈ live.erase root, (uses (fun j => parents (rule j)) live j - 1) :=
    Finset.single_le_sum (f := fun j => uses (fun k => parents (rule k)) live j - 1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hne, hi⟩)
  rcases Finset.mem_union.mp hp with hbig | hfork
  · obtain ⟨hpl, hlarge⟩ := Finset.mem_filter.mp hbig
    have hpr : ∃ p k, 2 ≤ k ∧ rule pivot = .inr (.inr (.inl (p, k))) := by
      rcases hrule : rule pivot with ax | (ab | (⟨p, k⟩ | d))
      all_goals simp [hrule, isLargeMultiply] at hlarge
      exact ⟨p, k, hlarge, rfl⟩
    obtain ⟨p,k,hk,heq⟩ := hpr
    have hpm : pivot ∈ mults rule live :=
      Finset.mem_filter.mpr ⟨hpl, by simp [heq, isMultiply]⟩
    have hM : 0 < (mults rule live).card := Finset.card_pos.mpr ⟨pivot, hpm⟩
    have hone : (mults rule live).card ≤ 1 := by omega
    refine ⟨pivot, hpl, reachall, Or.inl ⟨⟨p,k,hk,heq⟩,
      fun i hi => Finset.card_le_one.mp hone i hi pivot hpm, ?_⟩⟩
    intro i hi hne
    have hpp := uses_pos (hused i hi hne)
    have hex := excess_le i hi hne
    omega
  · obtain ⟨hmem, hgt⟩ := Finset.mem_filter.mp hfork
    obtain ⟨hne, hpl⟩ := Finset.mem_erase.mp hmem
    have hb := excess_le pivot hpl hne
    have hM0 : (mults rule live).card = 0 := by omega
    have huse2 : uses (fun j => parents (rule j)) live pivot = 2 := by omega
    refine ⟨pivot, hpl, reachall, Or.inr ⟨Finset.card_eq_zero.mp hM0, hne, huse2, ?_⟩⟩
    intro i hi hir hip
    have hpos := uses_pos (hused i hi hir)
    by_contra! hbad
    have hif : i ∈ forks (fun j => parents (rule j)) live root :=
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hir, hi⟩, by omega⟩
    exact hip (hunique i (Finset.mem_union_right _ hif))

theorem exactly_axiom_leaves {read : ℕ → CPLine Vars} {rule : ℕ → Rule Vars}
    {live : Finset ℕ} {root : ℕ}
    (hroot : root ∈ live) (hr : read root = (0, 1))
    (hl : ∀ i ∈ live, legalRule (PHP (3 + 1) 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (hsz : (live.filter (fun i => (parents (rule i)).length = 0)).card = 22) :
    ∃ pick : Fin 22 → ℕ, Function.Injective pick ∧
      Finset.univ.image pick = live.filter (fun i => parents (rule i) = []) ∧
      (∀ k, rule (pick k) = .inl (.inl (given k))) ∧
      ∀ k, read (pick k) = clauseCP (given k) := by
  classical
  have all := all_clauses_used hroot hr hl hc
  let pick (k : Fin 22) := Classical.choose (all k)
  have spec (k : Fin 22) : pick k ∈ live ∧ rule (pick k) = .inl (.inl (given k)) :=
    Classical.choose_spec (all k)
  have hinj : Function.Injective pick := by
    intro a b hab
    have ha := (spec a).2
    have hb := (spec b).2
    rw [hab, hb] at ha
    exact given_injective (Sum.inl.inj (Sum.inl.inj ha.symm))
  have hs : Finset.univ.image pick ⊆ live.filter (fun i => parents (rule i) = []) := by
    intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    refine Finset.mem_filter.mpr ⟨(spec k).1, ?_⟩
    rw [(spec k).2]
    rfl
  have hlo := Finset.card_image_of_injective (Finset.univ : Finset (Fin 22)) hinj
  have hsz' : (live.filter (fun i => parents (rule i) = [])).card = 22 := by
    simpa only [List.length_eq_zero_iff] using hsz
  have hEq : Finset.univ.image pick = live.filter (fun i => parents (rule i) = []) := by
    apply Finset.eq_of_subset_of_card_le hs
    rw [hsz', hlo, Finset.card_univ, Fintype.card_fin]
  refine ⟨pick, hinj, hEq, fun k => (spec k).2, ?_⟩
  intro k
  have h := hl (pick k) (spec k).1
  rw [(spec k).2] at h
  exact h.2

theorem sum_selected_axiom_leaves {A : Type} [AddCommMonoid A]
    {leaves group : Finset ℕ} {pick : Fin 22 → ℕ}
    (hi : Function.Injective pick) (he : Finset.univ.image pick = leaves)
    (hsub : group ⊆ leaves) (f : ℕ → A) :
    (∑ i ∈ group, f i) = ∑ k ∈ (Finset.univ.filter fun k => pick k ∈ group), f (pick k) := by
  classical
  have hg : (Finset.univ.filter fun k => pick k ∈ group).image pick = group := by
    ext i
    constructor
    · intro hm
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
      exact (Finset.mem_filter.mp hk).2
    · intro hm
      have hi' := hsub hm
      rw [← he] at hi'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi'
      exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hm⟩, rfl⟩
  rw [← Finset.sum_image (fun a _ b _ eq => hi eq), hg]

def factor (r : Rule Vars) : ℚ :=
  match r with
  | .inr (.inr (.inr (_, d))) => 1 / (max 1 d : ℕ)
  | _ => 1

theorem factor_range (r : Rule Vars) : 0 < factor r ∧ factor r ≤ 1 := by
  rcases r with ax | (ab | (m | ⟨p, d⟩))
  · norm_num [factor]
  · norm_num [factor]
  · norm_num [factor]
  · change 0 < 1 / ((max 1 d : ℕ) : ℚ) ∧ 1 / ((max 1 d : ℕ) : ℚ) ≤ 1
    have hd : (1 : ℚ) ≤ (max 1 d : ℕ) := by exact_mod_cast Nat.le_max_left 1 d
    have hp : (0 : ℚ) < (max 1 d : ℕ) := lt_of_lt_of_le (by norm_num) hd
    exact ⟨one_div_pos.mpr hp, (div_le_one hp).mpr hd⟩

theorem coeff_as_scaled_children {F : Set (Clause Vars)} {read : ℕ → CPLine Vars}
    {r : Rule Vars} {i : ℕ} (h : legalRule F i read (read i) r)
    (hnoMul : isMultiply r = false) (hne : parents r ≠ []) (v : Vars) :
    ((read i).1 v : ℚ) = factor r *
      ((parents r).map (fun p => ((read p).1 v : ℚ))).sum := by
  rcases r with ax | (⟨p, q⟩ | (⟨p, m⟩ | ⟨p, d⟩))
  · exact False.elim (hne rfl)
  · obtain ⟨_, _, he⟩ := h
    rw [he]
    simp [parents, factor]
  · simp [isMultiply] at hnoMul
  · obtain ⟨_, hd, hdiv, he⟩ := h
    rw [he]
    have hm : max 1 d = d := max_eq_right (by omega)
    simp only [factor, hm, parents, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    have hadd : (d : ℤ) * ((read p).1 v / (d : ℤ)) = (read p).1 v :=
      Int.mul_ediv_cancel' (hdiv v)
    have hq : (d : ℚ) * ((read p).1 v / (d : ℤ) : ℤ) = ((read p).1 v : ℚ) := by
      exact_mod_cast hadd
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    field_simp
    linarith

theorem weighted_leaf_coefficients {F : Set (Clause Vars)} {read : ℕ → CPLine Vars}
    {rule : ℕ → Rule Vars} {live : Finset ℕ} {root : ℕ}
    (hr : root ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (hlegal : ∀ i ∈ live, legalRule F i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j))
    (horder : ∀ i j, j ∈ parents (rule i) → j < i)
    (honce : ∀ i ∈ live, i ≠ root → uses (fun i => parents (rule i)) live i = 1)
    (hnoMul : ∀ i ∈ live, isMultiply (rule i) = false) :
    ∃ w : ℕ → ℚ, (∀ i, 0 < w i ∧ w i ≤ 1) ∧ ∀ v : Vars,
      ((read root).1 v : ℚ) =
        ∑ i ∈ live.filter (fun i => parents (rule i) = []), w i * ((read i).1 v : ℚ) := by
  obtain ⟨w, hwroot, hw, he⟩ := find_weights hsub (fun i j => horder j i) hc hused honce
    (fun i => factor (rule i)) (fun i => factor_range (rule i))
  refine ⟨w, hw, ?_⟩
  intro v
  let f (i : ℕ) := w i * ((read i).1 v : ℚ)
  have hsum (j : ℕ) (hj : j ∈ live) (hne : parents (rule j) ≠ []) :
      f j = ((parents (rule j)).map f).sum := by
    unfold f
    have hcoeff := coeff_as_scaled_children (hlegal j hj) (hnoMul j hj) hne v
    rw [hcoeff, ← mul_assoc]
    let c := w j * factor (rule j)
    change c * _ = _
    have haux : ∀ ps : List ℕ, (∀ i ∈ ps, w i = c) →
        c * (ps.map (fun i => ((read i).1 v : ℚ))).sum =
        (ps.map (fun i => w i * ((read i).1 v : ℚ))).sum := by
      intro ps
      induction ps with
      | nil => simp
      | cons x ps ih =>
        intro hs
        simp only [List.map_cons, List.sum_cons, mul_add]
        rw [hs x (List.mem_cons_self), ih (fun i hi => hs i (List.mem_cons_of_mem _ hi))]
    exact haux _ (fun i hi => he j hj i hi)
  have hout := value_from_leaves f hr (root_uses_zero hsub horder) hc
    (fun i hi hn => uses_pos (hused i hi hn)) hsum
  have hz : (∑ i ∈ live.erase root, (uses (fun i => parents (rule i)) live i - 1) • f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hi
    rw [honce i hm hne]
    simp
  rw [hz, add_zero] at hout
  simpa [f, hwroot] using hout

open PEqualNP.Outside.L_meta_9672_aux.Sol9668Cones in
theorem outer_value {read : ℕ → CPLine Vars} {rule : ℕ → Rule Vars}
    {live : Finset ℕ} {root pivot : ℕ}
    (hr : root ∈ live) (hp : pivot ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (hl : ∀ i ∈ live, legalRule (PHP (3 + 1) 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (horder : ∀ i j, j ∈ parents (rule i) → j < i)
    (hused : ∀ i ∈ live, i ≠ root → ∃ j ∈ live, i ∈ parents (rule j))
    (huniq : ∀ i ∈ live, i ≠ root → i ≠ pivot → uses (fun i => parents (rule i)) live i = 1)
    (hM : ∀ i ∈ mults rule live, i = pivot)
    (hD : ∀ i ∈ divs rule live,
      PEqualNP.Outside.L_meta_9672_aux.Gemini9668Path.Reach (fun j => parents (rule j)) live i pivot) :
    read root =
      (1 + (uses (fun j => parents (rule j)) live pivot - 1)) • read pivot +
        ∑ i ∈ leaves (fun j => parents (rule j)) ((outer (fun j => parents (rule j)) live pivot).erase pivot),
        read i := by
  classical
  let incoming := fun j => parents (rule j)
  let B := outer incoming live pivot
  let cut := cutIncoming incoming pivot
  have hOrd : ∀ i ∈ live, ∀ j ∈ incoming i, j < i := fun i _ j => horder i j
  have hrB : root ∈ B := root_mem_outer hr hp hsub hOrd
  have hBsub := outer_bound (incoming := incoming) (p := pivot) hsub
  have hco : closedUnder cut B := outer_closed_of_global_unique hp hsub hOrd hc huniq
  have hOrdCut : ∀ i j, j ∈ cut i → j < i := by
    intro i j h
    by_cases hn : i = pivot
    · simp [cut, cutIncoming, hn] at h
    · exact horder i j (by simpa [cut, cutIncoming, hn] using h)
  have hBused := outer_used hp hOrd hc hused
  have madd (i : ℕ) (hi : i ∈ B) (hn : cut i ≠ []) :
      read i = ((cut i).map read).sum := by
    have hip : i ≠ pivot := by
      intro he
      exact hn (by simp [cut, cutIncoming, he])
    have hol := outer_subset hi
    have law := hl i hol
    rcases hiR : rule i with ax | (⟨p, q⟩ | (m | d))
    · simp [cut, cutIncoming, hip, incoming, hiR, parents] at hn
    · rw [hiR] at law
      obtain ⟨_, _, eq⟩ := law
      have hcut : cut i = [p, q] := by simp [cut, cutIncoming, hip, incoming, hiR, parents]
      rw [hcut]
      change read i = read p + (read q + 0)
      rw [add_zero]
      change read i = ((read p).1 + (read q).1, (read p).2 + (read q).2)
      exact eq
    · have him : i ∈ mults rule live := Finset.mem_filter.mpr ⟨hol, by simp [isMultiply, hiR]⟩
      exact False.elim (hip (hM i him))
    · have hid : i ∈ divs rule live := Finset.mem_filter.mpr ⟨hol, by simp [isDivision, hiR]⟩
      exact False.elim ((mem_outer.mp hi).2 hip (mem_cone.mpr ⟨hol, hD i hid⟩))
  have hval := value_from_leaves read hrB (root_uses_zero hBsub hOrdCut) hco
    (fun i hi hne => uses_pos (hBused i hi hne)) madd
  change read root = (∑ i ∈ leaves cut B, read i) +
    ∑ i ∈ B.erase root, (uses cut B i - 1) • read i at hval
  have hextra : (∑ i ∈ B.erase root, (uses cut B i - 1) • read i) =
      (uses incoming live pivot - 1) • read pivot := by
    have heq : ∀ i ∈ B.erase root,
        (uses cut B i - 1) • read i =
          if i = pivot then (uses incoming live pivot - 1) • read pivot else 0 := by
      intro i hi
      obtain ⟨hir, hiB⟩ := Finset.mem_erase.mp hi
      have hue : uses cut B i = uses incoming live i := outer_uses_eq hp hOrd hc hiB
      rw [hue]
      by_cases h : i = pivot
      · subst i
        simp
      · have hu : uses incoming live i = 1 := huniq i (outer_subset hiB) hir h
        rw [hu]
        simp [h]
    rw [Finset.sum_congr rfl heq, Finset.sum_ite_eq']
    by_cases hpr : pivot = root
    · subst pivot
      rw [root_uses_zero hsub horder]
      simp
    · have hmem : pivot ∈ B.erase root := Finset.mem_erase.mpr ⟨hpr, pivot_mem_outer hp⟩
      simp [hmem]
  rw [hextra, outer_cut_leaves hp, Finset.sum_insert] at hval
  · rw [hval, add_nsmul, one_nsmul]
    abel
  · intro hn
    exact Finset.notMem_erase _ _ (Finset.mem_filter.mp hn).1

end Pigeon

end PEqualNP.Outside.L_meta_9672_aux.CPIntegrationScratch

namespace PEqualNP.Outside.L_meta_9672_aux.Sol9668Antichain

open PEqualNP.Search PEqualNP.ProofComplexity
open CPGraphScratch CPHalfScratch CPIntegrationScratch CPEssentialScratch
open Gemini9668Path hiding closedUnder uses
open Sol9668Cones
open scoped BigOperators

def thirds (e : CPLine Vars) : Prop := 3 * e.2 ≤ ∑ v : Vars, e.1 v

def rawLine (S : Finset (Fin 22)) : CPLine Vars :=
  (fun v => ∑ k ∈ S, (clauseCP (given k)).1 v, ∑ k ∈ S, (clauseCP (given k)).2)

def RawCutSource : Prop :=
  ∀ (S : Finset (Fin 22)) (d : ℕ), 0 < d →
    (∀ v, (d : ℤ) ∣ (rawLine S).1 v) → thirds (divLine d (rawLine S))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem given_thirds : ∀ k : Fin 22, thirds (clauseCP (given k)) := by
  unfold thirds
  decide +kernel

theorem thirds_add {e e' : CPLine Vars} (h : thirds e) (h' : thirds e') : thirds (sumLine e e') := by
  unfold thirds sumLine at *
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  omega

theorem raw_cone_as_subset {read : ℕ → CPLine Vars} {rule : ℕ → Rule Vars}
    {live : Finset ℕ} {root p : ℕ}
    (hl : ∀ i ∈ live, legalRule (PHP 4 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (hsub : live ⊆ Finset.range (root + 1))
    (horder : ∀ i j, j ∈ parents (rule i) → j < i)
    (honce : ∀ i ∈ live, i ≠ root → uses (fun j => parents (rule j)) live i = 1)
    (hp : p ∈ live)
    (hsafe : ∀ j ∈ cone (fun i => parents (rule i)) live p,
      isMultiply (rule j) = false ∧ isDivision (rule j) = false)
    {pick : Fin 22 → ℕ} (hinj : Function.Injective pick)
    (himage : Finset.univ.image pick = live.filter (fun i => parents (rule i) = []))
    (hreads : ∀ k, read (pick k) = clauseCP (given k)) :
    ∃ S : Finset (Fin 22), read p = rawLine S := by
  let incoming := fun i => parents (rule i)
  let A := cone incoming live p
  let group := A.filter (fun i => incoming i = [])
  have horder' : ∀ i ∈ live, ∀ j ∈ incoming i, j < i := fun i _ j => horder i j
  have hpA : p ∈ A := pivot_mem_cone hp
  have hAclosed : closedUnder incoming A := cone_closed hc
  have hAone : ∀ i ∈ A, i ≠ p → uses incoming A i = 1 :=
    cone_uses_one hp hsub horder' (fun i hi hn _ => honce i hi hn)
  have hadd : ∀ j ∈ A, incoming j ≠ [] → read j = ((incoming j).map read).sum := by
    intro j hj hne
    have hlaw := hl j (cone_subset hj)
    have hsafe' := hsafe j hj
    rcases he : rule j with ax | (⟨a, b⟩ | (m | d))
    · exact (hne (by simp [incoming, he, parents])).elim
    · rw [he] at hlaw
      obtain ⟨_, _, hz⟩ := hlaw
      rw [hz]
      simp [incoming, he, parents]
      rfl
    · simp [he, isMultiply] at hsafe'
    · simp [he, isDivision] at hsafe'
  have hr := value_from_leaves read hpA (root_uses_zero (cone_bound horder') horder)
    hAclosed (fun i hi hn => uses_pos (cone_used i hi hn)) hadd
  have hz : (∑ i ∈ A.erase p, (uses incoming A i - 1) • read i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hi
    rw [hAone i hm hne]
    simp
  change read p = (∑ i ∈ group, read i) + ∑ i ∈ A.erase p, (uses incoming A i - 1) • read i at hr
  rw [hz, add_zero] at hr
  have hr' := hr
  have hgroup : group ⊆ live.filter (fun i => parents (rule i) = []) := by
    intro i hi
    obtain ⟨hm, hnil⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨cone_subset hm, hnil⟩
  let S := Finset.univ.filter fun k => pick k ∈ group
  have hsum := sum_selected_axiom_leaves hinj himage hgroup read
  rw [hsum] at hr'
  simp_rw [hreads] at hr'
  refine ⟨S, ?_⟩
  apply Prod.ext
  · funext v
    change (read p).1 v = ∑ k ∈ S, (clauseCP (given k)).1 v
    rw [hr', Prod.fst_sum, Finset.sum_apply]
  · change (read p).2 = ∑ k ∈ S, (clauseCP (given k)).2
    rw [hr', Prod.snd_sum]

theorem no_antichain_refutation (hRawCut : RawCutSource)
    {read : ℕ → CPLine Vars} {rule : ℕ → Rule Vars} {live : Finset ℕ} {root : ℕ}
    (hroot : root ∈ live) (hresult : read root = (0, 1))
    (hl : ∀ i ∈ live, legalRule (PHP 4 3) i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (hsub : live ⊆ Finset.range (root + 1))
    (horder : ∀ i j, j ∈ parents (rule i) → j < i)
    (honce : ∀ i ∈ live, i ≠ root → uses (fun j => parents (rule j)) live i = 1)
    (hnoMul : ∀ i ∈ live, isMultiply (rule i) = false)
    (hleaves : (live.filter (fun i => (parents (rule i)).length = 0)).card = 22)
    (hanti : ∀ i ∈ live.filter (fun j => isDivision (rule j) = true),
      ∀ j ∈ live.filter (fun k => isDivision (rule k) = true), i ≠ j →
        ¬ Reach (fun k => parents (rule k)) live i j) : False := by
  obtain ⟨pick, hinj, himage, _, hreads⟩ := exactly_axiom_leaves hroot hresult hl hc hleaves
  let incoming := fun i => parents (rule i)
  have horder' : ∀ i ∈ live, ∀ j ∈ incoming i, j < i := fun i _ j => horder i j
  have hleaf : ∀ i ∈ live, incoming i = [] → thirds (read i) := by
    intro i hi hn
    have hi' : i ∈ Finset.univ.image pick := by rw [himage]; exact Finset.mem_filter.mpr ⟨hi, hn⟩
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi'
    rw [hreads]
    exact given_thirds k
  have hall : ∀ i ∈ live, thirds (read i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi
      have hlaw := hl i hi
      have prior (p : ℕ) (hp : p ∈ incoming i) : thirds (read p) :=
        ih p (horder' i hi p hp) (hc i hi p hp)
      rcases he : rule i with ax | (⟨a, b⟩ | (m | ⟨p, d⟩))
      · exact hleaf i hi (by simp [incoming, he, parents])
      · rw [he] at hlaw
        obtain ⟨_, _, hz⟩ := hlaw
        rw [hz]
        exact thirds_add (prior a (by simp [incoming, he, parents]))
          (prior b (by simp [incoming, he, parents]))
      · have hno := hnoMul i hi
        simp [he, isMultiply] at hno
      · rw [he] at hlaw
        obtain ⟨hp, hd, hdvd, hz⟩ := hlaw
        have hpin : p ∈ incoming i := by simp [incoming, he, parents]
        have hpl := hc i hi p hpin
        have hdi : i ∈ live.filter (fun j => isDivision (rule j) = true) :=
          Finset.mem_filter.mpr ⟨hi, by simp [he, isDivision]⟩
        have hsafe : ∀ j ∈ cone incoming live p,
            isMultiply (rule j) = false ∧ isDivision (rule j) = false := by
          intro j hj
          obtain ⟨hjl, hjp⟩ := mem_cone.mp hj
          refine ⟨hnoMul j hjl, ?_⟩
          cases hdiv : isDivision (rule j) with
          | false => rfl
          | true =>
            exfalso
            have hdj : j ∈ live.filter (fun k => isDivision (rule k) = true) :=
              Finset.mem_filter.mpr ⟨hjl, hdiv⟩
            have hjl' := reach_le horder' hjp
            have hji : j ≠ i := by omega
            exact hanti j hdj i hdi hji (Relation.ReflTransGen.tail hjp ⟨hi, hpin⟩)
        obtain ⟨S, hraw⟩ := raw_cone_as_subset hl hc hsub horder honce hpl hsafe hinj himage hreads
        rw [hraw] at hdvd hz
        rw [hz]
        exact hRawCut S d hd hdvd
  have hbad := hall root hroot
  rw [hresult] at hbad
  simp [thirds] at hbad

end PEqualNP.Outside.L_meta_9672_aux.Sol9668Antichain

namespace PEqualNP.Outside.L_meta_9672_aux.Sol9668MulInner

open PEqualNP.Search PEqualNP.ProofComplexity
open CPGraphScratch CPIntegrationScratch
open Sol9668Cones
open Gemini9668Path hiding closedUnder uses
open scoped BigOperators

theorem cone_unary {incoming : ℕ → List ℕ} {live : Finset ℕ} {pivot p : ℕ}
    (hpiv : pivot ∈ live) (hin : incoming pivot = [p]) :
    cone incoming live pivot = insert pivot (cone incoming live p) := by
  ext i
  constructor
  · intro hi
    obtain ⟨hil, hreach⟩ := mem_cone.mp hi
    rcases Relation.ReflTransGen.cases_tail hreach with he | ⟨j, hij, hjpiv⟩
    · exact Finset.mem_insert.mpr (Or.inl he.symm)
    · have hmem : j ∈ [p] := hin ▸ hjpiv.2
      have he : j = p := List.mem_singleton.mp hmem
      exact Finset.mem_insert.mpr (Or.inr (mem_cone.mpr ⟨hil, he ▸ hij⟩))
  · intro hi
    rcases Finset.mem_insert.mp hi with he | hcone
    · subst i
      exact pivot_mem_cone hpiv
    · obtain ⟨hil, hreach⟩ := mem_cone.mp hcone
      exact mem_cone.mpr ⟨hil, Relation.ReflTransGen.tail hreach ⟨hpiv, by simp [hin]⟩⟩

theorem unary_cone_leaves {incoming : ℕ → List ℕ} {live : Finset ℕ} {pivot p : ℕ}
    (hpiv : pivot ∈ live) (hin : incoming pivot = [p]) :
    leaves incoming (cone incoming live pivot) = leaves incoming (cone incoming live p) := by
  rw [cone_unary hpiv hin]
  simp [leaves, Finset.filter_insert, hin]

theorem read_mul_pivot {F : Set (Clause Vars)} {read : ℕ → CPLine Vars} {pivot p k : ℕ}
    (hl : legalRule F pivot read (read pivot) (.inr (.inr (.inl (p, k))))) :
    read pivot = k • read p := by
  rw [hl.2]
  apply Prod.ext
  · funext v
    simp [Pi.smul_apply, nsmul_eq_mul]
  · simp [nsmul_eq_mul]

theorem weighted_multiplier_parent {F : Set (Clause Vars)} {read : ℕ → CPLine Vars}
    {rule : ℕ → Rule Vars} {live : Finset ℕ} {root pivot p k : ℕ}
    (hpiv : pivot ∈ live) (hsub : live ⊆ Finset.range (root + 1))
    (hl : ∀ i ∈ live, legalRule F i read (read i) (rule i))
    (hc : closedUnder (fun i => parents (rule i)) live)
    (horder : ∀ i j, j ∈ parents (rule i) → j < i)
    (huniq : ∀ i ∈ live, i ≠ root → i ≠ pivot → uses (fun j => parents (rule j)) live i = 1)
    (hnoMul : ∀ i ∈ live, i ≠ pivot → isMultiply (rule i) = false)
    (hpivotRule : rule pivot = .inr (.inr (.inl (p, k)))) :
    read pivot = k • read p ∧
      ∃ w : ℕ → ℚ, (∀ i, 0 < w i ∧ w i ≤ 1) ∧ ∀ v : Vars,
        ((read p).1 v : ℚ) = ∑ i ∈ leaves (fun j => parents (rule j))
          (cone (fun j => parents (rule j)) live pivot), w i * ((read i).1 v : ℚ) := by
  let incoming := fun i => parents (rule i)
  let A := cone incoming live p
  have hin : incoming pivot = [p] := by simp [incoming, hpivotRule, parents]
  have hmem : p ∈ incoming pivot := by simp [hin]
  have hp : p ∈ live := hc pivot hpiv p hmem
  have hlt : p < pivot := horder pivot p hmem
  have hpivR : pivot < root + 1 := Finset.mem_range.mp (hsub hpiv)
  have horder' : ∀ i ∈ live, ∀ j ∈ incoming i, j < i := fun i _ j => horder i j
  have hneq (i : ℕ) (hi : i ∈ A) : i ≠ root ∧ i ≠ pivot := by
    have hle := reach_le horder' (mem_cone.mp hi).2
    omega
  have hAone : ∀ i ∈ A, i ≠ p → uses incoming A i = 1 := by
    apply cone_uses_one_of_local_unique
    intro i hi _
    exact huniq i (cone_subset hi) (hneq i hi).1 (hneq i hi).2
  have law := hl pivot hpiv
  rw [hpivotRule] at law
  refine ⟨read_mul_pivot law, ?_⟩
  obtain ⟨w, hw, hcoeff⟩ := weighted_leaf_coefficients (pivot_mem_cone hp) (cone_bound horder')
    (fun i hi => hl i (cone_subset hi)) (cone_closed hc) cone_used horder hAone
    (fun i hi => hnoMul i (cone_subset hi) (hneq i hi).2)
  refine ⟨w, hw, ?_⟩
  intro v
  change ((read p).1 v : ℚ) =
    ∑ i ∈ leaves incoming (cone incoming live pivot), w i * ((read i).1 v : ℚ)
  rw [unary_cone_leaves hpiv hin]
  exact hcoeff v

end PEqualNP.Outside.L_meta_9672_aux.Sol9668MulInner

namespace PEqualNP.Outside.L_meta_9672_aux.CPFinishScratch

open PEqualNP.Search PEqualNP.ProofComplexity
open PEqualNP.Outside.L_meta_9672_aux.CPGraphScratch PEqualNP.Outside.L_meta_9672_aux.CPHalfScratch
open PEqualNP.Outside.L_meta_9672_aux.CPIntegrationScratch PEqualNP.Outside.L_meta_9672_aux.CPEssentialScratch
open PEqualNP.Outside.L_meta_9672_aux.Gemini9668Scale PEqualNP.Outside.L_meta_9672_aux.Gemini9668Raw
open PEqualNP.Outside.L_meta_9672_aux.Sol9668Cones

theorem rawLine_eq_sum (S : Finset (Fin 22)) :
    (∑ k ∈ S, clauseCP (given k)) = clauseSum S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [clauseSum]; rfl
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, ih]
    apply Prod.ext
    · funext v
      change (clauseCP (given x)).1 v + (∑ k ∈ S, (clauseCP (given k)).1 v) =
        ∑ k ∈ insert x S, (clauseCP (given k)).1 v
      rw [Finset.sum_insert hx]
    · change (clauseCP (given x)).2 + (∑ k ∈ S, (clauseCP (given k)).2) =
        ∑ k ∈ insert x S, (clauseCP (given k)).2
      rw [Finset.sum_insert hx]

theorem scaled_aggregation_impossible {read : ℕ → CPLine Vars}
    {leaves A B : Finset ℕ} {w : ℕ → ℚ} {pick : Fin 22 → ℕ}
    {start : CPLine Vars} {k : ℕ}
    (hk : 2 ≤ k)
    (hpos : ∀ n, 0 < w n ∧ w n ≤ 1)
    (hinj : Function.Injective pick)
    (himage : Finset.univ.image pick = leaves)
    (hread : ∀ n, read (pick n) = clauseCP (given n))
    (hpart : A ∪ B = leaves) (hdis : Disjoint A B)
    (hcoeff : ∀ v : Vars, (start.1 v : ℚ) = ∑ n ∈ A, w n * ((read n).1 v : ℚ))
    (hcontr : ((0 : Vars → ℤ), (1 : ℤ)) = k • start + ∑ n ∈ B, read n) :
    False := by
  classical
  let selected := Finset.univ.filter fun n : Fin 22 => pick n ∈ B
  have hsubA : A ⊆ leaves := by
    rw [← hpart]
    exact Finset.subset_union_left
  have hsubB : B ⊆ leaves := by
    rw [← hpart]
    exact Finset.subset_union_right
  have hcomp : (Finset.univ.filter fun n : Fin 22 => pick n ∈ A) = Finset.univ \ selected := by
    ext i
    rw [Finset.mem_filter, Finset.mem_sdiff]
    simp only [Finset.mem_univ, true_and]
    have hi : pick i ∈ leaves := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [← hpart, Finset.mem_union] at hi
    have hsel : i ∈ selected ↔ pick i ∈ B := by simp [selected]
    rw [hsel]
    exact ⟨fun ha hb => Finset.disjoint_left.mp hdis ha hb, fun hb => hi.resolve_right hb⟩
  let w' (n : Fin 22) := w (pick n)
  have hw : ∀ n ∉ selected, 0 < w' n ∧ w' n ≤ 1 := fun n _ => hpos (pick n)
  have hb : (∑ n ∈ B, read n) = clauseSum selected := by
    have h := sum_selected_axiom_leaves hinj himage hsubB read
    change (∑ n ∈ B, read n) = ∑ n ∈ selected, read (pick n) at h
    simpa only [hread, rawLine_eq_sum] using h
  rw [hb] at hcontr
  refine scale_impossible (splitOfSubset selected) (leafWeightsOfSubset selected w' hw)
    (k : ℤ) (by exact_mod_cast hk) (fun i j => start.1 (i,j)) start.2 ?_ ?_ ?_
  · intro i j
    have ha := hcoeff (i,j)
    rw [sum_selected_axiom_leaves hinj himage hsubA, hcomp] at ha
    simp_rw [hread] at ha
    exact ha.trans (weighted_compl_eq_cAQ selected w' hw i j)
  · intro i j
    have h := congrArg (fun e : CPLine Vars => e.1 (i, j)) hcontr
    rw [← clauseSum_fst_eq_cB]
    simpa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] using h.symm
  · have h := congrArg (fun e : CPLine Vars => e.2) hcontr
    rw [← clauseSum_snd_eq_split_rhs]
    simpa [nsmul_eq_mul] using h.symm

theorem raw_cut_source : PEqualNP.Outside.L_meta_9672_aux.Sol9668Antichain.RawCutSource := by
  intro S d hd hcoef
  exact all_thirds_exact_divide S d hd _ (fun _ => rfl) rfl hcoef

theorem no_short_refutation (π : List (CPLine Vars))
    (hπ : IsCPRefutation (PHP (3 + 1) 3) π) (hsize : π.length ≤ 48) : False := by
  classical
  obtain ⟨read, rule, live, root, hr, hsub, hlen, hroot, hl, hc, horder, hused⟩ :=
    exists_live_trace hπ
  obtain ⟨hL, hD, limit⟩ :=
    live_budget PEqualNP.Outside.L_meta_9672_aux.Sol9668HalfBridge.half_point hr hsub (hlen.trans hsize)
      hroot hl hc horder hused
  let incoming := fun i => parents (rule i)
  let excess := ∑ i ∈ live.erase root, (uses incoming live i - 1)
  change 4 ≤ (divs rule live).card at hD
  change (divs rule live).card + (mults rule live).card + excess ≤ 5 at limit
  have horder' : ∀ i ∈ live, ∀ j ∈ incoming i, j < i := fun i _ j => horder i j
  have one_of_zero (zero : excess = 0) :
      ∀ i ∈ live, i ≠ root → uses incoming live i = 1 := by
    intro i hi hne
    have hlo : 0 < uses incoming live i := uses_pos (hused i hi hne)
    have hex : uses incoming live i - 1 ≤ excess :=
      Finset.single_le_sum (f := fun j => uses incoming live j - 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hne, hi⟩)
    rw [zero] at hex
    omega
  have mul_false (i : ℕ) (hi : i ∈ live) (hn : i ∉ mults rule live) :
      isMultiply (rule i) = false := by
    cases hm : isMultiply (rule i)
    · rfl
    · exact False.elim (hn (Finset.mem_filter.mpr ⟨hi, hm⟩))
  by_cases h4 : (divs rule live).card = 4
  · have remaining : (mults rule live).card + excess ≤ 1 := by omega
    obtain ⟨pivot, hp, reaches, hsplit⟩ :=
      four_div_cut hr hsub h4 remaining hroot hl hc horder hused
    obtain ⟨pick, hinj, himage, _, hreads⟩ := exactly_axiom_leaves hr hroot hl hc hL
    have hdis := leaves_partition_disjoint (incoming := incoming) (live := live) (p := pivot)
    have hpart := (leaves_partition (incoming := incoming) (live := live) (p := pivot)).symm
    rcases hsplit with ⟨⟨p, k, hk, hpk⟩, hM, hOnce⟩ | ⟨hM, hpne, hp2, hOnce⟩
    · have hOnce' (i : ℕ) (hi : i ∈ live) (hn : i ≠ root) (_ : i ≠ pivot) :=
        hOnce i hi hn
      have hnoM (i : ℕ) (hi : i ∈ live) (hn : i ≠ pivot) :
          isMultiply (rule i) = false :=
        mul_false i hi (fun hiM => hn (hM i hiM))
      obtain ⟨hpval, w, hw, hcoeff⟩ :=
        PEqualNP.Outside.L_meta_9672_aux.Sol9668MulInner.weighted_multiplier_parent
          hp hsub hl hc horder hOnce' hnoM hpk
      have hOut := outer_value hr hp hsub hl hc horder hused hOnce' hM reaches
      have hzero : uses incoming live pivot - 1 = 0 := by
        by_cases h : pivot = root
        · rw [h, root_uses_zero hsub horder]
        · rw [hOnce pivot hp h]
      change read root = (1 + (uses incoming live pivot - 1)) • read pivot + _ at hOut
      rw [hzero] at hOut
      simp only [Nat.add_zero, one_nsmul] at hOut
      rw [hpval, hroot] at hOut
      exact scaled_aggregation_impossible hk hw hinj himage hreads hpart hdis hcoeff hOut
    · have hM' : ∀ i ∈ mults rule live, i = pivot := by simp [hM]
      have hOut := outer_value hr hp hsub hl hc horder hused hOnce hM' reaches
      let A := cone incoming live pivot
      obtain ⟨w, hw, hcoeff⟩ := weighted_leaf_coefficients (pivot_mem_cone hp)
        (cone_bound horder') (fun i hi => hl i (cone_subset hi)) (cone_closed hc)
        cone_used horder (cone_uses_one hp hsub horder' hOnce)
        (fun i hi => mul_false i (cone_subset hi) (by simp [hM]))
      change read root = (1 + (uses incoming live pivot - 1)) • read pivot + _ at hOut
      change uses incoming live pivot = 2 at hp2
      rw [hp2, hroot] at hOut
      exact scaled_aggregation_impossible (k := 2) (by decide) hw hinj himage hreads hpart hdis hcoeff hOut
  · have h5 : (divs rule live).card = 5 := by omega
    have hz : excess = 0 := by omega
    have hM0 : (mults rule live).card = 0 := by omega
    have hM : mults rule live = ∅ := Finset.card_eq_zero.mp hM0
    have hO : obstructions rule live root = ∅ := by
      apply Finset.card_eq_zero.mp
      have hm := obstructions_card_le rule live root
      change (obstructions rule live root).card ≤ (mults rule live).card + excess at hm
      omega
    exact PEqualNP.Outside.L_meta_9672_aux.Sol9668Antichain.no_antichain_refutation raw_cut_source hr
      hroot hl hc hsub horder (one_of_zero hz)
      (fun i hi => mul_false i hi (by simp [hM])) hL
      (fun i hi j hj hne => five_divisions_incomparable hr hsub h5 hi hj hne hO hroot hl hc horder hused)

end PEqualNP.Outside.L_meta_9672_aux.CPFinishScratch

theorem PEqualNP.Outside.L_meta_9672 : ¬ (∃ π : List (PEqualNP.Search.CPLine (Fin (3 + 1) × Fin 3)), PEqualNP.Search.IsCPRefutation (PEqualNP.ProofComplexity.PHP (3 + 1) 3) π ∧ π.length ≤ 48) := by
  rintro ⟨π, hπ, hlen⟩
  exact PEqualNP.Outside.L_meta_9672_aux.CPFinishScratch.no_short_refutation π hπ hlen
