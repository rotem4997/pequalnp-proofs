import Mathlib

namespace PEqualNP.Outside.L_meta_9984

abbrev I := Fin 15
abbrev Box := Fin 50

def cell (i j : I) : Bool :=
  (([32256, 29120, 19872, 11104, 5856, 28700, 19482, 10774, 5646, 16793, 8533, 4301, 2355, 1195, 615] : List Nat).getD i.val 0).testBit j.val

def pair (p : I) : Nat := #[3, 5, 9, 17, 33, 6, 10, 18, 34, 12, 20, 36, 24, 40, 48][p.val]!

def part (k : Box) : Nat :=
  #[3, 5, 9, 17, 33, 6, 10, 18, 34, 12, 20, 36, 24, 40, 48,
    60, 58, 54, 46, 30, 57, 53, 45, 29, 51, 43, 27, 39, 23, 15,
    7, 11, 13, 14, 19, 21, 22, 25, 26, 28, 35, 37, 38, 41, 42, 44, 49, 50, 52, 56][k.val]!

def left (a : Nat) (p : I) : Bool := (a &&& pair p) == pair p
def right (a : Nat) (p : I) : Bool := (a &&& pair p) == 0
def covered (k : Box) (i j : I) : Bool := left (part k) i && right (part k) j
def Covers (S : Finset Box) : Prop := ∀ i j, cell i j = true → ∃ k ∈ S, covered k i j = true

theorem cellSym (i j : I) : cell i j = cell j i := by
  have h : ∀ i j : I, cell i j = cell j i := by decide +kernel
  exact h i j

def star (d : Bool) (p : I) : Box :=
  ⟨p.val + (if d then 15 else 0), by cases d <;> have := p.isLt <;> simp <;> omega⟩

def triTouches (d : Bool) (k : Box) (p : I) : Bool := if d then right (part k) p else left (part k) p
def stars (S : Finset Box) (d : Bool) : Finset I := Finset.univ.filter fun p => star d p ∈ S
def tris (S : Finset Box) : Finset Box := S.filter fun k => 30 ≤ k.val
def ownCnt (S : Finset Box) (d : Bool) (p : I) : Nat := if p ∈ stars S d then 1 else 0
def oppCnt (S : Finset Box) (d : Bool) (p : I) : Nat := ((stars S (!d)).filter fun q => cell p q = true).card
def triCnt (S : Finset Box) (d : Bool) (p : I) : Nat := ((tris S).filter fun k => triTouches d k p = true).card
def price (S : Finset Box) (d : Bool) (p : I) : Nat := 18 * ownCnt S d p + 4 * oppCnt S d p + 7 * triCnt S d p

abbrev Cap := Fin 64

def capGrow (e : Cap) (i : I) : Cap := Fin.ofNat 64 (e.val ||| pair i)

def capProject (e : Cap) : Box :=
  Fin.ofNat 50 (([0, 0, 0, 0, 0, 1, 5, 30, 0, 2, 6, 31, 9, 32, 33, 29,
    0, 3, 7, 34, 10, 35, 36, 28, 12, 37, 38, 26, 39, 23, 19, 0,
    0, 4, 8, 40, 11, 41, 42, 27, 13, 43, 44, 25, 45, 22, 18, 0,
    14, 46, 47, 24, 48, 21, 17, 0, 49, 20, 16, 0, 15, 0, 0, 0] : List Nat).getD e.val 0)

theorem capInitial : ∀ j : I, right (0 : Cap).val j = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem capAdds : ∀ (e : Cap) (i : I), left (capGrow e i).val i = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem capPreserves : ∀ (e : Cap) (i p : I),
    left e.val p = true → left (capGrow e i).val p = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem capIntersects : ∀ (e : Cap) (i j : I),
    right e.val j = true → cell i j = true → right (capGrow e i).val j = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem capProper : ∀ (e : Cap) (i j : I),
    left e.val i = true → right e.val j = true → covered (capProject e) i j = true := by
  decide +kernel

theorem capClosure (rows cols : Finset I)
    (clean : ∀ i ∈ rows, ∀ j ∈ cols, cell i j = true) :
    ∃ e : Cap, (∀ i ∈ rows, left e.val i = true) ∧ (∀ j ∈ cols, right e.val j = true) := by
  classical
  induction rows using Finset.induction_on with
  | empty => exact ⟨0, by simp, fun j _ => capInitial j⟩
  | @insert i rows fresh ih =>
    obtain ⟨e, hr, hc⟩ := ih (fun p hp => clean p (Finset.mem_insert_of_mem hp))
    refine ⟨capGrow e i, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact capAdds e _
      · exact capPreserves e i p (hr p hp)
    · intro j hj
      exact capIntersects e i j (hc j hj) (clean i (Finset.mem_insert_self i rows) j hj)

def Pure (r : Finset I × Finset I) : Prop := ∀ i ∈ r.1, ∀ j ∈ r.2, cell i j = true

theorem extendPure (r : Finset I × Finset I) (good : Pure r) :
    ∃ k : Box, ∀ i ∈ r.1, ∀ j ∈ r.2, covered k i j = true := by
  obtain ⟨e, hr, hc⟩ := capClosure r.1 r.2 good
  exact ⟨capProject e, fun i hi j hj => capProper e i j (hr i hi) (hc j hj)⟩

theorem normalizeRects (l : List (Finset I × Finset I)) (good : ∀ r ∈ l, Pure r) :
    ∃ S : Finset Box, S.card ≤ l.length ∧
      ∀ r ∈ l, ∀ i ∈ r.1, ∀ j ∈ r.2, ∃ k ∈ S, covered k i j = true := by
  induction l with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons r rs ih =>
    obtain ⟨k, hk⟩ := extendPure r (good r (List.mem_cons_self ..))
    obtain ⟨S, size, hs⟩ := ih (fun t ht => good t (List.mem_cons_of_mem r ht))
    refine ⟨insert k S, ?_, ?_⟩
    · have hCard := Finset.card_insert_le k S
      simp only [List.length_cons]
      omega
    · intro t ht i hi j hj
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨k, Finset.mem_insert_self .., hk i hi j hj⟩
      · obtain ⟨b, hb, hcover⟩ := hs t ht i hi j hj
        exact ⟨b, Finset.mem_insert_of_mem hb, hcover⟩

theorem normalize (l : List (Finset I × Finset I)) (good : ∀ r ∈ l, Pure r)
    (all : ∀ i j, cell i j = true → ∃ r ∈ l, i ∈ r.1 ∧ j ∈ r.2) :
    ∃ S : Finset Box, S.card ≤ l.length ∧ Covers S := by
  obtain ⟨S, size, hs⟩ := normalizeRects l good
  refine ⟨S, size, ?_⟩
  intro i j hc
  obtain ⟨r, hr, hi, hj⟩ := all i j hc
  exact hs r hr i hi j hj

open scoped BigOperators

private def chargeNeighbors (p : I) : Finset I :=
  Finset.univ.filter fun q => cell p q = true

private def chargeTouchSet (d : Bool) (k : Box) : Finset I :=
  Finset.univ.filter fun p => triTouches d k p = true

set_option maxRecDepth 2048 in
private theorem chargeNeighborCard : ∀ p : I, (chargeNeighbors p).card = 6 := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem chargeTouchCard :
    ∀ (d : Bool) (k : Box), 30 ≤ k.val → (chargeTouchSet d k).card = 3 := by
  decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem chargeStarUnique :
    ∀ (d : Bool) (p r : I), triTouches d (star d r) p = true → p = r := by
  decide +kernel

-- Two triples that share a pair on one side also share a pair on the other.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem chargeCommonTouch : ∀ (k l : Box), 30 ≤ k.val → 30 ≤ l.val →
    ((∃ p : I, triTouches false k p = true ∧ triTouches false l p = true) ↔
     (∃ p : I, triTouches true k p = true ∧ triTouches true l p = true)) := by
  decide +kernel

private theorem chargeTriUnion (d : Bool) (p : I) (k l : Box)
    (hk : 30 ≤ k.val) (hl : 30 ≤ l.val)
    (hkp : triTouches d k p = true) (hlp : triTouches d l p = true) :
    (chargeTouchSet (!d) k ∪ chargeTouchSet (!d) l).card ≤ 5 := by
  have hshare : ∃ q : I, triTouches (!d) k q = true ∧ triTouches (!d) l q = true := by
    have h := chargeCommonTouch k l hk hl
    cases d
    · exact h.mp ⟨p, hkp, hlp⟩
    · exact h.mpr ⟨p, hkp, hlp⟩
  obtain ⟨q, hqk, hql⟩ := hshare
  have hpos : 0 < (chargeTouchSet (!d) k ∩ chargeTouchSet (!d) l).card :=
    Finset.card_pos.mpr ⟨q, Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ q, hqk⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ q, hql⟩⟩⟩
  have hu := Finset.card_union_add_card_inter (chargeTouchSet (!d) k) (chargeTouchSet (!d) l)
  rw [chargeTouchCard (!d) k hk, chargeTouchCard (!d) l hl] at hu
  omega

private theorem chargeStarAt (d : Bool) (k : Box)
    (h : (if d then 15 else 0) ≤ k.val ∧ k.val < (if d then 15 else 0) + 15) :
    ∃ p : I, star d p = k := by
  let b : Nat := if d then 15 else 0
  change b ≤ k.val ∧ k.val < b + 15 at h
  obtain ⟨ha, hb⟩ := h
  refine ⟨⟨k.val - b, by omega⟩, Fin.ext ?_⟩
  change k.val - b + b = k.val
  omega

private theorem chargeBoxClass (d : Bool) (k : Box) :
    (∃ r : I, k = star d r) ∨ (∃ r : I, k = star (!d) r) ∨ 30 ≤ k.val := by
  have hclass : (∃ r : I, k = star false r) ∨ (∃ r : I, k = star true r) ∨ 30 ≤ k.val := by
    by_cases h0 : k.val < 15
    · obtain ⟨p, hp⟩ := chargeStarAt false k ⟨Nat.zero_le _, h0⟩
      exact Or.inl ⟨p, hp.symm⟩
    by_cases h1 : k.val < 30
    · have hb : 15 ≤ k.val := by omega
      obtain ⟨p, hp⟩ := chargeStarAt true k ⟨hb, h1⟩
      exact Or.inr (Or.inl ⟨p, hp.symm⟩)
    exact Or.inr (Or.inr (by omega))
  cases d
  · exact hclass
  · rcases hclass with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

private theorem chargeCoverTouches (S : Finset Box) (h : Covers S) (d : Bool) (p q : I)
    (hc : cell p q = true) :
    ∃ k ∈ S, triTouches d k p = true ∧ triTouches (!d) k q = true := by
  cases d
  · obtain ⟨k, hk, hkc⟩ := h p q hc
    change (left (part k) p && right (part k) q) = true at hkc
    exact ⟨k, hk, Bool.and_eq_true_iff.mp hkc⟩
  · obtain ⟨k, hk, hkc⟩ := h q p ((cellSym q p).trans hc)
    change (left (part k) q && right (part k) p) = true at hkc
    obtain ⟨hleft, hright⟩ := Bool.and_eq_true_iff.mp hkc
    exact ⟨k, hk, hright, hleft⟩

-- Every neighbor not covered by an opposite star lies in an incident triangle patch.
private theorem chargeNeighborSubset (S : Finset Box) (h : Covers S) (d : Bool) (p : I)
    (hno : p ∉ stars S d) (U : Finset I)
    (hU : ∀ k ∈ (tris S).filter (fun k => triTouches d k p = true),
      chargeTouchSet (!d) k ⊆ U) :
    chargeNeighbors p ⊆ ((stars S (!d)).filter fun q => cell p q = true) ∪ U := by
  intro q hq
  have hc := (Finset.mem_filter.mp hq).2
  obtain ⟨k, hk, hp, hq'⟩ := chargeCoverTouches S h d p q hc
  rcases chargeBoxClass d k with ⟨r, rfl⟩ | ⟨r, rfl⟩ | hkTri
  · have he := chargeStarUnique d p r hp
    subst r
    exact (hno (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hk⟩)).elim
  · have he := chargeStarUnique (!d) q r hq'
    subst r
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ q, hk⟩, hc⟩)
  · exact Finset.mem_union_right _ (hU k
      (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hk, hkTri⟩, hp⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq'⟩))

theorem localLimits (S : Finset Box) (h : Covers S) (d : Bool) (p : I)
    (hn : ownCnt S d p = 0) :
    (triCnt S d p = 0 → 6 ≤ oppCnt S d p) ∧
    (triCnt S d p = 1 → 3 ≤ oppCnt S d p) ∧
    (triCnt S d p = 2 → 1 ≤ oppCnt S d p) := by
  have hno : p ∉ stars S d := by
    intro hp
    simp [ownCnt, hp] at hn
  let O := (stars S (!d)).filter fun q => cell p q = true
  let T := (tris S).filter fun k => triTouches d k p = true
  have hbound (U : Finset I) (hU : ∀ k ∈ T, chargeTouchSet (!d) k ⊆ U) :
      6 ≤ oppCnt S d p + U.card := by
    calc
      6 = (chargeNeighbors p).card := (chargeNeighborCard p).symm
      _ ≤ (O ∪ U).card := Finset.card_le_card (chargeNeighborSubset S h d p hno U hU)
      _ ≤ O.card + U.card := Finset.card_union_le O U
  have hlarge (k : Box) (hk : k ∈ T) : 30 ≤ k.val ∧ triTouches d k p = true :=
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2, (Finset.mem_filter.mp hk).2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    have he := Finset.card_eq_zero.mp (show T.card = 0 from ht)
    have hb := hbound ∅ (by
      intro k hk
      simp [he] at hk)
    simpa using hb
  · intro ht
    obtain ⟨k, he⟩ := Finset.card_eq_one.mp (show T.card = 1 from ht)
    have hk : k ∈ T := by rw [he]; simp
    have hb := hbound (chargeTouchSet (!d) k) (by
      intro l hl q hq
      have hkl : l = k := by simpa only [he, Finset.mem_singleton] using hl
      subst l
      exact hq)
    rw [chargeTouchCard (!d) k (hlarge k hk).1] at hb
    omega
  · intro ht
    obtain ⟨k, l, _, he⟩ := Finset.card_eq_two.mp (show T.card = 2 from ht)
    have hk : k ∈ T := by rw [he]; simp
    have hl : l ∈ T := by rw [he]; simp
    have hb := hbound (chargeTouchSet (!d) k ∪ chargeTouchSet (!d) l) (by
      intro m hm q hq
      have hml : m = k ∨ m = l := by simpa only [he, Finset.mem_insert, Finset.mem_singleton] using hm
      rcases hml with rfl | rfl
      · exact Finset.mem_union_left _ hq
      · exact Finset.mem_union_right _ hq)
    have hu := chargeTriUnion d p k l (hlarge k hk).1 (hlarge l hl).1
      (hlarge k hk).2 (hlarge l hl).2
    omega

private theorem chargeSumOwn (S : Finset Box) (d : Bool) :
    (∑ p : I, ownCnt S d p) = (stars S d).card := by
  have hf : (Finset.univ.filter fun p : I => p ∈ stars S d) = stars S d := by
    ext p
    simp
  unfold ownCnt
  rw [← Finset.card_filter, hf]

theorem sumOppCnt (S : Finset Box) (d : Bool) :
    (∑ p : I, oppCnt S d p) = 6 * (stars S (!d)).card := by
  simp only [oppCnt, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    _ = ∑ q ∈ stars S (!d), (6 : Nat) := by
      apply Finset.sum_congr rfl
      intro q _
      calc
        (∑ p : I, if cell p q = true then 1 else 0) =
            ∑ p : I, if cell q p = true then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro p _
          rw [cellSym p q]
        _ = (chargeNeighbors q).card := (Finset.card_filter _ _).symm
        _ = 6 := chargeNeighborCard q
    _ = 6 * (stars S (!d)).card := by simp [Nat.mul_comm]

private theorem chargeSumTri (S : Finset Box) (d : Bool) :
    (∑ p : I, triCnt S d p) = 3 * (tris S).card := by
  simp only [triCnt, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    _ = ∑ k ∈ tris S, (3 : Nat) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.card_filter]
      exact chargeTouchCard d k (Finset.mem_filter.mp hk).2
    _ = 3 * (tris S).card := by simp [Nat.mul_comm]

theorem totalPrice (S : Finset Box) (d : Bool) :
    (∑ p : I, price S d p) =
      18 * (stars S d).card + 24 * (stars S (!d)).card + 21 * (tris S).card := by
  simp only [price, Finset.sum_add_distrib, ← Finset.mul_sum, chargeSumOwn, sumOppCnt, chargeSumTri]
  ring

private theorem chargeStarCard (S : Finset Box) (d : Bool) :
    (stars S d).card = (S.filter fun k =>
      (if d then 15 else 0) ≤ k.val ∧ k.val < (if d then 15 else 0) + 15).card := by
  let b : Nat := if d then 15 else 0
  change _ = (S.filter fun k => b ≤ k.val ∧ k.val < b + 15).card
  refine Finset.card_bij (fun p _ => star d p) ?_ ?_ ?_
  · intro p hp
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).2, ?_⟩
    change b ≤ p.val + b ∧ p.val + b < b + 15
    have := p.isLt
    omega
  · intro p _ q _ he
    have hv := congrArg (fun k : Box => k.val) he
    change p.val + b = q.val + b at hv
    exact Fin.ext (by omega)
  · intro k hk
    obtain ⟨hm, hv⟩ := Finset.mem_filter.mp hk
    obtain ⟨p, he⟩ := chargeStarAt d k hv
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, he.symm ▸ hm⟩, he⟩

theorem cardParts (S : Finset Box) :
    (stars S false).card + (stars S true).card + (tris S).card = S.card := by
  let small := S.filter fun k => k.val < 30
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun k : Box => k.val < 30)
  have htri : (S.filter fun k => ¬ k.val < 30) = tris S := by
    ext k
    simp only [tris, Finset.mem_filter, not_lt]
  rw [htri] at hsplit
  have hfirst : (small.filter fun k => k.val < 15) = S.filter (fun k => k.val < 15) := by
    ext k
    simp only [small, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hk, _⟩, hl⟩
      exact ⟨hk, hl⟩
    · rintro ⟨hk, hl⟩
      exact ⟨⟨hk, by omega⟩, hl⟩
  have hsecond : (small.filter fun k => ¬ k.val < 15) =
      S.filter (fun k => 15 ≤ k.val ∧ k.val < 30) := by
    ext k
    simp only [small, Finset.mem_filter, not_lt]
    tauto
  have hs := Finset.card_filter_add_card_filter_not (s := small) (fun k : Box => k.val < 15)
  rw [hfirst, hsecond] at hs
  have hf : (stars S false).card = (S.filter fun k => k.val < 15).card := by
    simpa using chargeStarCard S false
  have ht : (stars S true).card = (S.filter fun k => 15 ≤ k.val ∧ k.val < 30).card :=
    chargeStarCard S true
  change small.card + (tris S).card = S.card at hsplit
  rw [hf, ht, hs, hsplit]

def slack (S : Finset Box) (d : Bool) (p : I) : Nat := price S d p - 18

def sideSlack (S : Finset Box) (d : Bool) : Nat := ∑ p : I, slack S d p

theorem ownOne (S : Finset Box) (d : Bool) (p : I) (h : p ∈ stars S d) :
    ownCnt S d p = 1 := by simp [ownCnt, h]

theorem ownZero (S : Finset Box) (d : Bool) (p : I) (h : p ∉ stars S d) :
    ownCnt S d p = 0 := by simp [ownCnt, h]

theorem sumOwnCnt (S : Finset Box) (d : Bool) :
    (∑ p : I, ownCnt S d p) = (stars S d).card := by
  simp [ownCnt]

theorem basePrice (S : Finset Box) (h : Covers S) (d : Bool) (p : I) :
    18 ≤ price S d p := by
  by_cases own : p ∈ stars S d
  · unfold price
    rw [ownOne S d p own]
    omega
  · have ho := ownZero S d p own
    obtain ⟨h0, h1, h2⟩ := localLimits S h d p ho
    unfold price
    omega

theorem priceSlack (S : Finset Box) (h : Covers S) (d : Bool) (p : I) :
    price S d p = 18 + slack S d p := by
  have := basePrice S h d p
  unfold slack
  omega

theorem slackTotal (S : Finset Box) (h : Covers S) (d : Bool) :
    sideSlack S d + 270 = 18 * (stars S d).card + 24 * (stars S (!d)).card + 21 * (tris S).card := by
  have total := totalPrice S d
  simp only [priceSlack S h d, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul, show (15 : Nat) * 18 = 270 by decide] at total
  unfold sideSlack
  omega

theorem slackLe (S : Finset Box) (d : Bool) (p : I) : slack S d p ≤ sideSlack S d := by
  exact Finset.single_le_sum (f := slack S d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)

theorem oppLe (S : Finset Box) (d : Bool) (p : I) : oppCnt S d p ≤ (stars S (!d)).card :=
  Finset.card_filter_le _ _

theorem oppMem (S : Finset Box) (d : Bool) (p q : I)
    (hq : q ∈ stars S (!d)) (hpq : cell p q = true) : 1 ≤ oppCnt S d p := by
  exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, hpq⟩⟩

theorem oppTwo (S : Finset Box) (d : Bool) (p a b : I)
    (ha : a ∈ stars S (!d)) (hb : b ∈ stars S (!d)) (hab : a ≠ b)
    (hpa : cell p a = true) (hpb : cell p b = true) : 2 ≤ oppCnt S d p := by
  let T := (stars S (!d)).filter fun q => cell p q = true
  have sub : ({a, b} : Finset I) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨ha, hpa⟩
    · exact Finset.mem_filter.mpr ⟨hb, hpb⟩
  simpa [oppCnt, T, Finset.card_insert_of_notMem, hab] using Finset.card_le_card sub

theorem commonNeighbor : ∀ a b : I, ∃ p : I, cell p a = true ∧ cell p b = true := by
  decide +kernel

theorem ownNoOpp (S : Finset Box) (h : Covers S)
    (budget : sideSlack S false + sideSlack S true ≤ 6) (d : Bool) (p : I)
    (hp : p ∈ stars S d) : oppCnt S d p = 0 := by
  by_contra! nz
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < oppCnt S d p by omega)
  obtain ⟨hq, hpq⟩ := Finset.mem_filter.mp hq
  have hn : p ∈ stars S (!(!d)) := by simpa using hp
  have oq := oppMem S (!d) q p hn (by rwa [cellSym])
  have lp := priceSlack S h d p
  have lq := priceSlack S h (!d) q
  have sp := slackLe S d p
  have sq := slackLe S (!d) q
  rw [price, ownOne S d p hp] at lp
  rw [price, ownOne S (!d) q hq] at lq
  cases d <;> simp only [Bool.not_false, Bool.not_true] at * <;> omega

theorem ownNoTri (S : Finset Box) (h : Covers S)
    (budget : sideSlack S false + sideSlack S true ≤ 6) (d : Bool) (p : I)
    (hp : p ∈ stars S d) : triCnt S d p = 0 := by
  have lp := priceSlack S h d p
  rw [price, ownOne S d p hp] at lp
  have sp := slackLe S d p
  cases d <;> omega

theorem zeroSlackImpossible (S : Finset Box) (h : Covers S) (d : Bool)
    (zero : sideSlack S d = 0) (sizes : (stars S d).card = (stars S (!d)).card + 1) : False := by
  have units (p : I) : oppCnt S d p + ownCnt S d p = 1 := by
    have sp := slackLe S d p
    have lp := priceSlack S h d p
    unfold price at lp
    by_cases own : p ∈ stars S d
    · have := ownOne S d p own
      omega
    · have ho := ownZero S d p own
      obtain ⟨h0, h1, h2⟩ := localLimits S h d p ho
      omega
  have sum : (∑ p : I, (oppCnt S d p + ownCnt S d p)) = ∑ p : I, (1 : Nat) :=
    Finset.sum_congr rfl (fun p _ => units p)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul, mul_one, sumOwnCnt, sumOppCnt] at sum
  have n : (stars S (!d)).card = 2 := by omega
  obtain ⟨a, b, hab, eq⟩ := Finset.card_eq_two.mp n
  obtain ⟨p, hpa, hpb⟩ := commonNeighbor a b
  have ha : a ∈ stars S (!d) := by simp [eq]
  have hb : b ∈ stars S (!d) := by simp [eq]
  have := oppTwo S d p a b ha hb hab hpa hpb
  have := units p
  omega

theorem balancedDegree (S : Finset Box) (h : Covers S) (d : Bool) (p : I)
    (tight : sideSlack S d = 3) (ho : p ∉ stars S d) :
    (oppCnt S d p = 0 ∧ 3 ≤ slack S d p) ∨ oppCnt S d p = 1 ∨
      (oppCnt S d p = 3 ∧ 1 ≤ slack S d p) := by
  have sp := slackLe S d p
  have lp := priceSlack S h d p
  obtain ⟨h0, h1, h2⟩ := localLimits S h d p (ownZero S d p ho)
  rw [price, ownZero S d p ho] at lp
  omega

theorem balancedSize (S : Finset Box) (h : Covers S)
    (budget : sideSlack S false + sideSlack S true ≤ 6) (d : Bool)
    (tight : sideSlack S d = 3) (sizes : (stars S d).card = (stars S (!d)).card) :
    (stars S (!d)).card = 3 := by
  have upper (p : I) : oppCnt S d p + ownCnt S d p ≤ 1 + 2 * slack S d p := by
    by_cases hp : p ∈ stars S d
    · rw [ownNoOpp S h budget d p hp, ownOne S d p hp]
      omega
    · have := balancedDegree S h d p tight hp
      rw [ownZero S d p hp]
      omega
  have up := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun p _ => upper p)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul, mul_one, sumOwnCnt, sumOppCnt] at up
  rw [show (∑ p : I, slack S d p) = sideSlack S d from rfl] at up
  by_contra! ne
  have small : (stars S (!d)).card ≤ 2 := by omega
  have lower (p : I) : 3 ≤ 3 * oppCnt S d p + 3 * ownCnt S d p + slack S d p := by
    by_cases hp : p ∈ stars S d
    · rw [ownOne S d p hp]
      omega
    · have := balancedDegree S h d p tight hp
      omega
  have lo := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun p _ => lower p)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul, sumOwnCnt, sumOppCnt] at lo
  rw [show (∑ p : I, slack S d p) = sideSlack S d from rfl] at lo
  have two : (stars S (!d)).card = 2 := by omega
  obtain ⟨a, b, hab, eq⟩ := Finset.card_eq_two.mp two
  obtain ⟨p, hpa, hpb⟩ := commonNeighbor a b
  have ha : a ∈ stars S (!d) := by simp [eq]
  have hb : b ∈ stars S (!d) := by simp [eq]
  have atLeast := oppTwo S d p a b ha hb hab hpa hpb
  have atMost := oppLe S d p
  by_cases hp : p ∈ stars S d
  · have := ownNoOpp S h budget d p hp
    omega
  · have := balancedDegree S h d p tight hp
    omega

def degree (p a b c : I) : Nat :=
  (if cell p a then 1 else 0) + (if cell p b then 1 else 0) + (if cell p c then 1 else 0)

def blockedTriple (a b c : I) : Prop :=
  (∀ p : I, degree p a b c = 0 → p = a ∨ p = b ∨ p = c) ∧
  (∀ k : Box, 30 ≤ k.val → (triTouches false k a || triTouches false k b ||
    triTouches false k c || triTouches true k a || triTouches true k b || triTouches true k c) = true)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem tripleGeometry (a : I) : ∀ b c : I, a ≠ b → a ≠ c → b ≠ c →
    (∀ p : I, degree p a b c ≠ 2) → blockedTriple a b c := by
  fin_cases a <;> unfold blockedTriple <;> decide +kernel

theorem tripleDegree (S : Finset Box) (p a b c : I) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (eq : stars S true = {a, b, c}) : oppCnt S false p = degree p a b c := by
  unfold oppCnt degree
  simp only [Bool.not_false, eq]
  rw [Finset.card_filter]
  have ha : a ∉ ({b, c} : Finset I) := by simp [hab, hac]
  have hb : b ∉ ({c} : Finset I) := by simpa using hbc
  rw [Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_singleton]
  exact (Nat.add_assoc _ _ _).symm

theorem balancedImpossible (S : Finset Box) (h : Covers S) (small : S.card = 13)
    (budget : sideSlack S false + sideSlack S true ≤ 6) (tight : sideSlack S false = 3)
    (sizes : (stars S false).card = (stars S true).card) : False := by
  have size := balancedSize S h budget false tight sizes
  simp only [Bool.not_false] at size
  obtain ⟨a, b, c, hab, hac, hbc, eq⟩ := Finset.card_eq_three.mp size
  have deg := fun p => tripleDegree S p a b c hab hac hbc eq
  have notTwo (p : I) : degree p a b c ≠ 2 := by
    rw [← deg p]
    by_cases hp : p ∈ stars S false
    · rw [ownNoOpp S h budget false p hp]
      decide
    · have := balancedDegree S h false p tight hp
      omega
  obtain ⟨zeros, block⟩ := tripleGeometry a b c hab hac hbc notTwo
  have subset : stars S false ⊆ stars S true := by
    intro p hp
    have hz := zeros p ((deg p).symm.trans (ownNoOpp S h budget false p hp))
    simpa [eq] using hz
  have equal := Finset.eq_of_subset_of_card_le subset (Nat.le_of_eq sizes.symm)
  have parts := cardParts S
  have pos : 0 < (tris S).card := by omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp pos
  have htri := (Finset.mem_filter.mp hk).2
  have hit := block k htri
  have memA : a ∈ stars S true := by simp [eq]
  have memB : b ∈ stars S true := by simp [eq]
  have memC : c ∈ stars S true := by simp [eq]
  have noHit (d : Bool) (p : I) (hp : p ∈ stars S true) : triTouches d k p = false := by
    cases ht : triTouches d k p
    · rfl
    · have hposs : p ∈ stars S d := by cases d <;> simpa [equal] using hp
      have hz := ownNoTri S h budget d p hposs
      have hp' : 0 < triCnt S d p := Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, ht⟩⟩
      omega
  simp [noHit false a memA, noHit false b memB, noHit false c memC,
    noHit true a memA, noHit true b memB, noHit true c memC] at hit

theorem noSmall (S : Finset Box) (small : S.card ≤ 13) (h : Covers S) : False := by
  have l := slackTotal S h false
  have r := slackTotal S h true
  simp only [Bool.not_false, Bool.not_true] at l r
  have n := cardParts S
  have exactSize : S.card = 13 := by omega
  have budget : sideSlack S false + sideSlack S true ≤ 6 := by omega
  have cases' : (stars S false).card = (stars S true).card ∨
      (stars S false).card = (stars S true).card + 1 ∨
      (stars S true).card = (stars S false).card + 1 := by omega
  rcases cases' with eq | eq | eq
  · exact balancedImpossible S h exactSize budget (by omega) eq
  · exact zeroSlackImpossible S h false (by omega) eq
  · exact zeroSlackImpossible S h true (by omega) eq

end PEqualNP.Outside.L_meta_9984

theorem PEqualNP.Outside.L_meta_9984 : ¬ (∃ L : List (Finset (Fin 15) × Finset (Fin 15)), L.length ≤ 13 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([32256, 29120, 19872, 11104, 5856, 28700, 19482, 10774, 5646, 16793, 8533, 4301, 2355, 1195, 615] : List ℕ).getD i.val 0).testBit j.val = true) ∧ ∀ (i : Fin 15) (j : Fin 15), (([32256, 29120, 19872, 11104, 5856, 28700, 19482, 10774, 5646, 16793, 8533, 4301, 2355, 1195, 615] : List ℕ).getD i.val 0).testBit j.val = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨l, len, clean, all⟩
  obtain ⟨S, hS, covers⟩ := PEqualNP.Outside.L_meta_9984.normalize l clean all
  exact PEqualNP.Outside.L_meta_9984.noSmall S (hS.trans len) covers
