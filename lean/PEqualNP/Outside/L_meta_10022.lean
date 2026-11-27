import Mathlib.Algebra.BigOperators.ModEq
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10022_aux

open scoped BigOperators

def rows : List Nat := [34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688]

def cell (i : Fin 25) (j : Fin 30) : Bool := (rows.getD i.val 0).testBit j.val

def entry (i : Fin 25) (j : Fin 30) : Nat := if cell i j then 1 else 0

def good (I : Finset (Fin 25)) (J : Finset (Fin 30)) : Prop :=
  ∀ i ∈ I, ∀ j ∈ J, cell i j = false

def degree {α β : Type} (I : Finset α) (E : α → β → Nat) (j : β) : Nat :=
  ∑ i ∈ I, E i j

theorem degree_sum {α β : Type} [Fintype β] (I : Finset α) (E : α → β → Nat)
    (p : Nat) (rowSize : ∀ i, (∑ j : β, E i j) = p) :
    (∑ j : β, degree I E j) = p * I.card := by
  unfold degree
  rw [Finset.sum_comm]
  simp [rowSize, Nat.mul_comm]

theorem degree_sq_expand {α β : Type} [Fintype β] (I : Finset α) (E : α → β → Nat) :
    (∑ j : β, degree I E j * degree I E j) =
      ∑ i ∈ I, ∑ k ∈ I, ∑ j : β, E i j * E k j := by
  simp only [degree, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem pair_sum {α : Type} [DecidableEq α] (I : Finset α) (a : Nat) :
    (∑ i ∈ I, ∑ k ∈ I, (1 + if i = k then a else 0)) = I.card * (I.card + a) := by
  calc
    (∑ i ∈ I, ∑ k ∈ I, (1 + if i = k then a else 0)) =
        ∑ _i ∈ I, (I.card + a) := by
      exact Finset.sum_congr rfl fun i hi => by
        simp [Finset.sum_add_distrib, Finset.sum_ite_eq, hi]
    _ = _ := by simp

theorem row_sizes : ∀ i : Fin 25, (∑ j : Fin 30, entry i j) = 6 := by decide +kernel

theorem col_sizes : ∀ j : Fin 30, (∑ i : Fin 25, entry i j) = 5 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem row_pairs : ∀ i k : Fin 25, (∑ j : Fin 30, entry i j * entry k j) =
    1 + if i = k then 5 else 0 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem col_pairs : ∀ j k : Fin 30, (∑ i : Fin 25, entry i j * entry i k) ≤
    1 + if j = k then 4 else 0 := by decide +kernel

theorem row_sq (I : Finset (Fin 25)) :
    (∑ j : Fin 30, degree I entry j * degree I entry j) = I.card * (I.card + 5) := by
  rw [degree_sq_expand]
  simp only [row_pairs]
  exact pair_sum I 5

theorem col_sq (J : Finset (Fin 30)) :
    (∑ i : Fin 25, degree J (Function.swap entry) i * degree J (Function.swap entry) i) ≤
      J.card * (J.card + 4) := by
  rw [degree_sq_expand, ← pair_sum J 4]
  exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => col_pairs j k

theorem bound_three (n : Nat) : 3*n ≤ n*n + (if 0 < n then 2 else 0) := by
  by_cases h : n ≤ 3
  · interval_cases n <;> decide
  · have hn : 3 ≤ n := by omega
    exact (Nat.mul_le_mul_right n hn).trans (Nat.le_add_right _ _)

theorem bound_five (n : Nat) : 5*n ≤ n*n + (if 0 < n then 6 else 0) := by
  by_cases h : n ≤ 5
  · interval_cases n <;> decide
  · have hn : 5 ≤ n := by omega
    exact (Nat.mul_le_mul_right n hn).trans (Nat.le_add_right _ _)

def positive {β : Type} [Fintype β] (d : β → Nat) : Finset β :=
  Finset.univ.filter fun j => 0 < d j

theorem sum_positive {β : Type} [Fintype β] (d : β → Nat) (p : Nat) :
    (∑ j : β, if 0 < d j then p else 0) = p * (positive d).card := by
  rw [← Finset.sum_filter]
  simp [positive, Nat.mul_comm]

theorem count_positive {β : Type} [DecidableEq β] [Fintype β]
    (d : β → Nat) (J : Finset β) (hzero : ∀ j ∈ J, d j = 0) :
    (positive d).card ≤ Fintype.card β - J.card := by
  have hDis : Disjoint (positive d) J := Finset.disjoint_left.mpr (by
    intro j ha hb
    have hp := (Finset.mem_filter.mp ha).2
    have hz := hzero j hb
    omega)
  have hh := Finset.card_le_univ (positive d ∪ J)
  rw [Finset.card_union_of_disjoint hDis] at hh
  omega

theorem count_moments {β : Type} [DecidableEq β] [Fintype β]
    (d : β → Nat) (J : Finset β) (hzero : ∀ j ∈ J, d j = 0)
    (total squares : Nat) (htotal : (∑ j : β, d j) = total)
    (hsq : (∑ j : β, d j * d j) ≤ squares) :
    3 * total ≤ squares + 2 * (Fintype.card β - J.card) ∧
    5 * total ≤ squares + 6 * (Fintype.card β - J.card) := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset β)) fun j _ => bound_three (d j)
  have hs' := Finset.sum_le_sum (s := (Finset.univ : Finset β)) fun j _ => bound_five (d j)
  rw [← Finset.mul_sum, htotal, Finset.sum_add_distrib, sum_positive] at hs hs'
  have h := count_positive d J hzero
  omega

theorem row_moments (I : Finset (Fin 25)) (J : Finset (Fin 30)) (h : good I J) :
    18*I.card ≤ I.card*(I.card+5)+2*(30-J.card) ∧
    30*I.card ≤ I.card*(I.card+5)+6*(30-J.card) := by
  have zero : ∀ j ∈ J, degree I entry j = 0 := by
    intro j hj
    exact Finset.sum_eq_zero fun i hi => by simp [entry, h i hi j hj]
  have result := count_moments (degree I entry) J zero _ _
    (degree_sum I entry 6 row_sizes) (le_of_eq (row_sq I))
  simpa only [← Nat.mul_assoc, Fintype.card_fin] using result

theorem col_moments (I : Finset (Fin 25)) (J : Finset (Fin 30)) (h : good I J) :
    15*J.card ≤ J.card*(J.card+4)+2*(25-I.card) ∧
    25*J.card ≤ J.card*(J.card+4)+6*(25-I.card) := by
  have zero : ∀ i ∈ I, degree J (Function.swap entry) i = 0 := by
    intro i hi
    exact Finset.sum_eq_zero fun j hj => by simp [Function.swap, entry, h i hi j hj]
  have result := count_moments (degree J (Function.swap entry)) I zero _ _
    (degree_sum J (Function.swap entry) 5 col_sizes) (col_sq J)
  simpa only [← Nat.mul_assoc, Fintype.card_fin] using result

-- The two moment inequalities on each side leave just two shapes to exclude.
theorem area_shapes : ∀ a : Fin 26, ∀ b : Fin 31,
    a.val ≤ 20 →
    18*a.val ≤ a.val*(a.val+5)+2*(30-b.val) →
    30*a.val ≤ a.val*(a.val+5)+6*(30-b.val) →
    15*b.val ≤ b.val*(b.val+4)+2*(25-a.val) →
    25*b.val ≤ b.val*(b.val+4)+6*(25-a.val) →
    54 < a.val*b.val → (a.val = 7 ∧ 8 ≤ b.val) ∨ (a.val = 8 ∧ b.val = 7) := by
  decide +kernel

def pointsOn (j : Fin 30) : Finset (Fin 25) :=
  Finset.univ.filter fun i => cell i j = true

theorem pointsOn_card : ∀ j : Fin 30, (pointsOn j).card = 5 := by decide +kernel

theorem rows_bound (I : Finset (Fin 25)) (J : Finset (Fin 30)) (h : good I J)
    (hj : J.Nonempty) : I.card ≤ 20 := by
  obtain ⟨j,hj⟩ := hj
  have hd : Disjoint I (pointsOn j) := Finset.disjoint_left.mpr (by
    intro i ha hb
    have hz := h i ha j hj
    have ht := (Finset.mem_filter.mp hb).2
    simp [hz] at ht)
  have hc := Finset.card_le_univ (I ∪ pointsOn j)
  rw [Finset.card_union_of_disjoint hd, pointsOn_card] at hc
  simp at hc
  omega

theorem remaining_shapes (I : Finset (Fin 25)) (J : Finset (Fin 30))
    (h : good I J) (area : 54 < I.card*J.card) :
    (I.card = 7 ∧ 8 ≤ J.card) ∨ (I.card = 8 ∧ J.card = 7) := by
  have hi : I.card < 26 := by have a := Finset.card_le_univ I; simp at a; omega
  have hj : J.card < 31 := by have a := Finset.card_le_univ J; simp at a; omega
  have he : J.Nonempty := Finset.card_pos.mp (by
    by_contra! hz
    have hzero : J.card = 0 := by omega
    simp [hzero] at area)
  exact area_shapes ⟨_,hi⟩ ⟨_,hj⟩ (rows_bound I J h he) (row_moments I J h).1 (row_moments I J h).2
    (col_moments I J h).1 (col_moments I J h).2 area

def lineOf (d : Fin 6) (k : Fin 5) : Fin 30 :=
  finProdFinEquiv (d,k)

theorem split_line_sum (f : Fin 30 → Nat) :
    (∑ d : Fin 6, ∑ k : Fin 5, f (lineOf d k)) = ∑ j : Fin 30, f j := by
  let F (p : Fin 6 × Fin 5) := f (lineOf p.1 p.2)
  calc
    _ = ∑ p : Fin 6 × Fin 5, F p := (Fintype.sum_prod_type F).symm
    _ = _ := Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl

theorem one_per_direction : ∀ (i : Fin 25) (d : Fin 6),
    (∑ k : Fin 5, entry i (lineOf d k)) = 1 := by decide +kernel

def axisDegree (I : Finset (Fin 25)) (d : Fin 6) (k : Fin 5) :=
  degree I entry (lineOf d k)

def supportCount (I : Finset (Fin 25)) (d : Fin 6) : Nat :=
  (positive (axisDegree I d)).card

def squareCount (I : Finset (Fin 25)) (d : Fin 6) : Nat :=
  ∑ k : Fin 5, axisDegree I d k * axisDegree I d k

def oddLines (I : Finset (Fin 25)) (d : Fin 6) : Finset (Fin 5) :=
  Finset.univ.filter fun k => axisDegree I d k % 2 = 1

theorem sum_axis (I : Finset (Fin 25)) (d : Fin 6) :
    (∑ k : Fin 5, axisDegree I d k) = I.card := by
  exact (degree_sum I (fun i k => entry i (lineOf d k)) 1 (fun i => one_per_direction i d)).trans
    (Nat.one_mul _)

theorem sum_axis_squares (I : Finset (Fin 25)) :
    (∑ d : Fin 6, squareCount I d) = I.card*(I.card+5) := by
  unfold squareCount axisDegree
  rw [split_line_sum (fun j => degree I entry j * degree I entry j), row_sq]

theorem sum_axis_support (I : Finset (Fin 25)) :
    (∑ d : Fin 6, supportCount I d) = (positive (degree I entry)).card := by
  simp only [supportCount, positive]
  calc
    _ = ∑ d : Fin 6, ∑ k : Fin 5, if 0 < degree I entry (lineOf d k) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.card_filter _ _
    _ = _ := by
      rw [split_line_sum (fun j => if 0 < degree I entry j then 1 else 0)]
      exact (Finset.card_filter _ _).symm

theorem support_bound (I : Finset (Fin 25)) (J : Finset (Fin 30)) (h : good I J) :
    (∑ d : Fin 6, supportCount I d) ≤ 30-J.card := by
  rw [sum_axis_support]
  exact count_positive (degree I entry) J (fun j hj =>
    Finset.sum_eq_zero fun i hi => by simp [entry, h i hi j hj])

theorem quad_four (n : Nat) : 4*n ≤ n*n + (if 0 < n then 4 else 0) ∧
    (n % 2 = 1 → 4*n < n*n + (if 0 < n then 4 else 0)) := by
  by_cases h : n ≤ 4
  · interval_cases n <;> decide
  · have hn : 4 ≤ n := by omega
    have hquad := Nat.mul_le_mul_right n hn
    simp only [show 0 < n by omega, ite_true]
    omega

theorem odd_axis (I : Finset (Fin 25)) (hi : I.card = 7) (d : Fin 6) :
    ∃ k : Fin 5, axisDegree I d k % 2 = 1 := by
  by_contra! h
  have even : 2 ∣ ∑ k : Fin 5, axisDegree I d k := by
    apply Finset.dvd_sum
    intro k _
    have hk := h k
    omega
  rw [sum_axis, hi] at even
  omega

theorem seven_axis_bound (I : Finset (Fin 25)) (hi : I.card = 7) (d : Fin 6) :
    29 ≤ squareCount I d + 4 * supportCount I d := by
  obtain ⟨k,hk⟩ := odd_axis I hi d
  have ht := Finset.sum_lt_sum
    (fun (j : Fin 5) (_ : j ∈ Finset.univ) => (quad_four (axisDegree I d j)).1)
    ⟨k, Finset.mem_univ _, (quad_four (axisDegree I d k)).2 hk⟩
  rw [← Finset.mul_sum, sum_axis, hi, Finset.sum_add_distrib, sum_positive] at ht
  change 4*7 < squareCount I d + 4 * supportCount I d at ht
  omega

-- Every direction has at least one odd intersection with seven points.
theorem seven_rows (I : Finset (Fin 25)) (J : Finset (Fin 30)) (h : good I J) (hi : I.card = 7) :
    J.card ≤ 7 := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 6))) fun d _ => seven_axis_bound I hi d
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_axis_squares, hi] at hh
  simp at hh
  have hm := support_bound I J h
  omega

abbrev smallShape (m q o : Nat) : Prop :=
  40 + (if m = 3 ∨ m = 4 then 0 else 4) ≤ q + 6*m ∧
  (m = 3 → q ≤ 24 → (q = 22 ∧ o = 2) ∨ (q = 24 ∧ o = 0)) ∧
  (m = 4 → q ≤ 18 → (q = 16 ∧ o = 0) ∨ (q = 18 ∧ o = 2))

abbrev tupleShape (a b c d e : Nat) : Prop :=
  let L := [a,b,c,d,e]
  smallShape ((L.map fun n => if 0 < n then 1 else 0).sum)
    ((L.map fun n => n*n).sum) ((L.map fun n => if n % 2 = 1 then 1 else 0).sum)

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem tuple_check (a : Fin 9) : ∀ b c d : Fin 9, a.val+b.val+c.val+d.val ≤ 8 →
    tupleShape a.val b.val c.val d.val (8-(a.val+b.val+c.val+d.val)) := by
  fin_cases a <;> decide +kernel

set_option maxHeartbeats 4000000 in
theorem eight_axis (I : Finset (Fin 25)) (hi : I.card = 8) (d : Fin 6) :
    smallShape (supportCount I d) (squareCount I d) (oddLines I d).card := by
  let x := axisDegree I d
  have he : x 0 + x 1 + x 2 + x 3 + x 4 = 8 := by
    have h := (sum_axis I d).trans hi
    rwa [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_one, ← Nat.add_assoc, ← Nat.add_assoc, ← Nat.add_assoc] at h
  have a : x 0 < 9 := by omega
  have b : x 1 < 9 := by omega
  have c : x 2 < 9 := by omega
  have w : x 3 < 9 := by omega
  have hx : x 0+x 1+x 2+x 3 ≤ 8 := by omega
  have h := tuple_check ⟨x 0,a⟩ ⟨x 1,b⟩ ⟨x 2,c⟩ ⟨x 3,w⟩ hx
  change tupleShape (x 0) (x 1) (x 2) (x 3) (8-(x 0+x 1+x 2+x 3)) at h
  rw [show 8-(x 0+x 1+x 2+x 3) = x 4 by omega] at h
  unfold tupleShape at h
  unfold supportCount positive squareCount oddLines
  have h₁ : (0 : Fin 4).succ = (1 : Fin 5) := by decide
  have h₂ : (0 : Fin 3).succ.succ = (2 : Fin 5) := by decide
  have h₃ : (0 : Fin 2).succ.succ.succ = (3 : Fin 5) := by decide
  have h₄ : (0 : Fin 1).succ.succ.succ.succ = (4 : Fin 5) := by decide
  simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero, h₁, h₂, h₃, h₄]
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, x] using h

-- The square sum forces exactly one direction with three occupied lines and one direction with two units of slack.
theorem eight_pattern (I : Finset (Fin 25)) (J : Finset (Fin 30))
    (goodRect : good I J) (hi : I.card = 8) (hj : J.card = 7) :
    (∀ d, (oddLines I d).card = 0) ∨
      ∃ d e : Fin 6, d ≠ e ∧ (oddLines I d).card = 2 ∧ (oddLines I e).card = 2 ∧
        ∀ a, a ≠ d → a ≠ e → (oddLines I a).card = 0 := by
  let m := supportCount I
  let q := squareCount I
  let v (d : Fin 6) := q d + 6*m d
  have hbase (d : Fin 6) : 40 ≤ v d := by
    have h := (eight_axis I hi d).1
    change _ ≤ v d at h
    omega
  have hd (d : Fin 6) : m d = 3 ∨ m d = 4 := by
    by_contra! bad
    have hbig : 44 ≤ v d := by
      have h := (eight_axis I hi d).1
      change 40 + (if m d = 3 ∨ m d = 4 then 0 else 4) ≤ v d at h
      simpa [bad.1, bad.2] using h
    have hex (k : Fin 6) : 40 + (if k = d then 4 else 0) ≤ v k := by
      by_cases hk : k = d
      · simpa [hk] using hbig
      · simpa [hk] using hbase k
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 6))) fun k _ => hex k
    unfold v at hs
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_axis_squares, hi] at hs
    simp [Finset.sum_ite_eq'] at hs
    have hm := support_bound I J goodRect
    change (∑ d : Fin 6, m d) ≤ 30 - J.card at hm
    rw [hj] at hm
    omega
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 6))) fun k _ => hbase k
  unfold v at hs
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_axis_squares, hi] at hs
  simp at hs
  have hm := support_bound I J goodRect
  change (∑ d : Fin 6, m d) ≤ 30 - J.card at hm
  rw [hj] at hm
  have hm' : (∑ k : Fin 6, m k) = 23 := by omega
  let A : Finset (Fin 6) := Finset.univ.filter fun d => m d = 3
  have hA : A.card = 1 := by
    have eq (d : Fin 6) : m d + (if m d = 3 then 1 else 0) = 4 := by
      rcases hd d with h | h <;> simp [h]
    have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 6))) rfl fun d _ => eq d
    rw [Finset.sum_add_distrib, hm', ← Finset.sum_filter] at h
    change 23 + (∑ _d ∈ A, (1 : Nat)) = _ at h
    simp at h
    omega
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hA
  have ma : m a = 3 := by
    have h : a ∈ A := by simp [ha]
    exact (Finset.mem_filter.mp h).2
  have mother (d : Fin 6) (h : d ≠ a) : m d = 4 := by
    rcases hd d with hd | hd
    · exfalso
      have he : d ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd⟩
      simp [ha,h] at he
    · exact hd
  let extra (d : Fin 6) := v d - 40
  have he (d : Fin 6) : extra d + 40 = v d := Nat.sub_add_cancel (hbase d)
  have eq : (∑ d : Fin 6, extra d) = 2 := by
    have hx := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 6))) rfl fun d _ => he d
    unfold v at hx
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_axis_squares, hi,
      hm'] at hx
    simp at hx
    omega
  have heb (d : Fin 6) : extra d ≤ 2 := by
    rw [← eq]
    exact Finset.single_le_sum (fun d _ => Nat.zero_le (extra d)) (Finset.mem_univ d)
  have hqa : (q a = 22 ∧ (oddLines I a).card = 2) ∨
      (q a = 24 ∧ (oddLines I a).card = 0) := by
    apply (eight_axis I hi a).2.1 ma
    change q a ≤ 24
    have h₁ := he a
    have h₂ := heb a
    change extra a + 40 = q a + 6*m a at h₁
    omega
  have hqb (d : Fin 6) (h : d ≠ a) : (q d = 16 ∧ (oddLines I d).card = 0) ∨
      (q d = 18 ∧ (oddLines I d).card = 2) := by
    apply (eight_axis I hi d).2.2 (mother d h)
    change q d ≤ 18
    have h₁ := he d
    have h₂ := heb d
    have h₃ := mother d h
    change extra d + 40 = q d + 6*m d at h₁
    omega
  have hex : ∃ d, 0 < extra d := by
    by_contra! bad
    have hz : (∑ d : Fin 6, extra d) = 0 := Finset.sum_eq_zero (fun d _ => by have h := bad d; omega)
    omega
  obtain ⟨b,hb⟩ := hex
  have hb' : extra b = 2 := by
    have hx := he b
    change extra b + 40 = q b + 6*m b at hx
    by_cases h : b = a
    · subst b
      omega
    · have hq := hqb b h
      have hm := mother b h
      omega
  have other (d : Fin 6) (h : d ≠ b) : extra d = 0 := by
    have hsub : ({d,b} : Finset (Fin 6)) ⊆ Finset.univ := Finset.subset_univ _
    have hsmall := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le (extra i))
    rw [eq] at hsmall
    simp only [Finset.sum_insert, Finset.mem_singleton, h, not_false_eq_true,
      Finset.sum_singleton, hb'] at hsmall
    omega
  by_cases h : b = a
  · left
    subst b
    intro d
    have hh := he d
    change extra d + 40 = q d + 6*m d at hh
    by_cases h : d = a
    · subst d
      omega
    · have hm := mother d h
      have hq := hqb d h
      have ho := other d h
      omega
  · right
    refine ⟨a,b,Ne.symm h,?_,?_,?_⟩
    · have hh := he a
      change extra a + 40 = q a + 6*m a at hh
      have ho := other a (Ne.symm h)
      omega
    · have hh := he b
      change extra b + 40 = q b + 6*m b at hh
      have hm := mother b h
      have hq := hqb b h
      omega
    · intro d h₁ h₂
      have hh := he d
      change extra d + 40 = q d + 6*m d at hh
      have hm := mother d h₁
      have hq := hqb d h₁
      have ho := other d h₂
      omega

def axisTally (I : Finset (Fin 25)) (d : Fin 6) (i : Fin 25) : Nat :=
  ∑ k ∈ oddLines I d, entry i (lineOf d k)

theorem point_intersections (I : Finset (Fin 25)) (i : Fin 25) :
    (∑ j : Fin 30, degree I entry j * entry i j) = I.card + (if i ∈ I then 5 else 0) := by
  simp only [degree, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [row_pairs, Finset.sum_add_distrib, Finset.sum_ite_eq']

-- For an even point set, the odd lines recover membership by taking parity through each point.
theorem point_parity (I : Finset (Fin 25)) (hi : I.card = 8) (i : Fin 25) :
    (∑ d : Fin 6, axisTally I d i) % 2 = if i ∈ I then 1 else 0 := by
  have hs : (∑ d : Fin 6, axisTally I d i) =
      ∑ j : Fin 30, (degree I entry j % 2) * entry i j := by
    rw [← split_line_sum (fun j => (degree I entry j % 2) * entry i j)]
    apply Finset.sum_congr rfl
    intro d _
    unfold axisTally oddLines
    rw [Finset.sum_filter]
    unfold axisDegree
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : degree I entry (lineOf d k) % 2 = 1
    · simp [h]
    · have hz : degree I entry (lineOf d k) % 2 = 0 := by omega
      simp [hz]
  rw [hs]
  have hmod : Nat.ModEq 2 (∑ j : Fin 30, (degree I entry j % 2) * entry i j)
      (∑ j : Fin 30, degree I entry j * entry i j) :=
    Nat.ModEq.sum (fun j _ => (Nat.mod_modEq _ _).mul (Nat.ModEq.refl _))
  unfold Nat.ModEq at hmod
  rw [point_intersections, hi] at hmod
  rw [hmod]
  split <;> decide

def doubleLine (d : Fin 6) (a b : Fin 5) : Finset (Fin 25) :=
  pointsOn (lineOf d a) ∪ pointsOn (lineOf d b)

set_option maxRecDepth 10000 in
theorem parallel_disjoint : ∀ d : Fin 6, ∀ a b : Fin 5, a ≠ b →
    Disjoint (pointsOn (lineOf d a)) (pointsOn (lineOf d b)) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem cross_intersection (d : Fin 6) : ∀ e : Fin 6, d ≠ e → ∀ a b : Fin 5,
    (pointsOn (lineOf d a) ∩ pointsOn (lineOf e b)).card = 1 := by
  fin_cases d <;> decide +kernel

theorem double_card (d : Fin 6) (a b : Fin 5) (h : a ≠ b) : (doubleLine d a b).card = 10 := by
  rw [doubleLine, Finset.card_union_of_disjoint (parallel_disjoint d a b h), pointsOn_card, pointsOn_card]

theorem double_inter (d e : Fin 6) (hde : d ≠ e) (a b c f : Fin 5) (hab : a ≠ b) (hcf : c ≠ f) :
    (doubleLine d a b ∩ doubleLine e c f).card = 4 := by
  have hx (k : Fin 5) : (doubleLine d a b ∩ pointsOn (lineOf e k)).card = 2 := by
    rw [doubleLine, Finset.union_inter_distrib_right,
      Finset.card_union_of_disjoint ((parallel_disjoint d a b hab).mono
        Finset.inter_subset_left Finset.inter_subset_left),
      cross_intersection d e hde, cross_intersection d e hde]
  change (doubleLine d a b ∩ (pointsOn (lineOf e c) ∪ pointsOn (lineOf e f))).card = 4
  rw [Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint ((parallel_disjoint e c f hcf).mono
      Finset.inter_subset_right Finset.inter_subset_right), hx, hx]

theorem difference_total {A B : Finset (Fin 25)} (hA : A.card = 10) (hB : B.card = 10)
    (hI : (A ∩ B).card = 4) : ((A \ B) ∪ (B \ A)).card = 12 := by
  have ha : A \ B = A \ (A ∩ B) := by ext i; simp
  have hb : B \ A = B \ (A ∩ B) := by ext i; simp
  have hd : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro i ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  rw [Finset.card_union_of_disjoint hd, ha, hb,
    Finset.card_sdiff_of_subset Finset.inter_subset_left,
    Finset.card_sdiff_of_subset Finset.inter_subset_right, hA, hB, hI]

theorem axis_tally_pair (I : Finset (Fin 25)) (d : Fin 6) (a b : Fin 5) (hab : a ≠ b)
    (h : oddLines I d = {a,b}) (i : Fin 25) :
    axisTally I d i = if i ∈ doubleLine d a b then 1 else 0 := by
  rw [axisTally, h, Finset.sum_insert (by simpa using hab), Finset.sum_singleton]
  have hd := parallel_disjoint d a b hab
  have hbad : ¬ (cell i (lineOf d a) = true ∧ cell i (lineOf d b) = true) := by
    rintro ⟨ha,hb⟩
    exact (Finset.disjoint_left.mp hd)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
  cases ha : cell i (lineOf d a) <;> cases hb : cell i (lineOf d b) <;>
    simp_all [entry, doubleLine, pointsOn, Finset.mem_filter]

theorem eight_rows_impossible (I : Finset (Fin 25)) (J : Finset (Fin 30))
    (h : good I J) (hi : I.card = 8) (hj : J.card = 7) : False := by
  rcases eight_pattern I J h hi hj with hn | ⟨d,e,hde,hd,he,ho⟩
  · have hzero (i : Fin 25) (d : Fin 6) : axisTally I d i = 0 := by
      simp [axisTally, Finset.card_eq_zero.mp (hn d)]
    obtain ⟨i,hi'⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
    have he := point_parity I hi i
    simp [hzero,hi'] at he
  · obtain ⟨a,b,hab,hA⟩ := Finset.card_eq_two.mp hd
    obtain ⟨c,f,hcf,hB⟩ := Finset.card_eq_two.mp he
    let A := doubleLine d a b
    let B := doubleLine e c f
    have hcard : ((A \ B) ∪ (B \ A)).card = 12 := difference_total
      (double_card d a b hab) (double_card e c f hcf) (double_inter d e hde a b c f hab hcf)
    have hsum (i : Fin 25) : (∑ j : Fin 6, axisTally I j i) =
        axisTally I d i + axisTally I e i := by
      calc
        _ = ∑ j ∈ ({d,e} : Finset (Fin 6)), axisTally I j i := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          have hn : j ≠ d ∧ j ≠ e := by simpa [not_or] using hj
          simp [axisTally, Finset.card_eq_zero.mp (ho j hn.1 hn.2)]
        _ = _ := by simp [Finset.sum_insert, hde]
    have hEq : I = (A \ B) ∪ (B \ A) := by
      ext i
      have hh := point_parity I hi i
      rw [hsum, axis_tally_pair I d a b hab hA, axis_tally_pair I e c f hcf hB] at hh
      change ((if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0)) % 2 =
        (if i ∈ I then 1 else 0) at hh
      by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> by_cases hi : i ∈ I <;>
        simp_all
    rw [← hEq,hi] at hcard
    omega

theorem rectangle_area (I : Finset (Fin 25)) (J : Finset (Fin 30)) (h : good I J) :
    I.card*J.card ≤ 54 := by
  by_contra! bad
  rcases remaining_shapes I J h bad with ⟨hi,hj⟩ | ⟨hi,hj⟩
  · have h' := seven_rows I J h hi
    omega
  · exact eight_rows_impossible I J h hi hj

abbrev Rect := Finset (Fin 25) × Finset (Fin 30)

def zeros : Finset (Fin 25 × Fin 30) := Finset.univ.filter fun p => cell p.1 p.2 = false

theorem zeros_size : zeros.card = 600 := by decide +kernel

def tiles : List Rect → Finset (Fin 25 × Fin 30)
  | [] => ∅
  | r :: rest => (r.1 ×ˢ r.2) ∪ tiles rest

theorem mem_tiles (p : Fin 25 × Fin 30) (L : List Rect) :
    p ∈ tiles L ↔ ∃ r ∈ L, p.1 ∈ r.1 ∧ p.2 ∈ r.2 := by
  induction L with
  | nil => simp [tiles]
  | cons r rest ih => simp [tiles, ih]

theorem tiles_bound (L : List Rect) (h : ∀ r ∈ L, good r.1 r.2) :
    (tiles L).card ≤ 54*L.length := by
  induction L with
  | nil => simp [tiles]
  | cons r rest ih =>
    have hr := rectangle_area r.1 r.2 (h r (by simp))
    have hs := ih (fun s hs => h s (by simp [hs]))
    have hu : (tiles (r :: rest)).card ≤ (r.1 ×ˢ r.2).card + (tiles rest).card :=
      Finset.card_union_le _ _
    rw [Finset.card_product] at hu
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

-- Eleven rectangles of area at most fifty-four cannot cover six hundred zero entries.
theorem no_eleven : ¬ ∃ L : List Rect, L.length ≤ 11 ∧
    (∀ r ∈ L, good r.1 r.2) ∧
    ∀ i j, cell i j = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  rintro ⟨L,hlen,hgood,hcover⟩
  have hs : zeros ⊆ tiles L := by
    intro ⟨i,j⟩ h
    exact (mem_tiles (i,j) L).mpr (hcover i j (Finset.mem_filter.mp h).2)
  have hl := Finset.card_le_card hs
  rw [zeros_size] at hl
  have hu := tiles_bound L hgood
  omega

end PEqualNP.Outside.L_meta_10022_aux

theorem PEqualNP.Outside.L_meta_10022 :
    ¬ (∃ L : List (Finset (Fin 25) × Finset (Fin 30)), L.length ≤ 11 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 25) (j : Fin 30), (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) :=
  PEqualNP.Outside.L_meta_10022_aux.no_eleven
