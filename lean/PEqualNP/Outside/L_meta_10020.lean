import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10020

open scoped BigOperators

def hits {α β : Type} (R : α → β → Bool) (S : Finset α) (j : β) : ℕ :=
  ∑ i ∈ S, (R i j).toNat

lemma firstMoment {α β : Type} (R : α → β → Bool) (S : Finset α) (U : Finset β)
    (d : ℕ) (degree : ∀ i ∈ S, ∑ j ∈ U, (R i j).toNat = d) :
    ∑ j ∈ U, hits R S j = S.card * d := by
  unfold hits
  rw [Finset.sum_comm]
  simpa using Finset.sum_congr (rfl : S = S) degree

lemma secondMoment {α β : Type} [DecidableEq α] (R : α → β → Bool)
    (S : Finset α) (U : Finset β) (d : ℕ)
    (degree : ∀ i ∈ S, ∑ j ∈ U, (R i j).toNat = d)
    (pairs : ∀ i ∈ S, ∀ k ∈ S, i ≠ k →
      ∑ j ∈ U, (R i j).toNat * (R k j).toNat ≤ 1) :
    ∑ j ∈ U, (hits R S j)^2 ≤ S.card * (d + S.card - 1) := by
  simp only [hits, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  have aux (i : α) (hi : i ∈ S) :
      ∑ j ∈ U, ∑ k ∈ S, (R i j).toNat * (R k j).toNat ≤ d + S.card - 1 := by
    rw [Finset.sum_comm, ← Finset.sum_erase_add _ _ hi]
    have hd : (∑ j ∈ U, (R i j).toNat * (R i j).toNat) = d := by
      rw [← degree i hi]
      apply Finset.sum_congr rfl
      intro j _
      cases R i j <;> rfl
    rw [hd]
    have rest : ∑ k ∈ S.erase i, ∑ j ∈ U, (R i j).toNat * (R k j).toNat ≤
        ∑ _k ∈ S.erase i, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact pairs i hi k (Finset.mem_of_mem_erase hk) (Ne.symm (Finset.ne_of_mem_erase hk))
    have hcard := Finset.card_erase_of_mem hi
    have rest' : (∑ k ∈ S.erase i, ∑ j ∈ U, (R i j).toNat * (R k j).toNat) ≤ (S.erase i).card := by
      simpa using rest
    rw [hcard] at rest'
    have hpos := Finset.card_pos.mpr ⟨i,hi⟩
    omega
  calc
    _ ≤ ∑ i ∈ S, (d + S.card - 1) := Finset.sum_le_sum aux
    _ = _ := by simp [Nat.mul_comm]

lemma hitsZero {α β : Type} (R : α → β → Bool) (S : Finset α) (j : β)
    (zero : ∀ i ∈ S, R i j = false) : hits R S j = 0 := by
  unfold hits
  apply Finset.sum_eq_zero
  intro i hi
  simp [zero i hi]

lemma restrictedMoments {α β : Type} [DecidableEq α] [Fintype β] [DecidableEq β]
    (R : α → β → Bool) (S : Finset α) (B : Finset β) (d : ℕ)
    (degree : ∀ i ∈ S, ∑ j, (R i j).toNat = d)
    (pairs : ∀ i ∈ S, ∀ k ∈ S, i ≠ k →
      ∑ j, (R i j).toNat * (R k j).toNat ≤ 1)
    (zero : ∀ i ∈ S, ∀ j ∈ B, R i j = false) :
    (∑ j ∈ Finset.univ \ B, hits R S j) = S.card * d ∧
    (∑ j ∈ Finset.univ \ B, (hits R S j)^2) ≤ S.card * (d + S.card - 1) := by
  have h1 := firstMoment R S Finset.univ d degree
  have h2 := secondMoment R S Finset.univ d degree pairs
  have hz (j : β) (hj : j ∈ B) : hits R S j = 0 := hitsZero R S j (fun i hi => zero i hi j hj)
  have z1 : ∑ j ∈ B, hits R S j = 0 := Finset.sum_eq_zero hz
  have z2 : ∑ j ∈ B, (hits R S j)^2 = 0 := Finset.sum_eq_zero (fun j hj => by simp [hz j hj])
  rw [← Finset.sum_sdiff (Finset.subset_univ B), z1, add_zero] at h1
  rw [← Finset.sum_sdiff (Finset.subset_univ B), z2, add_zero] at h2
  exact ⟨h1,h2⟩

lemma momentInequality {β : Type} (U : Finset β) (g : β → ℕ) (t : ℕ)
    (step : ∀ j ∈ U, (2*t+1) * g j ≤ (g j)^2 + t*(t+1)) :
    (2*t+1) * (∑ j ∈ U, g j) ≤ (∑ j ∈ U, (g j)^2) + U.card * (t*(t+1)) := by
  have h := Finset.sum_le_sum step
  simpa [Finset.mul_sum, Finset.sum_add_distrib, nsmul_eq_mul] using h


def rowBits : List ℕ :=
  [34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852,
   83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192,
   276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098,
   539017476, 541132296, 545392688]

def entry (i : Fin 25) (j : Fin 30) : Bool := (rowBits.getD i.val 0).testBit j.val

abbrev isZero (i : Fin 25) (j : Fin 30) : Prop := entry i j = false

lemma rowDegree : ∀ i, ∑ j, (entry i j).toNat = 6 := by decide +kernel

lemma colDegree : ∀ j, ∑ i, (entry i j).toNat = 5 := by decide +kernel

lemma rowPair : ∀ i k : Fin 25, i ≠ k →
    (∑ j, (entry i j).toNat * (entry k j).toNat) ≤ 1 := by decide +kernel

lemma colPair : ∀ j l : Fin 30, j ≠ l →
    (∑ i, (entry i j).toNat * (entry i l).toNat) ≤ 1 := by decide +kernel

lemma hitsLeCard {α β : Type} (R : α → β → Bool) (A : Finset α) (j : β) :
    hits R A j ≤ A.card := by
  have h : ∑ i ∈ A, (R i j).toNat ≤ ∑ i ∈ A, (1 : ℕ) := by
    apply Finset.sum_le_sum
    intro i _
    cases R i j <;> decide
  simpa [hits] using h

def momentBound (a b d m : ℕ) (t : Fin 3) : Prop :=
  (2*(t.val+1)+1)*(a*d) ≤ a*(d+a-1) + (m-b)*((t.val+1)*(t.val+2))

lemma allBounds {α β : Type} [DecidableEq α] [DecidableEq β] [Fintype β]
    (R : α → β → Bool) (A : Finset α) (B : Finset β) (d : ℕ) (hA : A.card ≤ 30)
    (degree : ∀ i ∈ A, ∑ j, (R i j).toNat = d)
    (pairs : ∀ i ∈ A, ∀ k ∈ A, i ≠ k → ∑ j, (R i j).toNat * (R k j).toNat ≤ 1)
    (zero : ∀ i ∈ A, ∀ j ∈ B, R i j = false) :
    ∀ t, momentBound A.card B.card d (Fintype.card β) t := by
  obtain ⟨h1,h2⟩ := restrictedMoments R A B d degree pairs zero
  intro t
  have hs : ∀ j ∈ Finset.univ \ B,
      (2*(t.val+1)+1) * hits R A j ≤ (hits R A j)^2 + (t.val+1)*(t.val+1+1) := by
    intro j _
    have hj := (hitsLeCard R A j).trans hA
    generalize heq : hits R A j = k at hj ⊢
    fin_cases t <;> interval_cases k <;> decide
  have bound := momentInequality (Finset.univ \ B) (hits R A) (t.val+1) hs
  have count : (Finset.univ \ B).card = Fintype.card β - B.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B), Finset.card_univ]
  rw [h1,count] at bound
  unfold momentBound
  exact le_trans bound (Nat.add_le_add_right h2 _)

set_option maxRecDepth 30000 in
lemma onlyLarge : ∀ a : Fin 26, ∀ b : Fin 31,
    (∀ t, momentBound a.val b.val 6 30 t) →
    (∀ t, momentBound b.val a.val 5 25 t) →
    60 ≤ a.val * b.val → a.val = 7 ∧ b.val = 9 := by
  unfold momentBound
  decide +kernel

def firstDirection : Finset (Fin 30) := Finset.univ.filter (fun j => j.val < 5)

lemma firstDirectionDegree : ∀ i, ∑ j ∈ firstDirection, (entry i j).toNat = 1 := by
  decide +kernel

lemma area (A : Finset (Fin 25)) (B : Finset (Fin 30))
    (h : ∀ i ∈ A, ∀ j ∈ B, isZero i j) : A.card * B.card < 60 := by
  by_contra! big
  have ha : A.card ≤ 25 := by simpa using Finset.card_le_univ A
  have hb : B.card ≤ 30 := by simpa using Finset.card_le_univ B
  obtain ⟨a7,b9⟩ := onlyLarge (⟨A.card,by omega⟩ : Fin 26) (⟨B.card,by omega⟩ : Fin 31)
    (allBounds entry A B 6 (ha.trans (by decide)) (fun i _ => rowDegree i)
      (fun i _ k _ => rowPair i k) h)
    (allBounds (fun j i => entry i j) B A 5 hb (fun j _ => colDegree j)
      (fun j _ k _ => colPair j k) (fun j hj i hi => h i hi j hj)) big
  change A.card = 7 at a7
  change B.card = 9 at b9
  let U : Finset (Fin 30) := Finset.univ \ B
  have uCard : U.card = 21 := by
    simp [U, Finset.card_sdiff_of_subset (Finset.subset_univ B), b9]
  obtain ⟨h1,h2⟩ := restrictedMoments entry A B 6 (fun i _ => rowDegree i)
    (fun i _ k _ => rowPair i k) h
  change ∑ j ∈ U, hits entry A j = A.card * 6 at h1
  change ∑ j ∈ U, (hits entry A j)^2 ≤ A.card * (6 + A.card - 1) at h2
  rw [a7] at h1 h2
  have quad (j : Fin 30) : 4 * hits entry A j ≤ (hits entry A j)^2 + 4 := by
    have hj := (hitsLeCard entry A j).trans ha
    generalize he : hits entry A j = k at hj ⊢
    interval_cases k <;> decide
  have two (j : Fin 30) (hj : j ∈ U) : hits entry A j = 2 := by
    by_contra ne
    have strict : 4 * hits entry A j < (hits entry A j)^2 + 4 := by
      have hcap := (hitsLeCard entry A j).trans ha
      generalize he : hits entry A j = k at hcap ne ⊢
      interval_cases k <;> first | contradiction | decide
    have sumStrict := Finset.sum_lt_sum (fun i (_ : i ∈ U) => quad i) ⟨j,hj,strict⟩
    simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at sumStrict
    rw [← Finset.mul_sum,h1,uCard] at sumStrict
    omega
  have odd := firstMoment entry A firstDirection 1 (fun i _ => firstDirectionDegree i)
  have ev : ∀ j ∈ firstDirection, hits entry A j = 2 * (if j ∈ B then 0 else 1) := by
    intro j _
    by_cases hj : j ∈ B
    · simpa [hj] using hitsZero entry A j (fun i hi => h i hi j hj)
    · simp [hj, two j (by simp [U,hj])]
  have hsum := Finset.sum_congr (rfl : firstDirection = firstDirection) ev
  rw [← Finset.mul_sum,odd,a7] at hsum
  omega

def zeroCells : Finset (Fin 25 × Fin 30) :=
  Finset.univ.filter fun e => isZero e.1 e.2

lemma zeroCount : zeroCells.card = 600 := by decide +kernel

def coveredCells : List (Finset (Fin 25) × Finset (Fin 30)) → Finset (Fin 25 × Fin 30)
  | [] => ∅
  | r :: rs => r.1 ×ˢ r.2 ∪ coveredCells rs

lemma coverCount (L : List (Finset (Fin 25) × Finset (Fin 30)))
    (h : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, isZero i j) :
    (coveredCells L).card ≤ 59 * L.length := by
  induction L with
  | nil => simp [coveredCells]
  | cons r rs ih =>
    have hhead := area r.1 r.2 (h r (by simp))
    have htail := ih (fun q hq => h q (by simp [hq]))
    have bound := Finset.card_union_le (r.1 ×ˢ r.2) (coveredCells rs)
    simp only [coveredCells, List.length_cons, Nat.mul_succ]
    rw [Finset.card_product] at bound
    omega

lemma memCovered (L : List (Finset (Fin 25) × Finset (Fin 30)))
    (r : Finset (Fin 25) × Finset (Fin 30)) (hr : r ∈ L) (i : Fin 25) (j : Fin 30)
    (hi : i ∈ r.1) (hj : j ∈ r.2) : (i,j) ∈ coveredCells L := by
  induction L with
  | nil => simp at hr
  | cons s ss ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hi,hj⟩)
    · exact Finset.mem_union_right _ (ih hr)

end PEqualNP.Outside.L_meta_10020

open PEqualNP.Outside.L_meta_10020

theorem PEqualNP.Outside.L_meta_10020 : ¬ (∃ L : List (Finset (Fin 25) × Finset (Fin 30)), L.length ≤ 10 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 25) (j : Fin 30), (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L,hL,hzero,hcover⟩
  have subset : zeroCells ⊆ coveredCells L := by
    rintro ⟨i,j⟩ h
    have hz := (Finset.mem_filter.mp h).2
    obtain ⟨r,hr,hi,hj⟩ := hcover i j hz
    exact memCovered L r hr i j hi hj
  have hc := Finset.card_le_card subset
  rw [zeroCount] at hc
  have bound := coverCount L hzero
  omega


