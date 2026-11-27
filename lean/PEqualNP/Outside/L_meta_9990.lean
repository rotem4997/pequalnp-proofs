import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9990

open Finset

abbrev V := Fin 21
abbrev Point := Fin 7
abbrev Box := Finset V × Finset V

def rows : List Nat := [2095104,2066304,1865536,1273536,712128,375744,2064444,1863738,1271862,710702,374814,1836857,1246901,689581,361373,1074803,546155,275291,150759,76503,39375]
def entry (i j : V) := (rows.getD i.val 0).testBit j.val

-- Rows and columns index the unordered pairs of a seven-element set.
def pair : V → Finset Point := ![{0,1},{0,2},{0,3},{0,4},{0,5},{0,6},{1,2},{1,3},{1,4},{1,5},{1,6},{2,3},{2,4},{2,5},{2,6},{3,4},{3,5},{3,6},{4,5},{4,6},{5,6}]

theorem disjointEntry : ∀ i j : V, entry i j = true ↔ Disjoint (pair i) (pair j) := by decide +kernel

def side (s : Finset Point) : Finset V := univ.filter (fun i => pair i ⊆ s)
def other (s : Finset Point) : Finset V := univ.filter (fun i => Disjoint s (pair i))
def third (n : Nat) := (n+2)/3

-- The charge includes ordinary area and the rounded widths in both directions.
def charge (a b : Nat) := a*b + 3*(a*third b) + 3*(b*third a)

theorem localBound : ∀ s : Finset Point, charge (side s).card (other s).card ≤ 54 := by decide +kernel

def total {m : Nat} (A : Fin m → Finset V) (w : Fin m → Nat) (i : V) :=
  ∑ j, if i ∈ A j then w j else 0

theorem sumTotal {m : Nat} (A : Fin m → Finset V) (w : Fin m → Nat) :
    ∑ i, total A w i = ∑ j, (A j).card * w j := by
  unfold total
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp [sum_ite_mem]

theorem tenCovered {m : Nat} (A B : Fin m → Finset V) (N : V → Finset V)
    (deg : ∀ i, (N i).card = 10)
    (cov : ∀ i v, v ∈ N i → ∃ j, i ∈ A j ∧ v ∈ B j) (i : V) :
    10 ≤ total A (fun j => (B j).card) i := by
  let S := univ.filter (fun j => i ∈ A j)
  have h : N i ⊆ S.biUnion B := by
    intro v hv
    obtain ⟨j, hj, vj⟩ := cov i v hv
    exact mem_biUnion.mpr ⟨j, mem_filter.mpr ⟨mem_univ _,hj⟩, vj⟩
  calc
    10 = (N i).card := (deg i).symm
    _ ≤ (S.biUnion B).card := card_le_card h
    _ ≤ ∑ j ∈ S, (B j).card := card_biUnion_le
    _ = _ := by simp only [S, total, sum_filter]

theorem fourThirds {m : Nat} (A B : Fin m → Finset V) (i : V)
    (h : 10 ≤ total A (fun j => (B j).card) i) :
    4 ≤ total A (fun j => third (B j).card) i := by
  have lim : total A (fun j => (B j).card) i ≤ 3 * total A (fun j => third (B j).card) i := by
    unfold total
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    by_cases hj : i ∈ A j <;> simp [hj, third] <;> omega
  omega

theorem sumLower {m c : Nat} (A : Fin m → Finset V) (w : Fin m → Nat)
    (h : ∀ i, c ≤ total A w i) : 21*c ≤ ∑ j, (A j).card*w j := by
  calc
    21*c = ∑ _ : V, c := by simp
    _ ≤ ∑ i, total A w i := sum_le_sum fun i _ => h i
    _ = _ := sumTotal A w

theorem impossible (L : List Box) (size : L.length ≤ 13)
    (ok : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, entry i j = true)
    (cover : ∀ i j, entry i j = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) : False := by
  let s (k : Fin L.length) := (L.get k).1.biUnion pair
  let A := fun k => side (s k)
  let B := fun k => other (s k)
  have hits (i j : V) (h : entry i j = true) : ∃ k, i ∈ A k ∧ j ∈ B k := by
    obtain ⟨r, hr, hi, hj⟩ := cover i j h
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hr
    refine ⟨k, mem_filter.mpr ⟨mem_univ _, ?_⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    · intro z hz
      exact mem_biUnion.mpr ⟨i, hk ▸ hi, hz⟩
    · apply Finset.disjoint_left.mpr
      intro z hz hzj
      obtain ⟨u, hu, hzu⟩ := mem_biUnion.mp hz
      have dj := (disjointEntry u j).mp (ok r hr u (hk ▸ hu) j hj)
      exact Finset.disjoint_left.mp dj hzu hzj
  let N (i : V) := univ.filter (fun j => entry i j = true)
  let T (j : V) := univ.filter (fun i => entry i j = true)
  have d : ∀ i, (N i).card = 10 := by decide +kernel
  have e : ∀ i, (T i).card = 10 := by decide +kernel
  have h := tenCovered A B N d (fun i j h => hits i j (mem_filter.mp h).2)
  have t := tenCovered B A T e (by
    intro j i h
    obtain ⟨k, hi, hj⟩ := hits i j (mem_filter.mp h).2
    exact ⟨k, hj, hi⟩)
  have plain := sumLower A _ h
  have rowCost := sumLower A _ (fun i => fourThirds A B i (h i))
  have colCost := sumLower B _ (fun i => fourThirds B A i (t i))
  have upper : (∑ j, charge (A j).card (B j).card) ≤ 13*54 := calc
    _ ≤ ∑ _ : Fin L.length, 54 := sum_le_sum fun j _ => localBound (s j)
    _ = L.length*54 := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ size
  simp only [charge, sum_add_distrib, ← mul_sum] at upper
  omega

end PEqualNP.Outside.L_meta_9990


open PEqualNP.Outside.L_meta_9990 in
theorem PEqualNP.Outside.L_meta_9990 : ¬ (∃ L : List (Finset (Fin 21) × Finset (Fin 21)), L.length ≤ 13 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([2095104, 2066304, 1865536, 1273536, 712128, 375744, 2064444, 1863738, 1271862, 710702, 374814, 1836857, 1246901, 689581, 361373, 1074803, 546155, 275291, 150759, 76503, 39375] : List ℕ).getD i.val 0).testBit j.val = true) ∧ ∀ (i : Fin 21) (j : Fin 21), (([2095104, 2066304, 1865536, 1273536, 712128, 375744, 2064444, 1863738, 1271862, 710702, 374814, 1836857, 1246901, 689581, 361373, 1074803, 546155, 275291, 150759, 76503, 39375] : List ℕ).getD i.val 0).testBit j.val = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, size, ok, cov⟩
  exact impossible L size ok cov
