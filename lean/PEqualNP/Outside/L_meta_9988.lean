import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs

/- The 21 indices are the pairs of seven points. Extending an all-one rectangle
   to an oriented cut leaves only two possible large shapes, each with column
   width divisible by three. Counting widths in each row rules out twelve cuts. -/
namespace PEqualNP.Outside.L_meta_9988

-- The source matrix lists the two-point subsets of seven points in lexicographic order.
def f (i j : Fin 21) : Bool := (([2095104, 2066304, 1865536, 1273536, 712128, 375744, 2064444, 1863738, 1271862, 710702, 374814, 1836857, 1246901, 689581, 361373, 1074803, 546155, 275291, 150759, 76503, 39375] : List ℕ).getD i.val 0).testBit j.val

private def cutEndpoints (i : Fin 21) : Finset (Fin 7) :=
  (#[{0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {0,6}, {1,2}, {1,3}, {1,4}, {1,5}, {1,6}, {2,3}, {2,4}, {2,5}, {2,6}, {3,4}, {3,5}, {3,6}, {4,5}, {4,6}, {5,6}] : Array (Finset (Fin 7)))[i.val]?.getD ∅

private theorem matrix_disjoint : ∀ i j : Fin 21,
    f i j = true ↔ Disjoint (cutEndpoints i) (cutEndpoints j) := by decide +kernel

private def pointSet (c : Fin 128) : Finset (Fin 7) :=
  Finset.univ.filter fun v => c.val.testBit v.val = true

private def pointCode (S : Finset (Fin 7)) : Fin 128 :=
  Fin.ofNat 128 (∑ v ∈ S, 2 ^ v.val)

private theorem points_code : ∀ S : Finset (Fin 7), pointSet (pointCode S) = S := by decide +kernel

-- The normalized rectangle of a directed cut takes its row pairs on the chosen
-- side and its column pairs on the complementary side.
def rectOfCut (c : Fin 128) : Finset (Fin 21) × Finset (Fin 21) :=
  (Finset.univ.filter (fun i => cutEndpoints i ⊆ pointSet c),
   Finset.univ.filter (fun j => Disjoint (cutEndpoints j) (pointSet c)))

def normRect (r : Finset (Fin 21) × Finset (Fin 21)) : Finset (Fin 21) × Finset (Fin 21) :=
  rectOfCut (pointCode (r.1.biUnion cutEndpoints))

theorem inside (r : Finset (Fin 21) × Finset (Fin 21))
    (all : ∀ i ∈ r.1, ∀ j ∈ r.2, f i j = true) :
    r.1 ⊆ (normRect r).1 ∧ r.2 ⊆ (normRect r).2 := by
  constructor
  · intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [points_code]
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨i,hi,hv⟩
  · intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [points_code]
    apply Finset.disjoint_left.mpr
    intro v hv hrow
    obtain ⟨i,hi,hv'⟩ := Finset.mem_biUnion.mp hrow
    exact Finset.disjoint_left.mp ((matrix_disjoint i j).mp (all i hi j hj)) hv' hv

private def cutShape (c : Fin 128) : Prop :=
  (rectOfCut c).1.card * (rectOfCut c).2.card ≤ 10 ∨
    (rectOfCut c).1.card * (rectOfCut c).2.card ≤ 18 ∧ 3 ∣ (rectOfCut c).2.card

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem allCuts : ∀ c : Fin 128, cutShape c := by
  unfold cutShape
  decide +kernel

theorem shape (r : Finset (Fin 21) × Finset (Fin 21)) :
    (normRect r).1.card * (normRect r).2.card ≤ 10 ∨
    (normRect r).1.card * (normRect r).2.card ≤ 18 ∧ 3 ∣ (normRect r).2.card :=
  allCuts (pointCode (r.1.biUnion cutEndpoints))

theorem degree : ∀ i : Fin 21, (Finset.univ.filter (fun j => f i j = true)).card = 10 := by
  decide +kernel

abbrev Rect := Finset (Fin 21) × Finset (Fin 21)

theorem noTwelve (f : Fin 21 → Fin 21 → Bool)
    (degree : ∀ i, (Finset.univ.filter (fun j => f i j = true)).card = 10)
    (L : List Rect) (sz : L.length ≤ 12)
    (covered : ∀ i j, f i j = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2)
    (shape : ∀ r ∈ L, r.1.card * r.2.card ≤ 10 ∨
      (r.1.card * r.2.card ≤ 18 ∧ 3 ∣ r.2.card)) : False := by
  classical
  let S := L.toFinset
  let area (r : Rect) := r.1.card * r.2.card
  let width (i : Fin 21) (r : Rect) := if i ∈ r.1 then r.2.card else 0
  let load (i : Fin 21) := ∑ r ∈ S, width i r
  have count : S.card ≤ 12 := (List.toFinset_card_le L).trans sz
  have shapeS (r : Rect) (hr : r ∈ S) : area r ≤ 10 ∨ (area r ≤ 18 ∧ 3 ∣ r.2.card) :=
    shape r (List.mem_toFinset.mp hr)
  have ten (i : Fin 21) : 10 ≤ load i := by
    let part (r : Rect) : Finset (Fin 21) := if i ∈ r.1 then r.2 else ∅
    have incl : (Finset.univ.filter (fun j => f i j = true)) ⊆ S.biUnion part := by
      intro j hj
      obtain ⟨r,hr,hi,hj'⟩ := covered i j (Finset.mem_filter.mp hj).2
      exact Finset.mem_biUnion.mpr ⟨r,List.mem_toFinset.mpr hr,by simpa [part,hi] using hj'⟩
    calc
      10 = (Finset.univ.filter (fun j => f i j = true)).card := (degree i).symm
      _ ≤ (S.biUnion part).card := Finset.card_le_card incl
      _ ≤ ∑ r ∈ S, (part r).card := Finset.card_biUnion_le
      _ = load i := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases h : i ∈ r.1 <;> simp [part,width,h]
  have total : (∑ i : Fin 21, load i) = ∑ r ∈ S, area r := by
    change (∑ i : Fin 21, ∑ r ∈ S, width i r) = _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    change (∑ i : Fin 21, if i ∈ r.1 then r.2.card else 0) = r.1.card * r.2.card
    rw [← Finset.sum_filter]
    have h : Finset.univ.filter (fun i => i ∈ r.1) = r.1 := by ext i; simp
    simp [h]
  have floor (d : ℕ) (h : ∀ i, d ≤ load i) : 21*d ≤ ∑ r ∈ S, area r := by
    rw [← total]
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 21))) (fun i _ => h i)
    simpa using hsum
  have ceiling (T : Finset Rect) (incl : T ⊆ S) : (∑ r ∈ T, area r) ≤ T.card * 18 := by
    have each (r : Rect) (hr : r ∈ T) : area r ≤ 18 := by
      rcases shapeS r (incl hr) with low | good
      · omega
      · exact good.1
    simpa using Finset.sum_le_sum each
  by_cases cheap : ∃ r ∈ S, area r ≤ 10
  · obtain ⟨r,hr,small⟩ := cheap
    have lower := floor 10 ten
    have upper := ceiling (S.erase r) (Finset.erase_subset r S)
    have cost := Finset.sum_erase_add S area hr
    have card := Finset.card_erase_of_mem hr
    omega
  · have twelve (i : Fin 21) : 12 ≤ load i := by
      have div : 3 ∣ load i := by
        apply Finset.dvd_sum
        intro r hr
        have good := (shapeS r hr).resolve_left (fun h => cheap ⟨r,hr,h⟩)
        by_cases hi : i ∈ r.1
        · simpa [width,hi] using good.2
        · simp [width,hi]
      obtain ⟨t,ht⟩ := div
      have := ten i
      omega
    have lower := floor 12 twelve
    have upper := ceiling S (fun _ h => h)
    omega

end PEqualNP.Outside.L_meta_9988

theorem PEqualNP.Outside.L_meta_9988 : ¬ (∃ L : List (Finset (Fin 21) × Finset (Fin 21)), L.length ≤ 12 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([2095104, 2066304, 1865536, 1273536, 712128, 375744, 2064444, 1863738, 1271862, 710702, 374814, 1836857, 1246901, 689581, 361373, 1074803, 546155, 275291, 150759, 76503, 39375] : List ℕ).getD i.val 0).testBit j.val = true) ∧ ∀ (i : Fin 21) (j : Fin 21), (([2095104, 2066304, 1865536, 1273536, 712128, 375744, 2064444, 1863738, 1271862, 710702, 374814, 1836857, 1246901, 689581, 361373, 1074803, 546155, 275291, 150759, 76503, 39375] : List ℕ).getD i.val 0).testBit j.val = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, size, valid, cover⟩
  apply PEqualNP.Outside.L_meta_9988.noTwelve PEqualNP.Outside.L_meta_9988.f PEqualNP.Outside.L_meta_9988.degree
    (L.map PEqualNP.Outside.L_meta_9988.normRect) (by simpa using size)
  · intro i j present
    obtain ⟨r,mem,ri,rj⟩ := cover i j present
    obtain ⟨keepRows,keepCols⟩ := PEqualNP.Outside.L_meta_9988.inside r (valid r mem)
    exact ⟨_, List.mem_map.mpr ⟨r,mem,rfl⟩,keepRows ri,keepCols rj⟩
  · intro r mem
    obtain ⟨source,_,rfl⟩ := List.mem_map.mp mem
    exact PEqualNP.Outside.L_meta_9988.shape source
