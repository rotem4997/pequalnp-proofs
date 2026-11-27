import Mathlib

namespace PEqualNP.Outside.L_meta_10050

abbrev Vertex := Fin 16
abbrev Slot := Fin 6

def entry (i j : Vertex) : Bool :=
  (([49158, 32781, 27, 54, 108, 216, 432, 864, 1728, 3456, 6912, 13824, 27648, 55296, 45057, 24579] :
    List ℕ).getD i.val 0).testBit j.val

abbrev Rect := Finset Vertex × Finset Vertex

def rowCode (L : List Rect) (i : Vertex) : Finset Slot :=
  Finset.univ.filter fun k => (L[k.val]?.map fun r => decide (i ∈ r.1)).getD false = true

def colCode (L : List Rect) (j : Vertex) : Finset Slot :=
  Finset.univ.filter fun k => (L[k.val]?.map fun r => decide (j ∈ r.2)).getD false = true

theorem codes (L : List Rect) (bound : L.length ≤ 6)
    (sound : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, entry i j = false)
    (covers : ∀ i j, entry i j = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) (i j : Vertex) :
    entry i j = false ↔ ∃ k, k ∈ rowCode L i ∧ k ∈ colCode L j := by
  constructor
  · intro zero
    obtain ⟨r,member,hi,hj⟩ := covers i j zero
    obtain ⟨k,lt,rfl⟩ := List.getElem_of_mem member
    let slot : Slot := ⟨k,lt.trans_le bound⟩
    refine ⟨slot,?_,?_⟩
    · simp [rowCode,slot,List.getElem?_eq_getElem lt,hi]
    · simp [colCode,slot,List.getElem?_eq_getElem lt,hj]
  · rintro ⟨k,hi,hj⟩
    cases pick : L[k.val]? with
    | none => simp [rowCode,pick] at hi
    | some r =>
      have row : i ∈ r.1 := by simpa [rowCode,pick] using hi
      have column : j ∈ r.2 := by simpa [colCode,pick] using hj
      exact sound r (List.mem_of_getElem? pick) i row j column

theorem rowDistinguishes :
    ∀ a b : Vertex, a ≠ b → ∃ j : Vertex, entry a j = false ∧ entry b j = true := by
  decide +kernel

theorem colDistinguishes :
    ∀ a b : Vertex, a ≠ b → ∃ i : Vertex, entry i a = false ∧ entry i b = true := by
  decide +kernel

theorem onesInRow : ∀ i : Vertex, (Finset.univ.filter fun j : Vertex => entry i j = true).card = 4 := by
  decide +kernel

theorem antichainAtMostThree (U : Finset Slot) (small : U.card ≤ 3)
    (A : Finset (Finset Slot)) (inside : ∀ s ∈ A, s ⊆ U)
    (anti : IsAntichain (· ⊆ ·) (A : Set (Finset Slot))) : A.card ≤ 3 := by
  classical
  let restrict (s : Finset Slot) : Finset ↥U := s.subtype (· ∈ U)
  have reflects (s : Finset Slot) (hs : s ∈ A) (t : Finset Slot)
      (sub : restrict s ⊆ restrict t) : s ⊆ t := by
    intro i hi
    have tagged : (⟨i,inside s hs hi⟩ : ↥U) ∈ restrict s := Finset.mem_subtype.mpr hi
    exact Finset.mem_subtype.mp (sub tagged)
  have inj : Set.InjOn restrict (A : Set (Finset Slot)) := by
    intro s hs t ht same
    exact Finset.Subset.antisymm
      (reflects s hs t (same ▸ Finset.Subset.rfl))
      (reflects t ht s (same.symm ▸ Finset.Subset.rfl))
  have newAnti : IsAntichain (· ⊆ ·) (A.image restrict : Set (Finset ↥U)) := by
    intro x hx y hy ne sub
    change x ∈ A.image restrict at hx
    change y ∈ A.image restrict at hy
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hy
    exact anti hs ht (fun eq => ne (congrArg restrict eq)) (reflects s hs t sub)
  have cap := newAnti.sperner
  rw [Finset.card_image_of_injOn inj, Fintype.card_coe] at cap
  have arithmetic : ∀ k ≤ 3, k.choose (k/2) ≤ 3 := by
    intro k hk
    interval_cases k <;> decide
  exact cap.trans (arithmetic U.card small)

theorem noCover (L : List Rect) (bound : L.length ≤ 6)
    (sound : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, entry i j = false)
    (covers : ∀ i j, entry i j = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) : False := by
  classical
  let A := rowCode L
  let B := colCode L
  have exactMatrix := codes L bound sound covers
  have rowIncomparable (a b : Vertex) (ne : a ≠ b) : ¬ A a ⊆ A b := by
    intro sub
    obtain ⟨j,zero,one⟩ := rowDistinguishes a b ne
    obtain ⟨k,x,y⟩ := (exactMatrix a j).mp zero
    have forbidden := (exactMatrix b j).mpr ⟨k,sub x,y⟩
    rw [one] at forbidden
    contradiction
  have colIncomparable (a b : Vertex) (ne : a ≠ b) : ¬ B a ⊆ B b := by
    intro sub
    obtain ⟨i,zero,one⟩ := colDistinguishes a b ne
    obtain ⟨k,x,y⟩ := (exactMatrix i a).mp zero
    have forbidden := (exactMatrix i b).mpr ⟨k,x,sub y⟩
    rw [one] at forbidden
    contradiction
  have rowSmall (i : Vertex) : (A i).card ≤ 2 := by
    by_contra! size
    let U : Finset Slot := Finset.univ \ A i
    have uSmall : U.card ≤ 3 := by
      change (Finset.univ \ A i).card ≤ 3
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
      omega
    let J := Finset.univ.filter fun j : Vertex => entry i j = true
    let X := J.image B
    have inject : Set.InjOn B (J : Set Vertex) := by
      intro j _ k _ equal
      by_contra diff
      exact colIncomparable j k diff (le_of_eq equal)
    have sizeX : X.card = 4 := (Finset.card_image_of_injOn inject).trans (onesInRow i)
    have antiX : IsAntichain (· ⊆ ·) (X : Set (Finset Slot)) := by
      intro s hs t ht diff le
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp ht
      exact colIncomparable j k (fun eq => diff (congrArg B eq)) le
    have confined (s : Finset Slot) (hs : s ∈ X) : s ⊆ U := by
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hs
      intro k hk
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun h => ?_⟩
      have forbidden := (exactMatrix i j).mpr ⟨k,h,hk⟩
      rw [(Finset.mem_filter.mp hj).2] at forbidden
      contradiction
    have limited := antichainAtMostThree U uSmall X confined antiX
    omega
  let family := (Finset.univ : Finset Vertex).image A
  have injection : Set.InjOn A ((Finset.univ : Finset Vertex) : Set Vertex) := by
    intro i _ j _ same
    by_contra diff
    exact rowIncomparable i j diff (le_of_eq same)
  have familySize : family.card = 16 := by
    rw [show family = Finset.univ.image A from rfl,Finset.card_image_of_injOn injection]
    simp
  have anti : IsAntichain (· ⊆ ·) (family : Set (Finset Slot)) := by
    intro s hs t ht diff le
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
    exact rowIncomparable i j (fun eq => diff (congrArg A eq)) le
  have lym := Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose (𝕜 := ℚ) anti
  have lower : (∑ _s ∈ family, (15 : ℚ)⁻¹) ≤
      ∑ s ∈ family, ((Fintype.card Slot).choose s.card : ℚ)⁻¹ := by
    apply Finset.sum_le_sum
    intro s hs
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hs
    have small := rowSmall i
    rw [Fintype.card_fin]
    interval_cases (A i).card <;> norm_num [Nat.choose]
  have impossible := lower.trans lym
  simp [familySize] at impossible
  norm_num at impossible

end PEqualNP.Outside.L_meta_10050

theorem PEqualNP.Outside.L_meta_10050 : ¬ (∃ L : List (Finset (Fin 16) × Finset (Fin 16)), L.length ≤ 6 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([49158, 32781, 27, 54, 108, 216, 432, 864, 1728, 3456, 6912, 13824, 27648, 55296, 45057, 24579] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 16) (j : Fin 16), (([49158, 32781, 27, 54, 108, 216, 432, 864, 1728, 3456, 6912, 13824, 27648, 55296, 45057, 24579] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L,bound,sound,cover⟩
  exact PEqualNP.Outside.L_meta_10050.noCover L bound sound cover
