import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10034
def rows : List Nat := [69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528]
def Good (u : Finset (Fin 16)) (v : Finset (Fin 20)) : Prop :=
  ∀ i ∈ u, ∀ j ∈ v, (rows.getD i.val 0).testBit j.val = false
def starsRaw : List (List (Fin 16) × List (Fin 20)) := [
  ([9, 8, 6, 5, 2, 0], [3, 5, 9, 15, 19]),
  ([9, 8, 7, 4, 3, 1], [2, 4, 8, 14, 19]),
  ([10, 8, 5, 4, 2, 1], [3, 7, 8, 12, 19]),
  ([10, 8, 7, 6, 3, 0], [1, 5, 10, 14, 19]),
  ([10, 9, 6, 4, 1, 0], [3, 6, 11, 14, 19]),
  ([10, 9, 7, 5, 3, 2], [0, 5, 8, 13, 19]),
  ([11, 8, 6, 4, 3, 2], [1, 4, 9, 12, 19]),
  ([11, 8, 7, 5, 1, 0], [2, 7, 10, 15, 19]),
  ([11, 9, 5, 4, 3, 0], [2, 6, 9, 13, 19]),
  ([11, 9, 7, 6, 2, 1], [0, 4, 11, 15, 19]),
  ([11, 10, 6, 5, 3, 1], [0, 6, 10, 12, 19]),
  ([11, 10, 7, 4, 2, 0], [1, 7, 11, 13, 19]),
  ([13, 12, 6, 4, 2, 1], [3, 4, 11, 12, 18]),
  ([13, 12, 7, 5, 3, 0], [2, 5, 10, 13, 18]),
  ([13, 12, 10, 8, 6, 5], [3, 5, 10, 12, 16]),
  ([13, 12, 10, 9, 2, 0], [3, 5, 11, 13, 17]),
  ([13, 12, 11, 8, 3, 1], [2, 4, 10, 12, 17]),
  ([13, 12, 11, 9, 7, 4], [2, 4, 11, 13, 16]),
  ([14, 12, 6, 5, 1, 0], [3, 6, 10, 15, 18]),
  ([14, 12, 7, 4, 3, 2], [1, 4, 8, 13, 18]),
  ([14, 12, 9, 8, 2, 1], [3, 4, 8, 15, 17]),
  ([14, 12, 10, 9, 5, 4], [3, 6, 8, 13, 16]),
  ([14, 12, 11, 8, 7, 6], [1, 4, 10, 15, 16]),
  ([14, 12, 11, 10, 3, 0], [1, 6, 10, 13, 17]),
  ([14, 13, 5, 4, 2, 0], [3, 7, 9, 13, 18]),
  ([14, 13, 7, 6, 3, 1], [0, 4, 10, 14, 18]),
  ([14, 13, 9, 8, 6, 4], [3, 4, 9, 14, 16]),
  ([14, 13, 10, 8, 1, 0], [3, 7, 10, 14, 17]),
  ([14, 13, 11, 9, 3, 2], [0, 4, 9, 13, 17]),
  ([14, 13, 11, 10, 7, 5], [0, 7, 10, 13, 16]),
  ([15, 12, 5, 4, 3, 1], [2, 6, 8, 12, 18]),
  ([15, 12, 7, 6, 2, 0], [1, 5, 11, 15, 18]),
  ([15, 12, 9, 8, 7, 5], [2, 5, 8, 15, 16]),
  ([15, 12, 10, 8, 3, 2], [1, 5, 8, 12, 17]),
  ([15, 12, 11, 9, 1, 0], [2, 6, 11, 15, 17]),
  ([15, 12, 11, 10, 6, 4], [1, 6, 11, 12, 16]),
  ([15, 13, 6, 5, 3, 2], [0, 5, 9, 12, 18]),
  ([15, 13, 7, 4, 1, 0], [2, 7, 11, 14, 18]),
  ([15, 13, 9, 8, 3, 0], [2, 5, 9, 14, 17]),
  ([15, 13, 10, 9, 7, 6], [0, 5, 11, 14, 16]),
  ([15, 13, 11, 8, 5, 4], [2, 7, 9, 12, 16]),
  ([15, 13, 11, 10, 2, 1], [0, 7, 11, 12, 17]),
  ([15, 14, 6, 4, 3, 0], [1, 6, 9, 14, 18]),
  ([15, 14, 7, 5, 2, 1], [0, 7, 8, 15, 18]),
  ([15, 14, 10, 8, 7, 4], [1, 7, 8, 14, 16]),
  ([15, 14, 10, 9, 3, 1], [0, 6, 8, 14, 17]),
  ([15, 14, 11, 8, 2, 0], [1, 7, 9, 15, 17]),
  ([15, 14, 11, 9, 6, 5], [0, 6, 9, 15, 16])]
def stars : List (Finset (Fin 16) × Finset (Fin 20)) :=
  starsRaw.map fun p => (p.1.toFinset,p.2.toFinset)

def colsAfter (i : Fin 16) (cs : List (Fin 20)) :=
  cs.filter fun j => !(rows.getD i.val 0).testBit j.val

def check (us : List (Fin 16)) (cs : List (Fin 20)) : List (Fin 16) → Bool
  | [] => decide (us.length*cs.length < 30) ||
      (decide (us.length*cs.length = 30) && decide ((us,cs) ∈ starsRaw))
  | i::rest => decide ((us.length+(i::rest).length)*cs.length < 30) ||
      (check (i::us) (colsAfter i cs) rest && check us cs rest)
termination_by structural rest => rest

theorem searchSound {u v} (good : Good u v) (large : 30 ≤ u.card*v.card)
    (todo : List (Fin 16)) (us : List (Fin 16)) (cs : List (Fin 20))
    (incl : us.toFinset ⊆ u) (allU : u ⊆ us.toFinset ∪ todo.toFinset)
    (allV : v ⊆ cs.toFinset) (found : check us cs todo = true) :
    u.card*v.card = 30 ∧ (u,v) ∈ stars := by
  induction todo generalizing us cs with
  | nil =>
    have hu : u.card ≤ us.length+([] : List (Fin 16)).length := calc
      u.card ≤ (us.toFinset ∪ ([] : List (Fin 16)).toFinset).card := Finset.card_le_card allU
      _ ≤ us.toFinset.card + ([] : List (Fin 16)).toFinset.card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
    have hv := Finset.card_le_card allV
    have hvl := List.toFinset_card_le cs
    have maxArea := Nat.mul_le_mul hu (Nat.le_trans hv hvl)
    have eq : u = us.toFinset := Finset.Subset.antisymm (by simpa using allU) incl
    simp only [check, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at found
    rcases found with lt | ⟨area,mem⟩
    · simp at maxArea
      omega
    · have le : u.card ≤ us.length := by simpa using hu
      have exactArea : u.card*v.card = 30 := Nat.le_antisymm
        (area ▸ Nat.mul_le_mul le (hv.trans hvl)) large
      have eqv : v = cs.toFinset := by
        apply Finset.eq_of_subset_of_card_le allV
        by_contra! tooSmall
        have hpos : 0 < us.length := Nat.pos_of_ne_zero (by intro z; simp [z] at area)
        have low := Nat.mul_lt_mul_of_pos_left (tooSmall.trans_le hvl) hpos
        have step := Nat.mul_le_mul_right v.card le
        omega
      exact ⟨exactArea,by
        rw [eq,eqv]
        exact List.mem_map.mpr ⟨(us,cs),mem,rfl⟩⟩
  | cons i rest ih =>
    have hu : u.card ≤ us.length+(i::rest).length := calc
      u.card ≤ (us.toFinset ∪ (i::rest).toFinset).card := Finset.card_le_card allU
      _ ≤ us.toFinset.card + (i::rest).toFinset.card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
    have hv := Finset.card_le_card allV
    have hvl := List.toFinset_card_le cs
    have maxArea := Nat.mul_le_mul hu (Nat.le_trans hv hvl)
    simp only [check, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at found
    rcases found with lt | ⟨yes,no⟩
    · omega
    · by_cases hi : i ∈ u
      · apply ih (i::us) (colsAfter i cs) (by simpa using Finset.insert_subset hi incl)
        · intro x hx
          simpa [Finset.mem_union,or_comm,or_left_comm,or_assoc] using allU hx
        · intro x hx
          have mem := List.mem_toFinset.mp (allV hx)
          exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨mem,by simp only [good i hi x hx, Bool.not_false]⟩)
        · exact yes
      · apply ih us cs incl _ allV no
        intro x hx
        have ne : x ≠ i := by rintro rfl; exact hi hx
        simpa [ne] using allU hx

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem checked : check [] (List.finRange 20) (List.finRange 16) = true := by decide +kernel

theorem big {u v} (h : Good u v) (large : 30 ≤ u.card*v.card) :
    u.card*v.card = 30 ∧ (u,v) ∈ stars := by
  apply searchSound h large (List.finRange 16) [] (List.finRange 20) _ _ _ checked
  · simp
  · simp
  · simp

theorem area_le {u v} (h : Good u v) : u.card*v.card ≤ 30 := by
  by_contra! bad
  exact (Nat.ne_of_gt bad) (big h (Nat.le_of_lt bad)).1

theorem classify {u v} (h : Good u v) (large : 30 ≤ u.card*v.card) : (u,v) ∈ stars :=
  (big h large).2

def zeros : Finset (Fin 16 × Fin 20) :=
  Finset.univ.filter fun z => (rows.getD z.1.val 0).testBit z.2.val = false

def cells (r : Finset (Fin 16) × Finset (Fin 20)) := r.1 ×ˢ r.2

def witnesses : List (Fin 16 × Fin 20) := [(1,6),(1,7),(1,10),(1,11)]

def blocks (r : Finset (Fin 16) × Finset (Fin 20)) (z : Fin 16 × Fin 20) : Bool :=
  !(rows.getD z.1.val 0).testBit z.2.val && !decide (z.1 ∈ r.1 ∧ z.2 ∈ r.2) &&
    stars.all fun s => decide ((z.1 ∈ s.1 ∧ z.2 ∈ s.2) →
      (r.1 ∩ s.1).Nonempty ∧ (r.2 ∩ s.2).Nonempty)

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem obstruction_data :
    stars.all (fun r => !decide ((0 : Fin 16) ∈ r.1 ∧ (1 : Fin 20) ∈ r.2) ||
      witnesses.any (blocks r)) = true := by decide +kernel

theorem obstruct_stars {r} (hr : r ∈ stars) (h : (0,1) ∈ cells r) :
    ∃ z ∈ witnesses, z ∈ zeros ∧ z ∉ cells r ∧
      ∀ s ∈ stars, z ∈ cells s → (r.1 ∩ s.1).Nonempty ∧ (r.2 ∩ s.2).Nonempty := by
  have hh := List.all_eq_true.mp obstruction_data r hr
  have h0 := Finset.mem_product.mp h
  simp only [decide_eq_true h0,Bool.not_true,Bool.false_or] at hh
  obtain ⟨z,hz,hz'⟩ := List.any_eq_true.mp hh
  simp only [blocks,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true,decide_eq_true_eq,
    decide_eq_false_iff_not] at hz'
  exact ⟨z,hz,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz'.1.1⟩,
    fun hit => hz'.1.2 (Finset.mem_product.mp hit),fun s hs hit => hz'.2 s hs (Finset.mem_product.mp hit)⟩

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem zeros_card : zeros.card = 240 := by decide

theorem no_cover
    (maxArea : ∀ {u v}, Good u v → u.card*v.card ≤ 30)
    (characterize : ∀ {u v}, Good u v → 30 ≤ u.card*v.card → (u,v) ∈ stars) :
    ¬ ∃ L : List (Finset (Fin 16) × Finset (Fin 20)), L.length ≤ 8 ∧
      (∀ r ∈ L, Good r.1 r.2) ∧ (∀ z ∈ zeros, ∃ r ∈ L, z ∈ cells r) := by
  classical
  rintro ⟨L,plen,good,cover⟩
  let S := L.toFinset
  let hits (z : Fin 16 × Fin 20) := S.filter fun r => z ∈ cells r
  have sn : S.card ≤ 8 := (List.toFinset_card_le _).trans plen
  have inside {r} (hr : r ∈ S) : cells r ⊆ zeros := by
    intro z hz
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,good r (List.mem_toFinset.mp hr) z.1 hi z.2 hj⟩
  have amax (r) (hr : r ∈ S) : (cells r).card ≤ 30 := by
    rw [cells,Finset.card_product]
    exact maxArea (good r (List.mem_toFinset.mp hr))
  have hpos (z) (hz : z ∈ zeros) : 1 ≤ (hits z).card := by
    obtain ⟨r,hr,hz'⟩ := cover z hz
    exact Finset.card_pos.mpr ⟨r,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,hz'⟩⟩
  have balance : (∑ z ∈ zeros, (hits z).card) = ∑ r ∈ S, (cells r).card := by
    simp_rw [hits,Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Finset.card_filter]
    congr 1
    ext z
    change (z ∈ zeros.filter fun z => z ∈ cells r) ↔ z ∈ cells r
    rw [Finset.mem_filter]
    exact ⟨And.right,fun h => ⟨inside hr h,h⟩⟩
  have low : 240 ≤ ∑ z ∈ zeros, (hits z).card := by
    simpa [zeros_card] using Finset.sum_le_sum hpos
  have hi : (∑ r ∈ S, (cells r).card) ≤ S.card*30 := by
    simpa using Finset.sum_le_sum amax
  have total : (∑ r ∈ S, (cells r).card) = 240 := by omega
  have exactArea (r) (hr : r ∈ S) : (cells r).card = 30 := by
    by_contra neq
    have b := amax r hr
    have strict : (∑ t ∈ S, (cells t).card) < (∑ _t ∈ S, (30 : Nat)) :=
      Finset.sum_lt_sum amax ⟨r,hr,lt_of_le_of_ne b neq⟩
    have ss : (∑ _t ∈ S, (30 : Nat)) = S.card*30 := by simp
    rw [ss,total] at strict
    omega
  have once (z) (hz : z ∈ zeros) : (hits z).card = 1 := by
    by_contra neq
    have b := hpos z hz
    have strict := Finset.sum_lt_sum hpos ⟨z,hz,by omega⟩
    simp only [Finset.sum_const,nsmul_eq_mul,Nat.mul_one,zeros_card] at strict
    omega
  have star {r} (hr : r ∈ S) : r ∈ stars := by
    have big := exactArea r hr
    rw [cells,Finset.card_product] at big
    exact characterize (good r (List.mem_toFinset.mp hr)) big.ge
  obtain ⟨r,hr,hcell⟩ := cover (0,1) (by decide)
  have hrs : r ∈ S := List.mem_toFinset.mpr hr
  obtain ⟨z,_,z0,zr,all⟩ := obstruct_stars (star hrs) hcell
  obtain ⟨s,hs,sz⟩ := cover z z0
  have hss : s ∈ S := List.mem_toFinset.mpr hs
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := all s (star hss) sz
  have ha : (i,j) ∈ cells r := Finset.mem_product.mpr ⟨(Finset.mem_inter.mp hi).1,(Finset.mem_inter.mp hj).1⟩
  have hb : (i,j) ∈ cells s := Finset.mem_product.mpr ⟨(Finset.mem_inter.mp hi).2,(Finset.mem_inter.mp hj).2⟩
  have eq := Finset.card_le_one.mp (once (i,j) (inside hrs ha)).le
    r (Finset.mem_filter.mpr ⟨hrs,ha⟩) s (Finset.mem_filter.mpr ⟨hss,hb⟩)
  exact zr (eq ▸ sz)

end PEqualNP.Outside.L_meta_10034

theorem PEqualNP.Outside.L_meta_10034 :
    ¬ (∃ L : List (Finset (Fin 16) × Finset (Fin 20)), L.length ≤ 8 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 16) (j : Fin 20), (([69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L,hlen,hgood,hcover⟩
  apply PEqualNP.Outside.L_meta_10034.no_cover PEqualNP.Outside.L_meta_10034.area_le
    PEqualNP.Outside.L_meta_10034.classify
  refine ⟨L,hlen,hgood,?_⟩
  intro z hz
  obtain ⟨r,hr,hi,hj⟩ := hcover z.1 z.2 (Finset.mem_filter.mp hz).2
  exact ⟨r,hr,Finset.mem_product.mpr ⟨hi,hj⟩⟩
