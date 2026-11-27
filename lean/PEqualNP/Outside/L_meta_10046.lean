import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10046_aux

def raw : List ℕ := [107286, 83501, 35931, 71862, 12653, 25306, 50612, 101224, 71377, 11683, 23366, 46732, 93464, 55857, 111714, 92357, 53643]
def adj (i j : Fin 17) := (23785 : ℕ).testBit (j-i).val
def masks : Array ℕ := #[0, 1, 3, 5, 9, 17, 33, 65, 67, 73, 97, 99, 129, 133, 137, 145, 153, 161, 257, 521, 577, 645, 1033, 1057, 1193, 2081, 2309, 4231, 4675, 8777, 19357, 131071]
def bits (q : Fin 32) (j : Fin 17) := (masks.getD q.val 0).testBit j.val
def moves0 : Array (Array ℕ) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[17, 0, 0, 17, 0, 17, 17, 17, 0, 0, 17, 17, 17, 0, 17, 0, 0],
  #[17, 18, 0, 17, 18, 17, 34, 34, 18, 0, 17, 34, 34, 18, 17, 18, 0],
  #[17, 0, 19, 17, 0, 51, 17, 51, 19, 19, 17, 17, 51, 19, 51, 0, 19],
  #[68, 0, 0, 68, 0, 17, 68, 17, 20, 20, 68, 17, 17, 20, 68, 20, 0],
  #[17, 21, 0, 17, 21, 17, 17, 85, 0, 21, 85, 85, 17, 0, 85, 21, 21],
  #[102, 0, 22, 17, 0, 102, 17, 17, 22, 0, 102, 102, 102, 0, 17, 22, 22],
  #[119, 23, 0, 119, 0, 17, 119, 17, 0, 23, 17, 119, 119, 23, 17, 0, 23],
  #[119, 103, 0, 119, 18, 17, 136, 34, 18, 23, 17, 136, 136, 103, 17, 18, 23],
  #[153, 23, 0, 153, 0, 17, 153, 17, 20, 71, 68, 119, 119, 71, 68, 20, 23],
  #[170, 23, 22, 119, 0, 102, 119, 17, 22, 23, 102, 170, 170, 23, 17, 22, 39],
  #[170, 103, 22, 119, 18, 102, 136, 34, 86, 23, 102, 187, 187, 103, 17, 86, 39],
  #[204, 24, 24, 17, 24, 17, 17, 204, 0, 0, 204, 17, 204, 24, 204, 0, 0],
  #[204, 24, 104, 17, 24, 51, 17, 221, 19, 19, 204, 17, 221, 104, 221, 0, 19],
  #[238, 24, 24, 68, 24, 17, 68, 204, 20, 20, 238, 17, 204, 88, 238, 20, 0],
  #[204, 72, 24, 17, 72, 17, 17, 255, 0, 21, 255, 85, 204, 24, 255, 21, 21]]
def moves1 : Array (Array ℕ) := #[#[238, 72, 24, 68, 72, 17, 68, 255, 20, 37, 272, 85, 204, 88, 272, 37, 21],
  #[289, 24, 56, 17, 24, 102, 17, 204, 22, 0, 289, 102, 289, 24, 204, 22, 22],
  #[17, 25, 25, 306, 0, 306, 17, 17, 25, 0, 17, 306, 17, 25, 306, 25, 0],
  #[68, 0, 26, 323, 26, 17, 323, 17, 20, 122, 68, 17, 315, 20, 323, 122, 26],
  #[119, 23, 26, 340, 26, 17, 340, 17, 0, 74, 17, 119, 340, 23, 315, 26, 74],
  #[204, 24, 291, 315, 58, 51, 315, 221, 19, 206, 204, 17, 357, 104, 357, 26, 206],
  #[374, 0, 0, 374, 27, 214, 68, 214, 20, 20, 374, 17, 17, 207, 68, 207, 27],
  #[391, 0, 22, 214, 27, 391, 17, 214, 22, 0, 391, 102, 102, 27, 17, 107, 107],
  #[408, 24, 56, 374, 75, 391, 68, 381, 54, 20, 408, 102, 289, 258, 238, 224, 107],
  #[425, 28, 22, 17, 28, 425, 130, 17, 124, 0, 102, 425, 102, 0, 130, 22, 124],
  #[130, 76, 121, 306, 28, 442, 130, 51, 342, 19, 17, 331, 51, 121, 442, 25, 317],
  #[398, 432, 393, 17, 120, 301, 182, 459, 35, 216, 204, 34, 459, 137, 221, 131, 19],
  #[437, 426, 77, 340, 307, 114, 476, 182, 18, 159, 17, 136, 476, 103, 315, 332, 74],
  #[153, 210, 94, 493, 26, 17, 493, 98, 217, 156, 268, 119, 340, 377, 323, 122, 244],
  #[504, 276, 466, 484, 412, 442, 451, 422, 478, 461, 272, 501, 357, 189, 510, 190, 359],
  #[513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 510, 511, 512]]

def moves := moves0 ++ moves1
def transition (q : Fin 32) (i : Fin 17) : Fin 32 × Fin 17 :=
  let z := ((moves.getD q.val #[]).getD i.val 0)
  (Fin.ofNat 32 (z / 17), Fin.ofNat 17 z)

theorem entry : ∀ i j : Fin 17, adj i j = true ↔ (raw.getD i.val 0).testBit j.val = false := by decide +kernel

theorem top : ∀ j, bits 31 j = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem step : ∀ q i j, bits (transition q i).1 (j - (transition q i).2) = (bits q j && adj i j) := by decide +kernel

theorem shift (i j s : Fin 17) : adj (i-s) (j-s) = adj i j := by
  unfold adj
  congr 2
  abel

theorem intersection (R : Finset (Fin 17)) :
    ∃ q : Fin 32, ∃ s : Fin 17, ∀ j, bits q (j-s) = true ↔ ∀ i ∈ R, adj i j = true := by
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨31,0,fun j => ?_⟩
    simp [top]
  | @insert i R hi ih =>
    obtain ⟨q,s,hq⟩ := ih
    let p := transition q (i-s)
    refine ⟨p.1,s+p.2,fun j => ?_⟩
    have he : j-(s+p.2) = (j-s)-p.2 := by abel
    rw [he, step, shift, Bool.and_eq_true, hq, Finset.forall_mem_insert]
    exact and_comm

def offsets : Array ℕ := #[3, 5, 6, 7, 10, 11, 12, 14]
def offset (u : Fin 8) : Fin 17 := Fin.ofNat 17 (offsets.getD u.val 0)

theorem present : ∀ (i : Fin 17) (t : Fin 8), adj i (i+offset t) = true := by decide +kernel

def containing (q : Fin 32) (i : Fin 17) : Bool :=
  ((#[23785, 47570, 95140, 59209, 118418, 105765, 80459, 29847, 59694, 119388, 107705, 84339, 37607, 75214, 19357, 38714, 77428] : Array ℕ).getD i.val 0 &&& masks.getD q.val 0) == masks.getD q.val 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem allow : ∀ q i, (∀ j, bits q j = true → adj i j = true) → containing q i = true := by decide +kernel

def within (q : Fin 32) : Finset (Fin 17 × Fin 8) :=
  Finset.univ.filter fun p => containing q p.1 && bits q (p.1 + offset p.2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem bound : ∀ q, (within q).card ≤ 8 := by decide +kernel

def hits (r : Finset (Fin 17) × Finset (Fin 17)) : Finset (Fin 17 × Fin 8) :=
  Finset.univ.filter fun p => p.1 ∈ r.1 ∧ p.1 + offset p.2 ∈ r.2

theorem single (r : Finset (Fin 17) × Finset (Fin 17))
    (safe : ∀ i ∈ r.1, ∀ j ∈ r.2, adj i j = true) : (hits r).card ≤ 8 := by
  obtain ⟨q,s,hq⟩ := intersection r.1
  let move : (Fin 17 × Fin 8) ↪ (Fin 17 × Fin 8) :=
    ⟨fun p => (p.1-s,p.2), by
      intro a b h
      change (a.1 - s, a.2) = (b.1 - s, b.2) at h
      obtain ⟨ha,hb⟩ := Prod.mk.inj h
      exact Prod.ext (sub_left_inj.mp ha) hb⟩
  have sub : (hits r).map move ⊆ within q := by
    intro y hy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨hi,hj⟩ := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
    · apply allow
      intro j h
      have x := (hq (j+s)).mp (by simpa using h) p.1 hi
      have eq := shift p.1 (j+s) s
      change adj (p.1 - s) j = true
      simpa only [add_sub_cancel_right] using eq.trans x
    · change bits q ((p.1-s) + offset p.2) = true
      have eq : (p.1-s) + offset p.2 = (p.1 + offset p.2)-s := by abel
      rw [eq]
      exact (hq _).mpr fun i h => safe i h _ hj
  simpa using (Finset.card_le_card sub).trans (bound q)

end PEqualNP.Outside.L_meta_10046_aux

open PEqualNP.Outside.L_meta_10046_aux

theorem PEqualNP.Outside.L_meta_10046 : ¬ (∃ L : List (Finset (Fin 17) × Finset (Fin 17)), L.length ≤ 16 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([107286, 83501, 35931, 71862, 12653, 25306, 50612, 101224, 71377, 11683, 23366, 46732, 93464, 55857, 111714, 92357, 53643] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 17) (j : Fin 17), (([107286, 83501, 35931, 71862, 12653, 25306, 50612, 101224, 71377, 11683, 23366, 46732, 93464, 55857, 111714, 92357, 53643] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, hl, safe, cover⟩
  have hu : (Finset.univ : Finset (Fin 17 × Fin 8)) ⊆ L.toFinset.biUnion hits := by
    intro p _
    obtain ⟨r,hr,hi,hj⟩ := cover _ _ ((entry _ _).mp (present p.1 p.2))
    exact Finset.mem_biUnion.mpr ⟨r,List.mem_toFinset.mpr hr,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hj⟩⟩
  have total := Finset.card_le_card hu
  have boxes := Finset.card_biUnion_le_card_mul L.toFinset hits 8 (fun r hr => single r (fun i hi j hj => (entry i j).mpr (safe r (List.mem_toFinset.mp hr) i hi j hj)))
  have count := List.toFinset_card_le L
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at total
  omega
