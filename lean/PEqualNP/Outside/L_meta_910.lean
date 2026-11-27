import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_910_aux

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

abbrev V := Fin 14

def edgeList : List (ℕ × ℕ) :=
  [(7, 0), (7, 1), (7, 3), (8, 1), (8, 2), (8, 4), (9, 2), (9, 3), (9, 5), (10, 3), (10, 4), (10, 6), (11, 4), (11, 5), (11, 0), (12, 5), (12, 6), (12, 1), (13, 6), (13, 0), (13, 2)]

def hAdj (a b : V) : Bool :=
  decide (a ≠ b ∧ (((a : ℕ), (b : ℕ)) ∈ edgeList ∨ ((b : ℕ), (a : ℕ)) ∈ edgeList))

def Good (I : Finset V) : Prop :=
  (∀ a ∈ I, ∀ c ∈ I, hAdj a c = false) ∧
  (∀ w : V, w ∉ I → ∃ a ∈ I, hAdj a w = true)

def rows : Fin 37 → Finset V :=
  ![{0, 1, 2, 3, 4, 5, 6}, {2, 4, 5, 6, 7}, {0, 3, 5, 6, 8}, {5, 6, 7, 8},
    {0, 1, 4, 6, 9}, {4, 6, 7, 9}, {0, 6, 8, 9}, {0, 1, 2, 5, 10},
    {2, 5, 7, 10}, {0, 5, 8, 10}, {0, 1, 9, 10}, {1, 2, 3, 6, 11},
    {2, 6, 7, 11}, {3, 6, 8, 11}, {1, 6, 9, 11}, {6, 7, 8, 9, 11},
    {1, 2, 10, 11}, {0, 2, 3, 4, 12}, {2, 4, 7, 12}, {0, 3, 8, 12},
    {0, 4, 9, 12}, {0, 2, 10, 12}, {0, 8, 9, 10, 12}, {2, 3, 11, 12},
    {2, 7, 10, 11, 12}, {1, 3, 4, 5, 13}, {4, 5, 7, 13}, {3, 5, 8, 13},
    {1, 4, 9, 13}, {1, 5, 10, 13}, {5, 7, 8, 10, 13}, {1, 3, 11, 13},
    {1, 9, 10, 11, 13}, {3, 4, 12, 13}, {4, 7, 9, 12, 13}, {3, 8, 11, 12, 13},
    {7, 8, 9, 10, 11, 12, 13}]

def through : Fin 7 → Fin 9 → Fin 37 :=
  ![![0, 2, 4, 6, 7, 9, 10, 17, 19],
    ![0, 4, 7, 10, 11, 14, 16, 25, 28],
    ![0, 1, 7, 8, 11, 12, 16, 17, 18],
    ![0, 2, 11, 13, 17, 19, 23, 25, 27],
    ![0, 1, 4, 5, 17, 18, 20, 25, 26],
    ![0, 1, 2, 3, 7, 8, 9, 25, 26],
    ![0, 1, 2, 3, 4, 5, 6, 11, 12]]

def castX (x : Fin 7) : V := ⟨x.val, by omega⟩

theorem rowsGood : ∀ r : Fin 37, Good (rows r) := by
  unfold Good
  decide +kernel

theorem rowContains : ∀ (x : Fin 7) (i : Fin 9), castX x ∈ rows (through x i) := by
  decide +kernel

theorem rowDiff : ∀ (x : Fin 7) (i j : Fin 9), i ≠ j →
    ∃ w ∈ rows (through x i), w ∉ rows (through x j) := by
  decide +kernel

theorem rowPair : ∀ x y : Fin 7, ∃ r : Fin 37,
    ∀ z : Fin 7, castX z ∈ rows r ↔ z = x ∨ z = y := by
  decide +kernel

theorem rowEmpty : ∀ z : Fin 7, castX z ∉ rows 36 := by
  decide +kernel

theorem coverXY : ∀ v : V, v ∈ rows 0 ∨ v ∈ rows 36 := by
  decide +kernel

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma sideTrue_mono_U {n k : ℕ} {U W : Finset (Fin n)} (hUW : U ⊆ W)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue W B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUW hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

private lemma gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U W : Finset (Fin n)}
    (hUW : U ⊆ W) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel W d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUW _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUW _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

private lemma gateVal_mono_U {n : ℕ} (C : AndCountCircuit n) {U W : Finset (Fin n)}
    (hUW : U ⊆ W) (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal W i = true :=
  gateValFuel_mono_U C hUW C.size i h

private def singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) : Finset (Fin n) :=
  Finset.univ.filter (fun v => C.gateVal {v} i = true)

private lemma mem_singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ singSet C i ↔ C.gateVal {v} i = true := by
  unfold singSet
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

private def stripCircuit {n : ℕ} (C : AndCountCircuit n) : AndCountCircuit n where
  size := C.size
  leftVars i := (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  leftGates := C.leftGates
  rightVars i := (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  rightGates := C.rightGates
  outVars := C.outVars ∪ C.outGates.biUnion (singSet C)
  outGates := C.outGates

private lemma mem_strip_leftVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).leftVars i ↔
      (v ∈ C.leftVars i ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

private lemma mem_strip_rightVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).rightVars i ↔
      (v ∈ C.rightVars i ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

private lemma mem_strip_outVars {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    v ∈ (stripCircuit C).outVars ↔
      v ∈ C.outVars ∨ ∃ j ∈ C.outGates, C.gateVal {v} j = true := by
  change v ∈ C.outVars ∪ C.outGates.biUnion (singSet C) ↔ _
  simp only [Finset.mem_union, Finset.mem_biUnion, mem_singSet]

private lemma strip_singleton_false {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m → (stripCircuit C).gateVal {v} i = false := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    rw [Bool.eq_false_iff]
    intro htrue
    rw [gateVal_unfold (stripCircuit C) {v} i, Bool.and_eq_true] at htrue
    have hL := htrue.1
    have hR := htrue.2
    unfold sideTrue at hL hR
    rw [decide_eq_true_eq] at hL hR
    have hLv : v ∈ (stripCircuit C).leftVars i := by
      rcases hL with ⟨w, hw, hwv⟩ | ⟨j, _, hji, hjv⟩
      · rwa [Finset.mem_singleton.mp hwv] at hw
      · rw [ih j (by omega)] at hjv
        exact absurd hjv Bool.false_ne_true
    have hRv : v ∈ (stripCircuit C).rightVars i := by
      rcases hR with ⟨w, hw, hwv⟩ | ⟨j, _, hji, hjv⟩
      · rwa [Finset.mem_singleton.mp hwv] at hw
      · rw [ih j (by omega)] at hjv
        exact absurd hjv Bool.false_ne_true
    rw [mem_strip_leftVars] at hLv
    rw [mem_strip_rightVars] at hRv
    have hCv : C.gateVal {v} i = true := by
      rw [gateVal_unfold C {v} i, Bool.and_eq_true]
      constructor
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hLv.1 with hv | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hRv.1 with hv | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩
    exact hLv.2 hCv

private lemma strip_disjoint {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
    Disjoint ((stripCircuit C).leftVars i) ((stripCircuit C).rightVars i) := by
  rw [Finset.disjoint_left]
  intro v hvL hvR
  have hf := strip_singleton_false C v C.size i i.isLt
  have ht : (stripCircuit C).gateVal {v} i = true := by
    rw [gateVal_unfold (stripCircuit C) {v} i, Bool.and_eq_true]
    constructor
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvL, Finset.mem_singleton_self v⟩
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvR, Finset.mem_singleton_self v⟩
  rw [hf] at ht
  exact Bool.false_ne_true ht

private lemma strip_gateVal_le {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      (stripCircuit C).gateVal U i = true → C.gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true] at hval
    rw [gateVal_unfold C U i, Bool.and_eq_true]
    constructor
    · have hL := hval.1
      unfold sideTrue at hL ⊢
      rw [decide_eq_true_eq] at hL ⊢
      rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_leftVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩
    · have hR := hval.2
      unfold sideTrue at hR ⊢
      rw [decide_eq_true_eq] at hR ⊢
      rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_rightVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩

private lemma strip_gateVal_ge {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      C.gateVal U i = true →
        (∃ v ∈ U, C.gateVal {v} i = true) ∨ (stripCircuit C).gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    by_cases hsing : ∃ v ∈ U, C.gateVal {v} i = true
    · exact Or.inl hsing
    · right
      have hno : ∀ v ∈ U, C.gateVal {v} i ≠ true := fun v hvU hv => hsing ⟨v, hvU, hv⟩
      rw [gateVal_unfold C U i, Bool.and_eq_true] at hval
      rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true]
      constructor
      · have hL := hval.1
        unfold sideTrue at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩
      · have hR := hval.2
        unfold sideTrue at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩

private lemma strip_eval_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    (stripCircuit C).eval U = C.eval U := by
  unfold AndCountCircuit.eval
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · rw [mem_strip_outVars] at hvO
      rcases hvO with hvC | ⟨j, hjO, hvs⟩
      · exact Or.inl ⟨v, hvC, hvU⟩
      · exact Or.inr ⟨j, hjO, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
    · exact Or.inr ⟨j, hjO, strip_gateVal_le C U C.size j j.isLt hjv⟩
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inl hvO), hvU⟩
    · rcases strip_gateVal_ge C U C.size j j.isLt hjv with ⟨v, hvU, hvs⟩ | hj'
      · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inr ⟨j, hjO, hvs⟩), hvU⟩
      · exact Or.inr ⟨j, hjO, hj'⟩

def Free (C : AndCountCircuit 14) (v : V) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => v ∉ C.leftVars i ∧ v ∉ C.rightVars i)

def sideL (C : AndCountCircuit 14) (I : Finset V) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

def sideR (C : AndCountCircuit 14) (I : Finset V) (i : Fin C.size) : Bool :=
  sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I)

def Separates (C : AndCountCircuit 14) : Prop :=
  ∀ r : Fin 37, C.eval (rows r) = false ∧ ∀ w : V, w ∉ rows r → C.eval (insert w (rows r)) = true

theorem unionSide (C : AndCountCircuit 14) (U I J B : Finset V)
    (F : Finset (Fin C.size)) (i : Fin C.size) (hU : U ⊆ I ∪ J)
    (ih : ∀ j < i, C.gateVal U j = true → C.gateVal I j = true ∨ C.gateVal J j = true) :
    sideTrue U B F i (C.gateVal U) = true →
    sideTrue I B F i (C.gateVal I) = true ∨ sideTrue J B F i (C.gateVal J) = true := by
  simp only [sideTrue, decide_eq_true_eq]
  rintro (⟨v, hv, hu⟩ | ⟨j, hj, hji, ht⟩)
  · rcases Finset.mem_union.mp (hU hu) with h | h
    · exact Or.inl (Or.inl ⟨v, hv, h⟩)
    · exact Or.inr (Or.inl ⟨v, hv, h⟩)
  · rcases ih j hji ht with h | h
    · exact Or.inl (Or.inr ⟨j, hj, hji, h⟩)
    · exact Or.inr (Or.inr ⟨j, hj, hji, h⟩)

theorem mergeInput (C : AndCountCircuit 14) (I J U : Finset V) (v : V)
    (hi : v ∈ I) (hj : v ∈ J) (hU : U ⊆ I ∪ J)
    (hs : ∀ i ∈ Free C v, sideL C I i = sideL C J i) :
    C.eval U = true → C.eval I = true ∨ C.eval J = true := by
  have gate (i : Fin C.size) : C.gateVal U i = true →
      C.gateVal I i = true ∨ C.gateVal J i = true := by
    induction i using ((wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
    | h i ih =>
      intro ht
      rw [gateVal_unfold, Bool.and_eq_true] at ht
      rw [gateVal_unfold C I, gateVal_unfold C J]
      change (sideL C I i && sideR C I i) = true ∨ (sideL C J i && sideR C J i) = true
      have hl : sideL C I i = true ∨ sideL C J i = true := unionSide C U I J _ _ i hU ih ht.1
      have hr : sideR C I i = true ∨ sideR C J i = true := unionSide C U I J _ _ i hU ih ht.2
      simp only [Bool.and_eq_true]
      by_cases h1 : v ∈ C.leftVars i
      · have a : sideL C I i = true := decide_eq_true (Or.inl ⟨v, h1, hi⟩)
        have b : sideL C J i = true := decide_eq_true (Or.inl ⟨v, h1, hj⟩)
        rcases hr with hr | hr
        · exact Or.inl ⟨a, hr⟩
        · exact Or.inr ⟨b, hr⟩
      by_cases h2 : v ∈ C.rightVars i
      · have a : sideR C I i = true := decide_eq_true (Or.inl ⟨v, h2, hi⟩)
        have b : sideR C J i = true := decide_eq_true (Or.inl ⟨v, h2, hj⟩)
        rcases hl with hl | hl
        · exact Or.inl ⟨hl, a⟩
        · exact Or.inr ⟨hl, b⟩
      have hh := hs i (by simp [Free, h1, h2])
      have hlj : sideL C J i = true := by
        rcases hl with hl | hl
        · exact hh.symm.trans hl
        · exact hl
      have hli : sideL C I i = true := hh.trans hlj
      rcases hr with hr | hr
      · exact Or.inl ⟨hli, hr⟩
      · exact Or.inr ⟨hlj, hr⟩
  simp only [eval, decide_eq_true_eq]
  rintro (⟨w, hw, h⟩ | ⟨i, hi', h⟩)
  · rcases Finset.mem_union.mp (hU h) with h | h
    · exact Or.inl (Or.inl ⟨_, hw, h⟩)
    · exact Or.inr (Or.inl ⟨_, hw, h⟩)
  · rcases gate i h with h | h
    · exact Or.inl (Or.inr ⟨i, hi', h⟩)
    · exact Or.inr (Or.inr ⟨i, hi', h⟩)

theorem free_bound (C : AndCountCircuit 14) (h : Separates C) (x : Fin 7) :
    4 ≤ (Free C (castX x)).card := by
  let code (a : Fin 9) (i : ↥(Free C (castX x))) := sideL C (rows (through x a)) i
  have hinj : Function.Injective code := by
    intro a b hab
    by_contra hne
    obtain ⟨w, hwa, hwb⟩ := rowDiff x a b hne
    let A := rows (through x a)
    let B := rows (through x b)
    have ha := h (through x a)
    have hb := h (through x b)
    have he := mergeInput C A B (insert w B) (castX x) (rowContains x a) (rowContains x b)
      (Finset.insert_subset (Finset.mem_union_left B hwa) Finset.subset_union_right)
      (fun i hi => congrFun hab ⟨i, hi⟩) (hb.2 w hwb)
    dsimp only [A, B] at he
    simp [ha.1, hb.1] at he
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hc
  by_contra! hbad
  have hp : 2 ^ (Free C (castX x)).card ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem bare_out_empty (C : AndCountCircuit 14) (h : Separates C) (v : V) : v ∉ C.outVars := by
  intro hv
  rcases coverXY v with h0 | h36
  · have he := (h 0).1
    have ht : C.eval (rows 0) = true := decide_eq_true (Or.inl ⟨v, hv, h0⟩)
    simp [he] at ht
  · have he := (h 36).1
    have ht : C.eval (rows 36) = true := decide_eq_true (Or.inl ⟨v, hv, h36⟩)
    simp [he] at ht

def litSet (C : AndCountCircuit 14) (v : V) : Finset (Fin C.size × Bool) :=
  Finset.univ.filter (fun p => if p.2 then v ∈ C.rightVars p.1 else v ∈ C.leftVars p.1)

theorem mem_litSet (C : AndCountCircuit 14) (v : V) (g : Fin C.size) (b : Bool) :
    (g, b) ∈ litSet C v ↔ if b then v ∈ C.rightVars g else v ∈ C.leftVars g := by
  simp [litSet]

theorem litSet_disj (C : AndCountCircuit 14) (hdisj : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (v : V) (g : Fin C.size) : ¬ ((g, false) ∈ litSet C v ∧ (g, true) ∈ litSet C v) := by
  rintro ⟨hl, hr⟩
  rw [mem_litSet] at hl hr
  exact Finset.disjoint_left.mp (hdisj g) hl hr

theorem litSet_card_le (C : AndCountCircuit 14) (h : Separates C)
    (hdisj : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (hsz : C.size ≤ 6) (x : Fin 7) :
    (litSet C (castX x)).card ≤ 2 := by
  have hinj : Set.InjOn Prod.fst (litSet C (castX x) : Set (Fin C.size × Bool)) := by
    intro p1 hp1 p2 hp2 heq
    rcases p1 with ⟨g1, b1⟩
    rcases p2 with ⟨g2, b2⟩
    dsimp at heq
    subst heq
    cases b1 <;> cases b2
    · rfl
    · exact (litSet_disj C hdisj (castX x) g1 ⟨hp1, hp2⟩).elim
    · exact (litSet_disj C hdisj (castX x) g1 ⟨hp2, hp1⟩).elim
    · rfl
  have hcard : (litSet C (castX x)).card = ((litSet C (castX x)).image Prod.fst).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hsub : (litSet C (castX x)).image Prod.fst ⊆ Finset.univ \ Free C (castX x) := by
    intro g hg
    obtain ⟨⟨g', b⟩, hb, rfl⟩ := Finset.mem_image.mp hg
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Free, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not]
    rw [mem_litSet] at hb
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  have hle := Finset.card_le_card hsub
  have htot := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Free C (castX x)))
  have hfb := free_bound C h x
  simp only [Finset.card_univ, Fintype.card_fin] at htot
  omega

theorem mis_cover (C : AndCountCircuit 14) (h : Separates C) (r : Fin 37) :
    ∃ f : Fin C.size → Option Bool,
      (∀ v ∈ rows r, ∀ l ∈ litSet C v, f l.1 ≠ some l.2) ∧
      (∀ w : V, w ∉ rows r → ∃ l ∈ litSet C w, f l.1 = some l.2) := by
  let I := rows r
  let f : Fin C.size → Option Bool := fun i =>
    if sideL C I i = false then some false
    else if sideR C I i = false then some true
    else none
  refine ⟨f, ?_, ?_⟩
  · intro v hv l hl
    rcases l with ⟨g, b⟩
    rw [mem_litSet] at hl
    cases b
    · have hsL : sideL C I g = true := decide_eq_true (Or.inl ⟨v, hl, hv⟩)
      simp only [f, hsL, Bool.true_eq_false, ↓reduceIte]
      split_ifs <;> simp
    · have hsR : sideR C I g = true := decide_eq_true (Or.inl ⟨v, hl, hv⟩)
      simp only [f, hsR, Bool.true_eq_false, ↓reduceIte]
      split_ifs <;> simp
  · intro w hw
    have hev : C.eval (insert w I) = true := (h r).2 w hw
    have hfl : C.eval I = false := (h r).1
    let S : Finset (Fin C.size) :=
      Finset.univ.filter (fun i => C.gateVal I i = false ∧ C.gateVal (insert w I) i = true)
    have hSne : S.Nonempty := by
      rw [eval, decide_eq_true_eq] at hev
      rcases hev with ⟨v, hv, _⟩ | ⟨i, hi, hit⟩
      · exact (bare_out_empty C h v hv).elim
      · refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hit⟩⟩
        rw [Bool.eq_false_iff]
        intro hti
        have het : C.eval I = true := decide_eq_true (Or.inr ⟨i, hi, hti⟩)
        simp [hfl] at het
    let g := S.min' hSne
    have hgS : g ∈ S := S.min'_mem hSne
    have hgF : C.gateVal I g = false := (Finset.mem_filter.mp hgS).2.1
    have hgT : C.gateVal (insert w I) g = true := (Finset.mem_filter.mp hgS).2.2
    have hmin : ∀ j : Fin C.size, j < g → C.gateVal (insert w I) j = true → C.gateVal I j = true := by
      intro j hj hjt
      by_contra hnf
      have hjf : C.gateVal I j = false := Bool.eq_false_iff.mpr hnf
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjf, hjt⟩
      exact (not_le_of_gt hj) (S.min'_le j hjS)
    rw [gateVal_unfold C (insert w I) g, Bool.and_eq_true] at hgT
    rw [gateVal_unfold C I g] at hgF
    change (sideL C I g && sideR C I g) = false at hgF
    change sideL C (insert w I) g = true ∧ sideR C (insert w I) g = true at hgT
    by_cases hL : sideL C I g = false
    · refine ⟨(g, false), ?_, by simp [f, hL]⟩
      rw [mem_litSet]
      have hLT : sideL C (insert w I) g = true := hgT.1
      unfold sideL sideTrue at hLT hL
      rw [decide_eq_true_eq] at hLT
      rcases hLT with ⟨v, hv, hvI⟩ | ⟨j, hj, hji, hjt⟩
      · rcases Finset.mem_insert.mp hvI with rfl | hvi
        · exact hv
        · have ht : decide ((∃ u ∈ C.leftVars g, u ∈ I) ∨ ∃ j ∈ C.leftGates g, j < g ∧ C.gateVal I j = true) = true :=
            decide_eq_true (Or.inl ⟨v, hv, hvi⟩)
          simp [hL] at ht
      · have hjiT := hmin j hji hjt
        have ht : decide ((∃ u ∈ C.leftVars g, u ∈ I) ∨ ∃ j ∈ C.leftGates g, j < g ∧ C.gateVal I j = true) = true :=
          decide_eq_true (Or.inr ⟨j, hj, hji, hjiT⟩)
        simp [hL] at ht
    · have hLt : sideL C I g = true := by cases h' : sideL C I g <;> simp_all
      have hR : sideR C I g = false := by simp [hLt] at hgF; exact hgF
      refine ⟨(g, true), ?_, by simp [f, hLt, hR]⟩
      rw [mem_litSet]
      have hRT : sideR C (insert w I) g = true := hgT.2
      unfold sideR sideTrue at hRT hR
      rw [decide_eq_true_eq] at hRT
      rcases hRT with ⟨v, hv, hvI⟩ | ⟨j, hj, hji, hjt⟩
      · rcases Finset.mem_insert.mp hvI with rfl | hvi
        · exact hv
        · have ht : decide ((∃ u ∈ C.rightVars g, u ∈ I) ∨ ∃ j ∈ C.rightGates g, j < g ∧ C.gateVal I j = true) = true :=
            decide_eq_true (Or.inl ⟨v, hv, hvi⟩)
          simp [hR] at ht
      · have hjiT := hmin j hji hjt
        have ht : decide ((∃ u ∈ C.rightVars g, u ∈ I) ∨ ∃ j ∈ C.rightGates g, j < g ∧ C.gateVal I j = true) = true :=
          decide_eq_true (Or.inr ⟨j, hj, hji, hjiT⟩)
        simp [hR] at ht

lemma reflTransGen_exit {α : Type*} {r : α → α → Prop} {S : Finset α} {a b : α}
    (ha : a ∈ S) (hb : b ∉ S) (h : Relation.ReflTransGen r a b) :
    ∃ x ∈ S, ∃ y, y ∉ S ∧ r x y := by
  induction h with
  | refl => exact (hb ha).elim
  | tail h1 hr ih =>
    rename_i y z
    by_cases hy : y ∈ S
    · exact ⟨y, hy, z, hb, hr⟩
    · exact ih hy

lemma connected_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (E : Finset β) (ends : β → Finset α)
    (hVne : V.Nonempty)
    (hends : ∀ e ∈ E, ends e ⊆ V ∧ (ends e).card ≤ 2)
    (hconn : ∀ u ∈ V, ∀ v ∈ V,
      Relation.ReflTransGen (fun a b => ∃ e ∈ E, a ∈ ends e ∧ b ∈ ends e) u v) :
    V.card ≤ E.card + 1 := by
  classical
  let GoodSF (S : Finset α) (F : Finset β) : Prop :=
    S ⊆ V ∧ S.Nonempty ∧ F ⊆ E ∧ S.card ≤ F.card + 1 ∧ ∀ e ∈ F, ends e ⊆ S
  let cands := V.powerset.filter (fun S => ∃ F : Finset β, GoodSF S F)
  obtain ⟨v0, hv0⟩ := hVne
  have hcne : cands.Nonempty := by
    refine ⟨{v0}, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hv0), ∅, ?_⟩⟩
    exact ⟨Finset.singleton_subset_iff.mpr hv0, Finset.singleton_nonempty v0, Finset.empty_subset E, by simp, fun e he => (Finset.notMem_empty e he).elim⟩
  obtain ⟨S, hSc, hmax⟩ := cands.exists_max_image Finset.card hcne
  obtain ⟨F, hSV, ⟨s0, hs0⟩, hFE, hcard, hcl⟩ := (Finset.mem_filter.mp hSc).2
  by_cases hfull : S = V
  · rw [← hfull]
    have hFle := Finset.card_le_card hFE
    omega
  · have hdiff : (V \ S).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
      exact hfull (Finset.Subset.antisymm hSV hne)
    obtain ⟨w, hw⟩ := hdiff
    obtain ⟨hwV, hwS⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨a, haS, b, hbS, e, heE, hae, hbe⟩ :=
      reflTransGen_exit hs0 hwS (hconn s0 (hSV hs0) w hwV)
    have hbV : b ∈ V := (hends e heE).1 hbe
    have heF : e ∉ F := fun h => hbS (hcl e h hbe)
    have hends_sub : ends e ⊆ insert b S := by
      intro x hx
      have hne : a ≠ b := fun h => hbS (h ▸ haS)
      have hsub2 : ({a, b} : Finset α) ⊆ ends e := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hcard2 : ({a, b} : Finset α).card = 2 := Finset.card_pair hne
      have heq : ({a, b} : Finset α) = ends e :=
        Finset.eq_of_subset_of_card_le hsub2 (by linarith [(hends e heE).2])
      rw [← heq] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_insert_of_mem haS
      · exact Finset.mem_insert_self _ S
    have hgood' : GoodSF (insert b S) (insert e F) := by
      refine ⟨Finset.insert_subset hbV hSV, ⟨b, Finset.mem_insert_self b S⟩,
        Finset.insert_subset heE hFE, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hbS, Finset.card_insert_of_notMem heF]
        omega
      · intro e' he'
        rcases Finset.mem_insert.mp he' with rfl | he'F
        · exact hends_sub
        · exact (hcl e' he'F).trans (Finset.subset_insert b S)
    have hmem' : insert b S ∈ cands :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hgood'.1, insert e F, hgood'⟩
    have hle := hmax (insert b S) hmem'
    rw [Finset.card_insert_of_notMem hbS] at hle
    omega

theorem no_cover_gt {α β : Type*} [DecidableEq α] [DecidableEq β] :
    ∀ (n : ℕ) (G : Finset α) (X : Finset β) (s : β → Finset (α × Bool)),
      G.card = n →
      G.card < X.card →
      (∀ x ∈ X, (s x).card ≤ 2) →
      (∀ x ∈ X, ∀ l ∈ s x, l.1 ∈ G) →
      (∀ x ∈ X, ∀ g : α, ¬ ((g, false) ∈ s x ∧ (g, true) ∈ s x)) →
      (∀ P ⊆ X, P.card ≤ 2 → ∃ f : α → Option Bool,
        (∀ x ∈ P, ∀ l ∈ s x, f l.1 ≠ some l.2) ∧
        (∀ w ∈ X \ P, ∃ l ∈ s w, f l.1 = some l.2)) →
      False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G X s hGn hlt hcard2 hsubG hdisj hcov
    classical
    let Vl (l : α × Bool) : Finset β := X.filter (fun x => l ∈ s x)
    let privLits (x : β) : Finset (α × Bool) := (s x).filter (fun l => (Vl l).card = 1)
    have hpriv_ne : ∀ x ∈ X, (privLits x).Nonempty := by
      intro x hx
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hnotpriv : ∀ l ∈ s x, ∃ u ∈ X, u ≠ x ∧ l ∈ s u := by
        intro l hl
        have hxl : x ∈ Vl l := Finset.mem_filter.mpr ⟨hx, hl⟩
        have hne1 : (Vl l).card ≠ 1 := by
          intro h1
          have : l ∈ privLits x := Finset.mem_filter.mpr ⟨hl, h1⟩
          rw [hne] at this
          exact Finset.notMem_empty l this
        have hge2 : 2 ≤ (Vl l).card := by
          have hpos : 0 < (Vl l).card := Finset.card_pos.mpr ⟨x, hxl⟩
          omega
        obtain ⟨u, hu, hux⟩ := Finset.exists_mem_ne (by omega : 1 < (Vl l).card) x
        exact ⟨u, (Finset.mem_filter.mp hu).1, hux, (Finset.mem_filter.mp hu).2⟩
      let pickU (l : α × Bool) : β :=
        if h : l ∈ s x then (hnotpriv l h).choose else x
      let P : Finset β := (s x).image pickU
      have hPX : P ⊆ X := by
        intro u hu
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
        simp only [pickU, hl, ↓reduceDIte]
        exact (hnotpriv l hl).choose_spec.1
      have hxP : x ∉ P := by
        intro hx'
        obtain ⟨l, hl, heq⟩ := Finset.mem_image.mp hx'
        simp only [pickU, hl, ↓reduceDIte] at heq
        exact (hnotpriv l hl).choose_spec.2.1 heq
      have hPcard : P.card ≤ 2 := (Finset.card_image_le).trans (hcard2 x hx)
      obtain ⟨f, hfav, hfhit⟩ := hcov P hPX hPcard
      obtain ⟨l, hl, hfl⟩ := hfhit x (Finset.mem_sdiff.mpr ⟨hx, hxP⟩)
      have huP : pickU l ∈ P := Finset.mem_image_of_mem pickU hl
      have hlu : l ∈ s (pickU l) := by
        simp only [pickU, hl, ↓reduceDIte]
        exact (hnotpriv l hl).choose_spec.2.2
      exact hfav (pickU l) huP l hlu hfl
    have hpriv_unique : ∀ {x y : β} {l : α × Bool}, x ∈ X → y ∈ X →
        l ∈ privLits x → l ∈ s y → y = x := by
      intro x y l hx hy hlx hly
      have h1 : (Vl l).card = 1 := (Finset.mem_filter.mp hlx).2
      have hxl : x ∈ Vl l := Finset.mem_filter.mpr ⟨hx, (Finset.mem_filter.mp hlx).1⟩
      have hyl : y ∈ Vl l := Finset.mem_filter.mpr ⟨hy, hly⟩
      exact Finset.card_le_one.mp (le_of_eq h1) y hyl x hxl
    let adjH (x y : β) : Prop :=
      x ∈ X ∧ y ∈ X ∧ ∃ g : α, (∃ b : Bool, (g, b) ∈ privLits x) ∧ (∃ b' : Bool, (g, b') ∈ privLits y)
    let eqH : β → β → Prop := Relation.ReflTransGen adjH
    have heqH_symm : ∀ {x y : β}, eqH x y → eqH y x := by
      intro x y h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        obtain ⟨hxX, hyX, g, hx, hy⟩ := hstep
        exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single ⟨hyX, hxX, g, hy, hx⟩) ih
    let comp (x : β) : Finset β := X.filter (fun y => eqH x y)
    let gatesOf (C : Finset β) : Finset α := C.biUnion (fun x => (privLits x).image Prod.fst)
    let comps : Finset (Finset β) := X.image comp
    have hcomp_disj : Set.PairwiseDisjoint (comps : Set (Finset β)) id := by
      intro C1 hC1 C2 hC2 hne
      obtain ⟨x1, hx1, rfl⟩ := Finset.mem_image.mp hC1
      obtain ⟨x2, hx2, rfl⟩ := Finset.mem_image.mp hC2
      rw [Function.onFun, id_eq, Finset.disjoint_left]
      intro y hy1 hy2
      apply hne
      ext z
      simp only [comp, Finset.mem_filter]
      have h1 : eqH x1 y := (Finset.mem_filter.mp hy1).2
      have h2 : eqH x2 y := (Finset.mem_filter.mp hy2).2
      have h12 : eqH x1 x2 := Relation.ReflTransGen.trans h1 (heqH_symm h2)
      exact and_congr_right (fun _ => ⟨fun h => Relation.ReflTransGen.trans (heqH_symm h12) h,
        fun h => Relation.ReflTransGen.trans h12 h⟩)
    have hcomp_union : comps.biUnion id = X := by
      ext y
      simp only [Finset.mem_biUnion, id_eq, comps, Finset.mem_image]
      constructor
      · rintro ⟨C, ⟨x, _, rfl⟩, hy⟩
        exact (Finset.mem_filter.mp hy).1
      · intro hy
        exact ⟨comp y, ⟨y, hy, rfl⟩, Finset.mem_filter.mpr ⟨hy, Relation.ReflTransGen.refl⟩⟩
    have hgates_disj : Set.PairwiseDisjoint (comps : Set (Finset β)) gatesOf := by
      intro C1 hC1 C2 hC2 hne
      obtain ⟨x1, hx1, rfl⟩ := Finset.mem_image.mp hC1
      obtain ⟨x2, hx2, rfl⟩ := Finset.mem_image.mp hC2
      rw [Function.onFun, Finset.disjoint_left]
      intro g hg1 hg2
      obtain ⟨y1, hy1, hg1'⟩ := Finset.mem_biUnion.mp hg1
      obtain ⟨y2, hy2, hg2'⟩ := Finset.mem_biUnion.mp hg2
      obtain ⟨⟨g1, b1⟩, hb1, heq1⟩ := Finset.mem_image.mp hg1'
      obtain ⟨⟨g2, b2⟩, hb2, heq2⟩ := Finset.mem_image.mp hg2'
      dsimp at heq1 heq2
      subst heq1
      subst heq2
      have hadj : adjH y1 y2 :=
        ⟨(Finset.mem_filter.mp hy1).1, (Finset.mem_filter.mp hy2).1, g2, ⟨b1, hb1⟩, ⟨b2, hb2⟩⟩
      have h12 : eqH x1 x2 :=
        Relation.ReflTransGen.trans ((Finset.mem_filter.mp hy1).2)
          (Relation.ReflTransGen.trans (Relation.ReflTransGen.single hadj)
            (heqH_symm (Finset.mem_filter.mp hy2).2))
      apply hne
      ext z
      simp only [comp, Finset.mem_filter]
      exact and_congr_right (fun _ => ⟨fun h => Relation.ReflTransGen.trans (heqH_symm h12) h,
        fun h => Relation.ReflTransGen.trans h12 h⟩)
    have hgates_sub : comps.biUnion gatesOf ⊆ G := by
      intro g hg
      obtain ⟨C, hC, hgC⟩ := Finset.mem_biUnion.mp hg
      obtain ⟨x, hxC, hgx⟩ := Finset.mem_biUnion.mp hgC
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hgx
      obtain ⟨x0, _, rfl⟩ := Finset.mem_image.mp hC
      exact hsubG x (Finset.mem_filter.mp hxC).1 l (Finset.mem_filter.mp hl).1
    have hsumG : ∑ C ∈ comps, (gatesOf C).card ≤ G.card := by
      rw [← Finset.card_biUnion hgates_disj]
      exact Finset.card_le_card hgates_sub
    have hsumX : ∑ C ∈ comps, C.card = X.card := by
      conv_rhs => rw [← hcomp_union]
      rw [Finset.card_biUnion hcomp_disj]
      simp
    have hexC : ∃ C ∈ comps, (gatesOf C).card < C.card := by
      by_contra hall
      push Not at hall
      have hle : ∑ C ∈ comps, C.card ≤ ∑ C ∈ comps, (gatesOf C).card :=
        Finset.sum_le_sum (fun C hC => hall C hC)
      omega
    obtain ⟨C, hCmem, hClt⟩ := hexC
    obtain ⟨x0, hx0, hCeq⟩ := Finset.mem_image.mp hCmem
    have hCX : C ⊆ X := by
      rw [← hCeq]
      exact Finset.filter_subset _ _
    have hCne : C.Nonempty := by
      rw [← hCeq]
      exact ⟨x0, Finset.mem_filter.mpr ⟨hx0, Relation.ReflTransGen.refl⟩⟩
    let VC : Finset α := gatesOf C
    let C1 : Finset β := C.filter (fun x => (privLits x).card = 1)
    let C2 : Finset β := C.filter (fun x => (privLits x).card = 2)
    have hpriv_le2 : ∀ x ∈ C, (privLits x).card ≤ 2 := fun x hx =>
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (hcard2 x (hCX hx))
    have hpriv_12 : ∀ x ∈ C, (privLits x).card = 1 ∨ (privLits x).card = 2 := by
      intro x hx
      have hpos : 1 ≤ (privLits x).card := Finset.card_pos.mpr (hpriv_ne x (hCX hx))
      have hle := hpriv_le2 x hx
      omega
    have hC_split : C1.card + C2.card = C.card := by
      have hdisj12 : Disjoint C1 C2 := by
        rw [Finset.disjoint_left]
        intro x h1 h2
        have a := (Finset.mem_filter.mp h1).2
        have b := (Finset.mem_filter.mp h2).2
        omega
      have hunion12 : C1 ∪ C2 = C := by
        ext x
        simp only [Finset.mem_union, C1, C2, Finset.mem_filter]
        constructor
        · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        · intro hx
          rcases hpriv_12 x hx with h1 | h2
          · exact Or.inl ⟨hx, h1⟩
          · exact Or.inr ⟨hx, h2⟩
      rw [← Finset.card_union_of_disjoint hdisj12, hunion12]
    have hpriv_disj : Set.PairwiseDisjoint (C : Set β) privLits := by
      intro x hx y hy hxy
      rw [Function.onFun, Finset.disjoint_left]
      intro l hlx hly
      exact hxy (hpriv_unique (hCX hy) (hCX hx) hly (Finset.mem_filter.mp hlx).1)
    have hpriv_biUnion_sub : C.biUnion privLits ⊆ VC ×ˢ (Finset.univ : Finset Bool) := by
      intro l hl
      obtain ⟨x, hx, hlx⟩ := Finset.mem_biUnion.mp hl
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨l, hlx, rfl⟩⟩
    have hsum_priv : C1.card + 2 * C2.card = (C.biUnion privLits).card := by
      rw [Finset.card_biUnion hpriv_disj]
      have h1 : ∑ x ∈ C1, (privLits x).card = C1.card := by
        calc ∑ x ∈ C1, (privLits x).card = ∑ _x ∈ C1, 1 :=
              Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2)
          _ = C1.card := by simp
      have h2 : ∑ x ∈ C2, (privLits x).card = 2 * C2.card := by
        calc ∑ x ∈ C2, (privLits x).card = ∑ _x ∈ C2, 2 :=
              Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2)
          _ = 2 * C2.card := by simp [mul_comm]
      have hdisj12 : Disjoint C1 C2 := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        have a := (Finset.mem_filter.mp hx1).2
        have b := (Finset.mem_filter.mp hx2).2
        omega
      have hunion12 : C1 ∪ C2 = C := by
        ext x
        simp only [Finset.mem_union, C1, C2, Finset.mem_filter]
        constructor
        · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        · intro hx
          rcases hpriv_12 x hx with h1' | h2'
          · exact Or.inl ⟨hx, h1'⟩
          · exact Or.inr ⟨hx, h2'⟩
      rw [← hunion12, Finset.sum_union hdisj12, h1, h2]
    have hpriv_upper : C1.card + 2 * C2.card ≤ 2 * VC.card := by
      rw [hsum_priv]
      calc (C.biUnion privLits).card ≤ (VC ×ˢ (Finset.univ : Finset Bool)).card :=
            Finset.card_le_card hpriv_biUnion_sub
        _ = VC.card * 2 := by simp
        _ = 2 * VC.card := by ring
    have hVC_ne : VC.Nonempty := by
      obtain ⟨x, hx⟩ := hCne
      obtain ⟨l, hl⟩ := hpriv_ne x (hCX hx)
      exact ⟨l.1, Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩⟩
    have hVC_conn : VC.card ≤ C2.card + 1 := by
      let ends (x : β) : Finset α := (privLits x).image Prod.fst
      apply connected_card_le VC C2 ends hVC_ne
      · intro x hx
        have hxC : x ∈ C := (Finset.mem_filter.mp hx).1
        refine ⟨?_, (Finset.card_image_le).trans (hpriv_le2 x hxC)⟩
        intro g hg
        exact Finset.mem_biUnion.mpr ⟨x, hxC, hg⟩
      · have hsame_x : ∀ x ∈ C, ∀ g1 ∈ ends x, ∀ g2 ∈ ends x,
            Relation.ReflTransGen (fun a b => ∃ e ∈ C2, a ∈ ends e ∧ b ∈ ends e) g1 g2 := by
          intro x hx g1 hg1 g2 hg2
          by_cases h12 : g1 = g2
          · subst h12; exact Relation.ReflTransGen.refl
          · apply Relation.ReflTransGen.single
            refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, hg1, hg2⟩
            have hge2 : 2 ≤ (ends x).card := by
              have hsub : ({g1, g2} : Finset α) ⊆ ends x := by
                intro z hz
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl <;> assumption
              calc 2 = ({g1, g2} : Finset α).card := (Finset.card_pair h12).symm
                _ ≤ (ends x).card := Finset.card_le_card hsub
            have hle' : (ends x).card ≤ (privLits x).card := Finset.card_image_le
            have hp := hpriv_le2 x hx
            omega
        intro u hu v hv
        obtain ⟨xu, hxu, hgu⟩ := Finset.mem_biUnion.mp hu
        obtain ⟨xv, hxv, hgv⟩ := Finset.mem_biUnion.mp hv
        have heq_uv : eqH xu xv := by
          rw [← hCeq] at hxu hxv
          exact Relation.ReflTransGen.trans (heqH_symm (Finset.mem_filter.mp hxu).2)
            (Finset.mem_filter.mp hxv).2
        have walk : ∀ {y z : β}, y ∈ C → z ∈ C → eqH y z →
            ∀ gy ∈ ends y, ∀ gz ∈ ends z,
              Relation.ReflTransGen (fun a b => ∃ e ∈ C2, a ∈ ends e ∧ b ∈ ends e) gy gz := by
          intro y z hy hz heq
          induction heq with
          | refl => exact fun gy hgy gz hgz => hsame_x y hy gy hgy gz hgz
          | tail h1 hstep ih =>
            rename_i w t
            intro gy hgy gt hgt
            obtain ⟨hwX, _, gm, ⟨bm, hbm⟩, ⟨bt, hbt⟩⟩ := hstep
            have hwC : w ∈ C := by
              rw [← hCeq] at hy ⊢
              exact Finset.mem_filter.mpr ⟨hwX,
                Relation.ReflTransGen.trans (Finset.mem_filter.mp hy).2 h1⟩
            exact Relation.ReflTransGen.trans
              (ih hwC gy hgy gm (Finset.mem_image.mpr ⟨(gm, bm), hbm, rfl⟩))
              (hsame_x t hz gm (Finset.mem_image.mpr ⟨(gm, bt), hbt, rfl⟩) gt hgt)
        exact walk hxu hxv heq_uv u hgu v hgv
    have hVClt : VC.card < C.card := hClt
    have hC1_eq2 : C1.card = 2 := by omega
    have hC_eq : C.card = VC.card + 1 := by omega
    have hpriv_full : C.biUnion privLits = VC ×ˢ (Finset.univ : Finset Bool) := by
      apply Finset.eq_of_subset_of_card_le hpriv_biUnion_sub
      rw [← hsum_priv]
      simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool]
      omega
    have hVC_only_C : ∀ x ∈ X, ∀ l ∈ s x, l.1 ∈ VC → x ∈ C := by
      intro x hx l hl hg
      have hlmem : l ∈ C.biUnion privLits := by
        rw [hpriv_full]
        exact Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩
      obtain ⟨y, hyC, hly⟩ := Finset.mem_biUnion.mp hlmem
      rw [hpriv_unique (hCX hyC) hx hly hl]
      exact hyC
    have hC2_only_priv : ∀ x ∈ C2, ∀ l ∈ s x, l ∈ privLits x := by
      intro x hx l hl
      have heq : privLits x = s x := by
        apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        rw [(Finset.mem_filter.mp hx).2]
        exact hcard2 x (hCX (Finset.mem_filter.mp hx).1)
      rw [heq]
      exact hl
    have hno_priv_cover : ∀ f : α → Option Bool,
        (∀ w ∈ C, ∃ l ∈ privLits w, f l.1 = some l.2) → False := by
      intro f hf
      choose lp hlp hflp using fun (w : ↥C) => hf w.1 w.2
      let phi (w : ↥C) : ↥VC :=
        ⟨(lp w).1, Finset.mem_biUnion.mpr ⟨w.1, w.2, Finset.mem_image.mpr ⟨lp w, hlp w, rfl⟩⟩⟩
      have hinj : Function.Injective phi := by
        intro w1 w2 heq
        have hg : (lp w1).1 = (lp w2).1 := congrArg Subtype.val heq
        have hb : (lp w1).2 = (lp w2).2 := by
          have h1 := hflp w1
          have h2 := hflp w2
          rw [hg] at h1
          exact Option.some.inj (h1.symm.trans h2)
        have hleq : lp w1 = lp w2 := Prod.ext hg hb
        apply Subtype.ext
        exact hpriv_unique (hCX w2.2) (hCX w1.2) (hlp w2)
          (hleq ▸ (Finset.mem_filter.mp (hlp w1)).1)
      have hc := Fintype.card_le_of_injective phi hinj
      simp only [Fintype.card_coe] at hc
      omega
    obtain ⟨a, b, hab, hC1ab⟩ := Finset.card_eq_two.mp hC1_eq2
    have haC1 : a ∈ C1 := by rw [hC1ab]; simp
    have hbC1 : b ∈ C1 := by rw [hC1ab]; simp
    have haC : a ∈ C := (Finset.mem_filter.mp haC1).1
    have hbC : b ∈ C := (Finset.mem_filter.mp hbC1).1
    have hC_cases : ∀ w ∈ C, w = a ∨ w = b ∨ w ∈ C2 := by
      intro w hw
      rcases hpriv_12 w hw with h1 | h2
      · have hw1 : w ∈ C1 := Finset.mem_filter.mpr ⟨hw, h1⟩
        rw [hC1ab, Finset.mem_insert, Finset.mem_singleton] at hw1
        rcases hw1 with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hw, h2⟩))
    have hnonpriv_card : ∀ x ∈ C1, ((s x) \ privLits x).card ≤ 1 := by
      intro x hx
      have h1 : (privLits x).card = 1 := (Finset.mem_filter.mp hx).2
      have hsub : privLits x ⊆ s x := Finset.filter_subset _ _
      have htot := Finset.card_sdiff_add_card_eq_card hsub
      have hle := hcard2 x (hCX (Finset.mem_filter.mp hx).1)
      omega
    by_cases hcase2 : ∃ q : α × Bool, q ∈ (s a) \ privLits a ∧ ∀ u ∈ X \ C, q ∉ s u
    · obtain ⟨q, hqa, hqno⟩ := hcase2
      have hqa_s : q ∈ s a := (Finset.mem_sdiff.mp hqa).1
      have hqa_np : q ∉ privLits a := (Finset.mem_sdiff.mp hqa).2
      have hq_ge2 : 2 ≤ (Vl q).card := by
        have hpos : 0 < (Vl q).card :=
          Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨hCX haC, hqa_s⟩⟩
        have hne1 : (Vl q).card ≠ 1 := fun h1 =>
          hqa_np (Finset.mem_filter.mpr ⟨hqa_s, h1⟩)
        omega
      obtain ⟨y, hyq, hya⟩ := Finset.exists_mem_ne (by omega : 1 < (Vl q).card) a
      have hyX : y ∈ X := (Finset.mem_filter.mp hyq).1
      have hqy : q ∈ s y := (Finset.mem_filter.mp hyq).2
      have hyC : y ∈ C := by
        by_contra hyn
        exact hqno y (Finset.mem_sdiff.mpr ⟨hyX, hyn⟩) hqy
      have hyb : y = b := by
        rcases hC_cases y hyC with rfl | rfl | hy2
        · exact (hya rfl).elim
        · rfl
        · have hqp := hC2_only_priv y hy2 q hqy
          have h1 : (Vl q).card = 1 := (Finset.mem_filter.mp hqp).2
          omega
      subst y
      have hqb_np : q ∉ privLits b := fun hp => by
        have h1 : (Vl q).card = 1 := (Finset.mem_filter.mp hp).2
        omega
      have hqb_diff : q ∈ (s b) \ privLits b := Finset.mem_sdiff.mpr ⟨hqy, hqb_np⟩
      have hqa_only : (s a) \ privLits a = {q} :=
        (Finset.eq_singleton_iff_unique_mem.mpr ⟨hqa, fun l hl =>
          Finset.card_le_one.mp (hnonpriv_card a haC1) l hl q hqa⟩)
      have hqb_only : (s b) \ privLits b = {q} :=
        (Finset.eq_singleton_iff_unique_mem.mpr ⟨hqb_diff, fun l hl =>
          Finset.card_le_one.mp (hnonpriv_card b hbC1) l hl q hqb_diff⟩)
      have hq_not_VC : q.1 ∉ VC := by
        intro hqV
        have hmem : q ∈ C.biUnion privLits := by
          rw [hpriv_full]
          exact Finset.mem_product.mpr ⟨hqV, Finset.mem_univ _⟩
        obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.mp hmem
        have h1 : (Vl q).card = 1 := (Finset.mem_filter.mp hz).2
        omega
      have hqG : q.1 ∈ G := hsubG a (hCX haC) q hqa_s
      have hVC_sub_G : VC ⊆ G := by
        intro g hg
        obtain ⟨z, hzC, hgz⟩ := Finset.mem_biUnion.mp hg
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hgz
        exact hsubG z (hCX hzC) l (Finset.mem_filter.mp hl).1
      let G' : Finset α := G \ insert q.1 VC
      let X' : Finset β := X \ C
      let oppq : α × Bool := (q.1, !q.2)
      let s' (x : β) : Finset (α × Bool) := (s x).erase oppq
      have hrm_sub : insert q.1 VC ⊆ G := Finset.insert_subset hqG hVC_sub_G
      have hrm_card : (insert q.1 VC).card = VC.card + 1 := Finset.card_insert_of_notMem hq_not_VC
      have hG'_card : G'.card + (VC.card + 1) = G.card := by
        rw [← hrm_card]
        exact Finset.card_sdiff_add_card_eq_card hrm_sub
      have hX'_card : X'.card + (VC.card + 1) = X.card := by
        rw [← hC_eq]
        exact Finset.card_sdiff_add_card_eq_card hCX
      have hG'_lt_n : G'.card < n := by omega
      have hG'_lt_X' : G'.card < X'.card := by omega
      refine ih G'.card hG'_lt_n G' X' s' rfl hG'_lt_X' ?_ ?_ ?_ ?_
      · intro x hx
        exact (Finset.card_erase_le).trans (hcard2 x (Finset.mem_sdiff.mp hx).1)
      · intro x hx l hl
        have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
        have hxC : x ∉ C := (Finset.mem_sdiff.mp hx).2
        have hls : l ∈ s x := Finset.mem_of_mem_erase hl
        have hne_opp : l ≠ oppq := (Finset.mem_erase.mp hl).1
        rw [Finset.mem_sdiff]
        refine ⟨hsubG x hxX l hls, ?_⟩
        rw [Finset.mem_insert, not_or]
        refine ⟨?_, fun hlV => hxC (hVC_only_C x hxX l hls hlV)⟩
        intro hlq
        by_cases hlb : l.2 = q.2
        · exact hqno x hx (Prod.ext hlq hlb ▸ hls)
        · have hne_b : l.2 = !q.2 := by
            cases hl2 : l.2 <;> cases hq2 : q.2
            · exact (hlb (hl2.trans hq2.symm)).elim
            · rfl
            · rfl
            · exact (hlb (hl2.trans hq2.symm)).elim
          exact hne_opp (Prod.ext hlq hne_b)
      · intro x hx g ⟨hl, hr⟩
        exact hdisj x (Finset.mem_sdiff.mp hx).1 g
          ⟨Finset.mem_of_mem_erase hl, Finset.mem_of_mem_erase hr⟩
      · intro P hPX' hPcard
        have hPX : P ⊆ X := hPX'.trans Finset.sdiff_subset
        obtain ⟨f, hfav, hfhit⟩ := hcov P hPX hPcard
        have hfq : f q.1 = some q.2 := by
          by_contra hnfq
          apply hno_priv_cover f
          intro w hwC
          have hwP : w ∉ P := fun hw' => (Finset.mem_sdiff.mp (hPX' hw')).2 hwC
          obtain ⟨l, hlw, hfl⟩ := hfhit w (Finset.mem_sdiff.mpr ⟨hCX hwC, hwP⟩)
          by_cases hlp : l ∈ privLits w
          · exact ⟨l, hlp, hfl⟩
          · rcases hC_cases w hwC with rfl | rfl | hw2
            · have hlq : l = q := by
                have := Finset.mem_sdiff.mpr ⟨hlw, hlp⟩
                rw [hqa_only, Finset.mem_singleton] at this
                exact this
              exact (hnfq (hlq ▸ hfl)).elim
            · have hlq : l = q := by
                have := Finset.mem_sdiff.mpr ⟨hlw, hlp⟩
                rw [hqb_only, Finset.mem_singleton] at this
                exact this
              exact (hnfq (hlq ▸ hfl)).elim
            · exact (hlp (hC2_only_priv w hw2 l hlw)).elim
        refine ⟨f, ?_, ?_⟩
        · intro x hx l hl
          exact hfav x hx l (Finset.mem_of_mem_erase hl)
        · intro w hw
          obtain ⟨hwX', hwP⟩ := Finset.mem_sdiff.mp hw
          obtain ⟨l, hlw, hfl⟩ := hfhit w (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hwX').1, hwP⟩)
          refine ⟨l, Finset.mem_erase.mpr ⟨?_, hlw⟩, hfl⟩
          intro hlo
          rw [hlo] at hfl
          simp only [oppq, hfq, Option.some.injEq] at hfl
          cases hqb : q.2 <;> rw [hqb] at hfl <;> simp at hfl
    · push Not at hcase2
      have hb_case : ∀ q ∈ (s b) \ privLits b, ∃ u ∈ X \ C, q ∈ s u := by
        intro q hqb
        by_contra hno
        push Not at hno
        have hqb_s : q ∈ s b := (Finset.mem_sdiff.mp hqb).1
        have hqb_np : q ∉ privLits b := (Finset.mem_sdiff.mp hqb).2
        have hq_ge2 : 2 ≤ (Vl q).card := by
          have hpos : 0 < (Vl q).card :=
            Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hCX hbC, hqb_s⟩⟩
          have hne1 : (Vl q).card ≠ 1 := fun h1 =>
            hqb_np (Finset.mem_filter.mpr ⟨hqb_s, h1⟩)
          omega
        obtain ⟨y, hyq, hyb⟩ := Finset.exists_mem_ne (by omega : 1 < (Vl q).card) b
        have hyX : y ∈ X := (Finset.mem_filter.mp hyq).1
        have hqy : q ∈ s y := (Finset.mem_filter.mp hyq).2
        have hyC : y ∈ C := by
          by_contra hyn
          exact hno y (Finset.mem_sdiff.mpr ⟨hyX, hyn⟩) hqy
        have hya : y = a := by
          rcases hC_cases y hyC with rfl | rfl | hy2
          · rfl
          · exact (hyb rfl).elim
          · have hqp := hC2_only_priv y hy2 q hqy
            have h1 : (Vl q).card = 1 := (Finset.mem_filter.mp hqp).2
            omega
        subst y
        have hqa_np : q ∉ privLits a := fun hp => by
          have h1 : (Vl q).card = 1 := (Finset.mem_filter.mp hp).2
          omega
        obtain ⟨u, hu, hqu⟩ := hcase2 q (Finset.mem_sdiff.mpr ⟨hqy, hqa_np⟩)
        exact hno u hu hqu
      let pa : Finset β := ((s a) \ privLits a).attach.image (fun q => (hcase2 q.1 q.2).choose)
      let pb : Finset β := ((s b) \ privLits b).attach.image (fun q => (hb_case q.1 q.2).choose)
      let P : Finset β := pa ∪ pb
      have hPsub : P ⊆ X \ C := by
        intro u hu
        rcases Finset.mem_union.mp hu with hua | hub
        · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hua
          exact (hcase2 q.1 q.2).choose_spec.1
        · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hub
          exact (hb_case q.1 q.2).choose_spec.1
      have hPcard : P.card ≤ 2 := by
        have ha1 : pa.card ≤ 1 := by
          calc pa.card ≤ ((s a) \ privLits a).attach.card := Finset.card_image_le
            _ = ((s a) \ privLits a).card := Finset.card_attach
            _ ≤ 1 := hnonpriv_card a haC1
        have hb1 : pb.card ≤ 1 := by
          calc pb.card ≤ ((s b) \ privLits b).attach.card := Finset.card_image_le
            _ = ((s b) \ privLits b).card := Finset.card_attach
            _ ≤ 1 := hnonpriv_card b hbC1
        have hu : P.card ≤ pa.card + pb.card := Finset.card_union_le pa pb
        omega
      obtain ⟨f, hfav, hfhit⟩ := hcov P (hPsub.trans Finset.sdiff_subset) hPcard
      apply hno_priv_cover f
      intro w hwC
      have hwP : w ∉ P := fun hw' => (Finset.mem_sdiff.mp (hPsub hw')).2 hwC
      obtain ⟨l, hlw, hfl⟩ := hfhit w (Finset.mem_sdiff.mpr ⟨hCX hwC, hwP⟩)
      by_cases hlp : l ∈ privLits w
      · exact ⟨l, hlp, hfl⟩
      · rcases hC_cases w hwC with rfl | rfl | hw2
        · have hl' : l ∈ (s w) \ privLits w := Finset.mem_sdiff.mpr ⟨hlw, hlp⟩
          have huP : (hcase2 l hl').choose ∈ P :=
            Finset.mem_union_left pb (Finset.mem_image.mpr ⟨⟨l, hl'⟩, Finset.mem_attach _ _, rfl⟩)
          exact (hfav _ huP l (hcase2 l hl').choose_spec.2 hfl).elim
        · have hl' : l ∈ (s w) \ privLits w := Finset.mem_sdiff.mpr ⟨hlw, hlp⟩
          have huP : (hb_case l hl').choose ∈ P :=
            Finset.mem_union_right pa (Finset.mem_image.mpr ⟨⟨l, hl'⟩, Finset.mem_attach _ _, rfl⟩)
          exact (hfav _ huP l (hb_case l hl').choose_spec.2 hfl).elim
        · exact (hlp (hC2_only_priv w hw2 l hlw)).elim

theorem lower (C : AndCountCircuit 14) (h : Separates C) : 7 ≤ C.size := by
  by_contra! hlt
  have hsz : C.size ≤ 6 := by omega
  let D := stripCircuit C
  have hDsep : Separates D := by
    intro r
    simpa only [D, strip_eval_eq] using h r
  have hDsz : D.size ≤ 6 := hsz
  have hDdisj : ∀ i, Disjoint (D.leftVars i) (D.rightVars i) := strip_disjoint C
  apply no_cover_gt D.size (Finset.univ : Finset (Fin D.size)) (Finset.univ : Finset (Fin 7))
    (fun x => litSet D (castX x))
    (by simp) (by simp; omega)
    (fun x _ => litSet_card_le D hDsep hDdisj hDsz x)
    (fun _ _ _ _ => Finset.mem_univ _)
    (fun x _ g => litSet_disj D hDdisj (castX x) g)
  intro P _ hPcard
  have hPex : ∃ r : Fin 37, ∀ z : Fin 7, castX z ∈ rows r ↔ z ∈ P := by
    rcases Finset.eq_empty_or_nonempty P with rfl | ⟨x, hx⟩
    · refine ⟨36, fun z => ?_⟩
      simp [rowEmpty z]
    · by_cases h1 : P = {x}
      · subst h1
        obtain ⟨r, hr⟩ := rowPair x x
        exact ⟨r, fun z => by simpa using hr z⟩
      · have hgt : 1 < P.card := by
          by_contra hle
          have hc1 : P.card = 1 := by
            have := Finset.card_pos.mpr ⟨x, hx⟩
            omega
          obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hc1
          subst hy
          exact h1 (by simp [Finset.mem_singleton.mp hx])
        obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne hgt x
        have hPeq : P = {x, y} := by
          symm
          apply Finset.eq_of_subset_of_card_le
          · intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl <;> assumption
          · rw [Finset.card_pair hyx.symm]
            exact hPcard
        obtain ⟨r, hr⟩ := rowPair x y
        exact ⟨r, fun z => by rw [hr z, hPeq]; simp⟩
  obtain ⟨r, hr⟩ := hPex
  obtain ⟨f, hfav, hfhit⟩ := mis_cover D hDsep r
  refine ⟨f, ?_, ?_⟩
  · intro x hx l hl
    exact hfav (castX x) ((hr x).mpr hx) l hl
  · intro w hw
    have hwP : w ∉ P := (Finset.mem_sdiff.mp hw).2
    exact hfhit (castX w) (fun hmem => hwP ((hr w).mp hmem))

end PEqualNP.Outside.L_meta_910_aux

open PEqualNP.Outside.L_meta_910_aux

theorem PEqualNP.Outside.L_meta_910 :
    ∀ G : SimpleGraph (Fin 14), G = SimpleGraph.fromRel (fun a b : Fin 14 => ((a : ℕ), (b : ℕ)) ∈ ([(7, 0), (7, 1), (7, 3), (8, 1), (8, 2), (8, 4), (9, 2), (9, 3), (9, 5), (10, 3), (10, 4), (10, 6), (11, 4), (11, 5), (11, 0), (12, 5), (12, 6), (12, 1), (13, 6), (13, 0), (13, 2)] : List (ℕ × ℕ))) →
      ∀ C : PEqualNP.AndCount.AndCountCircuit 14, C.WellFormed →
        (∀ I : Finset (Fin 14), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 14, w ∉ I → ∃ a ∈ I, G.Adj a w) →
          C.eval I = false ∧ ∀ w : Fin 14, w ∉ I → C.eval (insert w I) = true) →
        7 ≤ C.size := by
  intro G hG C _ hsep
  apply lower C
  intro r
  have hAdj_iff : ∀ a b : Fin 14, G.Adj a b ↔ hAdj a b = true := by
    intro a b
    rw [hG, SimpleGraph.fromRel_adj, hAdj, decide_eq_true_eq]
    rfl
  have hgood := rowsGood r
  apply hsep (rows r)
  · intro a ha c hc hadj
    have ht := (hAdj_iff a c).mp hadj
    have hf := hgood.1 a ha c hc
    simp [hf] at ht
  · intro w hw
    obtain ⟨a, ha, hadj⟩ := hgood.2 w hw
    exact ⟨a, ha, (hAdj_iff a w).mpr hadj⟩
