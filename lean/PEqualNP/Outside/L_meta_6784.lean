import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6784

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

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
    gateValFuel_indep C U (C.size) i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma sideTrue_mono_U {n k : ℕ} {U V : Finset (Fin n)} (hUV : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue V B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUV hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

private lemma gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

private lemma eval_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) (hU : C.eval U = true) : C.eval V = true := by
  unfold AndCountCircuit.eval at hU ⊢
  rw [decide_eq_true_eq] at hU ⊢
  rcases hU with ⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩
  · exact Or.inl ⟨v, hvO, hUV hvU⟩
  · exact Or.inr ⟨j, hjO, gateValFuel_mono_U C hUV C.size j hjv⟩

private def restrictCircuit {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size)) :
    AndCountCircuit n where
  size := K.card
  leftVars i := C.leftVars (K.orderEmbOfFin rfl i)
  leftGates i := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i))
  rightVars i := C.rightVars (K.orderEmbOfFin rfl i)
  rightGates i := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i))
  outVars := C.outVars
  outGates := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.outGates)

private lemma restrict_mem_leftGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (i j : Fin K.card) :
    j ∈ (restrictCircuit C K).leftGates i ↔
      K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i) := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i)) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_mem_rightGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (i j : Fin K.card) :
    j ∈ (restrictCircuit C K).rightGates i ↔
      K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i) := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i)) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_mem_outGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (j : Fin K.card) :
    j ∈ (restrictCircuit C K).outGates ↔ K.orderEmbOfFin rfl j ∈ C.outGates := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.outGates) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_wf {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (hWF : C.WellFormed) : (restrictCircuit C K).WellFormed := by
  intro i
  constructor
  · intro j hj
    have hj' := (restrict_mem_leftGates C K i j).mp hj
    exact (K.orderEmbOfFin rfl).lt_iff_lt.mp ((hWF (K.orderEmbOfFin rfl i)).1 _ hj')
  · intro j hj
    have hj' := (restrict_mem_rightGates C K i j).mp hj
    exact (K.orderEmbOfFin rfl).lt_iff_lt.mp ((hWF (K.orderEmbOfFin rfl i)).2 _ hj')

private lemma restrict_gateVal_le {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin K.card), i.val < m →
      (restrictCircuit C K).gateVal U i = true →
        C.gateVal U (K.orderEmbOfFin rfl i) = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    rw [gateVal_unfold (restrictCircuit C K) U i, Bool.and_eq_true] at hval
    rw [gateVal_unfold C U, Bool.and_eq_true]
    constructor
    · have hL := hval.1
      unfold sideTrue at hL ⊢
      rw [decide_eq_true_eq] at hL ⊢
      rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · exact Or.inl ⟨v, hvB, hvU⟩
      · have hjF' := (restrict_mem_leftGates C K i j).mp hjF
        exact Or.inr ⟨K.orderEmbOfFin rfl j, hjF',
          (K.orderEmbOfFin rfl).lt_iff_lt.mpr hji, ih j (by omega) hjv⟩
    · have hR := hval.2
      unfold sideTrue at hR ⊢
      rw [decide_eq_true_eq] at hR ⊢
      rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · exact Or.inl ⟨v, hvB, hvU⟩
      · have hjF' := (restrict_mem_rightGates C K i j).mp hjF
        exact Or.inr ⟨K.orderEmbOfFin rfl j, hjF',
          (K.orderEmbOfFin rfl).lt_iff_lt.mpr hji, ih j (by omega) hjv⟩

private lemma restrict_eval_le {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (U : Finset (Fin n)) (h : (restrictCircuit C K).eval U = true) : C.eval U = true := by
  unfold AndCountCircuit.eval at h ⊢
  rw [decide_eq_true_eq] at h ⊢
  rcases h with ⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩
  · exact Or.inl ⟨v, hvO, hvU⟩
  · have hjO' := (restrict_mem_outGates C K j).mp hjO
    exact Or.inr ⟨K.orderEmbOfFin rfl j, hjO', restrict_gateVal_le C K U _ j j.isLt hjv⟩

private lemma restrict_gateVal_ge {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (U : Finset (Fin n)) (hK : ∀ j : Fin C.size, j ∉ K → C.gateVal U j = false) :
    ∀ (m : ℕ) (i : Fin K.card), i.val < m →
      C.gateVal U (K.orderEmbOfFin rfl i) = true →
        (restrictCircuit C K).gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    rw [gateVal_unfold C U, Bool.and_eq_true] at hval
    rw [gateVal_unfold (restrictCircuit C K) U i, Bool.and_eq_true]
    constructor
    · have hL := hval.1
      unfold sideTrue at hL ⊢
      rw [decide_eq_true_eq] at hL ⊢
      rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · exact Or.inl ⟨v, hvB, hvU⟩
      · have hjK : j ∈ K := by
          by_contra hnot
          have hf := hK j hnot
          rw [hf] at hjv
          exact Bool.false_ne_true hjv
        have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact hjK
        obtain ⟨j', hj'⟩ := hjr
        have hj'lt : j' < i := (K.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hj']; exact hji)
        refine Or.inr ⟨j', (restrict_mem_leftGates C K i j').mpr (by rw [hj']; exact hjF),
          hj'lt, ih j' (by omega) (by rw [hj']; exact hjv)⟩
    · have hR := hval.2
      unfold sideTrue at hR ⊢
      rw [decide_eq_true_eq] at hR ⊢
      rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · exact Or.inl ⟨v, hvB, hvU⟩
      · have hjK : j ∈ K := by
          by_contra hnot
          have hf := hK j hnot
          rw [hf] at hjv
          exact Bool.false_ne_true hjv
        have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact hjK
        obtain ⟨j', hj'⟩ := hjr
        have hj'lt : j' < i := (K.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hj']; exact hji)
        refine Or.inr ⟨j', (restrict_mem_rightGates C K i j').mpr (by rw [hj']; exact hjF),
          hj'lt, ih j' (by omega) (by rw [hj']; exact hjv)⟩

private lemma restrict_eval_ge {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (U : Finset (Fin n)) (hK : ∀ j : Fin C.size, j ∉ K → C.gateVal U j = false)
    (h : C.eval U = true) : (restrictCircuit C K).eval U = true := by
  unfold AndCountCircuit.eval at h ⊢
  rw [decide_eq_true_eq] at h ⊢
  rcases h with ⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩
  · exact Or.inl ⟨v, hvO, hvU⟩
  · have hjK : j ∈ K := by
      by_contra hnot
      have hf := hK j hnot
      rw [hf] at hjv
      exact Bool.false_ne_true hjv
    have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hjK
    obtain ⟨j', hj'⟩ := hjr
    refine Or.inr ⟨j', (restrict_mem_outGates C K j').mpr (by rw [hj']; exact hjO),
      restrict_gateVal_ge C K U hK _ j' j'.isLt (by rw [hj']; exact hjv)⟩


theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem sub_left {n : ℕ} (X U : Finset (Fin n)) : X ⊆ X ∪ U :=
  fun _ hx => Finset.mem_union_left U hx

theorem sub_ins {n : ℕ} (X : Finset (Fin n)) {U : Finset (Fin n)} {v : Fin n} (hv : v ∈ U) :
    X ∪ {v} ⊆ X ∪ U := by
  intro x hx
  rcases Finset.mem_union.mp hx with h | h
  · exact Finset.mem_union_left _ h
  · rw [Finset.mem_singleton.mp h]
    exact Finset.mem_union_right _ hv

theorem gateVal_mono {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)} (h : U ⊆ V)
    (i : Fin C.size) (hi : C.gateVal U i = true) : C.gateVal V i = true :=
  gateValFuel_mono_U C h C.size i hi

theorem side_mono {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)} (h : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (i : Fin C.size)
    (hs : sideTrue U B F i (C.gateVal U) = true) : sideTrue V B F i (C.gateVal V) = true :=
  sideTrue_mono_U h B F i _ _ (fun j _ hj => gateVal_mono C h j hj) hs

theorem sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val : Fin k → Bool) :
    sideTrue U B F i val = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

theorem eval_iff {n : ℕ} (D : AndCountCircuit n) (U : Finset (Fin n)) :
    D.eval U = true ↔ ((∃ v ∈ D.outVars, v ∈ U) ∨ ∃ j ∈ D.outGates, D.gateVal U j = true) := by
  unfold AndCountCircuit.eval
  exact decide_eq_true_iff

def keep {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => sideTrue X (C.leftVars i) (C.leftGates i) i (C.gateVal X) = false ∧
    sideTrue X (C.rightVars i) (C.rightGates i) i (C.gateVal X) = false)

theorem mem_keep {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) :
    i ∈ keep C X ↔ (sideTrue X (C.leftVars i) (C.leftGates i) i (C.gateVal X) = false ∧
      sideTrue X (C.rightVars i) (C.rightGates i) i (C.gateVal X) = false) := by
  unfold keep
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ i)

theorem chain_step {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (j : Fin C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size))
    (hB : sideTrue X B F j (C.gateVal X) = false)
    (hgj : ∀ U : Finset (Fin n), C.gateVal (X ∪ U) j = sideTrue (X ∪ U) B F j (C.gateVal (X ∪ U)))
    (ih : ∀ j' : Fin C.size, j' < j → C.gateVal X j' = false → ∀ U : Finset (Fin n),
       C.gateVal (X ∪ U) j' = true →
       (∃ v ∈ U, v ∉ X ∧ C.gateVal (X ∪ {v}) j' = true) ∨
       ∃ k ∈ keep C X, k ≤ j' ∧ C.gateVal (X ∪ U) k = true ∧
         ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true → C.gateVal (X ∪ U') j' = true)
    (U : Finset (Fin n)) (hU : C.gateVal (X ∪ U) j = true) :
    (∃ v ∈ U, v ∉ X ∧ C.gateVal (X ∪ {v}) j = true) ∨
       ∃ k ∈ keep C X, k ≤ j ∧ C.gateVal (X ∪ U) k = true ∧
         ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true → C.gateVal (X ∪ U') j = true := by
  have hB' : ¬ ((∃ v ∈ B, v ∈ X) ∨ ∃ j' ∈ F, j' < j ∧ C.gateVal X j' = true) := by
    intro h
    have h2 := (sideTrue_iff X B F j (C.gateVal X)).mpr h
    rw [hB] at h2
    exact Bool.false_ne_true h2
  rw [hgj, sideTrue_iff] at hU
  rcases hU with ⟨v, hvB, hvXU⟩ | ⟨j', hj'F, hj'j, hj'v⟩
  · have hvX : v ∉ X := fun h => hB' (Or.inl ⟨v, hvB, h⟩)
    have hvU : v ∈ U := (Finset.mem_union.mp hvXU).resolve_left hvX
    left
    refine ⟨v, hvU, hvX, ?_⟩
    rw [hgj, sideTrue_iff]
    exact Or.inl ⟨v, hvB, Finset.mem_union_right _ (Finset.mem_singleton_self v)⟩
  · have hj'X : C.gateVal X j' = false := by
      cases h : C.gateVal X j'
      · rfl
      · exact absurd (Or.inr ⟨j', hj'F, hj'j, h⟩) hB'
    rcases ih j' hj'j hj'X U hj'v with ⟨v, hvU, hvX, hv⟩ | ⟨k, hkK, hkj', hkU, hkimp⟩
    · left
      refine ⟨v, hvU, hvX, ?_⟩
      rw [hgj, sideTrue_iff]
      exact Or.inr ⟨j', hj'F, hj'j, hv⟩
    · right
      refine ⟨k, hkK, le_trans hkj' (le_of_lt hj'j), hkU, fun U' hU' => ?_⟩
      rw [hgj, sideTrue_iff]
      exact Or.inr ⟨j', hj'F, hj'j, hkimp U' hU'⟩

theorem chain {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) :
    ∀ (m : ℕ) (j : Fin C.size), j.val < m → C.gateVal X j = false → ∀ U : Finset (Fin n),
       C.gateVal (X ∪ U) j = true →
       (∃ v ∈ U, v ∉ X ∧ C.gateVal (X ∪ {v}) j = true) ∨
       ∃ k ∈ keep C X, k ≤ j ∧ C.gateVal (X ∪ U) k = true ∧
         ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true → C.gateVal (X ∪ U') j = true := by
  intro m
  induction m with
  | zero =>
    intro j hj
    exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro j hjm hjX U hU
    have ih' := fun (j' : Fin C.size) (hj' : j' < j) =>
      ih j' (lt_of_lt_of_le (Fin.lt_def.mp hj') (Nat.lt_succ_iff.mp hjm))
    by_cases hjK : j ∈ keep C X
    · right
      exact ⟨j, hjK, le_refl j, hU, fun _ h => h⟩
    · rw [mem_keep] at hjK
      have hg := gateVal_unfold C X j
      rw [hjX] at hg
      rcases Bool.eq_false_or_eq_true
          (sideTrue X (C.leftVars j) (C.leftGates j) j (C.gateVal X)) with hL | hL
      · have hR : sideTrue X (C.rightVars j) (C.rightGates j) j (C.gateVal X) = false := by
          rw [hL, Bool.true_and] at hg
          exact hg.symm
        refine chain_step C X j (C.rightVars j) (C.rightGates j) hR ?_ ih' U hU
        intro U'
        rw [gateVal_unfold C (X ∪ U') j, side_mono C (sub_left X U') _ _ j hL, Bool.true_and]
      · rcases Bool.eq_false_or_eq_true
            (sideTrue X (C.rightVars j) (C.rightGates j) j (C.gateVal X)) with hR | hR
        · refine chain_step C X j (C.leftVars j) (C.leftGates j) hL ?_ ih' U hU
          intro U'
          rw [gateVal_unfold C (X ∪ U') j, side_mono C (sub_left X U') _ _ j hR, Bool.and_true]
        · exact absurd ⟨hL, hR⟩ hjK

def eVars {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i : Fin C.size) : Finset (Fin n) :=
  Finset.univ.filter (fun v => i ∈ keep C X ∧ v ∉ X ∧
    sideTrue (X ∪ {v}) B F i (C.gateVal (X ∪ {v})) = true)

def eGates {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i : Fin C.size) : Finset (Fin C.size) :=
  Finset.univ.filter (fun k => i ∈ keep C X ∧ k ∈ keep C X ∧ k < i ∧
    ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true →
      sideTrue (X ∪ U') B F i (C.gateVal (X ∪ U')) = true)

theorem mem_eVars {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i : Fin C.size) (v : Fin n) :
    v ∈ eVars C X B F i ↔ (i ∈ keep C X ∧ v ∉ X ∧
      sideTrue (X ∪ {v}) B F i (C.gateVal (X ∪ {v})) = true) := by
  unfold eVars
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

theorem mem_eGates {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i k : Fin C.size) :
    k ∈ eGates C X B F i ↔ (i ∈ keep C X ∧ k ∈ keep C X ∧ k < i ∧
      ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true →
        sideTrue (X ∪ U') B F i (C.gateVal (X ∪ U')) = true) := by
  unfold eGates
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ k)

def build {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) : AndCountCircuit n where
  size := C.size
  leftVars i := eVars C X (C.leftVars i) (C.leftGates i) i
  leftGates i := eGates C X (C.leftVars i) (C.leftGates i) i
  rightVars i := eVars C X (C.rightVars i) (C.rightGates i) i
  rightGates i := eGates C X (C.rightVars i) (C.rightGates i) i
  outVars := Finset.univ.filter (fun v => v ∉ X ∧ C.eval (X ∪ {v}) = true)
  outGates := Finset.univ.filter (fun k => k ∈ keep C X ∧
    ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true → C.eval (X ∪ U') = true)

theorem mem_outV {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (v : Fin n) :
    v ∈ (build C X).outVars ↔ (v ∉ X ∧ C.eval (X ∪ {v}) = true) := by
  show v ∈ Finset.univ.filter (fun v => v ∉ X ∧ C.eval (X ∪ {v}) = true) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

theorem mem_outG {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (k : Fin C.size) :
    k ∈ (build C X).outGates ↔ (k ∈ keep C X ∧
      ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true → C.eval (X ∪ U') = true) := by
  show k ∈ Finset.univ.filter (fun k => k ∈ keep C X ∧
    ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true → C.eval (X ∪ U') = true) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ k)

theorem build_unfold {n : ℕ} (C : AndCountCircuit n) (X U : Finset (Fin n)) (i : Fin C.size) :
    (build C X).gateVal U i =
      (sideTrue U (eVars C X (C.leftVars i) (C.leftGates i) i)
          (eGates C X (C.leftVars i) (C.leftGates i) i) i ((build C X).gateVal U) &&
        sideTrue U (eVars C X (C.rightVars i) (C.rightGates i) i)
          (eGates C X (C.rightVars i) (C.rightGates i) i) i ((build C X).gateVal U)) :=
  gateVal_unfold (build C X) U i

theorem side_eq {n : ℕ} (C : AndCountCircuit n) (X U : Finset (Fin n)) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i : Fin C.size)
    (hiK : i ∈ keep C X) (hB : sideTrue X B F i (C.gateVal X) = false)
    (val : Fin C.size → Bool)
    (hval : ∀ k : Fin C.size, k < i → (val k = true ↔ k ∈ keep C X ∧ C.gateVal (X ∪ U) k = true)) :
    sideTrue U (eVars C X B F i) (eGates C X B F i) i val =
      sideTrue (X ∪ U) B F i (C.gateVal (X ∪ U)) := by
  have hB' : ¬ ((∃ v ∈ B, v ∈ X) ∨ ∃ j' ∈ F, j' < i ∧ C.gateVal X j' = true) := by
    intro h
    have h2 := (sideTrue_iff X B F i (C.gateVal X)).mpr h
    rw [hB] at h2
    exact Bool.false_ne_true h2
  apply bool_ext
  rw [sideTrue_iff, sideTrue_iff]
  constructor
  · rintro (⟨v, hv, hvU⟩ | ⟨k, hk, hki, hkv⟩)
    · rw [mem_eVars] at hv
      exact (sideTrue_iff _ _ _ _ _).mp (side_mono C (sub_ins X hvU) B F i hv.2.2)
    · rw [mem_eGates] at hk
      have h2 := (hval k hki).mp hkv
      exact (sideTrue_iff _ _ _ _ _).mp (hk.2.2.2 U h2.2)
  · rintro (⟨v, hvB, hvXU⟩ | ⟨j, hjF, hji, hjv⟩)
    · have hvX : v ∉ X := fun h => hB' (Or.inl ⟨v, hvB, h⟩)
      have hvU : v ∈ U := (Finset.mem_union.mp hvXU).resolve_left hvX
      left
      refine ⟨v, (mem_eVars C X B F i v).mpr ⟨hiK, hvX, ?_⟩, hvU⟩
      rw [sideTrue_iff]
      exact Or.inl ⟨v, hvB, Finset.mem_union_right _ (Finset.mem_singleton_self v)⟩
    · have hjX : C.gateVal X j = false := by
        cases h : C.gateVal X j
        · rfl
        · exact absurd (Or.inr ⟨j, hjF, hji, h⟩) hB'
      rcases chain C X C.size j j.isLt hjX U hjv with ⟨v, hvU, hvX, hv⟩ | ⟨k, hkK, hkj, hkU, hkimp⟩
      · left
        refine ⟨v, (mem_eVars C X B F i v).mpr ⟨hiK, hvX, ?_⟩, hvU⟩
        rw [sideTrue_iff]
        exact Or.inr ⟨j, hjF, hji, hv⟩
      · right
        have hki : k < i := lt_of_le_of_lt hkj hji
        refine ⟨k, (mem_eGates C X B F i k).mpr ⟨hiK, hkK, hki, fun U' hU' => ?_⟩, hki,
          (hval k hki).mpr ⟨hkK, hkU⟩⟩
        rw [sideTrue_iff]
        exact Or.inr ⟨j, hjF, hji, hkimp U' hU'⟩

theorem build_gateVal {n : ℕ} (C : AndCountCircuit n) (X U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ((build C X).gateVal U i = true ↔ (i ∈ keep C X ∧ C.gateVal (X ∪ U) i = true)) := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    have hval : ∀ k : Fin C.size, k < i →
        ((build C X).gateVal U k = true ↔ (k ∈ keep C X ∧ C.gateVal (X ∪ U) k = true)) :=
      fun k hk => ih k (lt_of_lt_of_le (Fin.lt_def.mp hk) (Nat.lt_succ_iff.mp hi))
    rw [build_unfold C X U i]
    by_cases hiK : i ∈ keep C X
    · have hK' := (mem_keep C X i).mp hiK
      rw [side_eq C X U _ _ i hiK hK'.1 _ hval, side_eq C X U _ _ i hiK hK'.2 _ hval,
        ← gateVal_unfold C (X ∪ U) i]
      exact ⟨fun h => ⟨hiK, h⟩, fun h => h.2⟩
    · have hfalse : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)),
          sideTrue U (eVars C X B F i) (eGates C X B F i) i ((build C X).gateVal U) = false := by
        intro B F
        cases h : sideTrue U (eVars C X B F i) (eGates C X B F i) i ((build C X).gateVal U)
        · rfl
        · exfalso
          have h' := (sideTrue_iff _ _ _ _ _).mp h
          rcases h' with ⟨v, hv, _⟩ | ⟨k, hk, _, _⟩
          · exact hiK ((mem_eVars C X B F i v).mp hv).1
          · exact hiK ((mem_eGates C X B F i k).mp hk).1
      rw [hfalse, Bool.false_and]
      exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h.1 hiK⟩

theorem build_eval {n : ℕ} (C : AndCountCircuit n) (X U : Finset (Fin n))
    (hX : C.eval X = false) : (build C X).eval U = C.eval (X ∪ U) := by
  have hX' : ¬ ((∃ v ∈ C.outVars, v ∈ X) ∨ ∃ j ∈ C.outGates, C.gateVal X j = true) := by
    intro h
    have h2 := (eval_iff C X).mpr h
    rw [hX] at h2
    exact Bool.false_ne_true h2
  apply bool_ext
  rw [eval_iff, eval_iff]
  constructor
  · rintro (⟨v, hv, hvU⟩ | ⟨k, hk, hkv⟩)
    · rw [mem_outV] at hv
      exact (eval_iff C _).mp (eval_mono_U C (sub_ins X hvU) hv.2)
    · have hk' := (mem_outG C X k).mp hk
      have h2 := (build_gateVal C X U C.size k k.isLt).mp hkv
      exact (eval_iff C _).mp (hk'.2 U h2.2)
  · rintro (⟨v, hvO, hvXU⟩ | ⟨j, hjO, hjv⟩)
    · have hvX : v ∉ X := fun h => hX' (Or.inl ⟨v, hvO, h⟩)
      have hvU : v ∈ U := (Finset.mem_union.mp hvXU).resolve_left hvX
      left
      refine ⟨v, (mem_outV C X v).mpr ⟨hvX, ?_⟩, hvU⟩
      rw [eval_iff]
      exact Or.inl ⟨v, hvO, Finset.mem_union_right _ (Finset.mem_singleton_self v)⟩
    · have hjX : C.gateVal X j = false := by
        cases h : C.gateVal X j
        · rfl
        · exact absurd (Or.inr ⟨j, hjO, h⟩) hX'
      rcases chain C X C.size j j.isLt hjX U hjv with ⟨v, hvU, hvX, hv⟩ | ⟨k, hkK, _, hkU, hkimp⟩
      · left
        refine ⟨v, (mem_outV C X v).mpr ⟨hvX, ?_⟩, hvU⟩
        rw [eval_iff]
        exact Or.inr ⟨j, hjO, hv⟩
      · right
        refine ⟨k, (mem_outG C X k).mpr ⟨hkK, fun U' hU' => ?_⟩,
          (build_gateVal C X U C.size k k.isLt).mpr ⟨hkK, hkU⟩⟩
        rw [eval_iff]
        exact Or.inr ⟨j, hjO, hkimp U' hU'⟩

theorem build_wf {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) : (build C X).WellFormed := by
  intro i
  constructor
  · intro j hj
    exact ((mem_eGates C X _ _ i j).mp hj).2.2.1
  · intro j hj
    exact ((mem_eGates C X _ _ i j).mp hj).2.2.1

theorem main (n : ℕ) (C : AndCountCircuit n) (X : Finset (Fin n)) (hX : C.eval X = false) :
    ∃ D : AndCountCircuit n, D.WellFormed ∧
      D.size + {x6 : Fin C.size | ∃ x7 ∈ X, x7 ∈ C.leftVars x6 ∨ x7 ∈ C.rightVars x6}.ncard
        ≤ C.size ∧
      ∀ U : Finset (Fin n), D.eval U = C.eval (X ∪ U) := by
  let K : Finset (Fin (build C X).size) := keep C X
  have hK : ∀ U : Finset (Fin n), ∀ j : Fin (build C X).size, j ∉ K →
      (build C X).gateVal U j = false := by
    intro U j hj
    cases h : (build C X).gateVal U j
    · rfl
    · exact absurd ((build_gateVal C X U C.size j j.isLt).mp h).1 hj
  refine ⟨restrictCircuit (build C X) K, restrict_wf (build C X) K (build_wf C X), ?_, ?_⟩
  · change (keep C X).card + _ ≤ C.size
    have hsub : {x6 : Fin C.size | ∃ x7 ∈ X, x7 ∈ C.leftVars x6 ∨ x7 ∈ C.rightVars x6} ⊆
        ((Finset.univ \ keep C X : Finset (Fin C.size)) : Set (Fin C.size)) := by
      intro i hi
      obtain ⟨x7, hx7X, hx7⟩ := hi
      rw [Finset.mem_coe, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hiK => ?_⟩
      have hK' := (mem_keep C X i).mp hiK
      rcases hx7 with h | h
      · have h2 : sideTrue X (C.leftVars i) (C.leftGates i) i (C.gateVal X) = true := by
          rw [sideTrue_iff]
          exact Or.inl ⟨x7, h, hx7X⟩
        rw [hK'.1] at h2
        exact Bool.false_ne_true h2
      · have h2 : sideTrue X (C.rightVars i) (C.rightGates i) i (C.gateVal X) = true := by
          rw [sideTrue_iff]
          exact Or.inl ⟨x7, h, hx7X⟩
        rw [hK'.2] at h2
        exact Bool.false_ne_true h2
    have hle := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at hle
    have hcard : (Finset.univ \ keep C X).card + (keep C X).card = C.size := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin]
    omega
  · intro U
    apply bool_ext
    constructor
    · intro h
      rw [← build_eval C X U hX]
      exact restrict_eval_le (build C X) K U h
    · intro h
      rw [← build_eval C X U hX] at h
      exact restrict_eval_ge (build C X) K U (hK U) h

end PEqualNP.Outside.L_meta_6784

theorem PEqualNP.Outside.L_meta_6784 : ∀ (x1 : ℕ) (x2 : PEqualNP.AndCount.AndCountCircuit x1) (x3 : Finset (Fin x1)), x2.eval x3 = Bool.false → ∃ (x5 : PEqualNP.AndCount.AndCountCircuit x1), x5.WellFormed ∧ x5.size + {x6 : Fin x2.size | ∃ x7 ∈ x3, x7 ∈ x2.leftVars x6 ∨ x7 ∈ x2.rightVars x6}.ncard ≤ x2.size ∧ ∀ (x6 : Finset (Fin x1)), x5.eval x6 = x2.eval (x3 ∪ x6) := by
  intro x1 x2 x3 h
  exact PEqualNP.Outside.L_meta_6784.main x1 x2 x3 h
