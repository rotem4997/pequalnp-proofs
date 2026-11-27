import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta565

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

end PEqualNP.Outside.LMeta565

theorem PEqualNP.Outside.L_meta_565 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.AndCount.AndCountCircuit n)
    (Y : Finset (Fin C.size)),
    C.WellFormed → C.Computes G →
      (∀ j ∈ Y, ∀ a c : Fin n, G.Adj a c → C.gateVal {a, c} j = false) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n,
        C'.WellFormed ∧ C'.Computes G ∧ C'.size + Y.card ≤ C.size := by
  intro n G C Y hWF hComp hY
  let K : Finset (Fin C.size) := Finset.univ \ Y
  refine ⟨PEqualNP.Outside.LMeta565.restrictCircuit C K,
    PEqualNP.Outside.LMeta565.restrict_wf C K hWF, ?_, ?_⟩
  · intro U
    constructor
    · intro hU
      exact (hComp U).mp (PEqualNP.Outside.LMeta565.restrict_eval_le C K U hU)
    · rintro ⟨a, haU, c, hcU, hadj⟩
      have hsub : ({a, c} : Finset (Fin n)) ⊆ U := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact haU
        · exact hcU
      have hCac : C.eval {a, c} = true :=
        (hComp {a, c}).mpr ⟨a, by simp, c, by simp, hadj⟩
      have hKac : ∀ j : Fin C.size, j ∉ K → C.gateVal {a, c} j = false := by
        intro j hj
        have hjY : j ∈ Y := by
          by_contra hnot
          exact hj (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hnot⟩)
        exact hY j hjY a c hadj
      have hC'ac : (PEqualNP.Outside.LMeta565.restrictCircuit C K).eval {a, c} = true :=
        PEqualNP.Outside.LMeta565.restrict_eval_ge C K {a, c} hKac hCac
      exact PEqualNP.Outside.LMeta565.eval_mono_U _ hsub hC'ac
  · change K.card + Y.card ≤ C.size
    have hcard : K.card + Y.card = (Finset.univ : Finset (Fin C.size)).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Y)
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    omega
