import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_706

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- A side only consults the gates before its own gate.
theorem side_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j, j < i → val j = val' j) :
    sideTrue U B F i val = sideTrue U B F i val' := by
  unfold sideTrue
  apply decide_eq_decide.mpr
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

-- Any fuel above the index of a gate gives the same value.
theorem fuel_stable {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val = m → ∀ d d' : ℕ, m < d → m < d' →
      gateValFuel C U d i = gateValFuel C U d' i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i hi d d' hd hd'
    cases d with
    | zero => omega
    | succ d =>
      cases d' with
      | zero => omega
      | succ d' =>
        simp only [gateValFuel]
        congr 1
        · apply side_congr
          intro j hj
          have hjv : j.val < i.val := hj
          exact ih j.val (by omega) j rfl d d' (by omega) (by omega)
        · apply side_congr
          intro j hj
          have hjv : j.val < i.val := hj
          exact ih j.val (by omega) j rfl d d' (by omega) (by omega)

theorem gv_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  unfold gateVal
  rw [fuel_stable C U i.val i rfl C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)]
  simp only [gateValFuel]
  congr 1
  · apply side_congr
    intro j hj
    have hjv : j.val < i.val := hj
    exact fuel_stable C U j.val j rfl _ _ hjv j.isLt
  · apply side_congr
    intro j hj
    have hjv : j.val < i.val := hj
    exact fuel_stable C U j.val j rfl _ _ hjv j.isLt

-- The value of a gate of a well-formed circuit, as a statement.
theorem gv_iff {n : ℕ} (C : AndCountCircuit n) (hW : C.WellFormed) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i = true ↔
      ((∃ v ∈ C.leftVars i, v ∈ U) ∨ ∃ j ∈ C.leftGates i, C.gateVal U j = true) ∧
      ((∃ v ∈ C.rightVars i, v ∈ U) ∨ ∃ j ∈ C.rightGates i, C.gateVal U j = true) := by
  rw [gv_unfold]
  simp only [Bool.and_eq_true, sideTrue, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
    · rcases h2 with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hW i).1 j hj, hv⟩
    · rcases h2 with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hW i).2 j hj, hv⟩

-- The old index of a gate of the circuit with gate `i` removed.
def emb {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (k : Fin (C.size - 1)) : Fin C.size :=
  if k.val < i.val then ⟨k.val, by have := k.isLt; omega⟩ else ⟨k.val + 1, by have := k.isLt; omega⟩

theorem emb_val {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (k : Fin (C.size - 1)) :
    (emb C i k).val = if k.val < i.val then k.val else k.val + 1 := by
  unfold emb
  split_ifs <;> rfl

theorem emb_lt {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (k' k : Fin (C.size - 1))
    (h : emb C i k' < emb C i k) : k' < k := by
  have h' : (emb C i k').val < (emb C i k).val := h
  rw [emb_val, emb_val] at h'
  show k'.val < k.val
  split_ifs at h' <;> omega

theorem emb_surj {n : ℕ} (C : AndCountCircuit n) (i j : Fin C.size) (h : j ≠ i) :
    ∃ k, emb C i k = j := by
  have hv : j.val ≠ i.val := fun e => h (Fin.ext e)
  have hj := j.isLt
  have hi := i.isLt
  by_cases c : j.val < i.val
  · refine ⟨⟨j.val, by omega⟩, Fin.ext ?_⟩
    rw [emb_val]
    simp [c]
  · refine ⟨⟨j.val - 1, by omega⟩, Fin.ext ?_⟩
    rw [emb_val]
    have c' : ¬ (j.val - 1 < i.val) := by omega
    simp only [c', if_false]
    omega

-- A set of gates after the removal: gate `i` is replaced by the gates of `F`.
def subG {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (F G : Finset (Fin C.size)) :
    Finset (Fin (C.size - 1)) :=
  Finset.univ.filter (fun k => emb C i k ∈ G ∨ (i ∈ G ∧ emb C i k ∈ F))

-- A set of variables after the removal: reading gate `i` adds the variables of `B`.
def subV {n : ℕ} {m : ℕ} (i : Fin m) (B : Finset (Fin n)) (G : Finset (Fin m))
    (V : Finset (Fin n)) : Finset (Fin n) :=
  V ∪ (if i ∈ G then B else ∅)

def remove {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) : AndCountCircuit n where
  size := C.size - 1
  leftVars k := subV i B (C.leftGates (emb C i k)) (C.leftVars (emb C i k))
  leftGates k := subG C i F (C.leftGates (emb C i k))
  rightVars k := subV i B (C.rightGates (emb C i k)) (C.rightVars (emb C i k))
  rightGates k := subG C i F (C.rightGates (emb C i k))
  outVars := subV i B C.outGates C.outVars
  outGates := subG C i F C.outGates

theorem mem_subG {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (F G : Finset (Fin C.size))
    (k : Fin (C.size - 1)) :
    k ∈ subG C i F G ↔ (emb C i k ∈ G ∨ (i ∈ G ∧ emb C i k ∈ F)) := by
  simp [subG]

theorem remove_wf {n : ℕ} (C : AndCountCircuit n) (hW : C.WellFormed) (i : Fin C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (hF : ∀ j ∈ F, j < i) :
    (remove C i B F).WellFormed := by
  intro k
  constructor
  · intro k' hk'
    have hk := (mem_subG C i F _ k').mp hk'
    apply emb_lt C i
    rcases hk with h | ⟨h1, h2⟩
    · exact (hW (emb C i k)).1 _ h
    · exact lt_trans (hF _ h2) ((hW (emb C i k)).1 i h1)
  · intro k' hk'
    have hk := (mem_subG C i F _ k').mp hk'
    apply emb_lt C i
    rcases hk with h | ⟨h1, h2⟩
    · exact (hW (emb C i k)).2 _ h
    · exact lt_trans (hF _ h2) ((hW (emb C i k)).2 i h1)

-- A side (or the output) of the new circuit is true exactly when the old one is.
theorem side_iff {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) (hF : ∀ j ∈ F, j < i) (U : Finset (Fin n))
    (hi : C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true))
    (gv' : Fin (C.size - 1) → Bool) (G : Finset (Fin C.size)) (V : Finset (Fin n))
    (hP : ∀ k', (emb C i k' ∈ G ∨ (i ∈ G ∧ emb C i k' ∈ F)) →
      (gv' k' = true ↔ C.gateVal U (emb C i k') = true)) :
    ((∃ v ∈ subV i B G V, v ∈ U) ∨ ∃ k' ∈ subG C i F G, gv' k' = true) ↔
      ((∃ v ∈ V, v ∈ U) ∨ ∃ j ∈ G, C.gateVal U j = true) := by
  constructor
  · rintro (⟨v, hv, hvU⟩ | ⟨k', hk', hg⟩)
    · rcases Finset.mem_union.mp hv with h | h
      · exact Or.inl ⟨v, h, hvU⟩
      · by_cases hiG : i ∈ G
        · rw [if_pos hiG] at h
          exact Or.inr ⟨i, hiG, hi.mpr (Or.inl ⟨v, h, hvU⟩)⟩
        · rw [if_neg hiG] at h
          simp at h
    · have hk := (Finset.mem_filter.mp hk').2
      have hv := (hP k' hk).mp hg
      rcases hk with h | ⟨h1, h2⟩
      · exact Or.inr ⟨_, h, hv⟩
      · exact Or.inr ⟨i, h1, hi.mpr (Or.inr ⟨_, h2, hv⟩)⟩
  · rintro (⟨v, hv, hvU⟩ | ⟨j, hj, hg⟩)
    · exact Or.inl ⟨v, Finset.mem_union_left _ hv, hvU⟩
    · by_cases hji : j = i
      · rw [hji] at hj hg
        rcases hi.mp hg with ⟨v, hv, hvU⟩ | ⟨j', hj', hg'⟩
        · exact Or.inl ⟨v, Finset.mem_union_right _ (by rw [if_pos hj]; exact hv), hvU⟩
        · obtain ⟨k', hk'⟩ := emb_surj C i j' (ne_of_lt (hF j' hj'))
          have hmem : emb C i k' ∈ G ∨ (i ∈ G ∧ emb C i k' ∈ F) :=
            Or.inr ⟨hj, by rw [hk']; exact hj'⟩
          exact Or.inr ⟨k', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩,
            (hP k' hmem).mpr (by rw [hk']; exact hg')⟩
      · obtain ⟨k', hk'⟩ := emb_surj C i j hji
        have hmem : emb C i k' ∈ G ∨ (i ∈ G ∧ emb C i k' ∈ F) :=
          Or.inl (by rw [hk']; exact hj)
        exact Or.inr ⟨k', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩,
          (hP k' hmem).mpr (by rw [hk']; exact hg)⟩

-- Every gate of the new circuit has the value of its old gate.
theorem gv_remove {n : ℕ} (C : AndCountCircuit n) (hW : C.WellFormed) (i : Fin C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (hF : ∀ j ∈ F, j < i) (U : Finset (Fin n))
    (hi : C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) :
    ∀ k : Fin (C.size - 1),
      ((remove C i B F).gateVal U k = true ↔ C.gateVal U (emb C i k) = true) := by
  have key : ∀ (m : ℕ) (k : Fin (C.size - 1)), k.val = m →
      ((remove C i B F).gateVal U k = true ↔ C.gateVal U (emb C i k) = true) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hk
      rw [gv_iff (remove C i B F) (remove_wf C hW i B F hF) U k, gv_iff C hW U (emb C i k)]
      refine and_congr ?_ ?_
      · refine side_iff C i B F hF U hi ((remove C i B F).gateVal U)
          (C.leftGates (emb C i k)) (C.leftVars (emb C i k)) (fun k' hk' => ?_)
        have hlt : k' < k := by
          apply emb_lt C i
          rcases hk' with h | ⟨h1, h2⟩
          · exact (hW (emb C i k)).1 _ h
          · exact lt_trans (hF _ h2) ((hW (emb C i k)).1 i h1)
        have hlt' : k'.val < k.val := hlt
        exact ih k'.val (by omega) k' rfl
      · refine side_iff C i B F hF U hi ((remove C i B F).gateVal U)
          (C.rightGates (emb C i k)) (C.rightVars (emb C i k)) (fun k' hk' => ?_)
        have hlt : k' < k := by
          apply emb_lt C i
          rcases hk' with h | ⟨h1, h2⟩
          · exact (hW (emb C i k)).2 _ h
          · exact lt_trans (hF _ h2) ((hW (emb C i k)).2 i h1)
        have hlt' : k'.val < k.val := hlt
        exact ih k'.val (by omega) k' rfl
  exact fun k => key k.val k rfl

end PEqualNP.Outside.L_meta_706

open PEqualNP.Outside.L_meta_706 PEqualNP.AndCount in
theorem PEqualNP.Outside.L_meta_706 : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n), C.WellFormed →
    ∀ (D : Set (Finset (Fin n))) (i : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size)),
      (∀ j ∈ F, j < i) →
      (∀ U ∈ D, C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n, C'.WellFormed ∧ C'.size + 1 ≤ C.size ∧
        ∀ U ∈ D, C'.eval U = C.eval U := by
  intro n C hW D i B F hF hD
  refine ⟨remove C i B F, remove_wf C hW i B F hF, ?_, ?_⟩
  · show C.size - 1 + 1 ≤ C.size
    have := i.isLt
    omega
  · intro U hU
    have hi := hD U hU
    rw [Bool.eq_iff_iff]
    simp only [AndCountCircuit.eval, decide_eq_true_eq]
    exact side_iff C i B F hF U hi ((remove C i B F).gateVal U) C.outGates C.outVars
      (fun k' _ => gv_remove C hW i B F hF U hi k')
