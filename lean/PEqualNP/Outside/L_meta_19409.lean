import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19409_aux

open PEqualNP.AndCount

def buildCircuit (x1 x2 : ℕ) (x3 : Finset (Finset (Fin x1)))
    (x4 : Fin x2 → Finset (Fin x1))
    (x5 : Fin x2 → Fin 2 → Finset (Finset (Fin x1))) : AndCountCircuit x1 where
  size := x2
  leftVars i := (x4 i).filter (fun v => ∀ z ∈ x5 i 0, v ∉ z)
  leftGates i := Finset.univ.filter (fun j => j < i ∧ x5 i 0 ⊆ x5 j 0 ∪ x5 j 1)
  rightVars i := (x4 i).filter (fun v => ∀ z ∈ x5 i 1, v ∉ z)
  rightGates i := Finset.univ.filter (fun j => j < i ∧ x5 i 1 ⊆ x5 j 0 ∪ x5 j 1)
  outVars := ∅
  outGates := Finset.univ.filter (fun i => x3 ⊆ x5 i 0 ∪ x5 i 1)

lemma buildCircuit_wf (x1 x2 : ℕ) (x3 : Finset (Finset (Fin x1)))
    (x4 : Fin x2 → Finset (Fin x1))
    (x5 : Fin x2 → Fin 2 → Finset (Finset (Fin x1))) :
    (buildCircuit x1 x2 x3 x4 x5).WellFormed := by
  intro i
  constructor
  · intro j hj
    dsimp only [buildCircuit] at hj
    exact (Finset.mem_filter.mp hj).2.1
  · intro j hj
    dsimp only [buildCircuit] at hj
    exact (Finset.mem_filter.mp hj).2.1

lemma buildCircuit_gateValFuel_false (x1 x2 : ℕ) (x3 : Finset (Finset (Fin x1)))
    (x4 : Fin x2 → Finset (Fin x1))
    (x5 : Fin x2 → Fin 2 → Finset (Finset (Fin x1))) :
    ∀ (d : ℕ) (i : Fin x2) (z : Finset (Fin x1)),
      z ∈ x5 i 0 ∪ x5 i 1 →
      (buildCircuit x1 x2 x3 x4 x5).gateValFuel z d i = false := by
  intro d
  induction d with
  | zero =>
    intro i z _
    rfl
  | succ d ih =>
    intro i z hz
    simp only [AndCountCircuit.gateValFuel, Bool.and_eq_false_iff]
    rw [Finset.mem_union] at hz
    rcases hz with hz0 | hz1
    · left
      simp only [AndCountCircuit.sideTrue, decide_eq_false_iff_not, not_or, not_exists, not_and]
      constructor
      · intro v hv
        dsimp only [buildCircuit] at hv
        exact (Finset.mem_filter.mp hv).2 z hz0
      · intro j hj _
        dsimp only [buildCircuit] at hj
        rw [ih j z ((Finset.mem_filter.mp hj).2.2 hz0)]
        decide
    · right
      simp only [AndCountCircuit.sideTrue, decide_eq_false_iff_not, not_or, not_exists, not_and]
      constructor
      · intro v hv
        dsimp only [buildCircuit] at hv
        exact (Finset.mem_filter.mp hv).2 z hz1
      · intro j hj _
        dsimp only [buildCircuit] at hj
        rw [ih j z ((Finset.mem_filter.mp hj).2.2 hz1)]
        decide

lemma buildCircuit_gateValFuel_true (x1 x2 : ℕ) (x3 : Finset (Finset (Fin x1)))
    (x4 : Fin x2 → Finset (Fin x1))
    (x5 : Fin x2 → Fin 2 → Finset (Finset (Fin x1)))
    (x6 : Fin x2 → Finset (Finset (Fin x1)))
    (hcover : ∀ (i : Fin x2), ∀ p ∈ x6 i, ∀ (s : Fin 2),
      (∃ v ∈ x4 i, v ∈ p ∧ ∀ z ∈ x5 i s, v ∉ z) ∨
      ∃ j < i, p ∈ x6 j ∧ x5 i s ⊆ x5 j 0 ∪ x5 j 1) :
    ∀ (d : ℕ) (i : Fin x2), i.val < d →
      ∀ p ∈ x6 i, ∀ (q : Finset (Fin x1)), p ⊆ q →
      (buildCircuit x1 x2 x3 x4 x5).gateValFuel q d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    omega
  | succ d ih =>
    intro i hi p hp q hpq
    simp only [AndCountCircuit.gateValFuel, Bool.and_eq_true]
    constructor
    · simp only [AndCountCircuit.sideTrue, decide_eq_true_eq]
      rcases hcover i p hp 0 with ⟨v, hv4, hvp, hvz⟩ | ⟨j, hji, hpj, hsub⟩
      · left
        refine ⟨v, ?_, hpq hvp⟩
        dsimp only [buildCircuit]
        exact Finset.mem_filter.mpr ⟨hv4, hvz⟩
      · right
        refine ⟨j, ?_, hji, ih j (by omega) p hpj q hpq⟩
        dsimp only [buildCircuit]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hji, hsub⟩
    · simp only [AndCountCircuit.sideTrue, decide_eq_true_eq]
      rcases hcover i p hp 1 with ⟨v, hv4, hvp, hvz⟩ | ⟨j, hji, hpj, hsub⟩
      · left
        refine ⟨v, ?_, hpq hvp⟩
        dsimp only [buildCircuit]
        exact Finset.mem_filter.mpr ⟨hv4, hvz⟩
      · right
        refine ⟨j, ?_, hji, ih j (by omega) p hpj q hpq⟩
        dsimp only [buildCircuit]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hji, hsub⟩

end PEqualNP.Outside.L_meta_19409_aux

theorem PEqualNP.Outside.L_meta_19409 : (∀ (x1 x2 : ℕ) (x3 : Finset (Finset (Fin x1))) (x4 : Fin x2 → Finset (Fin x1)) (x5 : Fin x2 → Fin (2 : ℕ) → Finset (Finset (Fin x1))) (x6 : Fin x2 → Finset (Finset (Fin x1))),   (50 : ℕ) ≤ x1 →     have x8 : Finset (Fin x2) := Finset.univ;     have x9 : Fin x2 → Finset (Finset (Fin x1)) := fun (x9 : Fin x2) => x5 x9 (0 : Fin (2 : ℕ)) ∪ x5 x9 (1 : Fin (2 : ℕ));     (∀ (x10 : Fin x2), ∀ x11 ∈ x6 x10, ∀ (x13 : Fin (2 : ℕ)), (∃ x14 ∈ x4 x10, x14 ∈ x11 ∧ ∀ x15 ∈ x5 x10 x13, x14 ∉ x15) ∨ ∃ x14 < x10, x11 ∈ x6 x14 ∧ x5 x10 x13 ⊆ x9 x14) →       ∃ (x11 : PEqualNP.AndCount.AndCountCircuit x1),         x11.WellFormed ∧           x11.size = x2 ∧             (have x12 : Finset (Fin x11.size) := Finset.univ;               ∀ (x13 : Fin x1), {x14 ∈ x12 | x13 ∈ x11.leftVars x14 ∨ x13 ∈ x11.rightVars x14}.card ≤ {x14 ∈ x8 | x13 ∈ x4 x14}.card) ∧               (∀ x12 ∈ x3, x11.eval x12 = Bool.false) ∧ ∀ (x12 : Fin x2), x3 ⊆ x9 x12 → ∀ x14 ∈ x6 x12, ∀ (x16 : Finset (Fin x1)), x14 ⊆ x16 → x11.eval x16 = Bool.true) := by
  intro x1 x2 x3 x4 x5 x6 _h50
  dsimp only
  intro hcover
  refine ⟨PEqualNP.Outside.L_meta_19409_aux.buildCircuit x1 x2 x3 x4 x5,
    PEqualNP.Outside.L_meta_19409_aux.buildCircuit_wf x1 x2 x3 x4 x5, rfl, ?_, ?_, ?_⟩
  · intro v
    show ({i ∈ (Finset.univ : Finset (Fin x2)) |
      v ∈ (x4 i).filter (fun w => ∀ z ∈ x5 i 0, w ∉ z) ∨
      v ∈ (x4 i).filter (fun w => ∀ z ∈ x5 i 1, w ∉ z)}).card ≤
      ({i ∈ (Finset.univ : Finset (Fin x2)) | v ∈ x4 i}).card
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ i, ?_⟩
    rcases hi.2 with hl | hr
    · exact (Finset.mem_filter.mp hl).1
    · exact (Finset.mem_filter.mp hr).1
  · intro z hz
    simp only [PEqualNP.AndCount.AndCountCircuit.eval, decide_eq_false_iff_not, not_or,
      not_exists, not_and]
    constructor
    · intro v hv
      dsimp only [PEqualNP.Outside.L_meta_19409_aux.buildCircuit] at hv
      exact False.elim (Finset.notMem_empty v hv)
    · intro j hj
      dsimp only [PEqualNP.Outside.L_meta_19409_aux.buildCircuit] at hj
      have hsub := (Finset.mem_filter.mp hj).2
      change (PEqualNP.Outside.L_meta_19409_aux.buildCircuit x1 x2 x3 x4 x5).gateValFuel z x2 j ≠ true
      rw [PEqualNP.Outside.L_meta_19409_aux.buildCircuit_gateValFuel_false x1 x2 x3 x4 x5 x2 j z (hsub hz)]
      decide
  · intro i hi p hp q hpq
    simp only [PEqualNP.AndCount.AndCountCircuit.eval, decide_eq_true_eq]
    right
    refine ⟨i, ?_, ?_⟩
    · dsimp only [PEqualNP.Outside.L_meta_19409_aux.buildCircuit]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    · exact PEqualNP.Outside.L_meta_19409_aux.buildCircuit_gateValFuel_true
        x1 x2 x3 x4 x5 x6 hcover x2 i i.isLt p hp q hpq
