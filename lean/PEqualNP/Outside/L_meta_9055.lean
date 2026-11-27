import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9055_aux

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem side_eq {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k) (val : Fin k → Bool) :
    sideTrue U B F i val = decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) := rfl

theorem stab {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d e : ℕ) (i : Fin C.size), i.val < d → i.val < e → C.gateValFuel U d i = C.gateValFuel U e i := by
  intro d
  induction d with
  | zero => intro e i h; omega
  | succ d ih =>
    intro e i hd he
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    simp only [gateValFuel, side_eq]
    have key : ∀ F : Finset (Fin C.size), (∃ j ∈ F, j < i ∧ C.gateValFuel U d j = true) ↔
        (∃ j ∈ F, j < i ∧ C.gateValFuel U e' j = true) := by
      intro F
      constructor
      · rintro ⟨j, hj, hji, hv⟩
        refine ⟨j, hj, hji, ?_⟩
        have hj' : j.val < i.val := hji
        rw [← ih e' j (by omega) (by omega)]; exact hv
      · rintro ⟨j, hj, hji, hv⟩
        refine ⟨j, hj, hji, ?_⟩
        have hj' : j.val < i.val := hji
        rw [ih e' j (by omega) (by omega)]; exact hv
    simp only [key]

theorem umono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U') :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel U' d i = true := by
  intro d
  induction d with
  | zero => intro i h; simp [gateValFuel] at h
  | succ d ih =>
    intro i h
    simp only [gateValFuel, side_eq, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · rcases h1 with ⟨v, hv, hvU⟩ | ⟨j, hj, hji, hval⟩
      · exact Or.inl ⟨v, hv, hU hvU⟩
      · exact Or.inr ⟨j, hj, hji, ih j hval⟩
    · rcases h2 with ⟨v, hv, hvU⟩ | ⟨j, hj, hji, hval⟩
      · exact Or.inl ⟨v, hv, hU hvU⟩
      · exact Or.inr ⟨j, hj, hji, ih j hval⟩

theorem gv_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (decide ((∃ v ∈ C.leftVars i, v ∈ U) ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal U j = true) &&
      decide ((∃ v ∈ C.rightVars i, v ∈ U) ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal U j = true)) := by
  obtain ⟨s, hs⟩ : ∃ s, C.size = s + 1 := ⟨C.size - 1, by have := i.isLt; omega⟩
  have key : ∀ F : Finset (Fin C.size), (∃ j ∈ F, j < i ∧ C.gateValFuel U s j = true) ↔
      (∃ j ∈ F, j < i ∧ C.gateVal U j = true) := by
    intro F
    have hi := i.isLt
    constructor
    · rintro ⟨j, hj, hji, hv⟩
      refine ⟨j, hj, hji, ?_⟩
      have hj' : j.val < i.val := hji
      unfold gateVal
      rw [← stab C U s C.size j (by omega) (by omega)]; exact hv
    · rintro ⟨j, hj, hji, hv⟩
      refine ⟨j, hj, hji, ?_⟩
      have hj' : j.val < i.val := hji
      unfold gateVal at hv
      rw [stab C U s C.size j (by omega) (by omega)]; exact hv
  have h1 : C.gateVal U i = C.gateValFuel U (s + 1) i := by
    unfold gateVal
    exact stab C U C.size (s + 1) i i.isLt (by have := i.isLt; omega)
  rw [h1]
  simp only [gateValFuel, side_eq]
  simp only [key]

theorem main (n m : ℕ) (f : Fin m → Fin n) (C : AndCountCircuit n) (hW : C.WellFormed) :
    ∃ D : AndCountCircuit m, D.WellFormed ∧ (∀ S : Finset (Fin m), D.eval S = C.eval (Finset.image f S)) ∧
      D.size ≤ {x : Fin C.size | C.gateVal (Finset.image f Finset.univ) x = true}.ncard := by
  classical
  let Wd := Finset.image f Finset.univ
  let T : Finset (Fin C.size) := Finset.univ.filter (fun i => C.gateVal Wd i = true)
  let e := T.orderEmbOfFin rfl
  have hinT : ∀ j ∈ T, ∃ k, e k = j := by
    intro j hj
    have : j ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hj
    exact this
  let D : AndCountCircuit m :=
    { size := T.card
      leftVars := fun k => Finset.univ.filter (fun v => f v ∈ C.leftVars (e k))
      leftGates := fun k => Finset.univ.filter (fun k2 => e k2 ∈ C.leftGates (e k))
      rightVars := fun k => Finset.univ.filter (fun v => f v ∈ C.rightVars (e k))
      rightGates := fun k => Finset.univ.filter (fun k2 => e k2 ∈ C.rightGates (e k))
      outVars := Finset.univ.filter (fun v => f v ∈ C.outVars)
      outGates := Finset.univ.filter (fun k => e k ∈ C.outGates) }
  have hfalse : ∀ (S : Finset (Fin m)) (j : Fin C.size), C.gateVal (Finset.image f S) j = true →
      ∃ k, e k = j := by
    intro S j hj
    apply hinT
    have : C.gateVal Wd j = true :=
      umono C _ _ (Finset.image_subset_image (Finset.subset_univ S)) _ j hj
    simp [T, this]
  have hsides : ∀ (S : Finset (Fin m)) (val : Fin T.card → Bool) (k : Fin T.card)
      (hval : ∀ k2 : Fin T.card, k2 < k → val k2 = C.gateVal (Finset.image f S) (e k2))
      (Vs : Finset (Fin n)) (Gs : Finset (Fin C.size)),
      (decide ((∃ v ∈ Finset.univ.filter (fun v => f v ∈ Vs), v ∈ S) ∨
        ∃ j ∈ Finset.univ.filter (fun k2 => e k2 ∈ Gs), j < k ∧ val j = true)) =
      decide ((∃ v ∈ Vs, v ∈ Finset.image f S) ∨
        ∃ j ∈ Gs, j < e k ∧ C.gateVal (Finset.image f S) j = true) := by
    intro S val k hval Vs Gs
    apply decide_eq_decide.mpr
    apply or_congr
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨v, hv, hvS⟩; exact ⟨f v, hv, v, hvS, rfl⟩
      · rintro ⟨u, hu, v, hvS, rfl⟩; exact ⟨v, hu, hvS⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨k2, hk2, hlt, hv⟩
        rw [hval k2 hlt] at hv
        exact ⟨e k2, hk2, e.lt_iff_lt.mpr hlt, hv⟩
      · rintro ⟨j, hj, hlt, hv⟩
        obtain ⟨k2, rfl⟩ := hfalse S j hv
        have hlt' : k2 < k := e.lt_iff_lt.mp hlt
        exact ⟨k2, hj, hlt', by rw [hval k2 hlt']; exact hv⟩
  have hgate : ∀ (S : Finset (Fin m)) (d : ℕ) (k : Fin T.card), k.val < d →
      D.gateValFuel S d k = C.gateVal (Finset.image f S) (e k) := by
    intro S d
    induction d with
    | zero => intro k h; omega
    | succ d ih =>
      intro k hk
      rw [gv_unfold C _ (e k)]
      simp only [gateValFuel, side_eq]
      have hv : ∀ k2 : Fin T.card, k2 < k → D.gateValFuel S d k2 = C.gateVal (Finset.image f S) (e k2) := by
        intro k2 hlt
        have : k2.val < k.val := hlt
        exact ih k2 (by omega)
      exact congrArg₂ (· && ·) (hsides S _ k hv _ _) (hsides S _ k hv _ _)
  refine ⟨D, ?_, ?_, ?_⟩
  · intro k
    constructor
    · intro k2 hk2
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hk2
      exact e.lt_iff_lt.mp ((hW (e k)).1 _ hk2)
    · intro k2 hk2
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hk2
      exact e.lt_iff_lt.mp ((hW (e k)).2 _ hk2)
  · intro S
    unfold AndCountCircuit.eval
    apply decide_eq_decide.mpr
    apply or_congr
    · simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨v, hv, hvS⟩; exact ⟨f v, hv, v, hvS, rfl⟩
      · rintro ⟨u, hu, v, hvS, rfl⟩; exact ⟨v, hu, hvS⟩
    · have hD : ∀ k : Fin T.card, D.gateVal S k = C.gateVal (Finset.image f S) (e k) :=
        fun k => hgate S T.card k k.isLt
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨k, hk, hv⟩
        exact ⟨e k, hk, (hD k) ▸ hv⟩
      · rintro ⟨j, hj, hv⟩
        obtain ⟨k, rfl⟩ := hfalse S j hv
        exact ⟨k, hj, (hD k).symm ▸ hv⟩
  · show T.card ≤ _
    have : {x : Fin C.size | C.gateVal (Finset.image f Finset.univ) x = true} = (T : Set (Fin C.size)) := by
      ext x; simp [T, Wd]
    rw [this, Set.ncard_coe_finset]

end PEqualNP.Outside.L_meta_9055_aux

theorem PEqualNP.Outside.L_meta_9055 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x1) (x4 : PEqualNP.AndCount.AndCountCircuit x1), x4.WellFormed → ∃ (x6 : PEqualNP.AndCount.AndCountCircuit x2), x6.WellFormed ∧ (∀ (x7 : Finset (Fin x2)), x6.eval x7 = x4.eval (Finset.image x3 x7)) ∧ x6.size ≤ {x7 : Fin x4.size | x4.gateVal (Finset.image x3 Finset.univ) x7 = Bool.true}.ncard := by
  intro x1 x2 x3 x4 hW
  exact PEqualNP.Outside.L_meta_9055_aux.main x1 x2 x3 x4 hW
