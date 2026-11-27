import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9089_aux

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false :=
  List.getD_eq_default _ _ (by simp; omega)

theorem mono_run : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ (x y : List Bool), x.length = y.length → (∀ i, x.getD i false = true → y.getD i false = true) →
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ x y _ h; exact h
  | cons g gs ih =>
    intro hops x y hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · intro i hi
      rcases lt_trichotomy i x.length with hlt | heq | hgt
      · rw [getD_snoc_lt _ _ _ hlt] at hi
        rw [getD_snoc_lt _ _ _ (hl ▸ hlt)]
        exact h i hi
      · subst heq
        rw [getD_snoc_eq] at hi
        rw [hl, getD_snoc_eq]
        rcases hops g (List.mem_cons_self) with hop | hop
        · rw [hop] at hi ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hi ⊢
          rintro b ⟨a, ha, rfl⟩
          exact h a (hi _ ⟨a, ha, rfl⟩)
        · rw [hop] at hi ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
          obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := hi
          exact ⟨_, ⟨a, ha, rfl⟩, h a hb⟩
      · rw [getD_snoc_gt _ _ _ hgt] at hi
        exact absurd hi (by simp)

theorem inc_len {n m : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    (incidenceInput X Y).length = n + m := by
  simp [incidenceInput]

theorem inc_mono {n m : ℕ} (X X' : Finset (Fin n)) (Y Y' : Finset (Fin m)) (hX : X ⊆ X') (hY : Y ⊆ Y') :
    ∀ i, (incidenceInput X Y).getD i false = true → (incidenceInput X' Y').getD i false = true := by
  intro i hi
  unfold incidenceInput at hi ⊢
  by_cases h1 : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h1)] at hi ⊢
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    simp only [h1, dite_true, Option.getD_some, decide_eq_true_eq] at hi ⊢
    exact hX hi
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)] at hi ⊢
    simp only [List.length_ofFn] at hi ⊢
    by_cases h2 : i - n < m
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
      simp only [h2, dite_true, Option.getD_some, decide_eq_true_eq] at hi ⊢
      exact hY hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)

theorem eval_mono {n m : ℕ} (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (X X' : Finset (Fin n)) (Y Y' : Finset (Fin m)) (hX : X ⊆ X') (hY : Y ⊆ Y') :
    C.eval (incidenceInput X Y) = true → C.eval (incidenceInput X' Y') = true := by
  intro h
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  exact mono_run C.gates hops _ _ (by rw [inc_len, inc_len]) (inc_mono X X' Y Y' hX hY) _ h

theorem main (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    (∀ (X : Finset (Fin n)) (Y : Finset (Fin m)), C.eval (incidenceInput X Y) = incidenceFun S X Y) ↔
      RightOnIncidentPairs S C ∧ ∀ (X : Finset (Fin n)) (Y : Finset (Fin m)),
        IsMaximalFalse S X Y → C.eval (incidenceInput X Y) = false := by
  constructor
  · intro h
    refine ⟨fun l p hp => ?_, fun X Y hM => ?_⟩
    · rw [h]
      simp only [incidenceFun, decide_eq_true_eq]
      exact ⟨p, Finset.mem_singleton_self p, l, Finset.mem_singleton_self l, hp⟩
    · rw [h]
      simp only [incidenceFun, decide_eq_false_iff_not, not_exists, not_and]
      intro p hp l hl hpl
      exact Finset.disjoint_left.mp (hM.1 l hl) hpl hp
  · rintro ⟨hR, hF⟩ X Y
    by_cases hI : incidenceFun S X Y = true
    · rw [hI]
      simp only [incidenceFun, decide_eq_true_eq] at hI
      obtain ⟨p, hp, l, hl, hpl⟩ := hI
      exact eval_mono C hC {p} X {l} Y (Finset.singleton_subset_iff.mpr hp)
        (Finset.singleton_subset_iff.mpr hl) (hR l p hpl)
    · have hI' : incidenceFun S X Y = false := by simpa using hI
      rw [hI']
      have hfalse : IsFalseInput S X Y := by
        intro l hl
        rw [Finset.disjoint_left]
        intro p hpl hp
        apply hI
        simp only [incidenceFun, decide_eq_true_eq]
        exact ⟨p, hp, l, hl, hpl⟩
      classical
      let P : Finset (Finset (Fin n) × Finset (Fin m)) :=
        Finset.univ.filter (fun Z => X ⊆ Z.1 ∧ Y ⊆ Z.2 ∧ IsFalseInput S Z.1 Z.2)
      have hne : P.Nonempty := ⟨(X, Y), by simp [P, hfalse]⟩
      obtain ⟨Z, hZ, hmax⟩ := Finset.exists_max_image P (fun Z => Z.1.card + Z.2.card) hne
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hZ
      obtain ⟨hXZ, hYZ, hZf⟩ := hZ
      have hMZ : IsMaximalFalse S Z.1 Z.2 := by
        refine ⟨hZf, fun p hp hpf => ?_, fun l hl hlf => ?_⟩
        · have := hmax (insert p Z.1, Z.2) (by
            simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hXZ.trans (Finset.subset_insert _ _), hYZ, hpf⟩)
          simp only at this
          rw [Finset.card_insert_of_notMem hp] at this
          omega
        · have := hmax (Z.1, insert l Z.2) (by
            simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hXZ, hYZ.trans (Finset.subset_insert _ _), hlf⟩)
          simp only at this
          rw [Finset.card_insert_of_notMem hl] at this
          omega
      have hZe := hF Z.1 Z.2 hMZ
      by_contra hc
      have hc' : C.eval (incidenceInput X Y) = true := by simpa using hc
      rw [eval_mono C hC X Z.1 Y Z.2 hXZ hYZ hc'] at hZe
      exact absurd hZe (by simp)

end PEqualNP.Outside.L_meta_9089_aux

theorem PEqualNP.Outside.L_meta_9089 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → ((∀ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x2)), x4.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = PEqualNP.GenericRejection.incidenceFun x3 x6 x7) ↔ PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 ∧ ∀ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x2)), PEqualNP.GenericRejection.IsMaximalFalse x3 x6 x7 → x4.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = Bool.false) := by
  intro x1 x2 x3 x4 hC
  exact PEqualNP.Outside.L_meta_9089_aux.main x1 x2 x3 x4 hC
