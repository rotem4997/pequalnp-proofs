import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership (pairInput)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_650_1
    (hGeometry :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ P L : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ L, p + l ∉ D) → P.card ≤ 3 ∨ L.card ≤ 3)
    (hSearch :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
        (∃ g, C.gates.head? = some g ∧
          ((g.op = GateOp.and ∧ g.inputs = [0, 13]) ∨
            (g.op = GateOp.or ∧ g.inputs ∈ ([[0, 1], [0, 13], [2, 13]] : List (List ℕ))))) ∧
        (∀ p l : Fin 13, p + l ∈ D →
          C.eval (List.ofFn (pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l))) = true) ∧
        (∀ S : Finset (Fin 13), S.card ≤ 3 →
          C.eval (List.ofFn (Fin.addCases (fun p => decide (p ∈ S))
            (fun l => decide (∀ p ∈ S, p + l ∉ D)))) = false ∧
          C.eval (List.ofFn (Fin.addCases (fun p => decide (∀ l ∈ S, p + l ∉ D))
            (fun l => decide (l ∈ S)))) = false)) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let E : List (ℕ × ℕ) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
  obtain ⟨C, hm, hs, _, hpos, hneg⟩ := hSearch
  refine ⟨C, hm, hs, ?_⟩
  change ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 26, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true
  have incident : ∀ p l : Fin 13,
      ((Fin.castAdd 13 p).val, (Fin.natAdd 13 l).val) ∈ E ↔ p + l ∈ D := by decide
  have bounds : ∀ u v : Fin 26, (u.val, v.val) ∈ E → u.val < 13 ∧ 13 ≤ v.val := by decide
  have evalAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have fold_mono (gs : List Gate)
      (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (a b : List Bool) (hab : ∀ i, a.getD i false = true → b.getD i false = true)
      (hlen : a.length = b.length) :
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) a).getD i false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) b).getD i false = true := by
    induction gs generalizing a b with
    | nil => exact hab
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hg : g.op.eval (g.inputs.map fun j => a.getD j false) = true →
          g.op.eval (g.inputs.map fun j => b.getD j false) = true := by
        rcases hm g (by simp) with h | h
        · simp only [h, evalAnd, List.all_map]
          rw [List.all_eq_true, List.all_eq_true]
          exact fun he j hj => hab j (he j hj)
        · simp only [h, evalOr, List.any_map]
          rw [List.any_eq_true, List.any_eq_true]
          rintro ⟨j, hj, he⟩
          exact ⟨j, hj, hab j he⟩
      apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg')) _ _ _ (by simp [hlen])
      intro i hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append, ← hlen] at hi ⊢
      split at hi <;> rename_i hlt
      · simp only [ite_eq_left hlt]
        exact hab _ hi
      · simp only [ite_eq_right hlt]
        by_cases he : i = a.length
        · subst i
          simpa using hg (by simpa using hi)
        · cases hs : i - a.length with
          | zero =>
            exact (he (Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hs) (Nat.le_of_not_gt hlt))).elim
          | succ k => simp [hs] at hi

  have eval_mono {n : ℕ} {x y : Fin n → Bool}
      (hxy : ∀ i, x i = true → y i = true) :
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    apply fold_mono _ (fun g hg => by simpa using (hm g hg).1) _ _ _ (by simp)
    intro i hi
    by_cases h : i < n
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] using
        hxy ⟨i, h⟩ (by simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] using hi)
    · simp [List.getD_eq_getElem?_getD, h] at hi
  intro x
  constructor
  · intro hx
    by_contra! hn
    let P : Finset (Fin 13) := Finset.univ.filter fun p => x (Fin.castAdd 13 p) = true
    let L : Finset (Fin 13) := Finset.univ.filter fun l => x (Fin.natAdd 13 l) = true
    have hind : ∀ p ∈ P, ∀ l ∈ L, p + l ∉ D := by
      intro p hp l hl hi
      exact hn _ _ ((incident p l).2 hi) (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hl).2
    rcases hGeometry P L hind with hp | hl
    · let y : Fin 26 → Bool := fun i =>
          Fin.addCases (m := 13) (n := 13) (motive := fun _ => Bool)
            (fun p => decide (p ∈ P)) (fun l => decide (∀ p ∈ P, p + l ∉ D)) i
      have hle : ∀ i : Fin 26, x i = true → y i = true := by
        intro i
        refine Fin.addCases (m := 13) (n := 13)
          (motive := fun j => x j = true → y j = true) ?_ ?_ i
        · intro p h
          simp only [y, Fin.addCases_left, decide_eq_true_eq]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        · intro l h
          simp only [y, Fin.addCases_right, decide_eq_true_eq]
          exact fun p hp' => hind p hp' l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact Bool.false_ne_true ((hneg P hp).1.symm.trans (eval_mono hle hx))
    · let y : Fin 26 → Bool := fun i =>
          Fin.addCases (m := 13) (n := 13) (motive := fun _ => Bool)
            (fun p => decide (∀ l ∈ L, p + l ∉ D)) (fun l => decide (l ∈ L)) i
      have hle : ∀ i : Fin 26, x i = true → y i = true := by
        intro i
        refine Fin.addCases (m := 13) (n := 13)
          (motive := fun j => x j = true → y j = true) ?_ ?_ i
        · intro p h
          simp only [y, Fin.addCases_left, decide_eq_true_eq]
          exact fun l hl' => hind p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩) l hl'
        · intro l h
          simp only [y, Fin.addCases_right, decide_eq_true_eq]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      exact Bool.false_ne_true ((hneg L hl).2.symm.trans (eval_mono hle hx))
  · rintro ⟨u, v, huv, hu, hv⟩
    obtain ⟨hu', hv'⟩ := bounds u v huv
    let p : Fin 13 := ⟨u.val, hu'⟩
    let l : Fin 13 := ⟨v.val - 13, (Nat.sub_lt_iff_lt_add hv').2 v.isLt⟩
    have he₁ : Fin.castAdd 13 p = u := Fin.ext rfl
    have he₂ : Fin.natAdd 13 l = v := Fin.ext (Nat.add_sub_of_le hv')
    have hi : p + l ∈ D := (incident p l).1 (by simpa only [he₁, he₂] using huv)
    apply eval_mono _ (hpos p l hi)
    intro i h
    rcases of_decide_eq_true h with rfl | rfl
    · simpa only [he₁] using hu
    · simpa only [he₂] using hv
