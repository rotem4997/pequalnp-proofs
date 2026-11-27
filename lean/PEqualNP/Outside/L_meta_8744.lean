import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8744

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

def Le (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, w.getD i false = true → w'.getD i false = true

theorem le_append {a a' b b' : List Bool} (h : Le a a') (h2 : Le b b') :
    Le (a ++ b) (a' ++ b') := by
  obtain ⟨hl, hp⟩ := h
  obtain ⟨hl2, hp2⟩ := h2
  refine ⟨by simp [hl, hl2], fun i hi => ?_⟩
  have hp' := hp i
  have hp2' := hp2 (i - a.length)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append] at hi hp' hp2' ⊢
  rw [← hl]
  by_cases hlt : i < a.length
  · simp only [hlt, ite_true] at hi ⊢
    exact hp' hi
  · simp only [hlt, ite_false] at hi ⊢
    exact hp2' hi

theorem le_snoc {w w' : List Bool} {v v' : Bool} (h : Le w w') (hv : v = true → v' = true) :
    Le (w ++ [v]) (w' ++ [v']) := by
  refine le_append h ⟨rfl, fun i hi => ?_⟩
  cases i with
  | zero => simpa using hv (by simpa using hi)
  | succ k => simp at hi

theorem gate_mono {w w' : List Bool} (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (h : Le w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun H i hi => h.2 i (H i hi)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, H⟩ => ⟨i, hi, h.2 i H⟩

theorem fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w w' : List Bool), Le w w' →
      Le (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
         (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (le_snoc h (gate_mono g (hgs g List.mem_cons_self) h))

theorem ofFn_le {n : ℕ} (a b : Fin n → Bool) (h : ∀ k, a k = true → b k = true) :
    Le (List.ofFn a) (List.ofFn b) := by
  refine ⟨by simp, fun i hi => ?_⟩
  simp only [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < n
  · simp only [List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some] at hi ⊢
    exact h _ hi
  · simp [hlt] at hi

theorem eval_mono {n m : ℕ} (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {X X' : Finset (Fin n)} {Y Y' : Finset (Fin m)} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    C.eval (incidenceInput X Y) = true → C.eval (incidenceInput X' Y') = true := by
  unfold Circuit.eval Circuit.wires incidenceInput
  refine (fold_mono C.gates hC _ _ (le_append (ofFn_le _ _ ?_) (ofFn_le _ _ ?_))).2 C.output
  · intro k hk
    simpa using hX (by simpa using hk)
  · intro k hk
    simpa using hY (by simpa using hk)

theorem acc_wit {n m : ℕ} (C : Circuit)
    (H : ∀ (X : Finset (Fin n)) (Y : Finset (Fin m)), C.eval (incidenceInput X Y) = true →
      (∀ p ∈ X, C.eval (incidenceInput (X.erase p) Y) = false) →
      (∀ l ∈ Y, C.eval (incidenceInput X (Y.erase l)) = false) → X.card = 1 ∧ Y.card = 1) :
    ∀ (k : ℕ) (X : Finset (Fin n)) (Y : Finset (Fin m)), X.card + Y.card = k →
      C.eval (incidenceInput X Y) = true →
      ∃ p ∈ X, ∃ l ∈ Y, C.eval (incidenceInput {p} {l}) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro X Y hk hacc
    by_cases h1 : ∃ p ∈ X, C.eval (incidenceInput (X.erase p) Y) = true
    · obtain ⟨p, hp, hpa⟩ := h1
      have hc := Finset.card_erase_of_mem hp
      have hpos := Finset.card_pos.mpr ⟨p, hp⟩
      obtain ⟨q, hq, l, hl, h⟩ := ih ((X.erase p).card + Y.card) (by omega) _ _ rfl hpa
      exact ⟨q, Finset.mem_of_mem_erase hq, l, hl, h⟩
    by_cases h2 : ∃ l ∈ Y, C.eval (incidenceInput X (Y.erase l)) = true
    · obtain ⟨l, hl, hla⟩ := h2
      have hc := Finset.card_erase_of_mem hl
      have hpos := Finset.card_pos.mpr ⟨l, hl⟩
      obtain ⟨q, hq, l', hl', h⟩ := ih (X.card + (Y.erase l).card) (by omega) _ _ rfl hla
      exact ⟨q, hq, l', Finset.mem_of_mem_erase hl', h⟩
    have hmin := H X Y hacc
      (fun p hp => by
        cases hb : C.eval (incidenceInput (X.erase p) Y) with
        | false => rfl
        | true => exact absurd ⟨p, hp, hb⟩ h1)
      (fun l hl => by
        cases hb : C.eval (incidenceInput X (Y.erase l)) with
        | false => rfl
        | true => exact absurd ⟨l, hl, hb⟩ h2)
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hmin.1
    obtain ⟨l, hl⟩ := Finset.card_eq_one.mp hmin.2
    subst hp
    subst hl
    exact ⟨p, Finset.mem_singleton_self p, l, Finset.mem_singleton_self l, hacc⟩

end PEqualNP.Outside.L_meta_8744

theorem PEqualNP.Outside.L_meta_8744 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →     (∀ (x4 x5 : Finset (Fin x1)), x2.eval (PEqualNP.GenericRejection.incidenceInput x4 x5) = Bool.true → (∀ x7 ∈ x4, x2.eval (PEqualNP.GenericRejection.incidenceInput (x4.erase x7) x5) = Bool.false) → (∀ x8 ∈ x5, x2.eval (PEqualNP.GenericRejection.incidenceInput x4 (x5.erase x8)) = Bool.false) → x4.card = (1 : ℕ) ∧ x5.card = (1 : ℕ)) →       have x5 : Fin x1 → Finset (Fin x1) := fun (x5 : Fin x1) => {x6 : Fin x1 | x2.eval (PEqualNP.GenericRejection.incidenceInput {x6} {x5}) = Bool.true};       PEqualNP.GenericRejection.ComputesIncidence x5 x2 := by
  intro x1 x2 hA H
  show PEqualNP.GenericRejection.ComputesIncidence _ x2
  intro X Y
  unfold PEqualNP.GenericRejection.incidenceFun
  cases hb : x2.eval (PEqualNP.GenericRejection.incidenceInput X Y) with
  | true =>
    obtain ⟨p, hp, l, hl, h⟩ := PEqualNP.Outside.L_meta_8744.acc_wit x2 H _ X Y rfl hb
    symm
    rw [decide_eq_true_eq]
    exact ⟨p, hp, l, hl, by simpa using h⟩
  | false =>
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨p, hp, l, hl, h⟩
    have h' : x2.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true := by simpa using h
    have := PEqualNP.Outside.L_meta_8744.eval_mono x2 hA.1
      (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl) h'
    rw [hb] at this
    exact Bool.noConfusion this
