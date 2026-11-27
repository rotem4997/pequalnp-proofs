import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2864

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Le (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma le_refl (a : List Bool) : Le a a := ⟨rfl, fun _ h => h⟩

lemma le_app {a a' b b' : List Bool} (h1 : Le a a') (h2 : Le b b') : Le (a ++ b) (a' ++ b') := by
  have hl := h1.1
  refine ⟨by simp [h1.1, h2.1], fun i hi => ?_⟩
  by_cases hlt : i < a.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h1.2 i hi
  · rw [not_lt] at hlt
    rw [List.getD_append_right _ _ _ _ hlt] at hi
    rw [List.getD_append_right _ _ _ _ (by omega), ← hl]
    exact h2.2 _ hi

lemma gate_mono (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) {w w' : List Bool}
    (h : ∀ i, w.getD i false = true → w'.getD i false = true)
    (hv : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg] at hv ⊢
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hv ⊢
    exact fun i hi => h i (hv i hi)
  · rw [Set.mem_singleton_iff] at hg
    rw [hg] at hv ⊢
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hv ⊢
    obtain ⟨i, hi, hv⟩ := hv
    exact ⟨i, hi, h i hv⟩

lemma fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ w w' : List Bool, Le w w' →
      Le (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
         (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    apply le_app h
    refine ⟨rfl, fun i hi => ?_⟩
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at hi ⊢
      exact gate_mono g (hgs g List.mem_cons_self) h.2 hi
    | succ i => simp at hi

lemma wmono {C : Circuit} (hC : Monotone2 C) {x y : List Bool} (h : Le x y) (k : ℕ)
    (hk : (C.wires x).getD k false = true) : (C.wires y).getD k false = true :=
  (fold_mono C.gates (fun g hg => (hC g hg).1) x y h).2 k hk

lemma le_false (n : ℕ) (l : Fin n → Bool) : Le (List.replicate n false) (List.ofFn l) := by
  refine ⟨by simp, fun i hi => ?_⟩
  exfalso
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate] at hi
  split at hi <;> simp at hi

lemma le_true (n : ℕ) (l : Fin n → Bool) : Le (List.ofFn l) (List.replicate n true) := by
  refine ⟨by simp, fun i hi => ?_⟩
  have hlt : i < n := by
    by_contra hge
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
    simp at hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_cond_eq_true _ _ (eq_true hlt)]
  rfl

lemma indepL {n : ℕ} {C : Circuit} (hC : Monotone2 C) (k : ℕ)
    (h : ∀ p : Fin n → Bool, (C.wires (List.ofFn p ++ List.replicate n false)).getD k false =
      (C.wires (List.ofFn p ++ List.replicate n true)).getD k false) (p l : Fin n → Bool) :
    (C.wires (List.ofFn p ++ List.ofFn l)).getD k false =
      (C.wires (List.ofFn p ++ List.replicate n false)).getD k false := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro hv
    rw [h p]
    exact wmono hC (le_app (le_refl _) (le_true n l)) k hv
  · exact wmono hC (le_app (le_refl _) (le_false n l)) k

lemma indepP {n : ℕ} {C : Circuit} (hC : Monotone2 C) (k : ℕ)
    (h : ∀ l : Fin n → Bool, (C.wires (List.replicate n false ++ List.ofFn l)).getD k false =
      (C.wires (List.replicate n true ++ List.ofFn l)).getD k false) (p l : Fin n → Bool) :
    (C.wires (List.ofFn p ++ List.ofFn l)).getD k false =
      (C.wires (List.replicate n false ++ List.ofFn l)).getD k false := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro hv
    rw [h l]
    exact wmono hC (le_app (le_true n p) (le_refl _)) k hv
  · exact wmono hC (le_app (le_false n p) (le_refl _)) k

lemma constW {n : ℕ} {C : Circuit} (k : ℕ)
    (HL : ∀ p l : Fin n → Bool, (C.wires (List.ofFn p ++ List.ofFn l)).getD k false =
      (C.wires (List.ofFn p ++ List.replicate n false)).getD k false)
    (HP : ∀ p l : Fin n → Bool, (C.wires (List.ofFn p ++ List.ofFn l)).getD k false =
      (C.wires (List.replicate n false ++ List.ofFn l)).getD k false) (p l : Fin n → Bool) :
    (C.wires (List.ofFn p ++ List.ofFn l)).getD k false =
      (C.wires (List.replicate n false ++ List.replicate n false)).getD k false := by
  rw [HP p l]
  have h := HL (fun _ => false) l
  rw [List.ofFn_const] at h
  exact h

lemma inc_of_acc {q n : ℕ} (inc : Fin n → Fin n → Prop) (C : Circuit) (hq : 0 < q)
    (hs : ∀ (x9 : Fin (n + n) → Bool), Fintype.card { x10 : Fin n // x9 (Fin.natAdd n x10) = Bool.true } ≤ q → (¬∃ (x11 : Fin n) (x12 : Fin n), inc x11 x12 ∧ x9 (Fin.castAdd n x11) = Bool.true ∧ x9 (Fin.natAdd n x12) = Bool.true) → circuitFun (n + n) C x9 = Bool.false)
    (a b : Fin n)
    (hacc : circuitFun (n + n) C (fun x20 : Fin (n + n) => decide (x20 = Fin.castAdd n a ∨ x20 = Fin.natAdd n b)) = true) : inc a b := by
  by_contra hinc
  have hsub : Subsingleton { x10 : Fin n // (fun x20 : Fin (n + n) => decide (x20 = Fin.castAdd n a ∨ x20 = Fin.natAdd n b)) (Fin.natAdd n x10) = Bool.true } := by
    constructor
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at hu hv
    apply Subtype.ext
    apply Fin.ext
    show (u : ℕ) = v
    have := a.isLt
    omega
  have hcard : Fintype.card { x10 : Fin n // (fun x20 : Fin (n + n) => decide (x20 = Fin.castAdd n a ∨ x20 = Fin.natAdd n b)) (Fin.natAdd n x10) = Bool.true } ≤ q := by
    have := Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  have hfalse := hs (fun x20 : Fin (n + n) => decide (x20 = Fin.castAdd n a ∨ x20 = Fin.natAdd n b)) hcard (by
    rintro ⟨a', b', hi, ha, hb⟩
    simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at ha hb
    have h1 := a'.isLt
    have h2 := a.isLt
    have ea : a' = a := Fin.ext (by omega)
    have eb : b' = b := Fin.ext (by omega)
    rw [ea, eb] at hi
    exact hinc hi)
  rw [hfalse] at hacc
  exact Bool.noConfusion hacc

lemma rect {q n : ℕ} (inc : Fin n → Fin n → Prop) (C : Circuit) (hq : 0 < q)
    (huniq : ∀ (x7 x8 : Fin n), x7 ≠ x8 → ∃! x10 : Fin n, inc x7 x10 ∧ inc x8 x10)
    (hs : ∀ (x9 : Fin (n + n) → Bool), Fintype.card { x10 : Fin n // x9 (Fin.natAdd n x10) = Bool.true } ≤ q → (¬∃ (x11 : Fin n) (x12 : Fin n), inc x11 x12 ∧ x9 (Fin.castAdd n x11) = Bool.true ∧ x9 (Fin.natAdd n x12) = Bool.true) → circuitFun (n + n) C x9 = Bool.false)
    (A B : (Fin n → Bool) → Bool)
    (hacc : ∀ a b : Fin n, (A (fun i => decide (i = a)) && B (fun i => decide (i = b))) = true →
      circuitFun (n + n) C (fun x20 : Fin (n + n) => decide (x20 = Fin.castAdd n a ∨ x20 = Fin.natAdd n b)) = true) :
    ∀ a a' b b' : Fin n, (A (fun i => decide (i = a)) && B (fun i => decide (i = b))) = true →
      (A (fun i => decide (i = a')) && B (fun i => decide (i = b'))) = true → a = a' ∨ b = b' := by
  intro a a' b b' h1 h2
  rw [Bool.and_eq_true] at h1 h2
  by_cases haa : a = a'
  · exact Or.inl haa
  · right
    have i1 := inc_of_acc inc C hq hs a b (hacc a b (by rw [Bool.and_eq_true]; exact ⟨h1.1, h1.2⟩))
    have i2 := inc_of_acc inc C hq hs a' b (hacc a' b (by rw [Bool.and_eq_true]; exact ⟨h2.1, h1.2⟩))
    have i3 := inc_of_acc inc C hq hs a b' (hacc a b' (by rw [Bool.and_eq_true]; exact ⟨h1.1, h2.2⟩))
    have i4 := inc_of_acc inc C hq hs a' b' (hacc a' b' (by rw [Bool.and_eq_true]; exact ⟨h2.1, h2.2⟩))
    exact (huniq a a' haa).unique ⟨i1, i2⟩ ⟨i3, i4⟩

end PEqualNP.Outside.L_meta_2864

theorem PEqualNP.Outside.L_meta_2864 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (0 : ℕ) < x1 →     (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10) →       PEqualNP.MetaComplexity.Monotone2 x5 →         (∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x9 = Bool.false) →           ∀ (x10 x11 : ℕ),             ¬((∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.false)).getD x12 Bool.false ≠ (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.true)).getD x12 Bool.false) ∨ ∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x14)).getD x12 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x14)).getD x12 Bool.false) →               have x13 : ℕ → (Fin x2 → Bool) → (Fin x2 → Bool) → Bool := fun (x13 : ℕ) (x14 x15 : Fin x2 → Bool) => (x5.wires (List.ofFn x14 ++ List.ofFn x15)).getD x13 Bool.false;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               (∃ x15 ∈ [x10, x11], ∀ (x16 x17 : Fin x2 → Bool), (x13 x10 x16 x17 && x13 x11 x16 x17) = x13 x15 x16 x17) ∨ ∃ (x15 : (Fin x2 → Bool) → Bool) (x16 : (Fin x2 → Bool) → Bool), (∀ (x17 x18 : Fin x2 → Bool), (x13 x10 x17 x18 && x13 x11 x17 x18) = (x15 x17 && x16 x18)) ∧ ((∀ (x17 x18 : Fin x2), (x15 (x14 x17) && x16 (x14 x18)) = Bool.true → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x20 : Fin (x2 + x2)) => Decidable.decide (x20 = Fin.castAdd x2 x17 ∨ x20 = Fin.natAdd x2 x18)) = Bool.true) → ∀ (x18 x19 x20 x21 : Fin x2), (x15 (x14 x18) && x16 (x14 x20)) = Bool.true → (x15 (x14 x19) && x16 (x14 x21)) = Bool.true → x18 = x19 ∨ x20 = x21) := by
  intro q n inc _ C hq huniq hC hs k1 k2 hnot
  dsimp only
  rw [not_or] at hnot
  obtain ⟨hnL, hnP⟩ := hnot
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, not_and_or, not_exists, not_not] at hnL hnP
  have rectL := PEqualNP.Outside.L_meta_2864.rect inc C hq huniq hs
  rcases hnL with hL | hL <;> rcases hnP with hP | hP
  · left
    have hc := PEqualNP.Outside.L_meta_2864.constW k1 (PEqualNP.Outside.L_meta_2864.indepL hC k1 hL) (PEqualNP.Outside.L_meta_2864.indepP hC k1 hP)
    cases hcv : (C.wires (List.replicate n false ++ List.replicate n false)).getD k1 false with
    | false => exact ⟨k1, by simp, fun p l => by rw [hc p l, hcv]; first | rfl | exact Bool.and_false _ | exact Bool.and_true _⟩
    | true => exact ⟨k2, by simp, fun p l => by rw [hc p l, hcv]; first | rfl | exact Bool.and_false _ | exact Bool.and_true _⟩
  · right
    have HL := PEqualNP.Outside.L_meta_2864.indepL hC k1 hL
    have HP := PEqualNP.Outside.L_meta_2864.indepP hC k2 hP
    exact ⟨(fun p => (C.wires (List.ofFn p ++ List.replicate n false)).getD k1 false), (fun l => (C.wires (List.replicate n false ++ List.ofFn l)).getD k2 false), fun p l => by rw [HL p l, HP p l], rectL (fun p => (C.wires (List.ofFn p ++ List.replicate n false)).getD k1 false) (fun l => (C.wires (List.replicate n false ++ List.ofFn l)).getD k2 false)⟩
  · right
    have HL := PEqualNP.Outside.L_meta_2864.indepL hC k2 hL
    have HP := PEqualNP.Outside.L_meta_2864.indepP hC k1 hP
    exact ⟨(fun p => (C.wires (List.ofFn p ++ List.replicate n false)).getD k2 false), (fun l => (C.wires (List.replicate n false ++ List.ofFn l)).getD k1 false), fun p l => by rw [HL p l, HP p l, Bool.and_comm], rectL (fun p => (C.wires (List.ofFn p ++ List.replicate n false)).getD k2 false) (fun l => (C.wires (List.replicate n false ++ List.ofFn l)).getD k1 false)⟩
  · left
    have hc := PEqualNP.Outside.L_meta_2864.constW k2 (PEqualNP.Outside.L_meta_2864.indepL hC k2 hL) (PEqualNP.Outside.L_meta_2864.indepP hC k2 hP)
    cases hcv : (C.wires (List.replicate n false ++ List.replicate n false)).getD k2 false with
    | false => exact ⟨k2, by simp, fun p l => by rw [hc p l, hcv]; first | rfl | exact Bool.and_false _ | exact Bool.and_true _⟩
    | true => exact ⟨k1, by simp, fun p l => by rw [hc p l, hcv]; first | rfl | exact Bool.and_false _ | exact Bool.and_true _⟩
