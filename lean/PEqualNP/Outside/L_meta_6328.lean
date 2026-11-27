import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6328

open PEqualNP.CircuitLowerBounds

theorem getD_snoc {α : Type} (L : List α) (a d : α) (w : ℕ) :
    (L ++ [a]).getD w d = if w < L.length then L.getD w d else if w = L.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]; simp

-- one step of evaluation, as in the definition of the wires
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

-- evaluation never changes an existing wire
theorem run_prefix (gs : List Gate) (W : List Bool) (i : ℕ) (hi : i < W.length) :
    (gs.foldl wstep W).getD i false = W.getD i false := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (wstep W g) (by simp [wstep]; omega)]
    rw [wstep, getD_snoc, if_pos hi]

-- two runs from inputs that differ only at wire a stay equal off a, when every gate either
-- does not read a or is an OR reading a wire b that is true in both
theorem run_agree (a b : ℕ) (gs : List Gate)
    (H : ∀ g ∈ gs, a ∉ g.inputs ∨ (g.op = GateOp.or ∧ b ∈ g.inputs))
    (X Y : List Bool) (hl : X.length = Y.length) (hbl : b < X.length)
    (hag : ∀ i, i ≠ a → X.getD i false = Y.getD i false)
    (hbX : X.getD b false = true) (hbY : Y.getD b false = true) :
    ∀ i, i ≠ a → (gs.foldl wstep X).getD i false = (gs.foldl wstep Y).getD i false := by
  induction gs generalizing X Y with
  | nil => exact hag
  | cons g gs ih =>
    have Hg := H g (by simp)
    have hv : g.op.eval (g.inputs.map fun i => X.getD i false) =
        g.op.eval (g.inputs.map fun i => Y.getD i false) := by
      rcases Hg with h | ⟨hop, hb⟩
      · congr 1
        apply List.map_congr_left
        intro i hi
        exact hag i (fun e => h (e ▸ hi))
      · rw [hop]
        simp only [GateOp.eval]
        have e1 : (g.inputs.map fun i => X.getD i false).any id = true := by
          rw [List.any_eq_true]
          exact ⟨true, List.mem_map.mpr ⟨b, hb, hbX⟩, rfl⟩
        have e2 : (g.inputs.map fun i => Y.getD i false).any id = true := by
          rw [List.any_eq_true]
          exact ⟨true, List.mem_map.mpr ⟨b, hb, hbY⟩, rfl⟩
        rw [e1, e2]
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => H g' (by simp [hg']))
    · simp [wstep, hl]
    · simp [wstep]; omega
    · intro i hi
      simp only [wstep, getD_snoc, hl, hv]
      split_ifs
      · exact hag i hi
      · rfl
      · rfl
    · simp only [wstep, getD_snoc]
      rw [if_pos hbl, hbX]
    · simp only [wstep, getD_snoc]
      rw [if_pos (hl ▸ hbl), hbY]

theorem ofFn_getD (y : Fin 9 → Bool) (i : ℕ) :
    (List.ofFn y).getD i false = if h : i < 9 then y ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · interval_cases i <;> rfl
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

def F : (Fin 9 → Bool) → Bool := fun (x5 : Fin (9 : ℕ) → Bool) => [(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)].any fun (x6 : ℕ) => Decidable.decide (∀ (x7 : Fin (9 : ℕ)), x6.testBit ↑x7 = Bool.true → x5 x7 = Bool.true)

theorem wit : ∀ a ∈ [(4 : Fin 9), 6, 7], ∀ b : Fin 9, a ≠ b → ∃ c : Fin 9, c ≠ a ∧
    F (fun i => decide (i = b ∨ i = c ∨ i = a)) = true ∧
    F (fun i => decide (i = b ∨ i = c)) = false := by
  decide +kernel

theorem single : ∀ a : Fin 9, F (fun i => decide (i = a)) = false := by
  decide +kernel

theorem main (C : Circuit) (a b : Fin 9) (j : Fin C.gates.length)
    (hf : ∀ y, PEqualNP.MetaComplexity.circuitFun 9 C y = F y)
    (ha : a ∈ [(4 : Fin 9), 6, 7]) (hab : a ≠ b)
    (hor : (C.gates.get j).op = GateOp.or)
    (honly : ∀ i : Fin C.gates.length, (a : ℕ) ∈ (C.gates.get i).inputs ↔ i = j)
    (hb : (b : ℕ) ∈ (C.gates.get j).inputs) : False := by
  have H : ∀ g ∈ C.gates, (a : ℕ) ∉ g.inputs ∨ (g.op = GateOp.or ∧ (b : ℕ) ∈ g.inputs) := by
    intro g hg
    by_cases h : (a : ℕ) ∈ g.inputs
    · right
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
      have := (honly i).1 h
      subst this
      exact ⟨hor, hb⟩
    · exact Or.inl h
  by_cases ho : C.output = (a : ℕ)
  · have h1 := hf (fun i => decide (i = a))
    rw [single a] at h1
    revert h1
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, wires_eq, ho]
    rw [run_prefix _ _ _ (by simp), ofFn_getD, dif_pos a.isLt]
    simp
  · obtain ⟨c, hca, h1, h0⟩ := wit a ha b hab
    have e := run_agree a b C.gates H
      (List.ofFn (fun i => decide (i = b ∨ i = c ∨ i = a)))
      (List.ofFn (fun i => decide (i = b ∨ i = c))) (by simp) (by simp)
      (by
        intro i hi
        rw [ofFn_getD, ofFn_getD]
        split_ifs with h
        · have : (⟨i, h⟩ : Fin 9) ≠ a := fun e => hi (by rw [← e])
          simp [this]
        · rfl)
      (by rw [ofFn_getD, dif_pos b.isLt]; simp)
      (by rw [ofFn_getD, dif_pos b.isLt]; simp)
      C.output ho
    have e1 := hf (fun i => decide (i = b ∨ i = c ∨ i = a))
    have e0 := hf (fun i => decide (i = b ∨ i = c))
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, wires_eq] at e1 e0
    rw [e, e0, h0] at e1
    rw [h1] at e1
    exact Bool.false_ne_true e1

end PEqualNP.Outside.L_meta_6328

theorem PEqualNP.Outside.L_meta_6328 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (9 : ℕ)) (x4 : Fin x1.size), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => [(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)].any fun (x6 : ℕ) => Decidable.decide (∀ (x7 : Fin (9 : ℕ)), x6.testBit ↑x7 = Bool.true → x5 x7 = Bool.true)) → x2 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))] → x2 ≠ x3 → (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or → (∀ (x9 : Fin x1.size), ↑x2 ∈ (x1.gates.get x9).inputs ↔ x9 = x4) → ↑x3 ∉ (x1.gates.get x4).inputs := by
  intro C a b j hf ha hab hor honly hb
  exact PEqualNP.Outside.L_meta_6328.main C a b j
    (fun y => by rw [hf]; rfl) ha hab hor honly hb
