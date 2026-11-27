import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7529

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_app_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem stepW_len (w : List Bool) (g : Gate) : (stepW w g).length = w.length + 1 := by
  simp [stepW]

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, stepW_len]
    simp
    omega

theorem foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by rw [stepW_len]; omega
    rw [ih (stepW w g) hlt]
    simp only [stepW]
    exact getD_app_lt _ _ _ _ hi

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

theorem agree (a b : ℕ) (hab : b ≠ a) (gs : List Gate)
    (hg : ∀ g ∈ gs, a ∉ g.inputs ∨ (g.op = GateOp.or ∧ b ∈ g.inputs)) :
    ∀ (w w' : List Bool), w.length = w'.length → b < w.length → w.getD b false = true →
      (∀ i, i ≠ a → w.getD i false = w'.getD i false) →
      ∀ i, i ≠ a → (gs.foldl stepW w).getD i false = (gs.foldl stepW w').getD i false := by
  induction gs with
  | nil =>
    intro w w' _ _ _ hag i hi
    exact hag i hi
  | cons g gs ih =>
    intro w w' hlen hb hbt hag
    have hg1 := hg g (List.mem_cons_self)
    have hgs : ∀ g' ∈ gs, a ∉ g'.inputs ∨ (g'.op = GateOp.or ∧ b ∈ g'.inputs) :=
      fun g' hm => hg g' (List.mem_cons_of_mem _ hm)
    simp only [List.foldl_cons]
    apply ih hgs
    · rw [stepW_len, stepW_len, hlen]
    · rw [stepW_len]; omega
    · simp only [stepW]; rw [getD_app_lt _ _ _ _ hb]; exact hbt
    · intro i hi
      have hbt' : w'.getD b false = true := by rw [← hag b hab]; exact hbt
      have hval : g.op.eval (g.inputs.map fun i => w.getD i false)
          = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
        rcases hg1 with hna | ⟨hor, hbin⟩
        · congr 1
          apply List.map_congr_left
          intro j hj
          apply hag
          intro hja
          exact hna (hja ▸ hj)
        · rw [hor]
          simp only [GateOp.eval]
          have h1 : (g.inputs.map fun i => w.getD i false).any id = true := by
            rw [List.any_eq_true]
            exact ⟨w.getD b false, List.mem_map.mpr ⟨b, hbin, rfl⟩, hbt⟩
          have h2 : (g.inputs.map fun i => w'.getD i false).any id = true := by
            rw [List.any_eq_true]
            exact ⟨w'.getD b false, List.mem_map.mpr ⟨b, hbin, rfl⟩, hbt'⟩
          rw [h1, h2]
      simp only [stepW]
      rcases lt_trichotomy i w.length with hlt | heq | hgt
      · rw [getD_app_lt _ _ _ _ hlt, getD_app_lt _ _ _ _ (hlen ▸ hlt)]
        exact hag i hi
      · subst heq
        rw [getD_app_len]
        rw [hlen, getD_app_len]
        exact hval
      · rw [getD_ge _ _ _ (by simp; omega), getD_ge _ _ _ (by simp; omega)]

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · exact getD_ge _ _ _ (by simp; omega)

theorem main : ∀ (x1 : ℕ) (x2 : Circuit) (x3 x4 : Fin x1) (x5 : Fin x2.size), x3 ≠ x4 →
    (x2.gates.get x5).op = GateOp.or →
    (x2.gates.get x5).inputs = [↑x3, ↑x4] ∨ (x2.gates.get x5).inputs = [↑x4, ↑x3] →
    (∀ (x9 : Fin x2.size), ↑x3 ∈ (x2.gates.get x9).inputs → x9 = x5) →
    (circuitFun x1 x2 fun (x10 : Fin x1) => decide (x10 = x3)) = false →
    ∀ (x11 : Fin x1 → Bool), x11 x4 = true →
      circuitFun x1 x2 (Function.update x11 x3 true) =
        circuitFun x1 x2 (Function.update x11 x3 false) := by
  intro x1 x2 x3 x4 x5 hne hop hin huniq hind x11 h4
  have hab : (x4 : ℕ) ≠ (x3 : ℕ) := fun h => hne (Fin.ext h).symm
  have hg : ∀ g ∈ x2.gates, (x3 : ℕ) ∉ g.inputs ∨ (g.op = GateOp.or ∧ (x4 : ℕ) ∈ g.inputs) := by
    intro g hgm
    by_cases ha : (x3 : ℕ) ∈ g.inputs
    · right
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hgm
      have hj5 : j = x5 := huniq j (by rw [hj]; exact ha)
      subst hj5
      rw [← hj]
      refine ⟨hop, ?_⟩
      rcases hin with h | h <;> rw [h] <;> simp
    · left; exact ha
  have hag := agree (x3 : ℕ) (x4 : ℕ) hab x2.gates hg
    (List.ofFn (Function.update x11 x3 true)) (List.ofFn (Function.update x11 x3 false))
    (by simp) (by simp) (by
      rw [ofFn_getD, dif_pos x4.isLt]
      rw [Function.update_of_ne (fun h => hne h.symm)]
      exact h4)
    (by
      intro i hi
      rw [ofFn_getD, ofFn_getD]
      split_ifs with h
      · have hne' : (⟨i, h⟩ : Fin x1) ≠ x3 := fun h' => hi (congrArg Fin.val h')
        rw [Function.update_of_ne hne', Function.update_of_ne hne']
      · rfl)
  simp only [circuitFun, Circuit.eval, wires_eq]
  by_cases ho : x2.output = (x3 : ℕ)
  · exfalso
    simp only [circuitFun, Circuit.eval, wires_eq, ho] at hind
    rw [foldl_getD_lt _ _ _ (by simp), ofFn_getD, dif_pos x3.isLt] at hind
    simp at hind
  · exact hag _ ho

end PEqualNP.Outside.L_meta_7529

theorem PEqualNP.Outside.L_meta_7529 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1) (x5 : Fin x2.size), x3 ≠ x4 → (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or → (x2.gates.get x5).inputs = [↑x3, ↑x4] ∨ (x2.gates.get x5).inputs = [↑x4, ↑x3] → (∀ (x9 : Fin x2.size), ↑x3 ∈ (x2.gates.get x9).inputs → x9 = x5) → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x10 : Fin x1) => Decidable.decide (x10 = x3)) = Bool.false → ∀ (x11 : Fin x1 → Bool), x11 x4 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x11 x3 Bool.true) = PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x11 x3 Bool.false) :=
  PEqualNP.Outside.L_meta_7529.main
