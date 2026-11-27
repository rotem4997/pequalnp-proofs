import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7585_aux

open PEqualNP.CircuitLowerBounds

theorem getD_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i < w.length then w.getD i false else if i = w.length then v else false := by
  rcases lt_trichotomy i w.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · have h1 : ¬ i < w.length := by omega
    have h2 : ¬ i = w.length := by omega
    have h3 : (w ++ [v]).length ≤ i := by simp; omega
    simp [List.getD_eq_getElem?_getD, h1, h2, List.getElem?_eq_none h3]

theorem pre (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by simp; omega), getD_snoc, if_pos hi]

theorem gate_eq (g : Gate) (k : ℕ) (w w' : List Bool)
    (hF : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hn : k ∉ List.take (bif g.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) g.inputs)
    (h : ∀ i, i ≠ k → w.getD i false = w'.getD i false) :
    g.op.eval (g.inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hF
  simp only at hop hlen hn ⊢
  have hall : k ∉ List.take 2 inputs →
      (inputs.map fun i => w.getD i false) = (inputs.map fun i => w'.getD i false) := by
    intro hk
    rw [List.take_of_length_le hlen] at hk
    apply List.map_congr_left
    intro a ha
    apply h
    rintro rfl
    exact hk ha
  cases op with
  | and => simp [GateOp.eval] at hn; rw [hall (by simpa using hn)]
  | or => simp [GateOp.eval] at hn; rw [hall (by simpa using hn)]
  | not =>
    cases inputs with
    | nil => rfl
    | cons a t =>
      simp [GateOp.eval] at hn
      have := h a (fun e => hn e.symm)
      simp only [List.getD_eq_getElem?_getD] at this
      simp [GateOp.eval, this]
  | mod m => simp at hop
  | maj => simp at hop

theorem key (k : ℕ) (gs : List Gate) : ∀ (w w' : List Bool),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ g ∈ gs, k ∉ List.take (bif g.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) g.inputs) →
    w.length = w'.length →
    (∀ i, i ≠ k → w.getD i false = w'.getD i false) →
    ∀ i, i ≠ k →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD i false := by
  induction gs with
  | nil => intro w w' _ _ _ h i hi; exact h i hi
  | cons g gs ih =>
    intro w w' hF hn hl h i hi
    rw [List.foldl_cons, List.foldl_cons]
    apply ih _ _ (fun g' hg' => hF g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hn g' (List.mem_cons_of_mem _ hg')) (by simp [hl]) _ i hi
    intro j hj
    rw [getD_snoc, getD_snoc, hl, h j hj,
      gate_eq g k w w' (hF g List.mem_cons_self) (hn g List.mem_cons_self) h]

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD i.val false = f i := by
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_7585_aux

theorem PEqualNP.Outside.L_meta_7585 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin x1), x2.Adj x5 x6 → PEqualNP.MetaComplexity.FanInTwo x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∃ x10 ∈ x4.gates, ↑x5 ∈ List.take (bif x10.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x10.inputs := by
  intro n G _ C u v huv hF hC
  by_contra hcon
  push_neg at hcon
  have hne : u ≠ v := G.ne_of_adj huv
  have ha := congrFun hC (fun i => decide (i = u ∨ i = v))
  have hb := congrFun hC (fun i => decide (i = v))
  have hc := congrFun hC (fun i => decide (i = u))
  have ga : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (fun i => decide (i = u ∨ i = v)) = true := by
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true, decide_eq_true_eq]
    right
    exact ⟨u, v, huv, by simp, by simp⟩
  have gb : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (fun i => decide (i = v)) = false := by
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    constructor
    · simp
    · rintro ⟨a, b, hab, h1, h2⟩
      simp at h1 h2
      subst h1
      subst h2
      exact (G.ne_of_adj hab) rfl
  have gc : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (fun i => decide (i = u)) = false := by
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    constructor
    · simp
    · rintro ⟨a, b, hab, h1, h2⟩
      simp at h1 h2
      subst h1
      subst h2
      exact (G.ne_of_adj hab) rfl
  rw [ga] at ha
  rw [gb] at hb
  rw [gc] at hc
  simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
    PEqualNP.CircuitLowerBounds.Circuit.wires] at ha hb hc
  by_cases ho : C.output = u.val
  · rw [ho, PEqualNP.Outside.L_meta_7585_aux.pre _ _ _ (by simp),
      PEqualNP.Outside.L_meta_7585_aux.ofFn_getD] at hc
    simp at hc
  · have := PEqualNP.Outside.L_meta_7585_aux.key u.val C.gates
      (List.ofFn fun i => decide (i = u ∨ i = v)) (List.ofFn fun i => decide (i = v))
      hF hcon (by simp) (by
        intro i hi
        by_cases h : i < n
        · have e := PEqualNP.Outside.L_meta_7585_aux.ofFn_getD (fun i => decide (i = u ∨ i = v)) ⟨i, h⟩
          have e' := PEqualNP.Outside.L_meta_7585_aux.ofFn_getD (fun i => decide (i = v)) ⟨i, h⟩
          simp only at e e'
          rw [e, e']
          have : (⟨i, h⟩ : Fin n) ≠ u := fun q => hi (by rw [← q])
          simp [this]
        · simp [List.getD_eq_getElem?_getD, h]) C.output ho
    rw [ha, hb] at this
    exact Bool.noConfusion this
