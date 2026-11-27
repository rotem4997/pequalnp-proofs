import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8891

open PEqualNP.CircuitLowerBounds

def Dom (g g' : Gate) : Prop :=
  ∀ w w' : List Bool, (∀ i, w.getD i false = true → w'.getD i false = true) →
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
    g'.op.eval (g'.inputs.map fun i => w'.getD i false) = true

theorem dom_self (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) : Dom g g := by
  intro w w' hw h
  rcases hg with hg | hg <;> rw [hg] at h ⊢ <;> simp [GateOp.eval] at h ⊢
  · intro i hi; exact hw i (h i hi)
  · obtain ⟨i, hi, h⟩ := h; exact ⟨i, hi, hw i h⟩

theorem dom_new (x3 x4 x5 : ℕ) (h5 : x5 = x3 ∨ x5 = x4) :
    Dom ⟨GateOp.and, [x3, x4]⟩ ⟨GateOp.and, [x5]⟩ := by
  intro w w' hw h
  simp [GateOp.eval] at h ⊢
  rcases h5 with rfl | rfl
  · exact hw _ h.1
  · exact hw _ h.2

theorem getD_app (L : List Bool) (a : Bool) (i : ℕ) :
    (L ++ [a]).getD i false = if i < L.length then L.getD i false else if i = L.length then a else false := by
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default]; simp; omega

theorem fold_mono : ∀ (gs gs' : List Gate), List.Forall₂ Dom gs gs' →
    ∀ w w' : List Bool, w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      (gs'.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').length ∧
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = true →
      (gs'.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD i false = true := by
  intro gs gs' hF
  induction hF with
  | nil => intro w w' hl hw; exact ⟨hl, hw⟩
  | @cons g g' gs gs' hd _ ih =>
    intro w w' hl hw
    simp only [List.foldl_cons]
    apply ih
    · simp [hl]
    · intro i hi
      rw [getD_app] at hi ⊢
      rw [← hl]
      split_ifs at hi ⊢ with h1 h2
      · exact hw i hi
      · exact hd w w' hw hi

theorem forall2_set : ∀ (gs : List Gate) (k : ℕ) (g0 g' : Gate), (∀ g ∈ gs, Dom g g) →
    gs[k]? = some g0 → Dom g0 g' → List.Forall₂ Dom gs (gs.set k g') := by
  intro gs
  induction gs with
  | nil => intro k g0 g' _ h; simp at h
  | cons x xs ih =>
    intro k g0 g' hs hk hd
    cases k with
    | zero =>
      simp at hk; subst hk
      simp only [List.set_cons_zero]
      exact List.Forall₂.cons hd (List.forall₂_same.mpr (fun a ha => hs a (by simp [ha])))
    | succ k =>
      simp only [List.set_cons_succ]
      simp at hk
      exact List.Forall₂.cons (hs x (by simp)) (ih k g0 g' (fun a ha => hs a (by simp [ha])) hk hd)

theorem countP_set (p : Gate → Bool) : ∀ (l : List Gate) (k : ℕ) (a b : Gate), l[k]? = some a →
    List.countP p (l.set k b) + (if p a then 1 else 0) = List.countP p l + (if p b then 1 else 0) := by
  intro l
  induction l with
  | nil => intro k a b h; simp at h
  | cons x xs ih =>
    intro k a b hk
    cases k with
    | zero =>
      simp at hk; subst hk
      simp only [List.set_cons_zero, List.countP_cons]
      omega
    | succ k =>
      simp at hk
      simp only [List.set_cons_succ, List.countP_cons]
      have := ih k a b hk
      omega

end PEqualNP.Outside.L_meta_8891

theorem PEqualNP.Outside.L_meta_8891 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 x4 x5 : ℕ),   x1.gates[x2]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } →     x5 = x3 ∨ x5 = x4 →       have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1.gates.set x2 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }, output := x1.output : PEqualNP.CircuitLowerBounds.Circuit };       PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size = x1.size ∧ List.countP (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => x10.inputs.length == (2 : ℕ)) x8.gates < List.countP (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => x10.inputs.length == (2 : ℕ)) x1.gates ∧ ∀ (x10 : List Bool), x1.eval x10 = Bool.true → x8.eval x10 = Bool.true := by
  intro C k x3 x4 x5 hk h5 C' hM
  have hmono : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have := (hM g hg).1
    simpa using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_or_eq_of_mem_set hg with hg | hg
    · exact hM g hg
    · subst hg; simp
  · simp [C', PEqualNP.CircuitLowerBounds.Circuit.size]
  · have := PEqualNP.Outside.L_meta_8891.countP_set
      (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => x10.inputs.length == (2 : ℕ)) C.gates k _
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5] } hk
    simp at this
    show _ < _
    simp only [C']
    omega
  · intro x hx
    have hF := PEqualNP.Outside.L_meta_8891.forall2_set C.gates k _ _
      (fun g hg => PEqualNP.Outside.L_meta_8891.dom_self g (hmono g hg)) hk
      (PEqualNP.Outside.L_meta_8891.dom_new x3 x4 x5 h5)
    have := (PEqualNP.Outside.L_meta_8891.fold_mono _ _ hF x x rfl (fun i h => h)).2 C.output
    exact this hx
