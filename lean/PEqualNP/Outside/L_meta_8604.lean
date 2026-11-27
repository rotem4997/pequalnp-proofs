import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8604_aux

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc {α : Type} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i < l.length then l.getD i d else if i = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

lemma fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

lemma fold_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    simp only [stepW]; rw [getD_snoc, if_pos hi]

lemma unread (gs : List Gate) (p : ℕ) (hp : ∀ g ∈ gs, p ∉ g.inputs) :
    ∀ w w' : List Bool, w.length = w'.length →
      (∀ i, i ≠ p → w.getD i false = w'.getD i false) →
      ∀ i, i ≠ p → (gs.foldl stepW w).getD i false = (gs.foldl stepW w').getD i false := by
  induction gs with
  | nil => intro w w' _ h; simpa using h
  | cons g gs ih =>
    intro w w' hl h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hp g' (List.mem_cons_of_mem _ hg'))
    · simp [stepW, hl]
    · intro i hi
      have hv : g.op.eval (g.inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => w'.getD i false) := by
        rw [List.map_congr_left (fun j hj => h j (fun e => hp g (List.mem_cons_self ..) (e ▸ hj)))]
      simp only [stepW]
      rw [getD_snoc, getD_snoc, hl, hv]
      split_ifs
      · exact h i hi
      · rfl
      · rfl

lemma all_perm (l l' : List Bool) (h : l.Perm l') : l.all id = l'.all id := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, id]
  exact ⟨fun H b hb => H b (h.mem_iff.2 hb), fun H b hb => H b (h.mem_iff.1 hb)⟩

end PEqualNP.Outside.L_meta_8604_aux

open PEqualNP.Outside.L_meta_8604_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8604 : ∀ (x1 : ℕ) (x2 x3 x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : List ℕ) (x7 x8 : ℕ),   have x9 : ℕ := x1 + x2.length;   have x10 : List ℕ → List ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x10 x11 : List ℕ) => { gates := x2 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := x10 : PEqualNP.CircuitLowerBounds.Gate } :: (x3 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := x11 : PEqualNP.CircuitLowerBounds.Gate } :: x4), output := x8 : PEqualNP.CircuitLowerBounds.Circuit };   x6.Perm [x9, x7] → x7 < x9 → (∀ x13 ∈ x5, x13 < x9) → x8 ≠ x9 → (∀ x15 ∈ x3 ++ x4, x9 ∉ x15.inputs) → PEqualNP.MetaComplexity.circuitFun x1 (x10 (List.take (1 : ℕ) x5 ++ [x7]) (x9 :: List.drop (1 : ℕ) x5)) = PEqualNP.MetaComplexity.circuitFun x1 (x10 x5 x6) := by
  intro n P M S a5 a6 q out
  dsimp only
  intro hperm hq ha5 hout hread
  funext x
  show List.getD (List.foldl stepW (List.ofFn x) _) out false =
    List.getD (List.foldl stepW (List.ofFn x) _) out false
  simp only [List.foldl_append, List.foldl_cons]
  set p := n + P.length with hp
  set w0 := P.foldl stepW (List.ofFn x) with hw0
  have hl0 : w0.length = p := by rw [hw0, fold_len]; simp [hp]
  have hM : ∀ g ∈ M, p ∉ g.inputs := fun g hg => hread g (List.mem_append_left _ hg)
  have hS : ∀ g ∈ S, p ∉ g.inputs := fun g hg => hread g (List.mem_append_right _ hg)
  set w1 := stepW w0 ⟨GateOp.and, a5⟩ with hw1
  set w1' := stepW w0 ⟨GateOp.and, List.take 1 a5 ++ [q]⟩ with hw1'
  have hl1 : w1.length = p + 1 := by simp [hw1, stepW, hl0]
  have hl1' : w1'.length = p + 1 := by simp [hw1', stepW, hl0]
  have e1 : ∀ i, i ≠ p → w1'.getD i false = w1.getD i false := by
    intro i hi
    simp only [hw1, hw1', stepW]
    rw [getD_snoc, getD_snoc, hl0, if_neg hi, if_neg hi]
  set w2 := M.foldl stepW w1 with hw2
  set w2' := M.foldl stepW w1' with hw2'
  have hl2 : w2.length = w2'.length := by rw [hw2, hw2', fold_len, fold_len, hl1, hl1']
  have e2 := unread M p hM w1' w1 (by rw [hl1, hl1']) e1
  have lo : ∀ i, i < p → w2.getD i false = w0.getD i false ∧ w2'.getD i false = w0.getD i false := by
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [hw2, fold_prefix _ _ _ (by omega), hw1]
      simp only [stepW]; rw [getD_snoc, if_pos (by omega)]
    · rw [hw2', fold_prefix _ _ _ (by omega), hw1']
      simp only [stepW]; rw [getD_snoc, if_pos (by omega)]
  have atp : w2.getD p false = (a5.map fun i => w0.getD i false).all id ∧
      w2'.getD p false = ((List.take 1 a5 ++ [q]).map fun i => w0.getD i false).all id := by
    refine ⟨?_, ?_⟩
    · rw [hw2, fold_prefix _ _ _ (by omega), hw1]
      simp only [stepW]; rw [getD_snoc, if_neg (by omega), if_pos hl0.symm]; rfl
    · rw [hw2', fold_prefix _ _ _ (by omega), hw1']
      simp only [stepW]; rw [getD_snoc, if_neg (by omega), if_pos hl0.symm]; rfl
  have hB : (GateOp.and).eval ((p :: List.drop 1 a5).map fun i => w2'.getD i false) =
      (GateOp.and).eval (a6.map fun i => w2.getD i false) := by
    simp only [GateOp.eval]
    rw [all_perm _ _ (hperm.map _)]
    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
    rw [atp.1, atp.2, (lo q hq).1]
    have hd : (List.drop 1 a5).map (fun i => w2'.getD i false) =
        (List.drop 1 a5).map (fun i => w0.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact (lo i (ha5 i (List.mem_of_mem_drop hi))).2
    rw [hd]
    conv_rhs => rw [← List.take_append_drop 1 a5]
    simp only [List.map_append, List.all_append, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id, Bool.and_true]
    cases (List.map (fun i => w0.getD i false) (List.take 1 a5)).all id <;>
      cases w0.getD q false <;> simp
  have e3 : ∀ i, i ≠ p → (stepW w2' ⟨GateOp.and, p :: List.drop 1 a5⟩).getD i false =
      (stepW w2 ⟨GateOp.and, a6⟩).getD i false := by
    intro i hi
    simp only [stepW]
    rw [getD_snoc, getD_snoc, hl2, hB]
    split_ifs
    · exact e2 i hi
    · rfl
    · rfl
  exact unread S p hS _ _ (by simp [stepW, hl2]) e3 out hout
