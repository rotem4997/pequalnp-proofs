import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_wiresStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wiresStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wiresStep, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
    (w ++ [b]).getD m false = b := by
  subst hm
  simp [List.getD_eq_getElem?_getD]

private lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

private def negRemap {n : ℕ} (u : Fin n) (i : ℕ) : ℕ :=
  if i < n then (if i = u.val then n else i) else i + 1

private def prependNot {n : ℕ} (u v : Fin n) (C : Circuit) : Circuit :=
  ⟨Gate.mk GateOp.not [v.val] ::
    C.gates.map (fun g => Gate.mk g.op (g.inputs.map (negRemap u))),
    negRemap u C.output⟩

private lemma prependNot_wires {n : ℕ} (u v : Fin n) (gs : List Gate) (x : Fin n → Bool) :
    let x' := Function.update x u (!(x v))
    let w0 := List.ofFn x ++ [!(x v)]
    ∀ i : ℕ,
      ((gs.map fun g => Gate.mk g.op (g.inputs.map (negRemap u))).foldl wiresStep w0).getD
        (negRemap u i) false =
      (gs.foldl wiresStep (List.ofFn x')).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro x' w0 i
    change w0.getD (negRemap u i) false = (List.ofFn x').getD i false
    by_cases hin : i < n
    · simp only [negRemap, hin, ite_true]
      by_cases hiu : i = u.val
      · simp only [hiu, ite_true]
        rw [getD_append_last_eq (List.ofFn x) _ n List.length_ofFn, getD_ofFn x' u.val u.isLt]
        simp [x']
      · simp only [hiu, ite_false]
        have hlt : i < (List.ofFn x).length := by simp [hin]
        rw [show w0.getD i false = (List.ofFn x).getD i false by
          simp [w0, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]]
        rw [getD_ofFn x i hin, getD_ofFn x' i hin]
        have hne : (⟨i, hin⟩ : Fin n) ≠ u := fun h => hiu (congrArg Fin.val h)
        simp [x', Function.update, hne]
    · simp only [negRemap, hin, ite_false]
      rw [getD_ge_length w0 (i + 1) (by simp [w0]; omega),
        getD_ge_length (List.ofFn x') i (by simp; omega)]
  | append_singleton gs g ih =>
    intro x' w0 i
    rw [List.map_append, List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons,
      List.foldl_nil, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set a := (gs.map fun g => Gate.mk g.op (g.inputs.map (negRemap u))).foldl wiresStep w0
    set b := gs.foldl wiresStep (List.ofFn x')
    have ha : a.length = n + 1 + gs.length := by
      rw [foldl_wiresStep_length, List.length_map]
      simp [w0]
    have hb : b.length = n + gs.length := by
      rw [foldl_wiresStep_length, List.length_ofFn]
    have hval : g.op.eval ((g.inputs.map (negRemap u)).map fun k => a.getD k false) =
        g.op.eval (g.inputs.map fun k => b.getD k false) := by
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      exact ih k
    change (a ++ [g.op.eval ((g.inputs.map (negRemap u)).map fun k => a.getD k false)]).getD
        (negRemap u i) false =
      (b ++ [g.op.eval (g.inputs.map fun k => b.getD k false)]).getD i false
    rw [hval]
    set val := g.op.eval (g.inputs.map fun k => b.getD k false)
    by_cases hlt : i < n + gs.length
    · have hlt' : negRemap u i < a.length := by
        dsimp only [negRemap]; split_ifs <;> omega
      rw [show (a ++ [val]).getD (negRemap u i) false = a.getD (negRemap u i) false by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt']]
      rw [show (b ++ [val]).getD i false = b.getD i false by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < b.length)]]
      exact ih i
    · by_cases heq : i = n + gs.length
      · subst heq
        have hrm : negRemap u (n + gs.length) = n + 1 + gs.length := by
          dsimp only [negRemap]; split_ifs <;> omega
        rw [hrm, getD_append_last_eq a val _ ha, getD_append_last_eq b val _ hb]
      · have hgt' : a.length + 1 ≤ negRemap u i := by
          dsimp only [negRemap]; split_ifs <;> omega
        rw [getD_ge_length (a ++ [val]) _ (by simp [ha]; omega),
          getD_ge_length (b ++ [val]) _ (by simp [hb]; omega)]

end PEqualNP.Outside.LMeta592

theorem PEqualNP.Outside.L_meta_592 : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n), PEqualNP.MetaComplexity.HasCircuitSize n F s → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => F (Function.update x u (!(x v)))) (s + 1) := by
  rintro n s F u v ⟨C, hF, hsize, heval⟩
  refine ⟨PEqualNP.Outside.LMeta592.prependNot u v C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.LMeta592.prependNot, List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | ⟨g0, hg0, rfl⟩
    · exact ⟨by simp, by simp⟩
    · obtain ⟨hop, hlen⟩ := hF g0 hg0
      exact ⟨hop, by simp [hlen]⟩
  · simp only [PEqualNP.Outside.LMeta592.prependNot, PEqualNP.CircuitLowerBounds.Circuit.size,
      List.length_cons, List.length_map]
    change C.gates.length ≤ s at hsize
    omega
  · intro x
    change ((PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.not [v.val] ::
      C.gates.map fun g => PEqualNP.CircuitLowerBounds.Gate.mk g.op
        (g.inputs.map (PEqualNP.Outside.LMeta592.negRemap u))).foldl
        PEqualNP.Outside.LMeta592.wiresStep (List.ofFn x)).getD
          (PEqualNP.Outside.LMeta592.negRemap u C.output) false =
      F (Function.update x u (!(x v)))
    rw [List.foldl_cons]
    have hstep : PEqualNP.Outside.LMeta592.wiresStep (List.ofFn x)
        (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.not [v.val]) =
        List.ofFn x ++ [!(x v)] := by
      rw [PEqualNP.Outside.LMeta592.wiresStep]
      simp only [List.map_cons, List.map_nil, PEqualNP.Outside.LMeta592.getD_ofFn x v.val v.isLt,
        PEqualNP.CircuitLowerBounds.GateOp.eval, List.headD_cons]
    rw [hstep, PEqualNP.Outside.LMeta592.prependNot_wires u v C.gates x C.output]
    exact heval (Function.update x u (!(x v)))
