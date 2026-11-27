import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2800_aux
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl


def cnt (n : ℕ) (gs : List Gate) : ℕ :=
  List.countP (fun i => decide (i < n)) (gs.flatMap Gate.inputs)

lemma cnt_snoc (n : ℕ) (gs : List Gate) (g : Gate) :
    cnt n (gs ++ [g]) = cnt n gs + List.countP (fun i => decide (i < n)) g.inputs := by
  simp [cnt, List.flatMap_append, List.countP_append]

lemma core (n : ℕ) : ∀ (gs : List Gate),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) →
    ∀ outs : List ℕ, ∃ gs' : List Gate, gs'.length = gs.length ∧
      (∀ g ∈ gs', g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) ∧
      (∀ o ∈ outs, ∀ f : Fin n → Bool, val gs' f o = val gs f o) ∧
      cnt n gs' + outs.countP (fun i => decide (i < n)) ≤ gs.length + outs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ outs
    refine ⟨[], rfl, by simp, fun _ _ _ => rfl, ?_⟩
    have := List.countP_le_length (p := fun i => decide (i < n)) (l := outs)
    simpa [cnt] using this
  | append_singleton gs g ih =>
    intro hfan outs
    have hfan' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    have hg := hfan g (by simp)
    by_cases hmem : n + gs.length ∈ outs
    · have hperm := List.perm_cons_erase hmem
      obtain ⟨gs', hlen, hf, hv, hc⟩ := ih hfan' (outs.erase (n + gs.length) ++ g.inputs)
      refine ⟨gs' ++ [g], by simp [hlen], ?_, ?_, ?_⟩
      · intro g' hg'
        rcases List.mem_append.mp hg' with h | h
        · exact hf g' h
        · rw [List.mem_singleton.mp h]
          exact hg
      · intro o ho f
        rw [val_snoc, val_snoc, hlen]
        by_cases ho' : o = n + gs.length
        · rw [if_pos ho', if_pos ho']
          congr 1
          apply List.map_congr_left
          intro j hj
          exact hv j (List.mem_append_right _ hj) f
        · rw [if_neg ho', if_neg ho']
          have hoe : o ∈ outs.erase (n + gs.length) := by
            have h3 := hperm.mem_iff.mp ho
            rcases List.mem_cons.mp h3 with h | h
            · exact absurd h ho'
            · exact h
          exact hv o (List.mem_append_left _ hoe) f
      · rw [cnt_snoc]
        have h1 := hperm.countP_eq (fun i => decide (i < n))
        have h2 := hperm.length_eq
        rw [List.countP_cons_of_neg (by simp)] at h1
        rw [List.countP_append, List.length_append] at hc
        simp only [List.length_cons, List.length_append, List.length_nil] at h2 ⊢
        have h4 := hg.2
        omega
    · obtain ⟨gs', hlen, hf, hv, hc⟩ := ih hfan' outs
      refine ⟨gs' ++ [⟨GateOp.or, []⟩], by simp [hlen], ?_, ?_, ?_⟩
      · intro g' hg'
        rcases List.mem_append.mp hg' with h | h
        · exact hf g' h
        · rw [List.mem_singleton.mp h]
          exact ⟨by simp, by simp⟩
      · intro o ho f
        have ho' : o ≠ n + gs.length := fun h => hmem (h ▸ ho)
        rw [val_snoc, val_snoc, hlen, if_neg ho', if_neg ho']
        exact hv o ho f
      · rw [cnt_snoc]
        simp only [List.countP_nil, List.length_append, List.length_cons, List.length_nil]
        omega

lemma evalL {n : ℕ} (gs : List Gate) (o : ℕ) (x : List Bool) (f : Fin n → Bool)
    (h : x = List.ofFn f) : Circuit.eval ⟨gs, o⟩ x = val gs f o := by
  subst h
  rfl

theorem main (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ C.size ∧
      List.countP (fun x5 : ℕ => decide (x5 < n))
        (D.output :: List.flatMap Gate.inputs D.gates) ≤ D.size + 1 ∧
      ∀ x : List Bool, x.length = n → D.eval x = C.eval x := by
  obtain ⟨gs', hlen, hf, hv, hc⟩ := core n C.gates hC [C.output]
  refine ⟨⟨gs', C.output⟩, hf, le_of_eq hlen, ?_, ?_⟩
  · show List.countP (fun x5 : ℕ => decide (x5 < n))
        (C.output :: List.flatMap Gate.inputs gs') ≤ gs'.length + 1
    rw [← List.singleton_append, List.countP_append]
    simp only [List.length_singleton, cnt] at hc
    omega
  · intro x hx
    subst hx
    have hxf : x = List.ofFn (fun i : Fin x.length => x[i]) := by
      apply List.ext_getElem <;> simp
    have e1 := evalL gs' C.output x _ hxf
    have e2 : C.eval x = val C.gates (fun i : Fin x.length => x[i]) C.output :=
      evalL C.gates C.output x _ hxf
    rw [e1, e2]
    exact hv C.output (by simp) _

end PEqualNP.Outside.L_meta_2800_aux

theorem PEqualNP.Outside.L_meta_2800 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size ≤ x2.size ∧ List.countP (fun (x5 : ℕ) => Decidable.decide (x5 < x1)) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) ≤ x4.size + (1 : ℕ) ∧ ∀ (x5 : List Bool), x5.length = x1 → x4.eval x5 = x2.eval x5 := by
  intro n C hC
  exact PEqualNP.Outside.L_meta_2800_aux.main n C hC
