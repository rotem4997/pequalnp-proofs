import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6454
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def normG (φ : ℕ → Gate → Gate) : ℕ → List Gate → List Gate
  | _, [] => []
  | L, g :: t => φ L g :: normG φ (L + 1) t

theorem normG_len (φ : ℕ → Gate → Gate) : ∀ (gs : List Gate) (L : ℕ),
    (normG φ L gs).length = gs.length := by
  intro gs
  induction gs with
  | nil => intro L; rfl
  | cons g t ih => intro L; simp [normG, ih]

theorem normG_mem (φ : ℕ → Gate → Gate) : ∀ (gs : List Gate) (L j : ℕ)
    (hj : j < (normG φ L gs).length), ∃ g ∈ gs, (normG φ L gs)[j] = φ (L + j) g := by
  intro gs
  induction gs with
  | nil => intro L j hj; simp [normG] at hj
  | cons g t ih =>
    intro L j hj
    cases j with
    | zero => exact ⟨g, by simp, by simp [normG]⟩
    | succ j =>
      have hj' : j < (normG φ (L + 1) t).length := by simpa [normG] using hj
      obtain ⟨g', hg', he⟩ := ih (L + 1) j hj'
      refine ⟨g', by simp [hg'], ?_⟩
      simp only [normG, List.getElem_cons_succ]
      rw [he]
      congr 1
      omega

theorem normG_wf (φ : ℕ → Gate → Gate) (Q : List Bool → Prop) (R : Gate → Prop)
    (hQ : ∀ U v, Q U → Q (U ++ [v]))
    (hφ : ∀ U g, Q U → R g →
      (φ U.length g).op.eval ((φ U.length g).inputs.map fun i => U.getD i false)
        = g.op.eval (g.inputs.map fun i => U.getD i false)) :
    ∀ (gs : List Gate) (U : List Bool), Q U → (∀ g ∈ gs, R g) →
      wf (normG φ U.length gs) U = wf gs U := by
  intro gs
  induction gs with
  | nil => intro U _ _; rfl
  | cons g t ih =>
    intro U hU hR
    show wf (φ U.length g :: normG φ (U.length + 1) t) U = wf (g :: t) U
    rw [wf_cons, wf_cons, hφ U g hU (hR g (by simp))]
    have h := ih (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)]) (hQ _ _ hU)
      (fun g' hg' => hR g' (by simp [hg']))
    simpa using h

theorem wf_pad (d : ℕ) : ∀ U : List Bool,
    wf (List.replicate d (⟨GateOp.or, []⟩ : Gate)) U = U ++ List.replicate d false := by
  induction d with
  | zero => intro U; simp [wf]
  | succ d ih =>
    intro U
    rw [List.replicate_succ, wf_cons, ih]
    simp [GateOp.eval, List.replicate_succ]

theorem getD_pad (W : List Bool) (d w : ℕ) :
    (W ++ List.replicate d false).getD w false = W.getD w false := by
  by_cases h : w < W.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [List.getD_eq_default W _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : W.length ≤ w),
      List.getElem?_replicate]
    split <;> rfl

def clipG (L : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map fun i => if i ≤ L then i else L⟩

end PEqualNP.Outside.L_meta_6454

open PEqualNP.Outside.L_meta_6454 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6454 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.size = x2 ∧ PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin x6.gates.length), ∀ x8 ∈ (x6.gates.get x7).inputs, x8 ≤ x1 + ↑x7) ∧ ∀ (x7 : List Bool), x7.length = x1 → ∀ (x9 : ℕ), (x6.wires x7).getD x9 Bool.false = (x3.wires x7).getD x9 Bool.false := by
  intro n k C hm hsize
  have hsz : C.gates.length ≤ k := hsize
  refine ⟨⟨normG clipG n C.gates ++ List.replicate (k - C.gates.length) (⟨GateOp.or, []⟩ : Gate), C.output⟩,
    ?_, ?_, ?_, ?_⟩
  · show (normG clipG n C.gates ++ List.replicate (k - C.gates.length) (⟨GateOp.or, []⟩ : Gate)).length = k
    rw [List.length_append, normG_len, List.length_replicate]
    omega
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
      obtain ⟨g0, hg0, he⟩ := normG_mem clipG C.gates n j hj
      rw [he]
      have := hm g0 hg0
      exact ⟨this.1, by simpa [clipG] using this.2⟩
    · rw [List.eq_of_mem_replicate h]
      exact ⟨Or.inr rfl, by simp⟩
  · intro j i hi
    rw [List.get_eq_getElem] at hi
    by_cases hj : (j : ℕ) < (normG clipG n C.gates).length
    · rw [List.getElem_append_left hj] at hi
      obtain ⟨g, _, he⟩ := normG_mem clipG C.gates n j hj
      rw [he] at hi
      obtain ⟨i0, _, rfl⟩ := List.mem_map.1 hi
      show (if i0 ≤ n + (j : ℕ) then i0 else n + (j : ℕ)) ≤ n + (j : ℕ)
      split <;> omega
    · rw [List.getElem_append_right (by omega)] at hi
      simp at hi
  · intro x hx w
    show (wf (normG clipG n C.gates ++ List.replicate (k - C.gates.length) (⟨GateOp.or, []⟩ : Gate)) x).getD w false
      = (wf C.gates x).getD w false
    rw [wf_append, ← hx, normG_wf clipG (fun _ => True) (fun _ => True) (fun _ _ _ => trivial)
      (fun U g _ _ => by
        show g.op.eval ((g.inputs.map fun i => if i ≤ U.length then i else U.length).map fun i => U.getD i false)
          = g.op.eval (g.inputs.map fun i => U.getD i false)
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        show U.getD (if i ≤ U.length then i else U.length) false = U.getD i false
        split
        · rfl
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)])
      C.gates x trivial (fun _ _ => trivial), wf_pad, getD_pad]
