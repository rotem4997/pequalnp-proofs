import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6214
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

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

def fixG (L : ℕ) (g : Gate) : Gate :=
  ⟨g.op, match g.op, g.inputs.map (fun i => if i < L then i else 27) with
    | GateOp.and, [] => [26, 26]
    | _, [] => [27, 27]
    | _, [i] => [i, i]
    | _, i :: j :: _ => [i, j]⟩

theorem clip_get (U : List Bool) (h27 : U.getD 27 false = false) (i : ℕ) :
    U.getD (if i < U.length then i else 27) false = U.getD i false := by
  split
  · rfl
  · rw [h27, List.getD_eq_default _ _ (by omega)]

theorem fixG_eval (U : List Bool) (g : Gate)
    (hQ : 28 ≤ U.length ∧ U.getD 26 false = true ∧ U.getD 27 false = false)
    (hR : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    (fixG U.length g).op.eval ((fixG U.length g).inputs.map fun i => U.getD i false)
      = g.op.eval (g.inputs.map fun i => U.getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hR
  have hc := clip_get U hQ.2.2
  have h26 := hQ.2.1
  have h27 := hQ.2.2
  simp only [List.getD_eq_getElem?_getD] at hc h26 h27
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · rcases hop with h | h <;> simp only at h <;> subst h <;> simp [fixG, GateOp.eval, h26, h27, List.getD_eq_getElem?_getD]
  · rcases hop with h | h <;> simp only at h <;> subst h <;> simp [fixG, GateOp.eval, hc, List.getD_eq_getElem?_getD]
  · rcases hop with h | h <;> simp only at h <;> subst h <;> simp [fixG, GateOp.eval, hc, List.getD_eq_getElem?_getD]
  · simp at hlen

theorem fixG_in (L : ℕ) (g : Gate) (hL : 28 ≤ L) :
    (fixG L g).inputs.length = 2 ∧ ∀ i ∈ (fixG L g).inputs, i < L := by
  obtain ⟨op, ins⟩ := g
  have hc : ∀ i, (if i < L then i else 27) < L := by
    intro i
    split <;> omega
  rcases ins with _ | ⟨i, _ | ⟨j, t⟩⟩ <;> cases op <;> simp [fixG, hc] <;> omega

end PEqualNP.Outside.L_meta_6214

open PEqualNP.Outside.L_meta_6214 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6214 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size = x1.size ∧ (∀ (x4 : Fin x3.gates.length), (x3.gates.get x4).inputs.length = (2 : ℕ) ∧ ∀ x5 ∈ (x3.gates.get x4).inputs, x5 < (28 : ℕ) + ↑x4) ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), x3.wires (List.ofFn x4 ++ [Bool.true, Bool.false]) = x1.wires (List.ofFn x4 ++ [Bool.true, Bool.false]) := by
  intro C hm
  have hR : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    refine ⟨?_, (hm g hg).2⟩
    rcases (hm g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨⟨normG fixG 28 C.gates, C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨g0, hg0, he⟩ := normG_mem fixG C.gates 28 j hj
    rw [he]
    refine ⟨(hm g0 hg0).1, ?_⟩
    rw [(fixG_in (28 + j) g0 (by omega)).1]
  · show (normG fixG 28 C.gates).length = C.gates.length
    exact normG_len fixG C.gates 28
  · intro j
    rw [List.get_eq_getElem]
    obtain ⟨g0, _, he⟩ := normG_mem fixG C.gates 28 j j.isLt
    have hh : (normG fixG 28 C.gates)[(j : ℕ)] = fixG (28 + (j : ℕ)) g0 := he
    show ((normG fixG 28 C.gates)[(j : ℕ)]).inputs.length = 2 ∧
      ∀ i ∈ ((normG fixG 28 C.gates)[(j : ℕ)]).inputs, i < 28 + (j : ℕ)
    rw [hh]
    exact fixG_in (28 + (j : ℕ)) g0 (by omega)
  · intro x
    have hX : (List.ofFn x ++ [true, false]).length = 28 := by simp
    have hQX : 28 ≤ (List.ofFn x ++ [true, false]).length ∧
        (List.ofFn x ++ [true, false]).getD 26 false = true ∧
        (List.ofFn x ++ [true, false]).getD 27 false = false := by
      refine ⟨by omega, ?_, ?_⟩
      · simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      · simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
    have h := normG_wf fixG
      (fun U => 28 ≤ U.length ∧ U.getD 26 false = true ∧ U.getD 27 false = false)
      (fun g => (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
      (fun U v hU => ⟨by simp; omega, by rw [getD_snoc_lt _ _ _ (by omega)]; exact hU.2.1,
        by rw [getD_snoc_lt _ _ _ (by omega)]; exact hU.2.2⟩)
      (fun U g hq hr => fixG_eval U g hq hr) C.gates (List.ofFn x ++ [true, false]) hQX hR
    rw [hX] at h
    exact h
