import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7165
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def fl (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

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

def fwd (L : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if ∀ i ∈ g.inputs, i < L then g else ⟨GateOp.or, []⟩
  | _ => ⟨g.op, g.inputs.filter fun i => decide (i < L)⟩

theorem fwd_and (L : ℕ) (g : Gate) (h : g.op = GateOp.and) :
    fwd L g = if ∀ i ∈ g.inputs, i < L then g else ⟨GateOp.or, []⟩ := by
  obtain ⟨op, ins⟩ := g
  simp only at h
  subst h
  rfl

theorem fwd_or (L : ℕ) (g : Gate) (h : g.op = GateOp.or) :
    fwd L g = ⟨GateOp.or, g.inputs.filter fun i => decide (i < L)⟩ := by
  obtain ⟨op, ins⟩ := g
  simp only at h
  subst h
  rfl

theorem any_filter (ins : List ℕ) (L : ℕ) (f : ℕ → Bool) (h : ∀ i, ¬ i < L → f i = false) :
    ((ins.filter fun i => decide (i < L)).map f).any id = (ins.map f).any id := by
  induction ins with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : a < L
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      simp only [List.map_cons, List.any_cons, ih]
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      simp only [List.map_cons, List.any_cons, h a ha, ih]
      simp

theorem fwd_legal (L : ℕ) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) :
    ((fwd L g).op = GateOp.and ∨ (fwd L g).op = GateOp.or) ∧ (fwd L g).inputs.length ≤ 2 ∧
      ∀ i ∈ (fwd L g).inputs, i < L := by
  rcases hop with h | h
  · rw [fwd_and L g h]
    split
    · rename_i hall
      exact ⟨Or.inl h, hlen, hall⟩
    · exact ⟨Or.inr rfl, by simp, by simp⟩
  · rw [fwd_or L g h]
    exact ⟨Or.inr rfl, le_trans (List.length_filter_le _ _) hlen,
      fun i hi => by simpa using (List.mem_filter.1 hi).2⟩

theorem fwd_eval (U : List Bool) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (fwd U.length g).op.eval ((fwd U.length g).inputs.map fun i => U.getD i false)
      = g.op.eval (g.inputs.map fun i => U.getD i false) := by
  rcases hop with h | h
  · rw [fwd_and _ g h]
    split
    · rfl
    · rename_i hall
      push_neg at hall
      obtain ⟨i, hi, hiL⟩ := hall
      rw [h]
      have h0 : (g.inputs.map fun i => U.getD i false).all id = false := by
        rw [List.all_eq_false]
        exact ⟨false, List.mem_map.2 ⟨i, hi, List.getD_eq_default _ _ (by omega)⟩, by simp⟩
      show ([] : List Bool).any id = (g.inputs.map fun i => U.getD i false).all id
      rw [h0]
      rfl
  · rw [fwd_or _ g h, h]
    show ((g.inputs.filter fun i => decide (i < U.length)).map fun i => U.getD i false).any id
      = (g.inputs.map fun i => U.getD i false).any id
    exact any_filter g.inputs U.length _ (fun i hi => List.getD_eq_default _ _ (by omega))

end PEqualNP.Outside.L_meta_7165

open PEqualNP.Outside.L_meta_7165 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7165 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x4 ∧ x4.size ≤ x2.size ∧ ∀ (x5 : Fin x1 → Bool), x4.eval (List.ofFn x5) = x2.eval (List.ofFn x5) := by
  intro n C hm
  have legal : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    rcases (hm g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨⟨normG fwd n C.gates, C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨g0, hg0, he⟩ := normG_mem fwd C.gates n j hj
    rw [he]
    have fl := fwd_legal (n + j) g0 (legal g0 hg0) (hm g0 hg0).2
    refine ⟨?_, fl.2.1⟩
    rcases fl.1 with h | h
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr rfl
  · intro j hj i hi
    have hj' : j < (normG fwd n C.gates).length := hj
    rw [gateAt_eq _ j hj'] at hi
    obtain ⟨g0, hg0, he⟩ := normG_mem fwd C.gates n j hj'
    have hi' : i ∈ ((normG fwd n C.gates)[j]).inputs := hi
    rw [he] at hi'
    exact (fwd_legal (n + j) g0 (legal g0 hg0) (hm g0 hg0).2).2.2 i hi'
  · exact le_of_eq (normG_len fwd C.gates n)
  · intro x
    show (wf (normG fwd n C.gates) (List.ofFn x)).getD C.output false
      = (wf C.gates (List.ofFn x)).getD C.output false
    have h := normG_wf fwd (fun _ => True) (fun g => g.op = GateOp.and ∨ g.op = GateOp.or)
      (fun _ _ _ => trivial) (fun U g _ hr => fwd_eval U g hr) C.gates (List.ofFn x) trivial legal
    rw [List.length_ofFn] at h
    rw [h]
