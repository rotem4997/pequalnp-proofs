import Mathlib
import PEqualNP.Defs

/-!
L-meta-3939.

Put twenty NOT gates in front of any circuit (gate `j` reads wire `j`); after them
wires `20 .. 29` repeat the ten inputs; the original gates are then shifted by `20`.  NOT gates
are not counted, the function on ten inputs is unchanged, and each wire below `20` is read by
exactly one gate.
-/

namespace PEqualNP.Outside.L_meta_3939

open PEqualNP.CircuitLowerBounds

/-- One evaluation step of `Circuit.wires`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- A gate with every wire index shifted by `20`. -/
def sh (g : Gate) : Gate := ⟨g.op, g.inputs.map (· + 20)⟩

/-- Twenty NOT gates, gate `j` reading wire `j`. -/
def pre : List Gate := (List.range 20).map fun i => (⟨GateOp.not, [i]⟩ : Gate)

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma getD_shift (P W : List Bool) (hP : P.length = 20) (i : ℕ) :
    (P ++ W).getD (i + 20) false = W.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  congr 2
  omega

lemma step_sh (P : List Bool) (hP : P.length = 20) (W : List Bool) (g : Gate) :
    step (P ++ W) (sh g) = P ++ step W g := by
  have h : (g.inputs.map (· + 20)).map (fun i => (P ++ W).getD i false)
      = g.inputs.map (fun i => W.getD i false) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact getD_shift P W hP i
  show (P ++ W) ++ [g.op.eval ((g.inputs.map (· + 20)).map fun i => (P ++ W).getD i false)]
    = P ++ (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)])
  rw [h, List.append_assoc]

lemma foldl_sh (P : List Bool) (hP : P.length = 20) (gs : List Gate) (W : List Bool) :
    (gs.map sh).foldl step (P ++ W) = P ++ gs.foldl step W := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [step_sh P hP, ih]

lemma pre_wires (a : Fin 10 → Bool) :
    ∃ P : List Bool, P.length = 20 ∧ pre.foldl step (List.ofFn a) = P ++ List.ofFn a := by
  refine ⟨[a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9,
    !a 0, !a 1, !a 2, !a 3, !a 4, !a 5, !a 6, !a 7, !a 8, !a 9], rfl, ?_⟩
  have h : List.ofFn a = [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9] := by
    simp [List.ofFn_succ]
  rw [h]
  simp [pre, step, GateOp.eval, List.range_succ]

lemma pre_get (k : ℕ) (hk : k < pre.length) : pre[k] = ⟨GateOp.not, [k]⟩ := by
  simp [pre]

lemma pre_length : pre.length = 20 := by simp [pre]

lemma reads_lt (gs : List Gate) (k : ℕ) (hk : k < (pre ++ gs.map sh).length) (w : ℕ)
    (hw : w < 20) (hmem : w ∈ ((pre ++ gs.map sh)[k]).inputs) : k = w := by
  by_cases hk20 : k < 20
  · rw [List.getElem_append_left (by rw [pre_length]; exact hk20), pre_get] at hmem
    simp at hmem
    exact hmem.symm
  · exfalso
    rw [List.getElem_append_right (by rw [pre_length]; omega), List.getElem_map] at hmem
    simp only [sh, List.mem_map] at hmem
    obtain ⟨i, _, hi⟩ := hmem
    omega

lemma count_pre (p : Gate → Bool) (hp : ∀ i, p ⟨GateOp.not, [i]⟩ = false) :
    List.countP p pre = 0 := by
  rw [List.countP_eq_zero]
  intro g hg
  simp only [pre, List.mem_map, List.mem_range] at hg
  obtain ⟨i, _, rfl⟩ := hg
  simp [hp]

lemma count_sh (p : Gate → Bool) (hp : ∀ g, p (sh g) = p g) (gs : List Gate) :
    List.countP p (gs.map sh) = List.countP p gs := by
  rw [List.countP_map]
  congr 1
  funext g
  exact hp g

end PEqualNP.Outside.L_meta_3939

open PEqualNP.Outside.L_meta_3939 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3939 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x4 : ℕ) => Bool.true) Bool.true x3.op) x1.gates ≤ (12 : ℕ) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x7 : ℕ) => Bool.true) Bool.true x6.op) x5.gates ≤ (12 : ℕ) ∧ (∀ x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (8 : ℕ)], ∀ (x8 x9 : Fin x5.gates.length), x6 ∈ (x5.gates.get x8).inputs → x6 ∈ (x5.gates.get x9).inputs → x8 = x9) ∧ ∀ (x6 : Fin (10 : ℕ) → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6) := by
  intro C hF hcnt _
  refine ⟨⟨pre ++ C.gates.map sh, C.output + 20⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · simp only [pre, List.mem_map, List.mem_range] at h
      obtain ⟨i, _, rfl⟩ := h
      simp
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h
      have := hF g0 hg0
      simpa [sh] using this
  · show List.countP _ (pre ++ C.gates.map sh) ≤ 12
    rw [List.countP_append, count_pre _ (fun i => rfl), count_sh _ (fun g => rfl), Nat.zero_add]
    exact hcnt
  · intro w hw i j hi hj
    have hw20 : w < 20 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      omega
    apply Fin.ext
    have h1 := reads_lt C.gates i.1 i.2 w hw20 (by simpa [List.get_eq_getElem] using hi)
    have h2 := reads_lt C.gates j.1 j.2 w hw20 (by simpa [List.get_eq_getElem] using hj)
    omega
  · intro x
    obtain ⟨P, hP, hpre⟩ := pre_wires x
    show (Circuit.wires ⟨pre ++ C.gates.map sh, C.output + 20⟩ (List.ofFn x)).getD
      (C.output + 20) false = (C.wires (List.ofFn x)).getD C.output false
    rw [wires_eq, wires_eq]
    show ((pre ++ C.gates.map sh).foldl step (List.ofFn x)).getD (C.output + 20) false = _
    rw [List.foldl_append, hpre, foldl_sh P hP, getD_shift P _ hP]
