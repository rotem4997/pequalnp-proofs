import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9109
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

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

def rho (n : ℕ) (σ : Fin n → Fin n) (i : ℕ) : ℕ :=
  if h : i < n then (σ ⟨i, h⟩).val else i

def rgs (n : ℕ) (σ : Fin n → Fin n) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho n σ)⟩

theorem simS (n : ℕ) (σ : Fin n → Fin n) : ∀ (gs : List Gate) (U U' : List Bool),
    U.length = U'.length → n ≤ U.length →
    (∀ i, U.getD i false = U'.getD (rho n σ i) false) →
    ∀ i, (wf gs U).getD i false = (wf (gs.map (rgs n σ)) U').getD (rho n σ i) false := by
  intro gs
  induction gs with
  | nil => intro U U' _ _ h i; exact h i
  | cons g gs ih =>
    intro U U' hlen hn h i
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : g.op.eval (g.inputs.map fun i => U.getD i false)
        = (rgs n σ g).op.eval ((rgs n σ g).inputs.map fun i => U'.getD i false) := by
      show _ = g.op.eval ((g.inputs.map (rho n σ)).map fun i => U'.getD i false)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h a
    refine ih _ _ (by simp [hlen]) (by simp; omega) ?_ i
    intro j
    rw [← hv]
    have hfix : ∀ j, n ≤ j → rho n σ j = j := by
      intro j hj
      unfold rho
      rw [dif_neg (by omega)]
    have hlt : ∀ j, j < n → rho n σ j < n := by
      intro j hj
      unfold rho
      rw [dif_pos hj]
      exact (σ ⟨j, hj⟩).isLt
    rcases Nat.lt_trichotomy j U.length with hj | hj | hj
    · rw [getD_snoc_lt _ _ _ hj]
      by_cases hjn : j < n
      · rw [getD_snoc_lt _ _ _ (by have := hlt j hjn; omega)]
        exact h j
      · rw [hfix j (by omega), getD_snoc_lt _ _ _ (by omega)]
        have := h j
        rwa [hfix j (by omega)] at this
    · rw [hfix j (by omega), hj, getD_snoc_eq, hlen, getD_snoc_eq]
    · rw [hfix j (by omega), getD_snoc_gt _ _ _ hj, getD_snoc_gt _ _ _ (by omega)]

end PEqualNP.Outside.L_meta_9109

open PEqualNP.Outside.L_meta_9109 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9109 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x6 : Fin (9 : ℕ)) (x7 : Fin (9 : ℕ)), x5 x6 = Bool.true ∧ x5 x7 = Bool.true ∧ ([(34 : ℕ), (69 : ℕ), (138 : ℕ), (260 : ℕ), (192 : ℕ), (385 : ℕ), (274 : ℕ), (52 : ℕ), (104 : ℕ)].getD ↑x6 (0 : ℕ)).testBit ↑x7 = Bool.true)) x4) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = (15 : ℕ) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x6) = (fun (x7 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (9 : ℕ) (x8 / (10 : ℕ))) && x7 (Fin.ofNat (9 : ℕ) (x8 % (10 : ℕ)))) x6 := by
  intro C hF hs hf
  dsimp only at hf ⊢
  have key : ∀ (x : Fin 9 → Bool) (i : ℕ), (wf C.gates (List.ofFn (x ∘ ![4, 0, 1, 6, 7, 3, 5, 2, 8]))).getD i false
      = (wf (C.gates.map (rgs 9 ![4, 0, 1, 6, 7, 3, 5, 2, 8])) (List.ofFn x)).getD (rho 9 ![4, 0, 1, 6, 7, 3, 5, 2, 8] i) false := by
    intro x i
    exact simS 9 ![4, 0, 1, 6, 7, 3, 5, 2, 8] C.gates (List.ofFn (x ∘ ![4, 0, 1, 6, 7, 3, 5, 2, 8])) (List.ofFn x) (by simp) (by simp) (by
      intro j
      by_cases hj : j < 9
      · have e1 := getD_ofFn (x ∘ ![4, 0, 1, 6, 7, 3, 5, 2, 8]) ⟨j, hj⟩
        have e2 := getD_ofFn x ((![4, 0, 1, 6, 7, 3, 5, 2, 8] : Fin 9 → Fin 9) ⟨j, hj⟩)
        simp only at e1 e2
        rw [e1]
        unfold rho
        rw [dif_pos hj, e2]
        rfl
      · unfold rho
        rw [dif_neg hj, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]) i
  have hrel : ∀ x : Fin 9 → Bool,
      decide (∃ (x6 : Fin 9) (x7 : Fin 9), (x ∘ ![4, 0, 1, 6, 7, 3, 5, 2, 8]) x6 = true ∧ (x ∘ ![4, 0, 1, 6, 7, 3, 5, 2, 8]) x7 = true ∧
        (([34, 69, 138, 260, 192, 385, 274, 52, 104] : List ℕ).getD (x6 : ℕ) 0).testBit (x7 : ℕ) = true)
      = ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun x8 => x (Fin.ofNat 9 (x8 / 10)) && x (Fin.ofNat 9 (x8 % 10)) := by
    decide +kernel
  refine ⟨⟨C.gates.map (rgs 9 ![4, 0, 1, 6, 7, 3, 5, 2, 8]) ++ List.replicate (15 - C.gates.length) (⟨GateOp.or, []⟩ : Gate),
    rho 9 ![4, 0, 1, 6, 7, 3, 5, 2, 8] C.output⟩, ?_, ?_, fun x => ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hF g0 hg0
      exact ⟨this.1, by simpa [rgs] using this.2⟩
    · rw [List.eq_of_mem_replicate h]
      simp
  · show (C.gates.map (rgs 9 ![4, 0, 1, 6, 7, 3, 5, 2, 8]) ++ List.replicate (15 - C.gates.length) (⟨GateOp.or, []⟩ : Gate)).length = 15
    have : C.gates.length ≤ 15 := hs
    simp
    omega
  · show (wf (C.gates.map (rgs 9 ![4, 0, 1, 6, 7, 3, 5, 2, 8]) ++ List.replicate (15 - C.gates.length) (⟨GateOp.or, []⟩ : Gate)) (List.ofFn x)).getD _ false = _
    rw [wf_append, wf_pad, getD_pad, ← key x C.output, ← hrel x]
    exact hf (x ∘ ![4, 0, 1, 6, 7, 3, 5, 2, 8])
