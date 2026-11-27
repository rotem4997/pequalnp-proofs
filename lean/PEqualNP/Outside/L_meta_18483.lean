import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18483

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem prefixRead (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem stepLength (w : List Bool) (g : Gate) :
    (step w g).length = w.length+1 := by simp [step]

private theorem gateRead (gs : List Gate) (w : List Bool) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (h : ∀ k ∈ g.inputs, k < w.length+i) :
    let W := gs.foldl step w
    W.getD (w.length+i) false = g.op.eval (g.inputs.map fun k => W.getD k false) := by
  induction gs generalizing w i with
  | nil => simp at hg
  | cons q qs ih =>
    cases i with
    | zero =>
      simp at hg
      subst q
      simp only [List.foldl_cons, Nat.add_zero] at h ⊢
      rw [prefixRead _ _ _ (by rw [stepLength]; omega)]
      have hx : (step w g).getD w.length false =
          g.op.eval (g.inputs.map fun k => w.getD k false) := by simp [step]
      rw [hx]
      congr 1
      apply List.map_congr_left
      intro k hk
      rw [prefixRead _ _ _ (by rw [stepLength]; specialize h k hk; omega)]
      exact (List.getD_append _ _ _ _ (h k hk)).symm
    | succ i =>
      have H : (step w q).length+i = w.length+(i+1) := by rw [stepLength]; omega
      simpa only [H, List.foldl_cons] using
        ih (step w q) i (by simpa using hg) (fun k hk => by simpa [H] using h k hk)
private def wires {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

end PEqualNP.Outside.L_meta_18483

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_18483 in
theorem PEqualNP.Outside.L_meta_18483 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →     have x3 : ℕ → ℕ → Bool := fun (x3 x4 : ℕ) => (x1.wires (List.ofFn fun (x5 : Fin (26 : ℕ)) => x3.testBit ↑x5)).getD x4 Bool.false;     ∀ x4 ∈ [(0 : ℕ), (13 : ℕ)],       have x6 : ℕ := if x4 = (0 : ℕ) then (25034751 : ℕ) else (67108341 : ℕ);       have x7 : ℕ := if x4 = (0 : ℕ) then (8191 : ℕ) else (67100672 : ℕ);       have x8 : ℕ := if x4 = (0 : ℕ) then (25018369 : ℕ) else (15860 : ℕ);       ∀ (x9 : Set ℕ), (∀ (x10 : Fin (26 : ℕ)), ↑x10 ∈ x9 → x6.testBit ↑x10 = Bool.false) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x11]? = Option.some x12 → (26 : ℕ) + x11 ∈ x9 → (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ x16 ∈ x12.inputs, x16 ∈ x9) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ x16 ∈ x12.inputs, x16 ∈ x9) ∨ (∀ x16 ∈ x12.inputs, x3 ((2 : ℕ) ^ x4) x16 = Bool.false) ∧ x3 x7 ((26 : ℕ) + x11) = Bool.false ∧ x3 x8 ((26 : ℕ) + x11) = Bool.false)) → ∀ x12 ∈ x9, x12 < (26 : ℕ) + x1.size → x3 x7 x12 = Bool.false ∧ x3 x8 x12 = Bool.false := by
  intro C hC raw v hv p a b S hinput hclosed
  let W (m i : ℕ) := (wires C.gates (fun j : Fin 26 => m.testBit j.val)).getD i false
  change ∀ i ∈ S, i < 26 + C.size → W a i = false ∧ W b i = false
  have primary : ∀ u : Fin 26, p.testBit u.val = false →
      a.testBit u.val = false ∧ b.testBit u.val = false := by
    simp at hv
    rcases hv with rfl | rfl <;> decide +kernel
  have readPrimary (m : ℕ) (u : Fin 26) : W m u.val = m.testBit u.val := by
    change (C.gates.foldl step (List.ofFn fun j : Fin 26 => m.testBit j.val)).getD u.val false = _
    rw [prefixRead _ _ _ (by simpa only [List.length_ofFn] using u.isLt),
      List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using u.isLt)]
    simp only [List.getElem_ofFn]
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi hbound
    by_cases hu : i < 26
    · let u : Fin 26 := ⟨i, hu⟩
      change W a u.val = false ∧ W b u.val = false
      rw [readPrimary, readPrimary]
      exact primary u (hinput u hi)
    · let j := i - 26
      have hj : j < C.gates.length := by
        change i < 26 + C.gates.length at hbound
        dsimp [j]
        omega
      have e : 26 + j = i := by dsimp [j]; omega
      let g := C.gates[j]
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
      have hmem : g ∈ C.gates := List.getElem_mem hj
      have hreads (k : ℕ) (hk : k ∈ g.inputs) : k < i := by
        rw [← e]
        apply hC.2.1 j hj k
        simpa [gateAt, hg] using hk
      have actual (m : ℕ) : W m i = g.op.eval (g.inputs.map (W m)) := by
        have H := gateRead C.gates (List.ofFn fun u : Fin 26 => m.testBit u.val) j g hg
        simp only [List.length_ofFn, e] at H
        exact H hreads
      have closed := hclosed j g hg (e.symm ▸ hi)
      rcases hC.1 g hmem with hop | hop
      · rcases closed.2 hop with ⟨k, hk, hkS⟩ | hval
        · have hkI := hreads k hk
          have hval := ih k hkI hkS (by omega)
          constructor <;> rw [actual, hop, GateOp.eval, List.all_map] <;> 
            apply Bool.eq_false_iff.mpr <;> intro hall
          · have hh := (List.all_eq_true.mp hall) k hk
            simp [hval.1] at hh
          · have hh := (List.all_eq_true.mp hall) k hk
            simp [hval.2] at hh
        · change raw a i = false ∧ raw b i = false
          simpa only [e] using hval.2
      · have hfalse (k : ℕ) (hk : k ∈ g.inputs) : W a k = false ∧ W b k = false :=
          ih k (hreads k hk) (closed.1 hop k hk) (by have := hreads k hk; omega)
        constructor <;> rw [actual, hop, GateOp.eval, List.any_map] <;>
          apply Bool.eq_false_iff.mpr <;> intro htrue
        · obtain ⟨k, hk, ht⟩ := List.any_eq_true.mp htrue
          simp [(hfalse k hk).1] at ht
        · obtain ⟨k, hk, ht⟩ := List.any_eq_true.mp htrue
          simp [(hfalse k hk).2] at ht
