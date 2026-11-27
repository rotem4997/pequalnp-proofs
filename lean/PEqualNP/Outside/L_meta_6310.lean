import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_6310

def wst (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def fn (x1 : Fin 9 → Bool) : Bool :=
  [1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun (x2 : ℕ) => x1 (Fin.ofNat 9 (x2 / 10)) && x1 (Fin.ofNat 9 (x2 % 10))

def tA (x5 : ℕ) : Fin 9 → Bool := fun i => x5.testBit i.val

def tB (x5 : ℕ) : Fin 9 → Bool := fun i => decide (i.val = 4) || x5.testBit i.val

def tE : Fin 9 → Bool := fun i => decide (i.val = 4)

theorem pref : ∀ (gs : List Gate) (w : List Bool),
    ∃ T : List Bool, List.foldl wst w gs = w ++ T ∧ T.length = gs.length
  | [], w => ⟨[], by simp, rfl⟩
  | g :: rest, w => by
    obtain ⟨T, hT, hl⟩ := pref rest (wst w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: T, ?_, by simp [hl]⟩
    rw [List.foldl_cons, hT]
    simp [wst]

theorem getD_left (v t : List Bool) (o : ℕ) (h : o < v.length) :
    (v ++ t).getD o false = v.getD o false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_big (v : List Bool) (o : ℕ) (h : v.length ≤ o) : v.getD o false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem getD_last (v : List Bool) (x : Bool) : (v ++ [x]).getD v.length false = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

theorem ofFn_getD (n : ℕ) (f : Fin n → Bool) (T : List Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f ++ T).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h),
    List.getElem?_eq_getElem (by simpa using h)]
  simp

theorem agree (n : ℕ) (f g : Fin n → Bool) (hfg : ∀ j : Fin n, j.val ≠ 4 → f j = g j) :
    ∀ i, i ≠ 4 → (List.ofFn f).getD i false = (List.ofFn g).getD i false := by
  intro i hi
  by_cases h : i < n
  · have e1 := ofFn_getD n f [] i h
    have e2 := ofFn_getD n g [] i h
    simp only [List.append_nil] at e1 e2
    rw [e1, e2]
    exact hfg ⟨i, h⟩ hi
  · rw [getD_big _ _ (by rw [List.length_ofFn]; omega), getD_big _ _ (by rw [List.length_ofFn]; omega)]

theorem ind : ∀ (gs : List Gate) (a b : List Bool), a.length = b.length →
    (∀ i, i ≠ 4 → a.getD i false = b.getD i false) →
    (∀ k (hk : k < gs.length), (∀ i ∈ gs[k].inputs, i < a.length + k) ∧ (4 ∈ gs[k].inputs → gs[k].op = GateOp.or)) →
    (∀ k (hk : k < gs.length), 4 ∈ gs[k].inputs → ∃ i ∈ gs[k].inputs, i ≠ 4 ∧ (List.foldl wst a gs).getD i false = true) →
    ∀ i, i ≠ 4 → (List.foldl wst a gs).getD i false = (List.foldl wst b gs).getD i false
  | [], a, b, _, hab, _, _ => hab
  | g :: rest, a, b, hl, hab, h1, h2 => by
    have h10 : (∀ i ∈ g.inputs, i < a.length + 0) ∧ (4 ∈ g.inputs → g.op = GateOp.or) := h1 0 (Nat.zero_lt_succ _)
    have hv : g.op.eval (g.inputs.map fun i => a.getD i false) = g.op.eval (g.inputs.map fun i => b.getD i false) := by
      by_cases h4 : 4 ∈ g.inputs
      · obtain ⟨i, hi, hne, hval⟩ : ∃ i ∈ g.inputs, i ≠ 4 ∧ (List.foldl wst (wst a g) rest).getD i false = true := h2 0 (Nat.zero_lt_succ _) h4
        obtain ⟨T, hT, _⟩ := pref rest (wst a g)
        have hia : i < a.length := by
          have := h10.1 i hi
          omega
        have hai : a.getD i false = true := by
          rw [hT] at hval
          unfold wst at hval
          rw [List.append_assoc, getD_left _ _ _ hia] at hval
          exact hval
        have hbi : b.getD i false = true := by
          rw [← hab i hne]
          exact hai
        rw [h10.2 h4]
        have e1 : GateOp.or.eval (g.inputs.map fun i => a.getD i false) = true := by
          simp only [GateOp.eval, List.any_eq_true]
          exact ⟨true, List.mem_map.mpr ⟨i, hi, hai⟩, rfl⟩
        have e2 : GateOp.or.eval (g.inputs.map fun i => b.getD i false) = true := by
          simp only [GateOp.eval, List.any_eq_true]
          exact ⟨true, List.mem_map.mpr ⟨i, hi, hbi⟩, rfl⟩
        rw [e1, e2]
      · congr 1
        apply List.map_congr_left
        intro i hi
        exact hab i (fun h => h4 (h ▸ hi))
    have hlen : (wst a g).length = a.length + 1 := by simp [wst]
    have hlen2 : (wst b g).length = b.length + 1 := by simp [wst]
    simp only [List.foldl_cons]
    refine ind rest (wst a g) (wst b g) (by rw [hlen, hlen2, hl]) ?_ ?_ ?_
    · intro i hi4
      unfold wst
      rw [hv]
      rcases Nat.lt_trichotomy i a.length with h | h | h
      · rw [getD_left _ _ _ h, getD_left _ _ _ (by omega), hab i hi4]
      · subst h
        rw [getD_last, hl, getD_last]
      · rw [getD_big _ _ (by rw [List.length_append, List.length_singleton]; omega),
          getD_big _ _ (by rw [List.length_append, List.length_singleton]; omega)]
    · intro k hk
      have h1k : (∀ i ∈ rest[k].inputs, i < a.length + (k + 1)) ∧ (4 ∈ rest[k].inputs → rest[k].op = GateOp.or) := h1 (k + 1) (Nat.succ_lt_succ hk)
      refine ⟨fun i hi => ?_, h1k.2⟩
      have := h1k.1 i hi
      rw [hlen]
      omega
    · intro k hk h4
      exact h2 (k + 1) (Nat.succ_lt_succ hk) h4

theorem core (x2 : Circuit) (hfun : PEqualNP.MetaComplexity.circuitFun 9 x2 = fn)
    (H : ∀ (x4 : Fin x2.size), (∀ x6 ∈ (x2.gates.get x4).inputs, x6 < 9 + ↑x4) ∧ (4 ∈ (x2.gates.get x4).inputs → (x2.gates.get x4).op = GateOp.or))
    (x5 : ℕ) (hA : fn (tA x5) = false) (hB : fn (tB x5) = true) :
    ∃ (x7 : Fin x2.size), 4 ∈ (x2.gates.get x7).inputs ∧ ∀ x9 ∈ (x2.gates.get x7).inputs, x9 ≠ 4 → (x2.wires (List.ofFn (tA x5))).getD x9 false = false := by
  by_contra hno
  have hout : x2.output ≠ 4 := by
    intro ho
    have h1 := congrFun hfun tE
    have h2 : fn tE = false := by decide +kernel
    rw [h2] at h1
    obtain ⟨T, hT, _⟩ := pref x2.gates (List.ofFn tE)
    have h3 : (List.foldl wst (List.ofFn tE) x2.gates).getD x2.output false = false := h1
    rw [hT, ho, ofFn_getD 9 _ T 4 (by omega)] at h3
    simp [tE] at h3
  have hAl : (List.ofFn (tA x5)).length = 9 := by simp
  have key := ind x2.gates (List.ofFn (tA x5)) (List.ofFn (tB x5)) (by simp)
    (agree 9 _ _ (fun j hj => by simp [tA, tB, hj]))
    (fun k hk => by
      rw [hAl]
      exact H ⟨k, hk⟩)
    (fun k hk h4 => by
      by_contra hc
      apply hno
      refine ⟨⟨k, hk⟩, h4, ?_⟩
      intro x9 hx9 hne
      by_contra hv
      exact hc ⟨x9, hx9, hne, Bool.eq_true_of_not_eq_false hv⟩)
    x2.output hout
  have eA : (List.foldl wst (List.ofFn (tA x5)) x2.gates).getD x2.output false = false := (congrFun hfun (tA x5)).trans hA
  have eB : (List.foldl wst (List.ofFn (tB x5)) x2.gates).getD x2.output false = true := (congrFun hfun (tB x5)).trans hB
  rw [eA, eB] at key
  exact Bool.false_ne_true key

end PEqualNP.Outside.L_meta_6310

theorem PEqualNP.Outside.L_meta_6310 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 →     (∀ (x4 : Fin x2.size),         have x5 : PEqualNP.CircuitLowerBounds.Gate := x2.gates.get x4;         (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ ((4 : ℕ) ∈ x5.inputs → x5.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →       ∀ x5 ∈ [(42 : ℕ), (69 : ℕ), (104 : ℕ), (138 : ℕ), (201 : ℕ), (261 : ℕ), (385 : ℕ)],         ∃ (x7 : Fin x2.size),           have x8 : PEqualNP.CircuitLowerBounds.Gate := x2.gates.get x7;           (4 : ℕ) ∈ x8.inputs ∧ ∀ x9 ∈ x8.inputs, x9 ≠ (4 : ℕ) → (x2.wires (List.ofFn fun (x12 : Fin (9 : ℕ)) => x5.testBit ↑x12)).getD x9 Bool.false = Bool.false := by
  intro x1 x2 hfun H x5 hx5
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx5
  rcases hx5 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_6310.core x2 hfun H 42 (by decide +kernel) (by decide +kernel)
  · exact PEqualNP.Outside.L_meta_6310.core x2 hfun H 69 (by decide +kernel) (by decide +kernel)
  · exact PEqualNP.Outside.L_meta_6310.core x2 hfun H 104 (by decide +kernel) (by decide +kernel)
  · exact PEqualNP.Outside.L_meta_6310.core x2 hfun H 138 (by decide +kernel) (by decide +kernel)
  · exact PEqualNP.Outside.L_meta_6310.core x2 hfun H 201 (by decide +kernel) (by decide +kernel)
  · exact PEqualNP.Outside.L_meta_6310.core x2 hfun H 261 (by decide +kernel) (by decide +kernel)
  · exact PEqualNP.Outside.L_meta_6310.core x2 hfun H 385 (by decide +kernel) (by decide +kernel)
