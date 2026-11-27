import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5999
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

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

theorem simR (ρ : ℕ → ℕ) (n : ℕ) (hlo : ∀ i, i < n → ρ i < n) (hhi : ∀ i, n ≤ i → ρ i = i)
    (B : List Gate) :
    ∀ U U' : List Bool, U.length = U'.length → n ≤ U.length →
    (∀ i, U.getD i false = U'.getD (ρ i) false) →
    ∀ i, (wf B U).getD i false
      = (wf (B.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate)) U').getD (ρ i) false := by
  induction B with
  | nil => intro U U' _ _ h i; exact h i
  | cons g B ih =>
    intro U U' hlen hn h i
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : g.op.eval (g.inputs.map fun i => U.getD i false)
        = g.op.eval ((g.inputs.map ρ).map fun i => U'.getD i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h j
    apply ih
    · simp [hlen]
    · simp; omega
    · intro j
      show (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)]).getD j false
        = (U' ++ [g.op.eval ((g.inputs.map ρ).map fun i => U'.getD i false)]).getD (ρ j) false
      rw [hv]
      rcases Nat.lt_trichotomy j U.length with hj | hj | hj
      · have hρ : ρ j < U'.length := by
          by_cases hjn : j < n
          · have := hlo j hjn; omega
          · rw [hhi j (by omega)]; omega
        rw [getD_snoc_lt _ _ _ hj, getD_snoc_lt _ _ _ hρ]; exact h j
      · subst hj
        rw [getD_snoc_eq, hhi _ hn, hlen, getD_snoc_eq]
      · rw [getD_snoc_gt _ _ _ hj, hhi j (by omega), getD_snoc_gt _ _ _ (by omega)]

end PEqualNP.Outside.L_meta_5999

open PEqualNP.Outside.L_meta_5999 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_5999 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ) → Fin (26 : ℕ)), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧ x4.size = x1.size ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x5) = x1.eval (List.ofFn fun (x6 : Fin (26 : ℕ)) => x5 (x2 x6)) := by
  intro C π hC
  obtain ⟨hao, hrb, h2⟩ := hC
  have hex : ∃ ρ : ℕ → ℕ, (∀ i (h : i < 26), ρ i = ((π ⟨i, h⟩ : Fin 26) : ℕ)) ∧ ∀ i, 26 ≤ i → ρ i = i :=
    ⟨fun i => if h : i < 26 then ((π ⟨i, h⟩ : Fin 26) : ℕ) else i,
      fun i h => by simp only [dif_pos h], fun i h => by simp only [dif_neg (by omega : ¬ i < 26)]⟩
  obtain ⟨ρ, hρ1, hhi⟩ := hex
  have hlo : ∀ i, i < 26 → ρ i < 26 := by
    intro i hi
    rw [hρ1 i hi]
    exact (π ⟨i, hi⟩).isLt
  have hlen : (C.gates.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate)).length = C.gates.length := by simp
  refine ⟨⟨C.gates.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate), ρ C.output⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact hao g0 hg0
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa using hj
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt
        (⟨C.gates.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate), ρ C.output⟩ : Circuit) j
        = ⟨C.gates[j].op, C.gates[j].inputs.map ρ⟩ := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    rw [hga] at hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi
    have hb := hrb j hj' i0 (by rw [gateAt_eq C j hj']; exact hi0)
    by_cases h26 : i0 < 26
    · have := hlo i0 h26; omega
    · rw [hhi i0 (by omega)]; exact hb
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    simpa using h2 g0 hg0
  · exact hlen
  · intro x
    show (wf (C.gates.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate)) (List.ofFn x)).getD (ρ C.output) false
      = (wf C.gates (List.ofFn fun k => x (π k))).getD C.output false
    refine (simR ρ 26 hlo hhi C.gates _ _ (by simp) (by simp) ?_ C.output).symm
    intro i
    by_cases h : i < 26
    · rw [hρ1 i h]
      have e1 := getD_ofFn (fun k => x (π k)) ⟨i, h⟩
      have e2 := getD_ofFn x (π ⟨i, h⟩)
      simp only at e1 e2
      rw [e1, e2]
    · rw [hhi i (by omega), List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
