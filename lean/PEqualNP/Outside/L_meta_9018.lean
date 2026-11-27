import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9018

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_foldl (G : List Gate) (s : List Bool) :
    (G.foldl step s).length = s.length + G.length := by
  induction G generalizing s with
  | nil => simp
  | cons g G ih => simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons,
      List.length_nil]; omega

def remap (L M K : ℕ) (w : Fin L → ℕ) (i : ℕ) : ℕ :=
  if h : i < L then (if w ⟨i, h⟩ < M then w ⟨i, h⟩ else M + K) else M + (i - L)

def mapGate (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem main (W y : List Bool) (r : ℕ → ℕ) (K : ℕ)
    (hr : ∀ E : List Bool, E.length ≤ K → ∀ i, (W ++ E).getD (r i) false = (y ++ E).getD i false) :
    ∀ (G : List Gate) (E : List Bool), E.length + G.length ≤ K →
      ∃ E' : List Bool, E'.length = E.length + G.length ∧
        (G.map (mapGate r)).foldl step (W ++ E) = W ++ E' ∧ G.foldl step (y ++ E) = y ++ E' := by
  intro G
  induction G with
  | nil => intro E _; exact ⟨E, by simp, by simp, by simp⟩
  | cons g G ih =>
    intro E hE
    simp only [List.length_cons] at hE
    have hv : (g.inputs.map r).map (fun i => (W ++ E).getD i false)
        = g.inputs.map (fun i => (y ++ E).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact hr E (by omega) i
    obtain ⟨E', h1, h2, h3⟩ :=
      ih (E ++ [g.op.eval (g.inputs.map fun i => (y ++ E).getD i false)])
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    refine ⟨E', ?_, ?_, ?_⟩
    · rw [h1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · simp only [List.map_cons, List.foldl_cons]
      have : step (W ++ E) (mapGate r g)
          = W ++ (E ++ [g.op.eval (g.inputs.map fun i => (y ++ E).getD i false)]) := by
        simp only [step, mapGate]
        rw [hv, List.append_assoc]
      rw [this, h2]
    · simp only [List.foldl_cons]
      have : step (y ++ E) g
          = y ++ (E ++ [g.op.eval (g.inputs.map fun i => (y ++ E).getD i false)]) := by
        simp only [step, List.append_assoc]
      rw [this, h3]

theorem getD_left (l l' : List Bool) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n false = l.getD n false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_right (l l' : List Bool) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n false = l'.getD (n - l.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_big (l : List Bool) (n : ℕ) (h : l.length ≤ n) : l.getD n false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem hr_of (L M K : ℕ) (w : Fin L → ℕ) (W : List Bool) (v : Fin L → Bool)
    (hW : W.length = M) (hw : ∀ j, W.getD (w j) false = v j) :
    ∀ E : List Bool, E.length ≤ K → ∀ i,
      (W ++ E).getD (remap L M K w i) false = (List.ofFn v ++ E).getD i false := by
  intro E hE i
  unfold remap
  by_cases h : i < L
  · rw [dif_pos h, getD_left (List.ofFn v) E i (by simp [h])]
    have hy : (List.ofFn v).getD i false = v ⟨i, h⟩ := by
      simp [List.getD_eq_getElem?_getD, h]
    rw [hy]
    by_cases h2 : w ⟨i, h⟩ < M
    · rw [if_pos h2, getD_left _ _ _ (by omega), hw]
    · rw [if_neg h2, ← hw, getD_big _ _ (by simp; omega), getD_big W _ (by omega)]
  · rw [dif_neg h, getD_right _ _ _ (by omega), getD_right _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    congr 1
    omega

end PEqualNP.Outside.L_meta_9018

open PEqualNP.Outside.L_meta_9018 in
theorem PEqualNP.Outside.L_meta_9018 : ∀ (N L : ℕ) (D : Set (List Bool)) (P : List PEqualNP.CircuitLowerBounds.Gate) (w : Fin L → ℕ) (g : Fin L → List Bool → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ x ∈ D, x.length = N) → PEqualNP.MetaComplexity.Monotone2 (⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x ∈ D, ∀ j, ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).getD (w j) false = g j x) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size ≤ P.length + C.size ∧ ∀ x ∈ D, C'.eval x = C.eval (List.ofFn fun j => g j x) := by
  intro N L D P w g C hD hP hC hw
  let M := N + P.length
  let K := C.gates.length
  let r := remap L M K w
  refine ⟨⟨P ++ C.gates.map (mapGate r), r C.output⟩, ?_, ?_, ?_⟩
  · intro gt hgt
    rw [List.mem_append] at hgt
    rcases hgt with hgt | hgt
    · exact hP gt hgt
    · rw [List.mem_map] at hgt
      obtain ⟨g0, hg0, rfl⟩ := hgt
      obtain ⟨h1, h2⟩ := hC g0 hg0
      exact ⟨h1, by simp only [mapGate, List.length_map]; exact h2⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x hx
    have hWlen : ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).length = M := by
      show (P.foldl step x).length = M
      rw [len_foldl, hD x hx]
    have hr := hr_of L M K w ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x)
      (fun j => g j x) hWlen (hw x hx)
    obtain ⟨E', h1, h2, h3⟩ := main _ _ r K hr C.gates [] (by simp [K])
    simp only [List.append_nil] at h2 h3
    show ((P ++ C.gates.map (mapGate r)).foldl step x).getD (r C.output) false
      = (C.gates.foldl step (List.ofFn fun j => g j x)).getD C.output false
    rw [List.foldl_append]
    have hPw : P.foldl step x = (⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x := rfl
    rw [hPw, h2, h3]
    exact hr E' (by simp at h1; omega) C.output
