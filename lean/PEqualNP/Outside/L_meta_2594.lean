import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2594_aux

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def rho (m N : ℕ) (σ : Fin m → Fin N) (k : ℕ) : ℕ :=
  if h : k < m then (σ ⟨k, h⟩).val else N + (k - m)

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma getD_rho {m N : ℕ} (W y T : List Bool) (σ : Fin m → Fin N) (hW : W.length = N)
    (hy : y.length = m) (hyv : ∀ k (h : k < m), y.getD k false = W.getD (σ ⟨k, h⟩) false)
    (k : ℕ) : (W ++ T).getD (rho m N σ k) false = (y ++ T).getD k false := by
  unfold rho
  split_ifs with h
  · have := (σ ⟨k, h⟩).isLt
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), hyv k h]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

lemma fold_rel {m N : ℕ} (W y : List Bool) (σ : Fin m → Fin N) (hW : W.length = N)
    (hy : y.length = m) (hyv : ∀ k (h : k < m), y.getD k false = W.getD (σ ⟨k, h⟩) false)
    (gs : List Gate) : ∀ T : List Bool, ∃ R : List Bool,
      (gs.map (reGate (rho m N σ))).foldl stepW (W ++ T) = W ++ R ∧
      gs.foldl stepW (y ++ T) = y ++ R := by
  induction gs with
  | nil => intro T; exact ⟨T, rfl, rfl⟩
  | cons g gs ih =>
    intro T
    have hm : (g.inputs.map (rho m N σ)).map (fun i => (W ++ T).getD i false)
        = g.inputs.map (fun i => (y ++ T).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => getD_rho W y T σ hW hy hyv i)
    have e1 : stepW (W ++ T) (reGate (rho m N σ) g)
        = W ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (W ++ T) ++ [g.op.eval ((g.inputs.map (rho m N σ)).map fun i => (W ++ T).getD i false)] = _
      rw [hm, List.append_assoc]
    have e2 : stepW (y ++ T) g
        = y ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (y ++ T) ++ _ = _
      rw [List.append_assoc]
    obtain ⟨R, h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)])
    refine ⟨R, ?_, ?_⟩
    · rw [List.map_cons, List.foldl_cons, e1, h1]
    · rw [List.foldl_cons, e2, h2]

end PEqualNP.Outside.L_meta_2594_aux

namespace PEqualNP.Outside.L_meta_2594_aux

open PEqualNP.CircuitLowerBounds

def sig (n : ℕ) (σ : Fin n → Fin n) (k : Fin (n + 1)) : Fin (n + 1) :=
  if h : k.val < n then ⟨(σ ⟨k.val, h⟩).val, by omega⟩ else k

lemma hyv_lem (n : ℕ) (σ : Fin n → Fin n) (x : Fin n → Bool) (b : Bool) :
    ∀ k (h : k < n + 1), (List.ofFn (x ∘ σ) ++ [b]).getD k false
      = (List.ofFn x ++ [b]).getD (sig n σ ⟨k, h⟩) false := by
  intro k h
  unfold sig
  by_cases hk : k < n
  · have := (σ ⟨k, hk⟩).isLt
    simp only [hk, dite_true]
    rw [List.getD_append _ _ _ _ (by simp [hk]), List.getD_append _ _ _ _ (by simpa using this)]
    simp [List.getD_eq_getElem?_getD, hk, this]
  · simp only [hk, dite_false]
    have hk' : k = n := by omega
    subst hk'
    rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simp

end PEqualNP.Outside.L_meta_2594_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2594_aux in
theorem PEqualNP.Outside.L_meta_2594 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧ ∀ (x6 : Fin x1 → Bool) (x7 : Bool), x5.eval (List.ofFn x6 ++ [x7]) = x3.eval (List.ofFn (x6 ∘ x2) ++ [x7]) := by
  intro n σ C hC
  refine ⟨⟨C.gates.map (reGate (rho (n + 1) (n + 1) (sig n σ))), rho (n + 1) (n + 1) (sig n σ) C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    have := hC g' hg'
    simpa [reGate] using this
  · simp [Circuit.size]
  · intro x b
    have hW : (List.ofFn x ++ [b]).length = n + 1 := by simp
    have hy : (List.ofFn (x ∘ σ) ++ [b]).length = n + 1 := by simp
    obtain ⟨R, h1, h2⟩ := fold_rel _ _ (sig n σ) hW hy (hyv_lem n σ x b) C.gates []
    simp only [List.append_nil] at h1 h2
    show (List.foldl stepW _ _).getD _ false = (List.foldl stepW _ _).getD _ false
    rw [h1, h2, getD_rho _ _ R (sig n σ) hW hy (hyv_lem n σ x b)]
