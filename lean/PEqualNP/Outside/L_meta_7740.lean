import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7740

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def rho (m N : ℕ) (σ : Fin m → Fin N) (k : ℕ) : ℕ :=
  if h : k < m then (σ ⟨k, h⟩).val else N + (k - m)

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

lemma hyv_lem {m N : ℕ} (σ : Fin m → Fin N) (x : Fin N → Bool) :
    ∀ k (h : k < m), (List.ofFn (x ∘ σ)).getD k false
      = (List.ofFn x).getD (σ ⟨k, h⟩) false := by
  intro k h
  have := (σ ⟨k, h⟩).isLt
  simp [List.getD_eq_getElem?_getD, h, this]

end PEqualNP.Outside.L_meta_7740

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_7740 in
theorem PEqualNP.Outside.L_meta_7740 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ → ℕ), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size = x4.size ∧ (∀ x8 < x1 + x4.size, x7 x8 < x2 + x6.size) ∧ ∀ (x8 : Fin x2 → Bool), ∀ x9 < x1 + x4.size, (x6.wires (List.ofFn x8)).getD (x7 x9) Bool.false = (x4.wires (List.ofFn (x8 ∘ x3))).getD x9 Bool.false := by
  intro m N σ C hC
  refine ⟨⟨C.gates.map (reGate (rho m N σ)), C.output⟩, rho m N σ, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    have := hC g' hg'
    simpa [reGate] using this
  · simp [Circuit.size]
  · intro k hk
    simp only [Circuit.size, List.length_map] at hk ⊢
    unfold rho
    split_ifs with h
    · have := (σ ⟨k, h⟩).isLt
      omega
    · omega
  · intro x k _
    have hW : (List.ofFn x).length = N := by simp
    have hy : (List.ofFn (x ∘ σ)).length = m := by simp
    obtain ⟨R, h1, h2⟩ := fold_rel _ _ σ hW hy (hyv_lem σ x) C.gates []
    simp only [List.append_nil] at h1 h2
    show (List.foldl stepW _ _).getD _ false = (List.foldl stepW _ _).getD _ false
    rw [h1, h2, getD_rho _ _ R σ hW hy (hyv_lem σ x)]
