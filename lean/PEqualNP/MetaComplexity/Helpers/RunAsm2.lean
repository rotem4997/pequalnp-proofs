import PEqualNP.MetaComplexity.Helpers.RunAsm
import PEqualNP.MetaComplexity.Helpers.ReadersPat

/-!
# Run-of-four assembly, part 2: relabelling a least list along an involution of the inputs

The checked rows L-meta-588 and L-meta-596 name one input `Fin.last n`. A least list for `F` is
moved along an involution `σ` of the inputs (a swap): gate positions and gate wires stay, input
wire `i` becomes `σ i`. The list stays clean and least for `x ↦ F (x ∘ σ)`, and the reader
relation moves with the wires. Also: a least list is a minimal circuit in the root sense.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.PermInputs

section Rel

variable {m : ℕ} (σ : Equiv.Perm (Fin m))

/-- The wire renaming along `σ`. -/
def asmW (w : ℕ) : ℕ := wmap m m σ w

/-- The list with its input wires renamed along `σ`. -/
def asmG (gs : List Gate) : List Gate := gs.map (relGate m m σ)

theorem asmW_ge {w : ℕ} (h : m ≤ w) : asmW σ w = w := by
  unfold asmW wmap
  rw [dif_neg (by omega)]
  omega

theorem asmW_fin (i : Fin m) : asmW σ i = σ i := by
  unfold asmW wmap
  rw [dif_pos i.isLt]

theorem asmW_lt {w : ℕ} (h : w < m) : asmW σ w < m := by
  unfold asmW wmap
  rw [dif_pos h]
  exact (σ _).isLt

theorem asmW_inv (hσ : ∀ i, σ (σ i) = i) (w : ℕ) : asmW σ (asmW σ w) = w := by
  by_cases h : w < m
  · have e : asmW σ w = (σ ⟨w, h⟩ : ℕ) := asmW_fin σ ⟨w, h⟩
    rw [e, asmW_fin σ (σ ⟨w, h⟩), hσ]
  · have e := asmW_ge σ (show m ≤ w by omega)
    rw [e, e]

theorem asmW_mono_lt {w b : ℕ} (hb : m ≤ b) (h : w < b) : asmW σ w < b := by
  by_cases hw : w < m
  · have := asmW_lt σ hw; omega
  · rw [asmW_ge σ (by omega)]; exact h

theorem asmG_get (gs : List Gate) (p : ℕ) :
    (asmG σ gs)[p]? = (gs[p]?).map (relGate m m σ) := by
  simp [asmG]

theorem asmG_len (gs : List Gate) : (asmG σ gs).length = gs.length := by
  simp [asmG]

theorem asm_reads (hσ : ∀ i, σ (σ i) = i) (gs : List Gate) (p w : ℕ) :
    Reads (asmG σ gs) p w ↔ Reads gs p (asmW σ w) := by
  constructor
  · rintro ⟨g', hg', hw⟩
    rw [asmG_get] at hg'
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hg'
    refine ⟨g, hg, ?_⟩
    simp only [relGate, List.mem_map] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    have : asmW σ (wmap m m σ a) = a := asmW_inv σ hσ a
    rw [this]; exact ha
  · rintro ⟨g, hg, hw⟩
    refine ⟨relGate m m σ g, by rw [asmG_get, hg]; rfl, ?_⟩
    simp only [relGate, List.mem_map]
    exact ⟨_, hw, asmW_inv σ hσ w⟩

theorem asm_clean (gs : List Gate) (hcl : CleanL m gs) : CleanL m (asmG σ gs) := by
  intro p g' hg'
  rw [asmG_get] at hg'
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hg'
  have hb : m ≤ m + p := by omega
  rcases hcl p g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact Or.inl ⟨hop, asmW σ j, asmW_mono_lt σ hb hj, by simp [relGate, hin, asmW]⟩
  · exact Or.inr ⟨hop, asmW σ j, asmW σ k, asmW_mono_lt σ hb hj, asmW_mono_lt σ hb hk,
      by simp [relGate, hin, asmW]⟩

theorem asm_vl (hσ : ∀ i, σ (σ i) = i) (gs : List Gate) (x : Fin m → Bool) (w : ℕ) :
    vl (asmG σ gs) x w = vl gs (x ∘ σ) (asmW σ w) := by
  have h := (rel_fold m m σ gs _ _ (rel_init m m σ x)).2.2 (asmW σ w)
  have h2 : wmap m m σ (asmW σ w) = w := asmW_inv σ hσ w
  rw [h2] at h
  exact h

theorem asm_least (hσ : ∀ i, σ (σ i) = i) {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) : Least m (fun x => f (x ∘ σ)) (asmG σ gs) (asmW σ o) := by
  refine ⟨asm_clean σ gs L.hcl, fun x => ?_, fun gs' o' hc' he' => ?_⟩
  · rw [asm_vl σ hσ, asmW_inv σ hσ, L.hev]
  · have h1 := L.hmin (asmG σ gs') (asmW σ o') (asm_clean σ gs' hc') (fun x => by
      rw [asm_vl σ hσ, asmW_inv σ hσ, he']
      congr 1; funext i; simp [hσ])
    simpa [asmG_len] using h1

end Rel

/-- A least list is a minimal circuit in the root sense. -/
theorem asm_least_min {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    IsMinimalCircuit m (Circuit.mk gs o) := by
  refine ⟨?_, fun D hD he => ?_⟩
  · intro g hg
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    rcases L.hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, hin⟩
    · exact ⟨by rw [hop]; simp, by rw [hin]; simp⟩
    · refine ⟨?_, by rw [hin]; simp⟩
      rcases hop with hop | hop <;> rw [hop] <;> simp
  · have hs : HasCircuitSize m f D.size := ⟨D, hD, le_refl _, fun x => by
      have := congrFun he x
      unfold circuitFun at this
      rw [this]
      exact L.hev x⟩
    exact L.lower hnc _ hs

end PEqualNP.MetaComplexity.Helpers.RunAsm
