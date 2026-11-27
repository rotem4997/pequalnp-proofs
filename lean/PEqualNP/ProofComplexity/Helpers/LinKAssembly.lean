import PEqualNP.ProofComplexity.Helpers.LinKPlan
import PEqualNP.ProofComplexity.Helpers.DegSizeGainK
import PEqualNP.ProofComplexity.Helpers.DegSizeArith

/-!
# Middle assembly for L-pcx-054 (degree to size for Res(k, ⊕))

The assembly inequality and the general theorem of `LinKPlan`, with the upstream statements
of the plan (the simulation of a refutation, the arithmetic) taken as hypotheses in the exact
form of the plan's `example`s. Nothing here is a recorded lemma.
-/

namespace PEqualNP.ProofComplexity.LinKAsm

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.LinKPlan PEqualNP.ProofComplexity.DegSizePlan

/-- The plan's "consequence for a refutation" statement, verbatim. -/
def StmtSimRefutation : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    PCDerivable (cnfSystem F) D f

/-- The plan's arithmetic statement, verbatim. -/
def StmtArith : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
    ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
    (∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
      1 ≤ (π.length : ℝ) * (1 - etaK (Fintype.card V) K k) ^ t) →
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
      ≤ (π.length : ℝ)

/-- The plan's assembly inequality, verbatim. -/
def StmtAssembly : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π → ¬ PCRefutable (cnfSystem F) D →
    k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
    1 ≤ (π.length : ℝ) * (1 - etaK (Fintype.card V) K k) ^ t

/-- The plan's general theorem, verbatim. -/
def StmtGeneral : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
    ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
      ≤ (π.length : ℝ)

/-- Every term of every line of a derivation has at most `k` equations. -/
theorem term_card {V : Type} [DecidableEq V] {k : ℕ} {W : LinKLine V → LinKLine V → Prop}
    {F : Set (LinKLine V)} {π : List (LinKLine V)} (h : IsLinKDerivation k W F π) :
    ∀ L ∈ π, ∀ T ∈ L, T.card ≤ k := by
  induction h with
  | nil => intro L hL; simp at hL
  | ax _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
  | cut _ _ _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
  | andIntro _ _ _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
  | weak _ _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL

theorem etaK_le_one (n K k : ℕ) : etaK n K k ≤ 1 := by
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast DegSizeGain.numMono_pos n K
  have hN1 : (numMono n (K - k) : ℝ) ≤ numMono n K := by
    exact_mod_cast DegSizeGain.numMono_mono n (Nat.sub_le K k)
  unfold etaK
  exact (div_le_one (by positivity)).mpr (by linarith)

/-- The assembly inequality, from the simulation of a refutation. -/
theorem assembly (hSim : StmtSimRefutation) : StmtAssembly := by
  classical
  intro V _ _ F π k w D K t hk hw href hnr hkK hB
  by_contra hlt
  rw [not_le] at hlt
  have hk2 : 2 * k ≤ 2 * t * k + 2 * k := Nat.le_add_left _ _
  have hD2 : 2 ≤ D := by omega
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure (cnfSystem F) D hD2 (fun v => Or.inl ⟨v, rfl⟩)
  have h1 : (1 : MvPolynomial V (ZMod 2)) ∉ pcClosure (cnfSystem F) D := hnr
  have hnn : (0 : ℝ) ≤ (1 - etaK (Fintype.card V) K k) ^ t :=
    pow_nonneg (sub_nonneg.mpr (etaK_le_one _ K k)) t
  have hcard : (π.toFinset.card : ℝ) ≤ (π.length : ℝ) := by
    exact_mod_cast List.toFinset_card_le π
  have hS : (π.toFinset.card : ℝ) * (1 - DegSizeGainK.eta_k (Fintype.card V) K k) ^ t < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcard hnn) hlt
  have htk : t * k + k ≤ 2 * t * k + 2 * k := by nlinarith
  obtain ⟨f, qs, hf, hfC, hspan, hmem⟩ :=
    DegSizeGainK.common_k V (pcClosure (cnfSystem F) D) D K t k (LinKLine V) π.toFinset
      (fun L => L.image (fun T => termPoly T)) hC h1
      (by
        intro L hL g hg
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hg
        exact le_trans (totalDegree_termPoly_le T)
          (term_card href.1 L (List.mem_toFinset.mp hL) T hT))
      hkK (by omega) hS
  apply hfC
  refine hSim V F π k w D K t f qs hk hw href hB hf ?_ ?_
  · intro L hL j
    have := hspan L (List.mem_toFinset.mpr hL) j
    simpa [lineInputs, Finset.coe_image] using this
  · intro L hL T hT
    exact hmem L (List.mem_toFinset.mpr hL) (termPoly T) (Finset.mem_image_of_mem _ hT)

/-- The general theorem: degree to size for Res(k, ⊕), from the simulation of a refutation
and the arithmetic. -/
theorem degree_to_size_k (hSim : StmtSimRefutation) (hArith : StmtArith) : StmtGeneral := by
  intro V _ _ F π k w D hw hk hkD hwD hnr href
  exact hArith V F π k w D hw hk hkD hwD hnr href
    (fun K t hkK hB => assembly hSim V F π k w D K t hk hw href hnr hkK hB)

end PEqualNP.ProofComplexity.LinKAsm
