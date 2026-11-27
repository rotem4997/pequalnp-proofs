import PEqualNP.ProofComplexity.Helpers.LinKPlan

/-!
# Helpers for L-pcx-054: the simulation of a Res(k, ⊕) derivation from the four rule steps

Helper module, proofs only. The statements are the `example : Prop` items of `LinKPlan` named
"The simulation of a derivation" and "Its consequence for a refutation". The four rule steps
(axiom, cut, and-introduction, termwise weakening) are taken as hypotheses, with the bodies of
the corresponding `example : Prop` items of `LinKPlan` copied verbatim into the local names
`AxRule`, `CutRule`, `AndRule`, `WeakRule`; the two statements proved are `SimDrv` and
`SimRef`, also verbatim copies.

* `drv_card_le`: every term of every line of a derivation has at most `k` equations.
* `simulation_of`: the induction over the derivation, mirroring `DegSizeSim.simulation`.
* `simulation_refutation_of`: the empty line finishes, mirroring
  `DegSizeSim.simulation_refutation`.
-/

namespace PEqualNP.ProofComplexity.LinKSim

open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan PEqualNP.ProofComplexity.LinKPlan

/-- The axiom rule, as stated in `LinKPlan`. -/
def AxRule : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k w : ℕ) (f : MvPolynomial V (ZMod 2)) (A : Clause V)
    (qs : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → clausePoly A ∈ C → A.card ≤ w →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs (linKOfClause A))) →
    f.totalDegree ≤ K → K + t * k + w ≤ D →
    (∀ T ∈ linKOfClause A, (∏ j, (1 + qs j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qs j)) * f ∈ C

/-- The cut rule, as stated in `LinKPlan`. -/
def CutRule : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
    (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKCut L₁ L₂ M →
    (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C

/-- The and-introduction rule, as stated in `LinKPlan`. -/
def AndRule : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
    (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKAndIntro L₁ L₂ M →
    (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C

/-- The termwise weakening rule, as stated in `LinKPlan`. -/
def WeakRule : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L M : LinKLine V)
    (qL qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → (∀ T ∈ L, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, qL j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKWeakening L M →
    (∏ j, (1 + qL j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C

/-- The simulation of a derivation, as stated in `LinKPlan`. -/
def SimDrv : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) →
    IsLinKDerivation k IsLinKWeakening ((fun A => linKOfClause A) '' F) π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    ∀ L ∈ π, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * f)

/-- The consequence for a refutation, as stated in `LinKPlan`. -/
def SimRef : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    PCDerivable (cnfSystem F) D f

/-- Every term of every line of a derivation has at most `k` equations. -/
theorem drv_card_le {V : Type} [DecidableEq V] {k : ℕ} {W : LinKLine V → LinKLine V → Prop}
    {F : Set (LinKLine V)} {π : List (LinKLine V)} (h : IsLinKDerivation k W F π) :
    ∀ L ∈ π, ∀ T ∈ L, T.card ≤ k := by
  induction h with
  | nil =>
    intro L hL
    simp at hL
  | ax _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
  | cut _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
  | andIntro _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
  | weak _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'

/-- The simulation of a derivation, from the four rule steps. -/
theorem simulation_of (hax : AxRule) (hcut : CutRule) (hand : AndRule) (hweak : WeakRule) :
    SimDrv := by
  intro V _ _ F π k w D K t f qs hk hw hder hB hf
  have hB1 : K + 2 * t * k + 2 * k ≤ D := by
    have := (Nat.add_le_add_left (le_max_left (2 * t * k + 2 * k) (t * k + w)) K).trans hB
    rwa [← Nat.add_assoc] at this
  have hB2 : K + t * k + w ≤ D := by
    have := (Nat.add_le_add_left (le_max_right (2 * t * k + 2 * k) (t * k + w)) K).trans hB
    rwa [← Nat.add_assoc] at this
  have hD2 : 2 ≤ D := by
    have h2 : 2 ≤ 2 * k := by omega
    exact h2.trans ((Nat.le_add_left _ _).trans hB1)
  have hwD : w ≤ D := (Nat.le_add_left _ _).trans hB2
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure _ _ hD2 fun v => Or.inl ⟨v, rfl⟩
  have key : ∀ ρ : List (LinKLine V),
      IsLinKDerivation k IsLinKWeakening ((fun A => linKOfClause A) '' F) ρ →
      (∀ L ∈ ρ, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
      (∀ L ∈ ρ, ∀ T ∈ L, (∏ j, (1 + qs L j)) * termPoly T * f ∈ pcClosure (cnfSystem F) D) →
      ∀ L ∈ ρ, (∏ j, (1 + qs L j)) * f ∈ pcClosure (cnfSystem F) D := by
    intro ρ hρ
    induction hρ with
    | nil =>
      intro _ _ L hL
      simp at hL
    | @ax ρ L0 _ hL0 _ ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        obtain ⟨A, hAF, hA⟩ := hL0
        subst hA
        have hAw := hw A hAF
        have hmem : clausePoly A ∈ pcClosure (cnfSystem F) D :=
          PCDerivable.ax (Or.inr ⟨A, hAF, rfl⟩)
            ((DegSizeSim.totalDegree_clausePoly_le A).trans (hAw.trans hwD))
        exact hax V (pcClosure (cnfSystem F) D) D K t k w f A (qs (linKOfClause A))
          hC hk hmem hAw (hs _ List.mem_cons_self) hf hB2 (hH _ List.mem_cons_self)
      · exact ih' L hL'
    | @cut ρ L1 L2 M hρ' h1 h2 hrule hkM ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact hcut V (pcClosure (cnfSystem F) D) D K t k f L1 L2 L (qs L1) (qs L2) (qs L)
          hC (drv_card_le hρ' L1 h1) (drv_card_le hρ' L2 h2) hkM
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L2 (List.mem_cons_of_mem _ h2))
          (hs L List.mem_cons_self) hf hB1 hrule (ih' L1 h1) (ih' L2 h2)
          (hH L List.mem_cons_self)
      · exact ih' L hL'
    | @andIntro ρ L1 L2 M hρ' h1 h2 hrule hkM ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact hand V (pcClosure (cnfSystem F) D) D K t k f L1 L2 L (qs L1) (qs L2) (qs L)
          hC (drv_card_le hρ' L1 h1) (drv_card_le hρ' L2 h2) hkM
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L2 (List.mem_cons_of_mem _ h2))
          (hs L List.mem_cons_self) hf hB1 hrule (ih' L1 h1) (ih' L2 h2)
          (hH L List.mem_cons_self)
      · exact ih' L hL'
    | @weak ρ L1 M hρ' h1 hrule hkM ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact hweak V (pcClosure (cnfSystem F) D) D K t k f L1 L (qs L1) (qs L)
          hC hk (drv_card_le hρ' L1 h1) hkM
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L List.mem_cons_self) hf hB1 hrule
          (ih' L1 h1) (hH L List.mem_cons_self)
      · exact ih' L hL'
  intro hs hH
  exact key π hder hs hH

/-- The consequence for a refutation, from the four rule steps: the common multiplier is
derivable. -/
theorem simulation_refutation_of (hax : AxRule) (hcut : CutRule) (hand : AndRule)
    (hweak : WeakRule) : SimRef := by
  intro V _ _ F π k w D K t f qs hk hw href hB hf hs hH
  obtain ⟨hder, hemp⟩ := href
  have h := simulation_of hax hcut hand hweak V F π k w D K t f qs hk hw hder hB hf hs hH
    ∅ hemp
  have hq : ∀ j, qs ∅ j = 0 := by
    intro j
    have := hs ∅ hemp j
    simpa [lineInputs] using this
  simpa [hq] using h

end PEqualNP.ProofComplexity.LinKSim
