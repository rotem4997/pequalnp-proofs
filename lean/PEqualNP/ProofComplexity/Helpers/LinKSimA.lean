import PEqualNP.ProofComplexity.Helpers.LinKPlan

/-!
# Helpers for L-pcx-054: the transfer step, the axiom rule and the cut rule of Res(k, ⊕)

Three of the link statements of `LinKPlan`, each proved exactly as stated there:

* `transfer_k`: the transfer step for inputs of degree at most `k`, budget `K + t * k + r`;
* `step_ax_k`: the axiom rule, budget `K + t * k + w` with `1 ≤ k`;
* `step_cut_k`: the cut rule, budget `K + 2 * t * k + 2 * k`.

They are the degree `k` twins of `DegSizeSim.transfer`, `DegSizeSim.step_ax` and
`DegSizeSim.step_res`. The reusable pieces are exported for the other rules:
`totalDegree_one_add_le_k`, `totalDegree_prod_le_k`, `prod_absorb_k`, `totalDegree_span_le_k`,
`totalDegree_appr_le_k`, `span_mul_mem`, `transfer_k'`, `totalDegree_lineInputs_le`,
`totalDegree_lineAppr_le`, `lineInputs_linKOfClause_subset`, `step_ax_k'`, `step_cut_k'`.
-/

namespace PEqualNP.ProofComplexity.LinKSimA

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan PEqualNP.ProofComplexity.LinKPlan

section Abstract

variable {σ : Type} {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}

theorem totalDegree_one_add_le_k {p : MvPolynomial σ (ZMod 2)} {k : ℕ}
    (h : p.totalDegree ≤ k) : (1 + p).totalDegree ≤ k := by
  refine (totalDegree_add _ _).trans ?_
  rw [totalDegree_one]
  exact max_le (Nat.zero_le _) h

/-- A product of `1 + a u` over a finite set, each `a u` of degree at most `k`. -/
theorem totalDegree_prod_le_k {ι : Type} (s : Finset ι) (a : ι → MvPolynomial σ (ZMod 2))
    {k : ℕ} (ha : ∀ u ∈ s, (a u).totalDegree ≤ k) :
    (∏ u ∈ s, (1 + a u)).totalDegree ≤ s.card * k := by
  have := Helpers.totalDegree_prod_one_add_le s a (e := k) ha
  rw [Nat.mul_comm]
  exact this

/-- Telescoping in a degree-closed space, factors of degree at most `k`: if every `a u * Q` is
in the space, so is `(∏ u ∈ s, (1 + a u)) * Q + Q`, in budget `s.card * k + deg Q`. -/
theorem prod_absorb_k (hC : DegClosed C D) {ι : Type} (s : Finset ι)
    (a : ι → MvPolynomial σ (ZMod 2)) (Q : MvPolynomial σ (ZMod 2)) {dQ k : ℕ}
    (hdQ : Q.totalDegree ≤ dQ) (ha : ∀ u ∈ s, a u * Q ∈ C)
    (hdeg : ∀ u ∈ s, (a u).totalDegree ≤ k) (hB : s.card * k + dQ ≤ D) :
    (∏ u ∈ s, (1 + a u)) * Q + Q ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, one_mul, char2_add_self]
    exact C.zero_mem
  | insert u s hu ih =>
    rw [Finset.card_insert_of_notMem hu, Nat.add_mul, Nat.one_mul] at hB
    have hdeg' : ∀ v ∈ s, (a v).totalDegree ≤ k := fun v hv =>
      hdeg v (Finset.mem_insert_of_mem hv)
    have ih' := ih (fun v hv => ha v (Finset.mem_insert_of_mem hv)) hdeg' (by omega)
    have hd : ((∏ v ∈ s, (1 + a v)) * Q + Q).totalDegree ≤ s.card * k + dQ := by
      refine (totalDegree_add _ _).trans (max_le ?_ (by omega))
      exact totalDegree_mul_le' (totalDegree_prod_le_k s a hdeg') hdQ
    have h1 : (1 + a u).totalDegree ≤ k :=
      totalDegree_one_add_le_k (hdeg u (Finset.mem_insert_self u s))
    have h2 := DegSizeSim.absorb_le hC (1 + a u) ih' h1 hd (by omega)
    have h3 := C.add_mem h2 (ha u (Finset.mem_insert_self u s))
    have e : (∏ v ∈ insert u s, (1 + a v)) * Q + Q
        = (1 + a u) * ((∏ v ∈ s, (1 + a v)) * Q + Q) + a u * Q := by
      rw [Finset.prod_insert hu]
      linear_combination (-1 : MvPolynomial σ (ZMod 2)) * char2_add_self (a u * Q)
    rw [e]
    exact h3

/-- A member of the span of polynomials of degree at most `k` has degree at most `k`. -/
theorem totalDegree_span_le_k {G : Set (MvPolynomial σ (ZMod 2))} {k : ℕ}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx

/-- The approximator `∏ j, (1 + qs j)` has degree at most `t * k`. -/
theorem totalDegree_appr_le_k {t k : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  have := totalDegree_prod_le_k Finset.univ qs (fun j _ => h j)
  simpa using this

/-- If every generator times `Q` is in the space, so is every member of the span times `Q`. -/
theorem span_mul_mem {G : Set (MvPolynomial σ (ZMod 2))} {Q : MvPolynomial σ (ZMod 2)}
    (hg : ∀ g ∈ G, g * Q ∈ C) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q * Q ∈ C := by
  induction hq using Submodule.span_induction with
  | mem g hg' => exact hg g hg'
  | zero => simp
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact C.add_mem hx hy
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx

/-- The transfer step for inputs of degree at most `k`, implicit form. -/
theorem transfer_k' (hC : DegClosed C D) {K t k r : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (qs : Fin t → MvPolynomial σ (ZMod 2)) {f R : MvPolynomial σ (ZMod 2)}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) G)
    (hf : f.totalDegree ≤ K) (hR : R.totalDegree ≤ r) (hB : K + t * k + r ≤ D)
    (hP : (∏ j, (1 + qs j)) * f ∈ C) (hg : ∀ g ∈ G, g * R * f ∈ C) : R * f ∈ C := by
  have hQ : (R * f).totalDegree ≤ r + K := totalDegree_mul_le' hR hf
  have hspan : ∀ q ∈ Submodule.span (ZMod 2) G, q * (R * f) ∈ C := fun q hq =>
    span_mul_mem (fun g hg' => by
      rw [← mul_assoc]
      exact hg g hg') hq
  have hdq : ∀ j, (qs j).totalDegree ≤ k := fun j => totalDegree_span_le_k hG (hqs j)
  have h1 := prod_absorb_k hC Finset.univ qs (R * f) hQ (fun u _ => hspan _ (hqs u))
    (fun u _ => hdq u) (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  have hPd : ((∏ j, (1 + qs j)) * f).totalDegree ≤ t * k + K :=
    totalDegree_mul_le' (totalDegree_appr_le_k qs hdq) hf
  have h2 := DegSizeSim.absorb_le hC R hP hR hPd (by omega)
  have h3 := C.add_mem h1 h2
  have e : (∏ j, (1 + qs j)) * (R * f) + R * f + R * ((∏ j, (1 + qs j)) * f) = R * f := by
    linear_combination char2_add_self ((∏ j, (1 + qs j)) * (R * f))
  rwa [e] at h3

/-- The transfer step for inputs of degree at most `k`. Budget `K + t * k + deg R ≤ D`. The
statement is the one of `LinKPlan`. -/
theorem transfer_k :
    ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k r : ℕ)
    (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
    (f R : MvPolynomial σ (ZMod 2)),
    DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
    K + t * k + r ≤ D →
    (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C :=
  fun _ _ _ _ _ _ _ _ qs _ _ hC hG hqs hf hR hB hP hg =>
    transfer_k' hC qs hG hqs hf hR hB hP hg

end Abstract

section Lines

variable {V : Type} {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D K t k : ℕ}
  {f : MvPolynomial V (ZMod 2)}

/-- The inputs of a line whose terms have at most `k` equations have degree at most `k`. -/
theorem totalDegree_lineInputs_le {L : LinKLine V} (hL : ∀ T ∈ L, T.card ≤ k) :
    ∀ g ∈ lineInputs L, g.totalDegree ≤ k := by
  rintro _ ⟨T, hT, rfl⟩
  exact (totalDegree_termPoly_le T).trans (hL T (Finset.mem_coe.mp hT))

/-- The approximator of a line whose terms have at most `k` equations has degree at most
`t * k`. -/
theorem totalDegree_lineAppr_le {L : LinKLine V} (hL : ∀ T ∈ L, T.card ≤ k)
    (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs L)) :
    (∏ j, (1 + qs j)).totalDegree ≤ t * k :=
  totalDegree_appr_le_k qs fun j =>
    totalDegree_span_le_k (totalDegree_lineInputs_le hL) (hqs j)

/-- The inputs of the line of a clause are the affine forms of its literals. -/
theorem lineInputs_linKOfClause_subset [DecidableEq V] (A : Clause V) :
    lineInputs (linKOfClause A) ⊆ (fun q => eqPoly q) '' (↑(linOfClause A) : Set (LinEq V)) := by
  rintro _ ⟨T, hT, rfl⟩
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hT)
  exact ⟨q, Finset.mem_coe.mpr hq, (termPoly_singleton q).symm⟩

/-- The axiom rule, implicit form: budget `K + t + w` (the inputs of an axiom have degree
one, whatever `k` is). -/
theorem step_ax_k' [DecidableEq V] (hC : DegClosed C D) (A : Clause V) {w : ℕ}
    (hA : clausePoly A ∈ C) (hw : A.card ≤ w) (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs (linKOfClause A)))
    (hf : f.totalDegree ≤ K) (hB : K + t + w ≤ D)
    (hH : ∀ T ∈ linKOfClause A, (∏ j, (1 + qs j)) * termPoly T * f ∈ C) :
    (∏ j, (1 + qs j)) * f ∈ C := by
  refine DegSizeSim.step_ax hC A hA hw qs
    (fun j => Submodule.span_mono (lineInputs_linKOfClause_subset A) (hqs j)) hf hB ?_
  intro q hq
  have := hH {q} (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  rwa [termPoly_singleton] at this

/-- The axiom rule. Budget `K + t * k + w ≤ D` with `1 ≤ k`. The statement is the one of
`LinKPlan`. -/
theorem step_ax_k :
    ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k w : ℕ) (f : MvPolynomial V (ZMod 2)) (A : Clause V)
    (qs : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → clausePoly A ∈ C → A.card ≤ w →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs (linKOfClause A))) →
    f.totalDegree ≤ K → K + t * k + w ≤ D →
    (∀ T ∈ linKOfClause A, (∏ j, (1 + qs j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qs j)) * f ∈ C := by
  intro V _ C D K t k w f A qs hC hk hA hw hqs hf hB hH
  have htk : t ≤ t * k := Nat.le_mul_of_pos_right t hk
  exact step_ax_k' hC A hA hw qs hqs hf (by omega) hH

/-- The cut rule, implicit form. Budget `K + 2 * t * k + 2 * k ≤ D`. -/
theorem step_cut_k' [DecidableEq V] (hC : DegClosed C D) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2))
    (h1 : ∀ T ∈ L₁, T.card ≤ k) (h2 : ∀ T ∈ L₂, T.card ≤ k) (hM : ∀ T ∈ M, T.card ≤ k)
    (hq1 : ∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁))
    (hq2 : ∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂))
    (hqM : ∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M))
    (hf : f.totalDegree ≤ K) (hB : K + 2 * t * k + 2 * k ≤ D) (hcut : IsLinKCut L₁ L₂ M)
    (hP1 : (∏ j, (1 + q₁ j)) * f ∈ C) (hP2 : (∏ j, (1 + q₂ j)) * f ∈ C)
    (hHM : ∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) :
    (∏ j, (1 + qM j)) * f ∈ C := by
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t * k := totalDegree_lineAppr_le hM qM hqM
  generalize (∏ j, (1 + qM j)) = P at hdM hHM ⊢
  obtain ⟨T, hT1, -, rfl⟩ := hcut
  have hTk : T.card ≤ k := h1 T hT1
  have hτ : (termPoly T).totalDegree ≤ k := (totalDegree_termPoly_le T).trans hTk
  have hQ : (P * f).totalDegree ≤ t * k + K := totalDegree_mul_le' hdM hf
  have hd1 : (1 + termPoly T).totalDegree ≤ k := totalDegree_one_add_le_k hτ
  have hmul : 2 * t * k = t * k + t * k := by ring
  -- through the first premise, with multiplier `(1 + termPoly T) * P`
  have hA : (1 + termPoly T) * P * f ∈ C := by
    have hdR : ((1 + termPoly T) * P).totalDegree ≤ k + t * k := totalDegree_mul_le' hd1 hdM
    refine transfer_k' hC q₁ (totalDegree_lineInputs_le h1) hq1 hf hdR (by omega) hP1 ?_
    rintro _ ⟨S, hS, rfl⟩
    have hS' : S ∈ L₁ := Finset.mem_coe.mp hS
    by_cases hST : S = T
    · rw [hST]
      have := idem_mul hC (termPoly T) (P * f) hQ hτ (by omega)
      have e1 : termPoly T * ((1 + termPoly T) * P) * f
          = P * f * (termPoly T * termPoly T + termPoly T) := by ring
      rw [e1]
      exact this
    · have hmem := hHM S (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hST, hS'⟩))
      have hd : (P * termPoly S * f).totalDegree ≤ t * k + k + K :=
        totalDegree_mul_le'
          (totalDegree_mul_le' hdM ((totalDegree_termPoly_le S).trans (h1 S hS'))) hf
      have := DegSizeSim.absorb_le hC (1 + termPoly T) hmem hd1 hd (by omega)
      have e1 : termPoly S * ((1 + termPoly T) * P) * f
          = (1 + termPoly T) * (P * termPoly S * f) := by ring
      rw [e1]
      exact this
  -- through the second premise, with multiplier `termPoly T * P`
  have hB' : termPoly T * P * f ∈ C := by
    have hdR : (termPoly T * P).totalDegree ≤ k + t * k := totalDegree_mul_le' hτ hdM
    refine transfer_k' hC q₂ (totalDegree_lineInputs_le h2) hq2 hf hdR (by omega) hP2 ?_
    rintro _ ⟨S, hS, rfl⟩
    have hS' : S ∈ L₂ := Finset.mem_coe.mp hS
    by_cases hSi : S ∈ T.image (fun e => ({negLinEq e} : LinTerm V))
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hSi
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨e, he⟩
      have := term_neg_mul hC T e he (P * f) hQ (by omega)
      show termPoly {negLinEq e} * (termPoly T * P) * f ∈ C
      rw [termPoly_singleton]
      have e1 : eqPoly (negLinEq e) * (termPoly T * P) * f
          = P * f * (termPoly T * eqPoly (negLinEq e)) := by ring
      rw [e1]
      exact this
    · have hmem := hHM S (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hS', hSi⟩))
      have hd : (P * termPoly S * f).totalDegree ≤ t * k + k + K :=
        totalDegree_mul_le'
          (totalDegree_mul_le' hdM ((totalDegree_termPoly_le S).trans (h2 S hS'))) hf
      have := DegSizeSim.absorb_le hC (termPoly T) hmem hτ hd (by omega)
      have e1 : termPoly S * (termPoly T * P) * f
          = termPoly T * (P * termPoly S * f) := by ring
      rw [e1]
      exact this
  have h3 := C.add_mem hA hB'
  have e1 : (1 + termPoly T) * P * f + termPoly T * P * f = P * f := by
    linear_combination char2_add_self (termPoly T * P * f)
  rwa [e1] at h3

/-- The cut rule. Budget `K + 2 * t * k + 2 * k ≤ D`. The statement is the one of
`LinKPlan`. -/
theorem step_cut_k :
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
    (∏ j, (1 + qM j)) * f ∈ C := by
  intro V _ C D K t k f L₁ L₂ M q₁ q₂ qM hC h1 h2 hM hq1 hq2 hqM hf hB hcut hP1 hP2 hHM
  exact step_cut_k' hC L₁ L₂ M q₁ q₂ qM h1 h2 hM hq1 hq2 hqM hf hB hcut hP1 hP2 hHM

end Lines

end PEqualNP.ProofComplexity.LinKSimA
