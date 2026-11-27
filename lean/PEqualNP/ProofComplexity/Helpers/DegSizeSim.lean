import PEqualNP.ProofComplexity.Helpers.DegSizePlan

/-!
# Helpers for L-pcx-042: the simulation links (degree to size for Res(⊕))

The statements are the `example : Prop` items of `DegSizePlan` named Lemma A, Lemma A', the
transfer step, Proposition 5.1 on our rules and its consequence for a refutation. Source of
the mathematics: the unrefereed preprint arXiv:2610.00837, Section 5, at `p = 2`, re-derived
for our rules (semantic weakening of one line, resolution on a linear form).

* `absorb`: a member of a degree-closed space may be multiplied by any polynomial inside the
  degree cap.
* `affine_idem`: `g * g + g` is in the space for every `g` of degree at most one.
* `transfer`: the transfer step.
* `simulation`: along a Res(⊕) derivation every line's approximator times the common
  multiplier is derivable.
* `simulation_refutation`: for a refutation the common multiplier itself is derivable.

Every line is simulated without extension variables. The degree used: axiom `K + t + w`,
weakening `K + 2 * t` and `K + t + 1`, resolution `K + 2 * t + 1` and `K + t + 2`.
-/

namespace PEqualNP.ProofComplexity.DegSizeSim

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan

section Abstract

variable {σ : Type} {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}

/-- Multiplication of a member by a monomial inside the degree cap. -/
theorem monomial_mul_mem (hC : DegClosed C D) (a : σ →₀ ℕ) :
    ∀ {g : MvPolynomial σ (ZMod 2)}, g ∈ C → (a.sum fun _ e => e) + g.totalDegree ≤ D →
      monomial a 1 * g ∈ C := by
  induction a using Finsupp.induction_linear with
  | zero =>
    intro g hg _
    have : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [this, one_mul]
    exact hg
  | add a b iha ihb =>
    intro g hg hdeg
    have hsplit : monomial (a + b) (1 : ZMod 2) * g = monomial a 1 * (monomial b 1 * g) := by
      rw [← mul_assoc, monomial_mul_monomial, one_mul]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hdeg
    have hb : (monomial b (1 : ZMod 2) * g).totalDegree
        ≤ (b.sum fun _ e => e) + g.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_monomial_le b 1) _)
    rw [hsplit]
    exact iha (ihb hg (by omega)) (by omega)
  | single j n =>
    induction n with
    | zero =>
      intro g hg _
      have : (monomial (Finsupp.single j 0) (1 : ZMod 2)) = 1 := by simp
      rw [this, one_mul]
      exact hg
    | succ n ih =>
      intro g hg hdeg
      have hsplit : monomial (Finsupp.single j (n + 1)) (1 : ZMod 2) * g
          = X j * (monomial (Finsupp.single j n) 1 * g) := by
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add,
          add_comm 1 n]
      have hd1 : ((Finsupp.single j (n + 1)).sum fun _ e => e) = n + 1 :=
        Finsupp.sum_single_index rfl
      have hd2 : ((Finsupp.single j n).sum fun _ e => e) = n :=
        Finsupp.sum_single_index rfl
      rw [hd1] at hdeg
      have hlow : (monomial (Finsupp.single j n) (1 : ZMod 2) * g).totalDegree
          ≤ n + g.totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_right
          ((totalDegree_monomial_le _ 1).trans_eq hd2) _)
      rw [hsplit]
      exact hC.mulX j _ (ih hg (by omega)) (by omega)

/-- Lemma A with explicit degree bounds. -/
theorem absorb_le (hC : DegClosed C D) (g : MvPolynomial σ (ZMod 2))
    {f : MvPolynomial σ (ZMod 2)} (hf : f ∈ C) {a b : ℕ} (hg : g.totalDegree ≤ a)
    (hfd : f.totalDegree ≤ b) (hB : a + b ≤ D) : g * f ∈ C := by
  have hq : g * f = ∑ u ∈ g.support, monomial u (g.coeff u) * f := by
    conv_lhs => rw [g.as_sum]
    rw [Finset.sum_mul]
  rw [hq]
  refine Submodule.sum_mem _ fun u hu => ?_
  have hc : g.coeff u = 1 := by
    have h0 : g.coeff u ≠ 0 := mem_support_iff.mp hu
    generalize g.coeff u = c at h0
    revert h0; revert c; decide
  rw [hc]
  have : (u.sum fun _ e => e) ≤ g.totalDegree := le_totalDegree hu
  exact monomial_mul_mem hC u hf (by omega)

/-- Lemma A (absorption). -/
theorem absorb : ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ),
    DegClosed C D →
    ∀ f g : MvPolynomial σ (ZMod 2), f ∈ C → g.totalDegree + f.totalDegree ≤ D → g * f ∈ C :=
  fun _ _ _ hC _ g hf hdeg => absorb_le hC g hf le_rfl le_rfl hdeg

/-- The polynomials `g` with `g * g + g` in the space are closed under finite sums. -/
theorem idem_sum {ι : Type} (s : Finset ι) (h : ι → MvPolynomial σ (ZMod 2))
    (hh : ∀ i ∈ s, h i * h i + h i ∈ C) :
    (∑ i ∈ s, h i) * (∑ i ∈ s, h i) + ∑ i ∈ s, h i ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have e : (h i + ∑ x ∈ s, h x) * (h i + ∑ x ∈ s, h x) + (h i + ∑ x ∈ s, h x)
        = (h i * h i + h i) + ((∑ x ∈ s, h x) * (∑ x ∈ s, h x) + ∑ x ∈ s, h x) := by
      linear_combination char2_add_self (h i * ∑ x ∈ s, h x)
    rw [e]
    exact C.add_mem (hh i (Finset.mem_insert_self i s))
      (ih fun k hk => hh k (Finset.mem_insert_of_mem hk))

/-- An exponent vector of degree at most one is zero or a single variable. -/
theorem exponent_le_one (u : σ →₀ ℕ) (hu : (u.sum fun _ e => e) ≤ 1) :
    u = 0 ∨ ∃ v, u = Finsupp.single v 1 := by
  classical
  by_cases h0 : u = 0
  · exact Or.inl h0
  right
  obtain ⟨v, hv⟩ := Finsupp.support_nonempty_iff.mpr h0
  refine ⟨v, ?_⟩
  have hsum : u v + ∑ x ∈ u.support.erase v, u x ≤ 1 := by
    rw [Finset.add_sum_erase _ _ hv]
    exact hu
  have hv1 : u v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hrest : ∑ x ∈ u.support.erase v, u x = 0 := by omega
  ext x
  by_cases hx : x = v
  · subst hx
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_eq_of_ne hx]
    by_contra hne
    have hmem : x ∈ u.support.erase v :=
      Finset.mem_erase.mpr ⟨hx, Finsupp.mem_support_iff.mpr hne⟩
    exact hne ((Finset.sum_eq_zero_iff.mp hrest) x hmem)

/-- Lemma A' in implicit form. -/
theorem affine_idem' (hC : DegClosed C D) {g : MvPolynomial σ (ZMod 2)}
    (hg : g.totalDegree ≤ 1) : g * g + g ∈ C := by
  have hsum : g = ∑ u ∈ g.support, monomial u (g.coeff u) := g.as_sum
  have key := idem_sum (C := C) g.support (fun u => monomial u (g.coeff u)) (fun u hu => by
    have hc : g.coeff u = 1 := by
      have h0 : g.coeff u ≠ 0 := mem_support_iff.mp hu
      generalize g.coeff u = c at h0
      revert h0; revert c; decide
    rw [hc]
    have hdu : (u.sum fun _ e => e) ≤ 1 := (le_totalDegree hu).trans hg
    rcases exponent_le_one u hdu with rfl | ⟨v, rfl⟩
    · have h1 : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
      rw [h1, one_mul, char2_add_self]
      exact C.zero_mem
    · exact hC.bool v)
  rw [← hsum] at key
  exact key

/-- Lemma A': an affine polynomial is idempotent modulo the closure. -/
theorem affine_idem : ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ),
    DegClosed C D →
    ∀ g : MvPolynomial σ (ZMod 2), g.totalDegree ≤ 1 → g * g + g ∈ C :=
  fun _ _ _ hC _ hg => affine_idem' hC hg

theorem totalDegree_one_add_le {p : MvPolynomial σ (ZMod 2)} (h : p.totalDegree ≤ 1) :
    (1 + p).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans ?_
  rw [totalDegree_one]
  exact max_le (Nat.zero_le _) h

/-- A product of `1 + a u` over a finite set, each `a u` of degree at most one. -/
theorem totalDegree_prod_le {ι : Type} (s : Finset ι) (a : ι → MvPolynomial σ (ZMod 2))
    (ha : ∀ u ∈ s, (a u).totalDegree ≤ 1) : (∏ u ∈ s, (1 + a u)).totalDegree ≤ s.card := by
  have := Helpers.totalDegree_prod_one_add_le s a (e := 1) ha
  omega

/-- Telescoping in a degree-closed space: if every `a u * Q` is in the space, so is
`(∏ u ∈ s, (1 + a u)) * Q + Q`, in budget `s.card + deg Q`. -/
theorem prod_absorb (hC : DegClosed C D) {ι : Type} (s : Finset ι)
    (a : ι → MvPolynomial σ (ZMod 2)) (Q : MvPolynomial σ (ZMod 2)) {dQ : ℕ}
    (hdQ : Q.totalDegree ≤ dQ) (ha : ∀ u ∈ s, a u * Q ∈ C)
    (hdeg : ∀ u ∈ s, (a u).totalDegree ≤ 1) (hB : s.card + dQ ≤ D) :
    (∏ u ∈ s, (1 + a u)) * Q + Q ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, one_mul, char2_add_self]
    exact C.zero_mem
  | insert u s hu ih =>
    rw [Finset.card_insert_of_notMem hu] at hB
    have hdeg' : ∀ v ∈ s, (a v).totalDegree ≤ 1 := fun v hv =>
      hdeg v (Finset.mem_insert_of_mem hv)
    have ih' := ih (fun v hv => ha v (Finset.mem_insert_of_mem hv)) hdeg' (by omega)
    have hd : ((∏ v ∈ s, (1 + a v)) * Q + Q).totalDegree ≤ s.card + dQ := by
      refine (totalDegree_add _ _).trans (max_le ?_ (by omega))
      exact totalDegree_mul_le' (totalDegree_prod_le s a hdeg') hdQ
    have h1 : (1 + a u).totalDegree ≤ 1 :=
      totalDegree_one_add_le (hdeg u (Finset.mem_insert_self u s))
    have h2 := absorb_le hC (1 + a u) ih' h1 hd (by omega)
    have h3 := C.add_mem h2 (ha u (Finset.mem_insert_self u s))
    have e : (∏ v ∈ insert u s, (1 + a v)) * Q + Q
        = (1 + a u) * ((∏ v ∈ s, (1 + a v)) * Q + Q) + a u * Q := by
      rw [Finset.prod_insert hu]
      linear_combination (-1 : MvPolynomial σ (ZMod 2)) * char2_add_self (a u * Q)
    rw [e]
    exact h3

/-- A member of the span of polynomials of degree at most one has degree at most one. -/
theorem totalDegree_span_le {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ 1 := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx

/-- The approximator `∏ j, (1 + qs j)` has degree at most `t`. -/
theorem totalDegree_appr_le {t : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ 1) : (∏ j, (1 + qs j)).totalDegree ≤ t := by
  have := totalDegree_prod_le Finset.univ qs (fun j _ => h j)
  simpa using this

/-- The transfer step in implicit form. -/
theorem transfer' (hC : DegClosed C D) {K t r : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (qs : Fin t → MvPolynomial σ (ZMod 2)) {f R : MvPolynomial σ (ZMod 2)}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) G)
    (hf : f.totalDegree ≤ K) (hR : R.totalDegree ≤ r) (hB : K + t + r ≤ D)
    (hP : (∏ j, (1 + qs j)) * f ∈ C) (hg : ∀ g ∈ G, g * R * f ∈ C) : R * f ∈ C := by
  have hQ : (R * f).totalDegree ≤ r + K := totalDegree_mul_le' hR hf
  have hspan : ∀ q ∈ Submodule.span (ZMod 2) G, q * (R * f) ∈ C := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem g hg' =>
      rw [← mul_assoc]
      exact hg g hg'
    | zero => simp
    | add x y _ _ hx hy =>
      rw [add_mul]
      exact C.add_mem hx hy
    | smul c x _ hx =>
      rcases zmod2_cases c with rfl | rfl
      · simp
      · simpa using hx
  have hdq : ∀ j, (qs j).totalDegree ≤ 1 := fun j => totalDegree_span_le hG (hqs j)
  have h1 := prod_absorb hC Finset.univ qs (R * f) hQ (fun u _ => hspan _ (hqs u))
    (fun u _ => hdq u) (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  have hPd : ((∏ j, (1 + qs j)) * f).totalDegree ≤ t + K :=
    totalDegree_mul_le' (totalDegree_appr_le qs hdq) hf
  have h2 := absorb_le hC R hP hR hPd (by omega)
  have h3 := C.add_mem h1 h2
  have e : (∏ j, (1 + qs j)) * (R * f) + R * f + R * ((∏ j, (1 + qs j)) * f) = R * f := by
    linear_combination char2_add_self ((∏ j, (1 + qs j)) * (R * f))
  rwa [e] at h3

/-- The transfer step: if `P * f` is in the closure for `P = ∏ (1 + qs j)` with every `qs j`
in the span of `G`, and `g * R * f` is in the closure for every `g ∈ G`, then `R * f` is, in
budget `K + t + deg R ≤ D`. -/
theorem transfer : ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t r : ℕ)
    (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
    (f R : MvPolynomial σ (ZMod 2)),
    DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
    K + t + r ≤ D →
    (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C :=
  fun _ _ _ _ _ _ _ qs _ _ hC hG hqs hf hR hB hP hg => transfer' hC qs hG hqs hf hR hB hP hg

end Abstract

section Lines

variable {V : Type} [Fintype V] [DecidableEq V]
  {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D K t : ℕ}
  {f : MvPolynomial V (ZMod 2)}

omit [Fintype V] [DecidableEq V] in
theorem totalDegree_eqImage_le (L : LinClause V) :
    ∀ g ∈ (fun q => eqPoly q) '' (↑L : Set (LinEq V)), g.totalDegree ≤ 1 := by
  rintro _ ⟨q, _, rfl⟩
  exact totalDegree_eqPoly_le q

omit [Fintype V] [DecidableEq V] in
theorem totalDegree_clausePoly_le (A : Clause V) : (clausePoly A).totalDegree ≤ A.card := by
  rw [clausePoly_eq_prod]
  exact totalDegree_prod_le A _ fun l _ => totalDegree_eqPoly_le _

omit [Fintype V] in
/-- The axiom rule: budget `K + t + w`. -/
theorem step_ax (hC : DegClosed C D) (A : Clause V) {w : ℕ} (hA : clausePoly A ∈ C)
    (hw : A.card ≤ w) (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2)
      ((fun q => eqPoly q) '' (↑(linOfClause A) : Set (LinEq V))))
    (hf : f.totalDegree ≤ K) (hB : K + t + w ≤ D)
    (hH : ∀ q ∈ linOfClause A, (∏ j, (1 + qs j)) * eqPoly q * f ∈ C) :
    (∏ j, (1 + qs j)) * f ∈ C := by
  have hdq : ∀ j, (qs j).totalDegree ≤ 1 := fun j =>
    totalDegree_span_le (totalDegree_eqImage_le _) (hqs j)
  have hQ : ((∏ j, (1 + qs j)) * f).totalDegree ≤ t + K :=
    totalDegree_mul_le' (totalDegree_appr_le qs hdq) hf
  have h1 := prod_absorb hC A
    (fun l : Literal V => eqPoly ((({l.1} : Finset V), l.2) : LinEq V))
    ((∏ j, (1 + qs j)) * f) hQ
    (fun l hl => by
      have := hH _ (Finset.mem_image.2 ⟨l, hl, rfl⟩)
      have e : eqPoly ((({l.1} : Finset V), l.2) : LinEq V) * ((∏ j, (1 + qs j)) * f)
          = (∏ j, (1 + qs j)) * eqPoly ((({l.1} : Finset V), l.2) : LinEq V) * f := by ring
      rw [e]
      exact this)
    (fun l _ => totalDegree_eqPoly_le _) (by omega)
  rw [← clausePoly_eq_prod] at h1
  have h2 := absorb_le hC ((∏ j, (1 + qs j)) * f) hA hQ (totalDegree_clausePoly_le A)
    (by omega)
  have h3 := C.add_mem h1 h2
  have e : clausePoly A * ((∏ j, (1 + qs j)) * f) + (∏ j, (1 + qs j)) * f
      + (∏ j, (1 + qs j)) * f * clausePoly A = (∏ j, (1 + qs j)) * f := by
    linear_combination char2_add_self (clausePoly A * ((∏ j, (1 + qs j)) * f))
  rwa [e] at h3

/-- The semantic weakening rule: budget `K + 2 * t` and `K + t + 1`. -/
theorem step_weak (hC : DegClosed C D) (L M : LinClause V)
    (qL qM : Fin t → MvPolynomial V (ZMod 2))
    (hqL : ∀ j, qL j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V))))
    (hqM : ∀ j, qM j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑M : Set (LinEq V))))
    (hf : f.totalDegree ≤ K) (hB1 : K + 2 * t ≤ D) (hB2 : K + t + 1 ≤ D)
    (himp : ∀ a : V → Bool, LinClauseSat a L → LinClauseSat a M)
    (hPL : (∏ j, (1 + qL j)) * f ∈ C)
    (hHM : ∀ q ∈ M, (∏ j, (1 + qM j)) * eqPoly q * f ∈ C) :
    (∏ j, (1 + qM j)) * f ∈ C := by
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t :=
    totalDegree_appr_le qM fun j => totalDegree_span_le (totalDegree_eqImage_le _) (hqM j)
  refine transfer' hC qL (totalDegree_eqImage_le L) hqL hf hdM (by omega) hPL ?_
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨J, hJ, hcase⟩ := lin_alternative q M fun a ha => himp a ⟨q, hq, ha⟩
  have hsum : (∑ d ∈ J, eqPoly d) * (∏ j, (1 + qM j)) * f ∈ C := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Submodule.sum_mem _ fun d hd => ?_
    have e : eqPoly d * (∏ j, (1 + qM j)) * f = (∏ j, (1 + qM j)) * eqPoly d * f := by ring
    rw [e]
    exact hHM d (hJ hd)
  rcases hcase with h1 | h2
  · rw [h1, one_mul] at hsum
    have := absorb_le hC (eqPoly q) hsum (totalDegree_eqPoly_le q)
      (totalDegree_mul_le' hdM hf) (by omega)
    rw [mul_assoc]
    exact this
  · rw [h2] at hsum
    exact hsum

omit [Fintype V] in
/-- One half of the resolution rule: budget `K + 2 * t + 1` and `K + t + 2`. The line `L`
has the equation `q0`, every other equation of `L` is in `M`, and `e'` is the affine form of
the opposite equation, so that `eqPoly q0 * e'` vanishes modulo the closure. -/
theorem step_half (hC : DegClosed C D) (L M : LinClause V) (q0 : LinEq V)
    (e' : MvPolynomial V (ZMod 2)) (qL qM : Fin t → MvPolynomial V (ZMod 2))
    (hqL : ∀ j, qL j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V))))
    (hqM : ∀ j, qM j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑M : Set (LinEq V))))
    (hf : f.totalDegree ≤ K) (hB : K + 2 * t + 2 ≤ D) (he' : e'.totalDegree ≤ 1)
    (hbad : eqPoly q0 * e' * ((∏ j, (1 + qM j)) * f) ∈ C)
    (hsub : ∀ q ∈ L, q ≠ q0 → q ∈ M)
    (hPL : (∏ j, (1 + qL j)) * f ∈ C)
    (hHM : ∀ q ∈ M, (∏ j, (1 + qM j)) * eqPoly q * f ∈ C) :
    e' * (∏ j, (1 + qM j)) * f ∈ C := by
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t :=
    totalDegree_appr_le qM fun j => totalDegree_span_le (totalDegree_eqImage_le _) (hqM j)
  have hdR : (e' * ∏ j, (1 + qM j)).totalDegree ≤ 1 + t := totalDegree_mul_le' he' hdM
  refine transfer' hC qL (totalDegree_eqImage_le L) hqL hf hdR (by omega) hPL ?_
  rintro _ ⟨q, hq, rfl⟩
  by_cases hq0 : q = q0
  · subst hq0
    have e : eqPoly q * (e' * ∏ j, (1 + qM j)) * f
        = eqPoly q * e' * ((∏ j, (1 + qM j)) * f) := by ring
    rw [e]
    exact hbad
  · have hmem := hHM q (hsub q hq hq0)
    have hd : ((∏ j, (1 + qM j)) * eqPoly q * f).totalDegree ≤ t + 1 + K :=
      totalDegree_mul_le' (totalDegree_mul_le' hdM (totalDegree_eqPoly_le q)) hf
    have := absorb_le hC e' hmem he' hd (by omega)
    have e : eqPoly q * (e' * ∏ j, (1 + qM j)) * f
        = e' * ((∏ j, (1 + qM j)) * eqPoly q * f) := by ring
    rw [e]
    exact this

omit [Fintype V] in
/-- The resolution rule: budget `K + 2 * t + 1` and `K + t + 2`. -/
theorem step_res (hC : DegClosed C D) (L1 L2 M : LinClause V)
    (q1 q2 qM : Fin t → MvPolynomial V (ZMod 2))
    (hq1 : ∀ j, q1 j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L1 : Set (LinEq V))))
    (hq2 : ∀ j, q2 j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L2 : Set (LinEq V))))
    (hqM : ∀ j, qM j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑M : Set (LinEq V))))
    (hf : f.totalDegree ≤ K) (hB : K + 2 * t + 2 ≤ D)
    (hres : IsLinResolvent L1 L2 M)
    (hP1 : (∏ j, (1 + q1 j)) * f ∈ C) (hP2 : (∏ j, (1 + q2 j)) * f ∈ C)
    (hHM : ∀ q ∈ M, (∏ j, (1 + qM j)) * eqPoly q * f ∈ C) :
    (∏ j, (1 + qM j)) * f ∈ C := by
  obtain ⟨g, hg1, hg2, rfl⟩ := hres
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t :=
    totalDegree_appr_le qM fun j => totalDegree_span_le (totalDegree_eqImage_le _) (hqM j)
  have hQ : ((∏ j, (1 + qM j)) * f).totalDegree ≤ t + K := totalDegree_mul_le' hdM hf
  have he : eqPoly ((g, false) : LinEq V) = eqPoly ((g, true) : LinEq V) + 1 := by
    simp [eqPoly]
  have hd1 : (eqPoly ((g, true) : LinEq V)).totalDegree ≤ 1 := totalDegree_eqPoly_le _
  have hd0 : (eqPoly ((g, false) : LinEq V)).totalDegree ≤ 1 := totalDegree_eqPoly_le _
  have hidem := affine_idem' hC hd1
  have hdi : (eqPoly ((g, true) : LinEq V) * eqPoly ((g, true) : LinEq V)
      + eqPoly ((g, true) : LinEq V)).totalDegree ≤ 2 :=
    (totalDegree_add _ _).trans (max_le (totalDegree_mul_le' hd1 hd1) (by omega))
  have hbad := absorb_le hC ((∏ j, (1 + qM j)) * f) hidem hQ hdi (by omega)
  have hA := step_half hC L1 _ (g, false) (eqPoly ((g, true) : LinEq V)) q1 qM hq1 hqM hf hB
    hd1
    (by
      have e : eqPoly ((g, false) : LinEq V) * eqPoly ((g, true) : LinEq V)
            * ((∏ j, (1 + qM j)) * f)
          = (∏ j, (1 + qM j)) * f * (eqPoly ((g, true) : LinEq V) * eqPoly ((g, true) : LinEq V)
            + eqPoly ((g, true) : LinEq V)) := by
        rw [he]; ring
      rw [e]
      exact hbad)
    (fun q hq hne => Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hq⟩)) hP1 hHM
  have hB' := step_half hC L2 _ (g, true) (eqPoly ((g, false) : LinEq V)) q2 qM hq2 hqM hf hB
    hd0
    (by
      have e : eqPoly ((g, true) : LinEq V) * eqPoly ((g, false) : LinEq V)
            * ((∏ j, (1 + qM j)) * f)
          = (∏ j, (1 + qM j)) * f * (eqPoly ((g, true) : LinEq V) * eqPoly ((g, true) : LinEq V)
            + eqPoly ((g, true) : LinEq V)) := by
        rw [he]; ring
      rw [e]
      exact hbad)
    (fun q hq hne => Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hq⟩)) hP2 hHM
  have h3 := C.add_mem hA hB'
  have e : eqPoly ((g, true) : LinEq V) * (∏ j, (1 + qM j)) * f
      + eqPoly ((g, false) : LinEq V) * (∏ j, (1 + qM j)) * f = (∏ j, (1 + qM j)) * f := by
    rw [he]
    linear_combination char2_add_self (eqPoly ((g, true) : LinEq V) * (∏ j, (1 + qM j)) * f)
  rwa [e] at h3

end Lines

/-- Proposition 5.1 on our rules (axioms of a CNF of width at most `w`, resolution on a
linear form, SEMANTIC weakening of one line). Budget `K + max (2 * t + 2) (t + w) ≤ D`. -/
theorem simulation : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V))
    (π : List (LinClause V))
    (w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinClause V → Fin t → MvPolynomial V (ZMod 2)),
    (∀ A ∈ F, A.card ≤ w) → IsLinDerivation ((fun A => linOfClause A) '' F) π →
    K + max (2 * t + 2) (t + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V)))) →
    (∀ L ∈ π, ∀ q ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * eqPoly q * f)) →
    ∀ L ∈ π, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * f) := by
  intro V _ _ F π w D K t f qs hw hder hB hf
  have hB1 : K + (2 * t + 2) ≤ D := (Nat.add_le_add_left (le_max_left _ _) K).trans hB
  have hB2 : K + (t + w) ≤ D := (Nat.add_le_add_left (le_max_right _ _) K).trans hB
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure _ _ (by omega) fun v => Or.inl ⟨v, rfl⟩
  have key : ∀ ρ : List (LinClause V), IsLinDerivation ((fun A => linOfClause A) '' F) ρ →
      (∀ L ∈ ρ, ∀ j, qs L j ∈ Submodule.span (ZMod 2)
        ((fun q => eqPoly q) '' (↑L : Set (LinEq V)))) →
      (∀ L ∈ ρ, ∀ q ∈ L, (∏ j, (1 + qs L j)) * eqPoly q * f ∈ pcClosure (cnfSystem F) D) →
      ∀ L ∈ ρ, (∏ j, (1 + qs L j)) * f ∈ pcClosure (cnfSystem F) D := by
    intro ρ hρ
    induction hρ with
    | nil =>
      intro _ _ L hL
      simp at hL
    | @ax ρ L0 _ hL0 ih =>
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
            ((totalDegree_clausePoly_le A).trans (by omega))
        exact step_ax hC A hmem hAw (qs (linOfClause A))
          (hs _ List.mem_cons_self) hf (by omega) (hH _ List.mem_cons_self)
      · exact ih' L hL'
    | @res ρ L1 L2 M _ h1 h2 hres ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact step_res hC L1 L2 L (qs L1) (qs L2) (qs L)
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L2 (List.mem_cons_of_mem _ h2))
          (hs L List.mem_cons_self) hf (by omega) hres (ih' L1 h1) (ih' L2 h2)
          (hH L List.mem_cons_self)
      · exact ih' L hL'
    | @weak ρ L1 M _ h1 himp ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact step_weak hC L1 L (qs L1) (qs L)
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L List.mem_cons_self) hf (by omega)
          (by omega) himp (ih' L1 h1) (hH L List.mem_cons_self)
      · exact ih' L hL'
  intro hs hH
  exact key π hder hs hH

/-- Its consequence for a refutation: the common multiplier is in the closure. -/
theorem simulation_refutation : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V))
    (π : List (LinClause V))
    (w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinClause V → Fin t → MvPolynomial V (ZMod 2)),
    (∀ A ∈ F, A.card ≤ w) → IsLinRefutation F π →
    K + max (2 * t + 2) (t + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V)))) →
    (∀ L ∈ π, ∀ q ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * eqPoly q * f)) →
    PCDerivable (cnfSystem F) D f := by
  intro V _ _ F π w D K t f qs hw href hB hf hs hH
  obtain ⟨hder, hemp⟩ := href
  have h := simulation V F π w D K t f qs hw hder hB hf hs hH ∅ hemp
  have hq : ∀ j, qs ∅ j = 0 := by
    intro j
    have := hs ∅ hemp j
    simpa using this
  simpa [hq] using h

end PEqualNP.ProofComplexity.DegSizeSim
