import PEqualNP.Defs.ProofComplexityBit
import PEqualNP.Defs.ProofComplexityChain
import PEqualNP.ProofComplexity.Helpers.PCToolkit

/-!
# Helpers: from Res(⊕) lines to block products, the rule lemmas

Every linear clause `C` gets a block whose inputs are the affine forms `eqPoly q`, `q ∈ C`,
where `eqPoly q` is `1` exactly at the points that satisfy the equation `q`. The product of
the block then stands for "the clause `C` is false", and the invariant of the simulation is:
the block product of every line of the Res(⊕) derivation is derivable in low degree.

* `pcDerivable_prod_absorb`: if `a u * Q` is derivable for every `u`, then so is
  `(∏ u, (1 + a u)) * Q + Q` (the telescoping identity, in derivation form);
* `block_transfer`: if the product of block `j` is derivable and `g j i * Q` is derivable for
  every input of block `j`, then `Q` is derivable (degree `2 * h + deg Q`);
* `block_weak`, `block_res`, `block_ax`: the three rules of Res(⊕).
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial PEqualNP.ProofComplexity

section Generic

variable {σ : Type}

theorem char2_add_self (x : MvPolynomial σ (ZMod 2)) : x + x = 0 :=
  CharTwo.add_self_eq_zero x

theorem totalDegree_mul_le' {p q : MvPolynomial σ (ZMod 2)} {a b : ℕ}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) : (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)

/-- Multiplication of a derived line by a polynomial, with explicit degree bounds. -/
theorem pcDerivable_mul_le {F : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (hp : PCDerivable F B p) (q : MvPolynomial σ (ZMod 2))
    {dq dp : ℕ} (hq : q.totalDegree ≤ dq) (hpd : p.totalDegree ≤ dp) (hB : B ≤ B')
    (hd : dq + dp ≤ B') : PCDerivable F B' (q * p) :=
  pcDerivable_mono (pcDerivable_mul_left hp q) (max_le hB (by omega)) subset_rfl

theorem totalDegree_prod_one_add_le {ι : Type} (s : Finset ι)
    (a : ι → MvPolynomial σ (ZMod 2)) {e : ℕ} (ha : ∀ u ∈ s, (a u).totalDegree ≤ e) :
    (∏ u ∈ s, (1 + a u)).totalDegree ≤ e * s.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ u ∈ s, (1 + a u).totalDegree ≤ ∑ _u ∈ s, e := by
        refine Finset.sum_le_sum fun u hu => ?_
        refine (totalDegree_add _ _).trans ?_
        rw [totalDegree_one]
        exact max_le (Nat.zero_le _) (ha u hu)
    _ = e * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The telescoping identity in derivation form: if every `a u * Q` is derivable, then so is
`(∏ u ∈ s, (1 + a u)) * Q + Q`, in degree `e * s.card + deg Q` where `e` bounds the degrees
of the `a u`. -/
theorem pcDerivable_prod_absorb {F : Set (MvPolynomial σ (ZMod 2))} {B e dQ : ℕ} {ι : Type}
    [DecidableEq ι] (s : Finset ι) (a : ι → MvPolynomial σ (ZMod 2))
    (Q : MvPolynomial σ (ZMod 2)) (hdQ : Q.totalDegree ≤ dQ)
    (ha : ∀ u ∈ s, PCDerivable F B (a u * Q))
    (hdeg : ∀ u ∈ s, (a u).totalDegree ≤ e)
    (hB : e * s.card + dQ ≤ B) :
    PCDerivable F B ((∏ u ∈ s, (1 + a u)) * Q + Q) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, one_mul, char2_add_self]
    exact .zero
  | insert u s hu ih =>
    rw [Finset.card_insert_of_notMem hu, Nat.mul_succ] at hB
    have h1 := ih (fun v hv => ha v (Finset.mem_insert_of_mem hv))
      (fun v hv => hdeg v (Finset.mem_insert_of_mem hv)) (by omega)
    have h2 := pcDerivable_mul_le (ha u (Finset.mem_insert_self u s)) (∏ v ∈ s, (1 + a v))
      (totalDegree_prod_one_add_le s a fun v hv => hdeg v (Finset.mem_insert_of_mem hv))
      (totalDegree_mul_le' (hdeg u (Finset.mem_insert_self u s)) hdQ) le_rfl (by omega)
    have h3 := h1.add h2
    have hEq : (∏ v ∈ insert u s, (1 + a v)) * Q + Q
        = (∏ v ∈ s, (1 + a v)) * Q + Q + (∏ v ∈ s, (1 + a v)) * (a u * Q) := by
      rw [Finset.prod_insert hu]
      ring
    rw [hEq]
    exact h3

/-- In characteristic two, `x * x + x` is additive on finite sums. -/
theorem sum_mul_self_add (ι : Type) [DecidableEq ι] (s : Finset ι)
    (x : ι → MvPolynomial σ (ZMod 2)) :
    (∑ v ∈ s, x v) * (∑ v ∈ s, x v) + ∑ v ∈ s, x v = ∑ v ∈ s, (x v * x v + x v) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert u s hu ih =>
    rw [Finset.sum_insert hu, Finset.sum_insert hu, ← ih]
    linear_combination char2_add_self (x u * ∑ v ∈ s, x v)

end Generic

section Blocks

variable {V : Type} {F : Set (MvPolynomial V (ZMod 2))} {h M W : ℕ}
  {g : Fin M → Fin W → MvPolynomial V (ZMod 2)}

theorem totalDegree_rename_inl_le (p : MvPolynomial V (ZMod 2)) {d : ℕ}
    (hp : p.totalDegree ≤ d) :
    (rename (Sum.inl : V → BlockVar V h M W) p).totalDegree ≤ d :=
  (totalDegree_rename_le _ _).trans hp

theorem totalDegree_blockFactor_le (j : Fin M) (u : Fin h)
    (hg : ∀ i, (g j i).totalDegree ≤ 1) :
    (∑ i : Fin W, X (Sum.inr (j, u, i)) * rename (Sum.inl : V → BlockVar V h M W)
      (g j i)).totalDegree ≤ 2 := by
  refine totalDegree_finsetSum_le fun i _ => ?_
  have := totalDegree_mul_le' (a := 1) (b := 1)
    (p := (X (Sum.inr (j, u, i)) : MvPolynomial (BlockVar V h M W) (ZMod 2)))
    (q := rename Sum.inl (g j i)) (totalDegree_X _).le (totalDegree_rename_inl_le _ (hg i))
  exact this

theorem totalDegree_blockProduct_le (j : Fin M) (hg : ∀ i, (g j i).totalDegree ≤ 1) :
    (blockProduct h M W g j).totalDegree ≤ 2 * h := by
  have := totalDegree_prod_one_add_le (Finset.univ : Finset (Fin h))
    (fun u => ∑ i : Fin W, X (Sum.inr (j, u, i)) * rename (Sum.inl : V → BlockVar V h M W)
      (g j i)) (e := 2) (fun u _ => totalDegree_blockFactor_le j u hg)
  simpa [blockProduct] using this

/-- The transfer lemma. If the product of block `j` is derivable, and `g j i * Q` is
derivable for every input `g j i` of the block, then `Q` is derivable. The degree needed is
`2 * h + deg Q`. -/
theorem block_transfer (j : Fin M) (hg : ∀ i, (g j i).totalDegree ≤ 1) {B dQ : ℕ}
    (Q : MvPolynomial (BlockVar V h M W) (ZMod 2)) (hdQ : Q.totalDegree ≤ dQ)
    (hB : 2 * h + dQ ≤ B)
    (hP : PCDerivable (blockSystem F h M W g) B (blockProduct h M W g j))
    (hQ : ∀ i, PCDerivable (blockSystem F h M W g) B (rename Sum.inl (g j i) * Q)) :
    PCDerivable (blockSystem F h M W g) B Q := by
  classical
  have ha : ∀ u ∈ (Finset.univ : Finset (Fin h)), PCDerivable (blockSystem F h M W g) B
      ((∑ i : Fin W, X (Sum.inr (j, u, i)) * rename (Sum.inl : V → BlockVar V h M W)
        (g j i)) * Q) := by
    intro u _
    have hh : 1 ≤ h := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
    rw [Finset.sum_mul]
    refine pcDerivable_sum _ _ fun i _ => ?_
    rw [mul_assoc]
    exact pcDerivable_mul_le (hQ i) _ (totalDegree_X _).le
      (totalDegree_mul_le' (totalDegree_rename_inl_le _ (hg i)) hdQ) le_rfl (by omega)
  have h1 := pcDerivable_prod_absorb (Finset.univ : Finset (Fin h)) _ Q hdQ ha
    (fun u _ => totalDegree_blockFactor_le j u hg) (by simpa using hB)
  have h2 := pcDerivable_mul_le hP Q hdQ (totalDegree_blockProduct_le j hg) le_rfl (by omega)
  have h3 := h1.add h2
  have hEq : (∏ u : Fin h, (1 + ∑ i : Fin W, X (Sum.inr (j, u, i)) *
      rename (Sum.inl : V → BlockVar V h M W) (g j i))) * Q + Q
      + Q * blockProduct h M W g j = Q := by
    unfold blockProduct
    linear_combination char2_add_self ((∏ u : Fin h, (1 + ∑ i : Fin W, X (Sum.inr (j, u, i)) *
      rename (Sum.inl : V → BlockVar V h M W) (g j i))) * Q)
  rw [hEq] at h3
  exact h3

end Blocks

section Clauses

variable {V : Type} [DecidableEq V]

/-- The affine form of a linear equation: at a Boolean point it is `1` exactly when the
equation holds. -/
noncomputable def eqPoly (q : LinEq V) : MvPolynomial V (ZMod 2) :=
  ∑ v ∈ q.1, X v + C (if q.2 = true then 0 else 1)

omit [DecidableEq V] in
theorem totalDegree_eqPoly_le (q : LinEq V) : (eqPoly q).totalDegree ≤ 1 := by
  unfold eqPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact totalDegree_finsetSum_le fun v _ => (totalDegree_X v).le
  · rw [totalDegree_C]
    exact Nat.zero_le _

/-- The inputs of the blocks of a family of linear clauses: block `j` has the affine form of
every equation of the clause `cl j`, and zero inputs elsewhere. -/
noncomputable def clauseInputs {M W : ℕ} (e : Fin W → LinEq V) (cl : Fin M → LinClause V) :
    Fin M → Fin W → MvPolynomial V (ZMod 2) :=
  fun j i => if e i ∈ cl j then eqPoly (e i) else 0

theorem totalDegree_clauseInputs_le {M W : ℕ} (e : Fin W → LinEq V)
    (cl : Fin M → LinClause V) (j : Fin M) (i : Fin W) :
    (clauseInputs e cl j i).totalDegree ≤ 1 := by
  unfold clauseInputs
  split_ifs
  · exact totalDegree_eqPoly_le _
  · simp

variable {F : Set (MvPolynomial V (ZMod 2))} {h M W : ℕ} {e : Fin W → LinEq V}
  {cl : Fin M → LinClause V}

/-- The companion of an equation of the clause of block `j` is derivable. -/
theorem block_companion (he : Function.Surjective e) (j : Fin M) {q : LinEq V}
    (hq : q ∈ cl j) {B : ℕ} (hB : 2 * h + 1 ≤ B) :
    PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (rename Sum.inl (eqPoly q) * blockProduct h M W (clauseInputs e cl) j) := by
  obtain ⟨i, rfl⟩ := he q
  have hgi : clauseInputs e cl j i = eqPoly (e i) := by simp [clauseInputs, hq]
  rw [← hgi]
  refine .ax (Or.inr (Or.inr ⟨j, i, rfl⟩)) ?_
  have := totalDegree_mul_le'
    (totalDegree_rename_inl_le (h := h) (M := M) (W := W) _
      (totalDegree_clauseInputs_le e cl j i))
    (totalDegree_blockProduct_le (h := h) j (totalDegree_clauseInputs_le e cl j))
  omega

/-- The transfer lemma for clause blocks: it is enough to treat the equations of the
clause. -/
theorem clause_transfer (j : Fin M) {B dQ : ℕ}
    (Q : MvPolynomial (BlockVar V h M W) (ZMod 2)) (hdQ : Q.totalDegree ≤ dQ)
    (hB : 2 * h + dQ ≤ B)
    (hP : PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) j))
    (hQ : ∀ q ∈ cl j, PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (rename Sum.inl (eqPoly q) * Q)) :
    PCDerivable (blockSystem F h M W (clauseInputs e cl)) B Q := by
  refine block_transfer j (totalDegree_clauseInputs_le e cl j) Q hdQ hB hP fun i => ?_
  unfold clauseInputs
  split_ifs with hi
  · exact hQ _ hi
  · rw [map_zero, zero_mul]
    exact .zero

/-- Semantic weakening, given the linear algebra: every equation `q` of the premise has a
set `J` of equations of the conclusion whose affine forms sum to `1` or to the form of
`q`. -/
theorem block_weak (he : Function.Surjective e) (jC jD : Fin M) {B : ℕ}
    (hB : 4 * h + 1 ≤ B) (hh : 1 ≤ h)
    (halt : ∀ q ∈ cl jC, ∃ J : Finset (LinEq V), J ⊆ cl jD ∧
      (∑ d ∈ J, eqPoly d = 1 ∨ ∑ d ∈ J, eqPoly d = eqPoly q))
    (hP : PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) jC)) :
    PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) jD) := by
  have hdP := totalDegree_blockProduct_le (h := h) jD (totalDegree_clauseInputs_le e cl jD)
  refine clause_transfer jC _ hdP (by omega) hP fun q hq => ?_
  obtain ⟨J, hJ, hsum⟩ := halt q hq
  have hcomp : ∀ d ∈ J, PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (rename Sum.inl (eqPoly d) * blockProduct h M W (clauseInputs e cl) jD) :=
    fun d hd => block_companion he jD (hJ hd) (by omega)
  rcases hsum with h1 | h1
  · have hEq : rename (Sum.inl : V → BlockVar V h M W) (eqPoly q)
          * blockProduct h M W (clauseInputs e cl) jD
        = ∑ d ∈ J, rename Sum.inl (eqPoly q) *
          (rename Sum.inl (eqPoly d) * blockProduct h M W (clauseInputs e cl) jD) := by
      have := congrArg (rename (Sum.inl : V → BlockVar V h M W)) h1
      rw [map_sum, map_one] at this
      rw [← Finset.mul_sum, ← Finset.sum_mul, this, one_mul]
    rw [hEq]
    refine pcDerivable_sum _ _ fun d hd => ?_
    exact pcDerivable_mul_le (hcomp d hd) _
      (totalDegree_rename_inl_le _ (totalDegree_eqPoly_le q))
      (totalDegree_mul_le' (totalDegree_rename_inl_le _ (totalDegree_eqPoly_le d)) hdP)
      le_rfl (by omega)
  · have hEq : rename (Sum.inl : V → BlockVar V h M W) (eqPoly q)
          * blockProduct h M W (clauseInputs e cl) jD
        = ∑ d ∈ J,
          (rename Sum.inl (eqPoly d) * blockProduct h M W (clauseInputs e cl) jD) := by
      rw [← h1, map_sum, Finset.sum_mul]
    rw [hEq]
    exact pcDerivable_sum _ _ hcomp

/-- The Boolean axioms of the old variables give `u * u + u` for the affine form `u` of a
linear equation, in degree `2`. -/
theorem block_bool (hbool : ∀ v : V, X v * X v + X v ∈ F) (q : LinEq V) {B : ℕ}
    (hB : 2 ≤ B) :
    PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (rename Sum.inl (eqPoly q) * rename Sum.inl (eqPoly q) + rename Sum.inl (eqPoly q)) := by
  have hc : ∀ c : ZMod 2, c * c + c = 0 := by decide
  have hEq : rename (Sum.inl : V → BlockVar V h M W) (eqPoly q) * rename Sum.inl (eqPoly q)
        + rename Sum.inl (eqPoly q)
      = ∑ v ∈ q.1, (X (Sum.inl v) * X (Sum.inl v) + X (Sum.inl v)) := by
    rw [← sum_mul_self_add]
    simp only [eqPoly, map_add, map_sum, rename_X, rename_C]
    have hC : (C (if q.2 = true then (0 : ZMod 2) else 1) :
        MvPolynomial (BlockVar V h M W) (ZMod 2)) * C (if q.2 = true then 0 else 1)
        + C (if q.2 = true then 0 else 1) = 0 := by
      rw [← C_mul, ← C_add, hc, C_0]
    linear_combination hC + char2_add_self ((∑ v ∈ q.1, X (Sum.inl v)) *
      (C (if q.2 = true then (0 : ZMod 2) else 1) : MvPolynomial (BlockVar V h M W) (ZMod 2)))
  rw [hEq]
  refine pcDerivable_sum _ _ fun v _ => ?_
  refine .ax (Or.inl ⟨_, hbool v, by simp⟩) ?_
  refine ((totalDegree_add _ _).trans (max_le ?_ ?_)).trans hB
  · exact totalDegree_mul_le' (totalDegree_X _).le (totalDegree_X _).le
  · exact (totalDegree_X _).le.trans (by omega)

/-- The resolution rule of Res(⊕) on a linear form `f`. -/
theorem block_res (he : Function.Surjective e) (hbool : ∀ v : V, X v * X v + X v ∈ F)
    (jC jD jR : Fin M) {B : ℕ} (hB : 4 * h + 1 ≤ B) (hh : 1 ≤ h)
    (hres : IsLinResolvent (cl jC) (cl jD) (cl jR))
    (hPC : PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) jC))
    (hPD : PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) jD)) :
    PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) jR) := by
  obtain ⟨f, hfC, hfD, hR⟩ := hres
  have hdP := totalDegree_blockProduct_le (h := h) jR (totalDegree_clauseInputs_le e cl jR)
  have hdu := totalDegree_rename_inl_le (h := h) (M := M) (W := W) _
    (totalDegree_eqPoly_le (f, true))
  have hu1 : rename (Sum.inl : V → BlockVar V h M W) (eqPoly (f, false))
      = rename Sum.inl (eqPoly (f, true)) + 1 := by
    simp [eqPoly]
  -- first: `u * P_R`, where `u` is the affine form of `f = 1`
  have hstep1 : PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (rename Sum.inl (eqPoly (f, true)) * blockProduct h M W (clauseInputs e cl) jR) := by
    refine clause_transfer jC _ (totalDegree_mul_le' hdu hdP) (by omega) hPC fun q hq => ?_
    by_cases hqf : q = (f, false)
    · subst hqf
      have hb := block_bool (F := F) (h := h) (M := M) (W := W) (e := e) (cl := cl) hbool
        (f, true) (B := B) (by omega)
      have hm := pcDerivable_mul_le hb (blockProduct h M W (clauseInputs e cl) jR) hdP
        (dp := 2) ((totalDegree_add _ _).trans (max_le
          (totalDegree_mul_le' hdu hdu) (hdu.trans (by omega)))) le_rfl (by omega)
      rw [hu1]
      have hEq : (rename (Sum.inl : V → BlockVar V h M W) (eqPoly (f, true)) + 1) *
          (rename Sum.inl (eqPoly (f, true)) * blockProduct h M W (clauseInputs e cl) jR)
          = blockProduct h M W (clauseInputs e cl) jR *
            (rename Sum.inl (eqPoly (f, true)) * rename Sum.inl (eqPoly (f, true))
              + rename Sum.inl (eqPoly (f, true))) := by ring
      rw [hEq]
      exact hm
    · have hqR : q ∈ cl jR := by
        rw [hR]
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hqf, hq⟩)
      have hc := block_companion (F := F) (h := h) he jR hqR (B := B) (by omega)
      have hm := pcDerivable_mul_le hc (rename Sum.inl (eqPoly (f, true))) hdu
        (totalDegree_mul_le' (totalDegree_rename_inl_le _ (totalDegree_eqPoly_le q)) hdP)
        le_rfl (by omega)
      have hEq : rename (Sum.inl : V → BlockVar V h M W) (eqPoly q) *
          (rename Sum.inl (eqPoly (f, true)) * blockProduct h M W (clauseInputs e cl) jR)
          = rename Sum.inl (eqPoly (f, true)) *
            (rename Sum.inl (eqPoly q) * blockProduct h M W (clauseInputs e cl) jR) := by
        ring
      rw [hEq]
      exact hm
  -- second: `P_R`
  refine clause_transfer jD _ hdP (by omega) hPD fun q hq => ?_
  by_cases hqf : q = (f, true)
  · subst hqf
    exact hstep1
  · have hqR : q ∈ cl jR := by
      rw [hR]
      exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hqf, hq⟩)
    exact block_companion he jR hqR (by omega)

end Clauses

section Axioms

variable {m l h M W : ℕ} {e : Fin W → LinEq (Fin m × Fin l)}
  {cl : Fin M → LinClause (Fin m × Fin l)}

/-- An axiom of the bit pigeonhole formula: its block product comes from the pair axiom of
the polynomial system, in degree `2 * h + l`. -/
theorem block_ax (he : Function.Surjective e) (j : Fin M) {B : ℕ}
    (hB1 : 2 * h + l ≤ B) (hB2 : 2 * h + 1 ≤ B)
    (hax : cl j ∈ (fun C => linOfClause C) '' BPHP m l) :
    PCDerivable (blockSystem (bitPHPSystem m l) h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) j) := by
  classical
  obtain ⟨A, ⟨i, i', α, hii, rfl⟩, hA⟩ := hax
  have hdP := totalDegree_blockProduct_le (h := h) j (totalDegree_clauseInputs_le e cl j)
  have hmem1 : ∀ t : Fin l, (({(i, t)} : Finset (Fin m × Fin l)), !α t) ∈ cl j := by
    intro t
    rw [← hA]
    simp only [linOfClause, Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and]
    exact ⟨((i, t), !α t), Or.inl ⟨t, rfl⟩, rfl⟩
  have hmem2 : ∀ t : Fin l, (({(i', t)} : Finset (Fin m × Fin l)), !α t) ∈ cl j := by
    intro t
    rw [← hA]
    simp only [linOfClause, Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and]
    exact ⟨((i', t), !α t), Or.inr ⟨t, rfl⟩, rfl⟩
  set S := blockSystem (bitPHPSystem m l) h M W (clauseInputs e cl) with hS
  set P := blockProduct h M W (clauseInputs e cl) j with hPdef
  let a : Fin l → MvPolynomial (BlockVar (Fin m × Fin l) h M W) (ZMod 2) :=
    fun t => X (Sum.inl (i, t)) + X (Sum.inl (i', t))
  have hda : ∀ t ∈ (Finset.univ : Finset (Fin l)), (a t).totalDegree ≤ 1 := fun t _ =>
    (totalDegree_add _ _).trans (max_le (totalDegree_X _).le (totalDegree_X _).le)
  have ha : ∀ t ∈ (Finset.univ : Finset (Fin l)), PCDerivable S B (a t * P) := by
    intro t _
    have h1 := block_companion (F := bitPHPSystem m l) (h := h) he j (hmem1 t) (B := B) hB2
    have h2 := block_companion (F := bitPHPSystem m l) (h := h) he j (hmem2 t) (B := B) hB2
    have h3 := h1.add h2
    have hEq : rename (Sum.inl : _ → BlockVar (Fin m × Fin l) h M W)
          (eqPoly (({(i, t)} : Finset (Fin m × Fin l)), !α t)) * P
        + rename Sum.inl (eqPoly (({(i', t)} : Finset (Fin m × Fin l)), !α t)) * P
        = a t * P := by
      simp only [eqPoly, Finset.sum_singleton, map_add, rename_X, rename_C, a]
      linear_combination char2_add_self
        ((C (if (!α t) = true then (0 : ZMod 2) else 1) :
          MvPolynomial (BlockVar (Fin m × Fin l) h M W) (ZMod 2)) * P)
    rw [← hEq]
    exact h3
  have h1 := pcDerivable_prod_absorb (Finset.univ : Finset (Fin l)) a P hdP ha hda
    (by simpa using (by omega : 1 * l + 2 * h ≤ B))
  have hE : PCDerivable S B (∏ t : Fin l, (1 + a t)) := by
    refine .ax (Or.inl ⟨_, Or.inr ⟨i, i', hii, rfl⟩, ?_⟩) ?_
    · simp [a, add_assoc]
    · have := totalDegree_prod_one_add_le (Finset.univ : Finset (Fin l)) a hda
      simp only [Finset.card_univ, Fintype.card_fin, one_mul] at this
      omega
  have h2 := pcDerivable_mul_le hE P hdP
    (by simpa using totalDegree_prod_one_add_le (Finset.univ : Finset (Fin l)) a hda)
    le_rfl (by omega)
  have h3 := h1.add h2
  have hEq : (∏ t : Fin l, (1 + a t)) * P + P + P * ∏ t : Fin l, (1 + a t) = P := by
    linear_combination char2_add_self ((∏ t : Fin l, (1 + a t)) * P)
  rw [hEq] at h3
  exact h3

end Axioms

end PEqualNP.ProofComplexity.Helpers
