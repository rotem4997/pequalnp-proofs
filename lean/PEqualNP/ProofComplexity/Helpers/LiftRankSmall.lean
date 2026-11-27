import PEqualNP.ProofComplexity.Helpers.LiftRankPlan
import PEqualNP.ProofComplexity.Helpers.BoolVanish
import PEqualNP.ProofComplexity.Helpers.DegSizeSim

/-!
# Small parts of L-pcx-065

Proofs of four interface statements of `Helpers.LiftRankPlan`:

* `rename_rank`: pulling a line back along a renaming keeps its rank (the indicator vectors
  are moved by the linear equivalence of precomposition with the renaming);
* `rename_pc`: renaming the variables keeps polynomial calculus refutations;
* `dependency`: more equations than variables give a nonempty set of supports that cancel;
* `formula_pc`: a set of equations whose supports cancel and whose right sides sum to one
  gives a polynomial calculus refutation of the lifted formula in degree `4 * b`.
-/

namespace PEqualNP.ProofComplexity.LiftRank

open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.ThreeCnfFamily

/-! ### Renaming keeps the rank -/

theorem rename_rank : StmtRenameRank := by
  intro V W _ _ e L
  let Φ : (W → ZMod 2) ≃ₗ[ZMod 2] (V → ZMod 2) := LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e
  have hset : ((fun q : LinEq V => (fun v : V => if v ∈ q.1 then (1 : ZMod 2) else 0)) ''
      ((backLin e L : LinClause V) : Set (LinEq V))) =
      (Φ : (W → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2)) ''
        ((fun q : LinEq W => (fun w : W => if w ∈ q.1 then (1 : ZMod 2) else 0)) ''
          ((L : LinClause W) : Set (LinEq W))) := by
    ext f
    simp only [backLin, Finset.coe_image, Set.image_image, Set.mem_image, Finset.mem_coe]
    refine exists_congr fun q => and_congr_right fun _ => ?_
    have : (fun v : V => if v ∈ (back e q).1 then (1 : ZMod 2) else 0) =
        Φ (fun w : W => if w ∈ q.1 then (1 : ZMod 2) else 0) := by
      funext v
      simp [Φ, back, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    rw [this]
    rfl
  unfold linRank
  rw [hset, ← Submodule.map_span, LinearEquiv.finrank_map_eq]

/-! ### Renaming keeps polynomial calculus refutations -/

theorem rename_clausePoly {V W : Type} [DecidableEq W] (e : V ≃ W) (C : Clause V) :
    MvPolynomial.rename e (clausePoly C) = clausePoly (ren e C) := by
  unfold clausePoly ren
  rw [map_prod, Finset.prod_image]
  · refine Finset.prod_congr rfl fun l _ => ?_
    split_ifs <;> simp
  · intro l _ l' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (e.injective h.1) h.2

theorem rename_pc : StmtRenamePC := by
  intro V W _ _ e F d h
  have hr := Helpers.pcDerivable_replay (F := cnfSystem F) (G := cnfSystem (ren e '' F))
    (T := 1) (D := d) (s := 0) (fun v => MvPolynomial.X (e v)) (fun j => by simp)
    1 (by simp) ?_ h
  · simpa [PCRefutable] using hr
  · intro a ha hdeg
    have hb : MvPolynomial.bind₁ (fun v => (MvPolynomial.X (e v) : MvPolynomial W (ZMod 2))) a
        = MvPolynomial.rename e a := by
      have := MvPolynomial.bind₁_rename (R := ZMod 2) MvPolynomial.X e a
      rw [MvPolynomial.bind₁_X_left] at this
      exact this.symm
    rw [one_mul, hb, one_mul, add_zero]
    have hdeg' := (MvPolynomial.totalDegree_rename_le e a).trans hdeg
    refine .ax ?_ hdeg'
    rcases ha with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
    · exact Or.inl ⟨e v, by simp⟩
    · exact Or.inr ⟨ren e C, ⟨C, hC, rfl⟩, rename_clausePoly e C⟩

/-! ### More equations than variables -/

theorem dependency : StmtDependency := by
  classical
  intro n G
  let v : Fin (n + 1) → (Fin n → ZMod 2) := fun i j => if j ∈ G i then 1 else 0
  have hli : ¬ LinearIndependent (ZMod 2) v := by
    intro h
    have := h.fintype_card_le_finrank
    simp at this
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hli
  have hg1 : ∀ i, g i ≠ 0 → g i = 1 := by
    intro i
    generalize g i = z
    revert z
    decide
  refine ⟨Finset.univ.filter (fun i => g i ≠ 0), ⟨i₀, by simp [hi₀]⟩, fun j => ?_⟩
  have hj := congrFun hg j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at hj
  rw [← ZMod.natCast_eq_zero_iff_even, Finset.filter_filter, Finset.natCast_card_filter]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hj
  by_cases h0 : g i = 0
  · simp [h0]
  · simp [h0, hg1 i h0]

/-! ### The lifted formula has a refutation of low degree -/

theorem z2_lit : ∀ (b : Bool) (z : ZMod 2),
    (if b = true then 1 + z else z) = if decide (z = 1) = b then 0 else 1 := by decide

open MvPolynomial Classical in
/-- The polynomial of a clause at a point: `0` when the Boolean reading of the point
satisfies the clause, `1` otherwise. -/
theorem eval_clausePoly {σ : Type} (x : σ → ZMod 2) (C : Clause σ) :
    eval x (clausePoly C) = if ClauseSat (fun v => decide (x v = 1)) C then 0 else 1 := by
  unfold clausePoly
  rw [map_prod]
  have hf : ∀ l ∈ C, eval x (if l.2 = true then 1 + X l.1 else X l.1) =
      if decide (x l.1 = 1) = l.2 then 0 else 1 := by
    intro l _
    rw [apply_ite (eval x), map_add, map_one, eval_X]
    exact z2_lit l.2 (x l.1)
  rw [Finset.prod_congr rfl hf]
  by_cases h : ClauseSat (fun v => decide (x v = 1)) C
  · rw [if_pos h]
    obtain ⟨l, hl, hs⟩ := h
    exact Finset.prod_eq_zero hl (if_pos hs)
  · rw [if_neg h]
    exact Finset.prod_eq_one fun l hl => if_neg fun hs => h ⟨l, hl, hs⟩

open Classical in
/-- An assignment falsifies exactly one clause of a lifted equation it violates, and none of
one it satisfies. -/
theorem count_falsified {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (i : Fin m)
    (T : Finset (Clause (Fin N × Fin 4))) (hT : ∀ C, C ∈ T ↔ C ∈ liftEq G c i)
    (a : Fin N × Fin 4 → Bool) :
    (∑ C ∈ T, if ClauseSat a C then (0 : ZMod 2) else 1) = if EqSat G c a i then 0 else 1 := by
  by_cases hs : EqSat G c a i
  · rw [if_pos hs]
    refine Finset.sum_eq_zero fun C hC => if_pos ?_
    exact (formula_sem m N G c a i).2 hs C ((hT C).1 hC)
  · rw [if_neg hs]
    rw [Finset.sum_eq_single_of_mem (blockClause G i a) ((hT _).2 ⟨a, hs, rfl⟩)]
    · refine if_neg ?_
      rintro ⟨l, hl, hal⟩
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hl
      simp at hal
    · intro C hC hne
      refine if_pos ?_
      obtain ⟨α, -, rfl⟩ := (hT C).1 hC
      by_contra hn
      apply hne
      unfold blockClause
      refine Finset.image_congr fun v hv => ?_
      have hav : α v = a v := by
        by_contra h'
        refine hn ⟨(v, !α v), Finset.mem_image_of_mem _ hv, ?_⟩
        revert h'
        cases α v <;> cases a v <;> simp
      simp [hav]

theorem parity_key : ∀ (k : ℕ) (t : Bool),
    (if (Odd k ↔ t = true) then (0 : ZMod 2) else 1) = (k : ZMod 2) + if t = true then 1 else 0 := by
  intro k t
  rcases Nat.even_or_odd k with h | h
  · have h' := Nat.not_odd_iff_even.mpr h
    rw [(ZMod.natCast_eq_zero_iff_even).mpr h]
    cases t <;> simp [h']
  · rw [(ZMod.natCast_eq_one_iff_odd).mpr h]
    cases t <;> simp [h]
    decide

open Classical in
/-- On a set of equations whose supports cancel and whose right sides sum to one, every
assignment violates an odd number of lifted equations. -/
theorem odd_violated {m N : ℕ} (G : BipGraph m N) (c : Fin m → Bool) (S : Finset (Fin m))
    (hS : ∀ j : Fin N, Even (S.filter (fun i => j ∈ G i)).card)
    (hodd : Odd (S.filter (fun i => c i = true)).card) (a : Fin N × Fin 4 → Bool) :
    (∑ i ∈ S, if EqSat G c a i then (0 : ZMod 2) else 1) = 1 := by
  classical
  have h1 : ∀ i ∈ S, (if EqSat G c a i then (0 : ZMod 2) else 1) =
      (∑ j ∈ G i, if gval a j = true then (1 : ZMod 2) else 0) + if c i = true then 1 else 0 := by
    intro i _
    rw [← Finset.natCast_card_filter]
    have := parity_key ((G i).filter (fun j => gval a j = true)).card (c i)
    convert this using 2
    rfl
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_boole,
    (ZMod.natCast_eq_one_iff_odd).mpr hodd]
  have h2 : (∑ i ∈ S, ∑ j ∈ G i, if gval a j = true then (1 : ZMod 2) else 0) =
      ∑ j : Fin N, ∑ i ∈ S.filter (fun i => j ∈ G i),
        if gval a j = true then (1 : ZMod 2) else 0 :=
    Finset.sum_comm' (fun i j => by simp [and_comm])
  rw [h2, Finset.sum_eq_zero, zero_add]
  intro j _
  rw [Finset.sum_const, nsmul_eq_mul, (ZMod.natCast_eq_zero_iff_even).mpr (hS j), zero_mul]

open MvPolynomial in
theorem formula_pc : StmtFormulaPC := by
  classical
  intro m N G c b hb S hS hodd
  have hT : ∀ i : Fin m, ∃ T : Finset (Clause (Fin N × Fin 4)),
      ∀ C, C ∈ T ↔ C ∈ liftEq G c i :=
    fun i => ⟨(Set.toFinite (liftEq G c i)).toFinset, fun C => Set.Finite.mem_toFinset _⟩
  choose T hT using hT
  have hdegC : ∀ i, ∀ C ∈ T i, (clausePoly C).totalDegree ≤ 4 * b := fun i C hC =>
    (DegSizeSim.totalDegree_clausePoly_le C).trans
      (formula_width m N G c b hb C ⟨i, (hT i C).1 hC⟩)
  have hax : ∀ i, ∀ C ∈ T i, PCDerivable (cnfSystem (liftSys G c)) (4 * b) (clausePoly C) :=
    fun i C hC => .ax (Or.inr ⟨C, ⟨i, (hT i C).1 hC⟩, rfl⟩) (hdegC i C hC)
  obtain ⟨P, hP⟩ : ∃ P : MvPolynomial (Fin N × Fin 4) (ZMod 2),
      P = ∑ i ∈ S, ∑ C ∈ T i, clausePoly C := ⟨_, rfl⟩
  have hPd : PCDerivable (cnfSystem (liftSys G c)) (4 * b) P := by
    rw [hP]
    exact Helpers.pcDerivable_sum S _ fun i _ => Helpers.pcDerivable_sum _ _ (hax i)
  have hdegP : P.totalDegree ≤ 4 * b := by
    rw [hP]
    exact totalDegree_finsetSum_le fun i _ => totalDegree_finsetSum_le (hdegC i)
  have hV : PCDerivable (cnfSystem (liftSys G c)) (4 * b) (1 + P) := by
    refine Helpers.BoolVanish.vanish_derivable _ _ _ _ (fun v => Or.inl ⟨v, rfl⟩)
      ((totalDegree_add _ _).trans (max_le (by simp) hdegP)) (fun x => ?_)
    rw [map_add, map_one, hP, map_sum]
    have h3 : ∀ i ∈ S, eval x (∑ C ∈ T i, clausePoly C) =
        if EqSat G c (fun v => decide (x v = 1)) i then 0 else 1 := by
      intro i _
      rw [map_sum, ← count_falsified G c i (T i) (hT i)]
      exact Finset.sum_congr rfl fun C _ => eval_clausePoly x C
    rw [Finset.sum_congr rfl h3, odd_violated G c S hS hodd]
    decide
  have he : (1 : MvPolynomial (Fin N × Fin 4) (ZMod 2)) = (1 + P) + P := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  unfold PCRefutable
  rw [he]
  exact .add hV hPd

end PEqualNP.ProofComplexity.LiftRank
