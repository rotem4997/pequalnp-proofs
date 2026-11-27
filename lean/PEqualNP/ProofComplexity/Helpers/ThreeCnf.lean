import PEqualNP.Defs.ProofComplexityGeneral
import PEqualNP.ProofComplexity.Helpers.PCToolkit
import PEqualNP.ProofComplexity.Helpers.BoolVanish

/-!
# Helpers: from a CNF formula of width `w` to a 3-CNF formula, keeping polynomial calculus degree

## What is defined

For a CNF formula `F : Set (Clause V)` and a number `w`, the formula
`to3 F w : Set (Clause (V ⊕ (↥F × Fin (w + 1))))`. The new variables are the pairs `(C, j)`
of a clause `C` of `F` and a position `j ≤ w`. With `l_0, ..., l_{k-1}` the literals of `C`
in the order of `C.toList`, the variable `(C, j)` is meant to say "the literals
`l_0, ..., l_{j-1}` are all false". The clauses of `to3 F w`, for every clause `C` of `F`:

* start: `{(C, 0)}`, one positive literal;
* step, for every `i < k`: `{¬ (C, i), l_i, (C, i + 1)}`;
* end: `{¬ (C, k)}`, one negative literal.

Positions are clamped to `w` by `idx`, so the definition makes sense for every clause; the
clamp does nothing on a clause of at most `w` literals. The original variables are the left
summand, the literal `l_i` keeps its sign.

## What is proved

* `to3_width`: every clause of `to3 F w` has at most `3` literals.
* `to3_unsat`: if `F` is unsatisfiable, so is `to3 F w` (no width hypothesis).
* `to3_pc`: if `1 ≤ w` and every clause of `F` has at most `w` literals, a polynomial calculus
  refutation of `cnfSystem (to3 F w)` in degree `D` gives one of `cnfSystem F` in degree
  `w * D + 2 * w`.
* `to3_pc_lower`: the contrapositive, the form a degree lower bound is carried in.
* `to3_card`: when `V` and `F` are finite, the number of variables of `to3 F w` is
  `card V + card F * (w + 1)`.

The proof of `to3_pc` substitutes for the variable `(C, j)` the polynomial `pre C j`, the
product of the polynomials of the first `j` literals of `C` (degree at most `j ≤ w`), and
replays the refutation with `pcDerivable_replay`. The start clause becomes the zero
polynomial, a step clause becomes `h * (1 + h)` for a polynomial `h` of degree at most `w`,
which vanishes on the cube and so is derivable from the Boolean axioms in its own degree, and
the end clause becomes exactly `clausePoly C`.
-/

namespace PEqualNP.ProofComplexity.Helpers.ThreeCnf

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers

variable {V : Type}

/-- The position `i`, clamped to `w`. -/
def idx (w i : ℕ) : Fin (w + 1) := ⟨min i w, by omega⟩

theorem idx_val (w i : ℕ) : (idx w i).val = min i w := rfl

open Classical in
/-- The 3-CNF formula of `F`. See the head of the file. -/
noncomputable def to3 (F : Set (Clause V)) (w : ℕ) :
    Set (Clause (V ⊕ (↥F × Fin (w + 1)))) :=
  {K | ∃ C : ↥F,
      K = {(Sum.inr (C, idx w 0), true)} ∨
      (∃ (i : ℕ) (l : Literal V), C.1.toList[i]? = some l ∧
        K = {(Sum.inr (C, idx w i), false), (Sum.inl l.1, l.2),
          (Sum.inr (C, idx w (i + 1)), true)}) ∨
      K = {(Sum.inr (C, idx w C.1.card), false)}}

/-- Every clause of `to3 F w` has at most three literals. -/
theorem to3_width (F : Set (Clause V)) (w : ℕ) : ∀ K ∈ to3 F w, K.card ≤ 3 := by
  classical
  rintro K ⟨C, rfl | ⟨i, l, -, rfl⟩ | rfl⟩
  · simp
  · exact Finset.card_le_three
  · simp

/-- If `F` is unsatisfiable, so is `to3 F w`. -/
theorem to3_unsat (F : Set (Clause V)) (w : ℕ) (h : ¬ Satisfiable F) :
    ¬ Satisfiable (to3 F w) := by
  classical
  rintro ⟨a, ha⟩
  apply h
  refine ⟨fun v => a (Sum.inl v), fun C hC => ?_⟩
  by_contra hns
  have hall : ∀ i, i ≤ C.card → a (Sum.inr (⟨C, hC⟩, idx w i)) = true := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨l, hl, hal⟩ := ha _ ⟨⟨C, hC⟩, Or.inl rfl⟩
      rw [Finset.mem_singleton] at hl
      subst hl
      exact hal
    | succ i ih =>
      intro hi
      have hlen : i < C.toList.length := by
        rw [Finset.length_toList]
        omega
      have hget : C.toList[i]? = some C.toList[i] := List.getElem?_eq_getElem hlen
      obtain ⟨l, hl, hal⟩ := ha _ ⟨⟨C, hC⟩, Or.inr (Or.inl ⟨i, C.toList[i], hget, rfl⟩)⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      · have := ih (by omega)
        rw [this] at hal
        exact absurd hal (by simp)
      · exfalso
        exact hns ⟨C.toList[i], Finset.mem_toList.mp (List.getElem_mem hlen), hal⟩
      · exact hal
  obtain ⟨l, hl, hal⟩ := ha _ ⟨⟨C, hC⟩, Or.inr (Or.inr rfl)⟩
  rw [Finset.mem_singleton] at hl
  subst hl
  have := hall C.card le_rfl
  rw [this] at hal
  exact absurd hal (by simp)

/-- The polynomial of one literal: the factor it contributes to `clausePoly`. -/
noncomputable def litPoly (l : Literal V) : MvPolynomial V (ZMod 2) :=
  if l.2 = true then 1 + X l.1 else X l.1

theorem totalDegree_litPoly_le (l : Literal V) : (litPoly l).totalDegree ≤ 1 := by
  unfold litPoly
  split_ifs
  · refine (totalDegree_add _ _).trans ?_
    rw [totalDegree_one, totalDegree_X]
    simp
  · rw [totalDegree_X]

/-- The product of the polynomials of the first `i` literals of `C`. At a point of the cube it
is `1` exactly when these literals are all false. -/
noncomputable def pre (C : Clause V) (i : ℕ) : MvPolynomial V (ZMod 2) :=
  ((C.toList.take i).map litPoly).prod

theorem pre_zero (C : Clause V) : pre C 0 = 1 := by
  simp [pre]

theorem pre_succ (C : Clause V) (i : ℕ) (l : Literal V) (hl : C.toList[i]? = some l) :
    pre C (i + 1) = pre C i * litPoly l := by
  unfold pre
  rw [List.take_add_one, hl]
  simp

theorem pre_card (C : Clause V) : pre C C.card = clausePoly C := by
  unfold pre
  have h : C.toList.take C.card = C.toList :=
    List.take_of_length_le (by rw [Finset.length_toList])
  rw [h, Finset.prod_map_toList]
  rfl

theorem totalDegree_list_le (L : List (Literal V)) :
    ((L.map litPoly).prod).totalDegree ≤ L.length := by
  induction L with
  | nil => simp
  | cons l L ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons]
    refine (totalDegree_mul _ _).trans ?_
    have := totalDegree_litPoly_le l
    omega

theorem totalDegree_pre_le (C : Clause V) (i : ℕ) : (pre C i).totalDegree ≤ i := by
  unfold pre
  refine (totalDegree_list_le _).trans ?_
  rw [List.length_take]
  exact min_le_left _ _

/-- The substitution: an original variable goes to itself, the variable `(C, j)` to
`pre C j`. -/
noncomputable def sub (F : Set (Clause V)) (w : ℕ) :
    V ⊕ (↥F × Fin (w + 1)) → MvPolynomial V (ZMod 2) :=
  Sum.elim X (fun p => pre p.1.1 p.2.val)

theorem totalDegree_sub_le (F : Set (Clause V)) (w : ℕ) (hw1 : 1 ≤ w)
    (j : V ⊕ (↥F × Fin (w + 1))) : (sub F w j).totalDegree ≤ w := by
  rcases j with v | ⟨C, j⟩
  · simp only [sub, Sum.elim_inl]
    rw [totalDegree_X]
    exact hw1
  · simp only [sub, Sum.elim_inr]
    exact (totalDegree_pre_le _ _).trans (Nat.lt_succ_iff.mp j.isLt)

/-- The image of a clause polynomial under a substitution. -/
theorem bind_clausePoly {σ τ : Type} (φ : σ → MvPolynomial τ (ZMod 2)) (K : Clause σ) :
    bind₁ φ (clausePoly K) = ∏ l ∈ K, (if l.2 = true then 1 + φ l.1 else φ l.1) := by
  unfold clausePoly
  rw [map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  split_ifs
  · rw [map_add, map_one, bind₁_X_right]
  · rw [bind₁_X_right]

/-- Over `ZMod 2`, a polynomial `g * g + g` vanishes on the cube. -/
theorem eval_sq_add (x : V → ZMod 2) (g : MvPolynomial V (ZMod 2)) :
    eval x (g * g + g) = 0 := by
  rw [map_add, map_mul]
  generalize eval x g = c
  revert c
  decide

theorem eval_mul_one_add (x : V → ZMod 2) (g f : MvPolynomial V (ZMod 2)) :
    eval x (g * (f * (1 + g * f))) = 0 := by
  simp only [map_add, map_mul, map_one]
  generalize eval x g = c
  generalize eval x f = d
  revert c d
  decide

/-- A polynomial calculus refutation of the 3-CNF formula in degree `D` gives one of the
original formula in degree `w * D + 2 * w`. -/
theorem to3_pc (F : Set (Clause V)) (w D : ℕ) (hw1 : 1 ≤ w) (hw : ∀ C ∈ F, C.card ≤ w)
    (h : PCRefutable (cnfSystem (to3 F w)) D) :
    PCRefutable (cnfSystem F) (w * D + 2 * w) := by
  classical
  have hbool : ∀ v : V, (X v * X v + X v : MvPolynomial V (ZMod 2)) ∈ cnfSystem F :=
    fun v => Or.inl ⟨v, rfl⟩
  have hB : 2 * w ≤ w * D + 2 * w := Nat.le_add_left _ _
  have hax : ∀ a ∈ cnfSystem (to3 F w), a.totalDegree ≤ D →
      PCDerivable (cnfSystem F) (w * D + 2 * w) (1 * bind₁ (sub F w) a) := by
    intro a ha _
    rw [one_mul]
    rcases ha with ⟨y, rfl⟩ | ⟨K, hK, rfl⟩
    · -- the Boolean axioms
      rw [map_add, map_mul, bind₁_X_right]
      refine pcDerivable_mono (BoolVanish.vanish_derivable V (cnfSystem F) (2 * w) _ hbool ?_
        (fun x => eval_sq_add x _)) hB subset_rfl
      have hd := totalDegree_sub_le F w hw1 y
      refine (totalDegree_add _ _).trans (max_le ?_ (by omega))
      refine (totalDegree_mul _ _).trans ?_
      omega
    · rw [bind_clausePoly]
      obtain ⟨C, rfl | ⟨i, l, hl, rfl⟩ | rfl⟩ := hK
      · -- the start clause: the zero polynomial
        rw [Finset.prod_singleton]
        have : (1 : MvPolynomial V (ZMod 2)) + 1 = 0 := by
          rw [← two_smul (ZMod 2) (1 : MvPolynomial V (ZMod 2)),
            show (2 : ZMod 2) = 0 from rfl, zero_smul]
        simp only [sub, Sum.elim_inr, idx_val, Nat.zero_min, pre_zero, ite_true, this]
        exact .zero
      · -- a step clause: vanishes on the cube
        have hi : i < C.1.card := by
          have := (List.getElem?_eq_some_iff.mp hl).1
          rwa [Finset.length_toList] at this
        have hCw : C.1.card ≤ w := hw C.1 C.2
        rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
        have e1 : min i w = i := by omega
        have e2 : min (i + 1) w = i + 1 := by omega
        have e3 : (if l.2 = true then (1 : MvPolynomial V (ZMod 2)) + X l.1 else X l.1)
            = litPoly l := rfl
        simp only [sub, Sum.elim_inr, Sum.elim_inl, idx_val, e1, e2, ite_true, e3,
          Bool.false_eq_true, ite_false]
        rw [pre_succ C.1 i l hl]
        refine pcDerivable_mono (BoolVanish.vanish_derivable V (cnfSystem F) (2 * w) _ hbool ?_
          (fun x => eval_mul_one_add x _ _)) hB subset_rfl
        have d1 := totalDegree_pre_le C.1 i
        have d2 := totalDegree_litPoly_le l
        have d3 : (pre C.1 i * litPoly l).totalDegree ≤ i + 1 :=
          (totalDegree_mul _ _).trans (by omega)
        have d4 : (1 + pre C.1 i * litPoly l).totalDegree ≤ i + 1 := by
          refine (totalDegree_add _ _).trans (max_le ?_ d3)
          rw [totalDegree_one]
          omega
        have d5 : (litPoly l * (1 + pre C.1 i * litPoly l)).totalDegree ≤ 1 + (i + 1) :=
          (totalDegree_mul _ _).trans (by omega)
        refine (totalDegree_mul _ _).trans ?_
        omega
      · -- the end clause: the polynomial of the original clause
        have hCw : C.1.card ≤ w := hw C.1 C.2
        rw [Finset.prod_singleton]
        have e1 : min C.1.card w = C.1.card := by omega
        simp only [sub, Sum.elim_inr, idx_val, e1, Bool.false_eq_true, ite_false, pre_card]
        refine .ax (Or.inr ⟨C.1, C.2, rfl⟩) ?_
        rw [← pre_card]
        have := totalDegree_pre_le C.1 C.1.card
        omega
  have key := pcDerivable_replay (G := cnfSystem F) (T := w) (D := D) (s := 2 * w)
    (sub F w) (totalDegree_sub_le F w hw1) 1 (by rw [totalDegree_one]; omega) hax h
  rw [map_one, one_mul] at key
  exact key

/-- The contrapositive of `to3_pc`: a degree lower bound for `F` gives one for `to3 F w`. -/
theorem to3_pc_lower (F : Set (Clause V)) (w D : ℕ) (hw1 : 1 ≤ w) (hw : ∀ C ∈ F, C.card ≤ w)
    (h : ¬ PCRefutable (cnfSystem F) (w * D + 2 * w)) :
    ¬ PCRefutable (cnfSystem (to3 F w)) D :=
  fun h3 => h (to3_pc F w D hw1 hw h3)

/-- The number of variables of `to3 F w`. -/
theorem to3_card (F : Set (Clause V)) (w : ℕ) [Fintype V] [Fintype ↥F] :
    Fintype.card (V ⊕ (↥F × Fin (w + 1))) = Fintype.card V + Fintype.card ↥F * (w + 1) := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]


end PEqualNP.ProofComplexity.Helpers.ThreeCnf
