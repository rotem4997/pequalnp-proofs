import PEqualNP.Defs

-- Every cutting planes refutation of the pigeonhole formula with five pigeons and four holes has at
-- least 91 lines, so none has at most 90. Three counts, all made along the derivation:
--
-- * Each of the 45 clauses is needed: dropping any one leaves a satisfiable formula. For clause `k`,
--   `pt k` is a 0/1 point satisfying all the other clauses, and a line depends on `k` when it fails
--   at `pt k` (`D`). The line of a clause depends on at most that clause, a bound `0 ≤ x ≤ 1` on
--   none, and a sum, a multiple or a rounding only on what its parents depend on. The contradiction depends on
--   all 45.
-- * Joining: the dependencies of every line lie in one block of a labelling `col` of the clauses met
--   so far. A new clause adds one block and one clause, a sum joins at most two blocks, so
--   `2 * (clauses met) - (blocks)` grows by at most one per line, and it is 89 at the end.
-- * Rounding: at the test points `IsTest` (twice a point of the relaxation: the all-1/2 point, and
--   both ends of a unit segment along each coordinate) every clause line and bound holds, and sums
--   and multiples keep holding. The rounding of a line true at all test points still holds at one of them (the end of
--   the segment along a coordinate with a nonzero coefficient gains at least one), so a derivation
--   with at most one rounding has a point where all its lines hold. The contradiction holds nowhere.
-- So the lines number at least 89 + 2 = 91.

namespace PEqualNP.Outside.L_meta_9687_aux

open PEqualNP.Search PEqualNP.ProofComplexity

abbrev V : Type := Fin (4 + 1) × Fin 4

abbrev Ln : Type := CPLine V

/-- The weighted sum of a coefficient vector. -/
def sw (w f : V → ℤ) : ℤ := ∑ v, f v * w v

/-- The line `e` holds at the point `w / c`. -/
abbrev holdW (c : ℤ) (w : V → ℤ) (e : Ln) : Prop := c * e.2 ≤ sw w e.1

theorem sw_add (w f g : V → ℤ) : sw w (f + g) = sw w f + sw w g := by
  unfold sw
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _ => by rw [Pi.add_apply, add_mul])

theorem sw_smul (w f : V → ℤ) (k : ℤ) : sw w (k • f) = k * sw w f := by
  unfold sw
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun v _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc])

theorem sw_div (w f : V → ℤ) (d : ℤ) (hd : ∀ v, d ∣ f v) :
    sw w f = d * sw w (fun v => f v / d) := by
  unfold sw
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun v _ => by rw [← mul_assoc, Int.mul_ediv_cancel' (hd v)])

theorem sw_zero (w : V → ℤ) : sw w 0 = 0 := by
  simp [sw]

theorem holdW_add {c : ℤ} {w : V → ℤ} {e e' : Ln} (h : holdW c w e) (h' : holdW c w e') :
    holdW c w (e.1 + e'.1, e.2 + e'.2) := by
  show c * (e.2 + e'.2) ≤ sw w (e.1 + e'.1)
  rw [sw_add, mul_add]
  exact add_le_add h h'

theorem holdW_mul {c : ℤ} {w : V → ℤ} {e : Ln} (k : ℕ) (h : holdW c w e) :
    holdW c w ((k : ℤ) • e.1, (k : ℤ) * e.2) := by
  show c * ((k : ℤ) * e.2) ≤ sw w ((k : ℤ) • e.1)
  rw [sw_smul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- At an integer point, rounding keeps a line true. -/
theorem holdW_div {w : V → ℤ} {e : Ln} (d : ℕ) (hd0 : 0 < d) (hdv : ∀ v, (d : ℤ) ∣ e.1 v)
    (h : holdW 1 w e) : holdW 1 w (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) := by
  show 1 * -((-e.2) / (d : ℤ)) ≤ sw w (fun v => e.1 v / (d : ℤ))
  have h1 : 1 * e.2 ≤ sw w e.1 := h
  rw [sw_div w e.1 d hdv] at h1
  have hd : (0 : ℤ) < d := by exact_mod_cast hd0
  have h2 : -sw w (fun v => e.1 v / (d : ℤ)) ≤ (-e.2) / (d : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hd]
    nlinarith
  linarith

/-! The test points: twice a point of the relaxation. -/

def h1 (j : Fin 4) : Fin 4 := if j.val = 0 then 1 else 0

def h2 (j : Fin 4) : Fin 4 := if j.val ≤ 1 then 2 else 1

/-- The segment through `v`, without `v`: pigeon `v.1` at one half in its other holes, every other
pigeon at one half in the two smallest holes other than `v.2` (all doubled). -/
def base (v : V) (u : V) : ℤ :=
  if u.1 = v.1 then (if u.2 = v.2 then 0 else 1)
  else (if u.2 = h1 v.2 ∨ u.2 = h2 v.2 then 1 else 0)

def Xv (v : V) (t : ℤ) (u : V) : ℤ := base v u + if u = v then t else 0

def Xstar (_ : V) : ℤ := 1

def IsTest (X : V → ℤ) : Prop := X = Xstar ∨ ∃ v : V, X = Xv v 0 ∨ X = Xv v 2

theorem sw_Xv (v : V) (t : ℤ) (f : V → ℤ) : sw (Xv v t) f = sw (base v) f + f v * t := by
  unfold sw Xv
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem arith_core (d e2 q B av : ℤ) (hd : 0 < d) (hq : -e2 < (q + 1) * d)
    (h0 : 2 * e2 ≤ d * B) (hav : 1 ≤ av) : 2 * -q ≤ B + av * 2 := by
  by_contra hcon
  replace hcon := lt_of_not_ge hcon
  have m1 : d * (B + av * 2) < d * (2 * -q) := mul_lt_mul_of_pos_left hcon hd
  have m2 : d * 1 ≤ d * av := mul_le_mul_of_nonneg_left hav hd.le
  nlinarith

/-- The rounding of a line true at every test point holds at one of them. -/
theorem div_key {e : Ln} (d : ℕ) (hd0 : 0 < d) (hdv : ∀ v, (d : ℤ) ∣ e.1 v)
    (h : ∀ X, IsTest X → holdW 2 X e) :
    ∃ X, IsTest X ∧ holdW 2 X (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) := by
  have hd : (0 : ℤ) < d := by exact_mod_cast hd0
  have hq : -e.2 < ((-e.2) / (d : ℤ) + 1) * d := Int.lt_ediv_add_one_mul_self _ hd
  have hfix : ∀ X, sw X e.1 = d * sw X (fun v => e.1 v / (d : ℤ)) := fun X => sw_div X e.1 d hdv
  by_cases hz : ∀ v, e.1 v / (d : ℤ) = 0
  · refine ⟨Xstar, Or.inl rfl, ?_⟩
    have h0 : sw Xstar (fun v => e.1 v / (d : ℤ)) = 0 := by
      have : (fun v => e.1 v / (d : ℤ)) = 0 := funext hz
      rw [this, sw_zero]
    have hs : 2 * e.2 ≤ sw Xstar e.1 := h Xstar (Or.inl rfl)
    rw [hfix, h0, mul_zero] at hs
    show 2 * -((-e.2) / (d : ℤ)) ≤ sw Xstar (fun v => e.1 v / (d : ℤ))
    rw [h0]
    have : 0 ≤ (-e.2) / (d : ℤ) := Int.ediv_nonneg (by linarith) hd.le
    linarith
  · obtain ⟨v0, hv0⟩ := not_forall.mp hz
    have h0 : 2 * e.2 ≤ sw (Xv v0 0) e.1 := h _ (Or.inr ⟨v0, Or.inl rfl⟩)
    have h2 : 2 * e.2 ≤ sw (Xv v0 2) e.1 := h _ (Or.inr ⟨v0, Or.inr rfl⟩)
    rw [hfix, sw_Xv, mul_zero, add_zero] at h0
    rw [hfix, sw_Xv] at h2
    rcases lt_or_gt_of_ne hv0 with hneg | hpos
    · refine ⟨Xv v0 0, Or.inr ⟨v0, Or.inl rfl⟩, ?_⟩
      show 2 * -((-e.2) / (d : ℤ)) ≤ sw (Xv v0 0) (fun v => e.1 v / (d : ℤ))
      rw [sw_Xv, mul_zero, add_zero]
      have := arith_core d e.2 ((-e.2) / (d : ℤ))
        (sw (base v0) (fun v => e.1 v / (d : ℤ)) + e.1 v0 / (d : ℤ) * 2) (-(e.1 v0 / (d : ℤ)))
        hd hq h2 (by omega)
      linarith
    · refine ⟨Xv v0 2, Or.inr ⟨v0, Or.inr rfl⟩, ?_⟩
      show 2 * -((-e.2) / (d : ℤ)) ≤ sw (Xv v0 2) (fun v => e.1 v / (d : ℤ))
      rw [sw_Xv]
      exact arith_core d e.2 ((-e.2) / (d : ℤ)) (sw (base v0) (fun v => e.1 v / (d : ℤ)))
        (e.1 v0 / (d : ℤ)) hd hq h0 (by omega)

/-! The 0/1 points: `pt k` violates clause `k` only. -/

def pairOf (q : ℕ) : ℕ × ℕ :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)].getD q (0, 0)

def tri (a b : ℕ) : ℕ := a * 4 - a * (a - 1) / 2 + (b - a - 1)

def holeIdx (i i' : Fin (4 + 1)) (j : Fin 4) : ℕ :=
  5 + 4 * (if i.val < i'.val then tri i.val i'.val else tri i'.val i.val) + j.val

/-- For `k < 5` pigeon `k` sits nowhere and the others fill the holes in order; for
`k = holeIdx a b j` pigeons `a` and `b` share hole `j` and the other three fill the other holes. -/
def pt (k : ℕ) (u : V) : Bool :=
  if k < 5 then
    decide (u.1.val ≠ k) && decide (u.2.val = (if u.1.val < k then u.1.val else u.1.val - 1))
  else
    if u.1.val = (pairOf ((k - 5) / 4)).1 ∨ u.1.val = (pairOf ((k - 5) / 4)).2 then
      decide (u.2.val = (k - 5) % 4)
    else
      decide (u.2.val =
        (if u.1.val - (if (pairOf ((k - 5) / 4)).1 < u.1.val then 1 else 0)
            - (if (pairOf ((k - 5) / 4)).2 < u.1.val then 1 else 0) < (k - 5) % 4
         then u.1.val - (if (pairOf ((k - 5) / 4)).1 < u.1.val then 1 else 0)
            - (if (pairOf ((k - 5) / 4)).2 < u.1.val then 1 else 0)
         else u.1.val - (if (pairOf ((k - 5) / 4)).1 < u.1.val then 1 else 0)
            - (if (pairOf ((k - 5) / 4)).2 < u.1.val then 1 else 0) + 1))

def b01 (a : V → Bool) (u : V) : ℤ := if a u then 1 else 0

/-! Finite checks. -/

set_option maxRecDepth 8000 in
theorem F1 : ∀ i : Fin (4 + 1), ∀ k : Fin 45, k.val ≠ i.val →
    1 ≤ ∑ j : Fin 4, b01 (pt k.val) (i, j) := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem F2 : ∀ i i' : Fin (4 + 1), ∀ j : Fin 4, i ≠ i' → ∀ k : Fin 45, k.val ≠ holeIdx i i' j →
    -1 ≤ -b01 (pt k.val) (i, j) - b01 (pt k.val) (i', j) := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem F3 : ∀ i : Fin (4 + 1), (2 * 1 ≤ ∑ j : Fin 4, Xstar (i, j)) ∧ ∀ v : V,
    (2 * 1 ≤ ∑ j : Fin 4, Xv v 0 (i, j)) ∧ (2 * 1 ≤ ∑ j : Fin 4, Xv v 2 (i, j)) := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem F4 : ∀ i i' : Fin (4 + 1), ∀ j : Fin 4, i ≠ i' →
    (2 * -1 ≤ -Xstar (i, j) - Xstar (i', j)) ∧ ∀ v : V,
    (2 * -1 ≤ -Xv v 0 (i, j) - Xv v 0 (i', j)) ∧ (2 * -1 ≤ -Xv v 2 (i, j) - Xv v 2 (i', j)) := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem F5 : ∀ u : V, (2 * 0 ≤ Xstar u ∧ 2 * -1 ≤ -Xstar u) ∧ ∀ w : V,
    (2 * 0 ≤ Xv w 0 u ∧ 2 * -1 ≤ -Xv w 0 u) ∧ (2 * 0 ≤ Xv w 2 u ∧ 2 * -1 ≤ -Xv w 2 u) := by
  decide +kernel

/-! The lines of the clauses. -/

theorem sw_clauseCP (w : V → ℤ) (C : Clause V) :
    sw w (clauseCP C).1 = ∑ l ∈ C, (if l.2 then 1 else -1) * w l.1 := by
  simp only [sw, clauseCP, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem sw_pig (w : V → ℤ) (i : Fin (4 + 1)) :
    sw w (clauseCP (Finset.univ.image (fun j : Fin 4 => ((i, j), true)))).1 =
      ∑ j : Fin 4, w (i, j) := by
  rw [sw_clauseCP, Finset.sum_image]
  · simp
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq, true_and, and_true] at hxy
    exact hxy

theorem cst_pig (i : Fin (4 + 1)) :
    (clauseCP (Finset.univ.image (fun j : Fin 4 => ((i, j), true)))).2 = 1 := by
  show 1 - ∑ l ∈ Finset.univ.image (fun j : Fin 4 => ((i, j), true)),
    (if l.2 then (0 : ℤ) else 1) = 1
  rw [Finset.sum_eq_zero]
  · norm_num
  · intro l hl
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    simp

theorem hole_ne (i i' : Fin (4 + 1)) (j : Fin 4) (h : i ≠ i') :
    (((i, j), false) : V × Bool) ≠ ((i', j), false) := by
  intro e
  apply h
  simp only [Prod.mk.injEq, and_true] at e
  exact e

theorem sw_hole (w : V → ℤ) (i i' : Fin (4 + 1)) (j : Fin 4) (h : i ≠ i') :
    sw w (clauseCP ({((i, j), false), ((i', j), false)} : Clause V)).1 =
      -w (i, j) - w (i', j) := by
  rw [sw_clauseCP, Finset.sum_pair (hole_ne i i' j h)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring

theorem cst_hole (i i' : Fin (4 + 1)) (j : Fin 4) (h : i ≠ i') :
    (clauseCP ({((i, j), false), ((i', j), false)} : Clause V)).2 = -1 := by
  show 1 - ∑ l ∈ ({((i, j), false), ((i', j), false)} : Clause V),
    (if l.2 then (0 : ℤ) else 1) = -1
  rw [Finset.sum_pair (hole_ne i i' j h)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  norm_num

theorem sw_lo (w : V → ℤ) (v : V) : sw w (fun u => if u = v then 1 else 0) = w v := by
  simp [sw]

theorem sw_hi (w : V → ℤ) (v : V) : sw w (fun u => if u = v then -1 else 0) = -w v := by
  simp [sw, ite_mul]

/-! Dependencies. -/

def D (e : Ln) : Finset ℕ := (Finset.range 45).filter (fun k => ¬ holdW 1 (b01 (pt k)) e)

theorem D_ax {C : Clause V} (hC : C ∈ PHP (4 + 1) 4) : ∃ kC, D (clauseCP C) ⊆ {kC} := by
  simp only [PHP, Set.mem_union, Set.mem_ofPred_eq] at hC
  rcases hC with ⟨i, rfl⟩ | ⟨i, i', j, hii, rfl⟩
  · refine ⟨i.val, fun k hk => ?_⟩
    rw [Finset.mem_singleton]
    by_contra hne
    simp only [D, Finset.mem_filter, Finset.mem_range] at hk
    apply hk.2
    show 1 * (clauseCP _).2 ≤ sw _ (clauseCP _).1
    rw [cst_pig, sw_pig, one_mul]
    exact F1 i ⟨k, hk.1⟩ hne
  · refine ⟨holeIdx i i' j, fun k hk => ?_⟩
    rw [Finset.mem_singleton]
    by_contra hne
    simp only [D, Finset.mem_filter, Finset.mem_range] at hk
    apply hk.2
    show 1 * (clauseCP _).2 ≤ sw _ (clauseCP _).1
    rw [cst_hole i i' j hii, sw_hole _ i i' j hii, one_mul]
    exact F2 i i' j hii ⟨k, hk.1⟩ hne

theorem test_ax {C : Clause V} (hC : C ∈ PHP (4 + 1) 4) {X : V → ℤ} (hX : IsTest X) :
    holdW 2 X (clauseCP C) := by
  simp only [PHP, Set.mem_union, Set.mem_ofPred_eq] at hC
  rcases hC with ⟨i, rfl⟩ | ⟨i, i', j, hii, rfl⟩
  · show 2 * (clauseCP _).2 ≤ sw X (clauseCP _).1
    rw [cst_pig, sw_pig]
    rcases hX with rfl | ⟨v, rfl | rfl⟩
    · exact (F3 i).1
    · exact ((F3 i).2 v).1
    · exact ((F3 i).2 v).2
  · show 2 * (clauseCP _).2 ≤ sw X (clauseCP _).1
    rw [cst_hole i i' j hii, sw_hole X i i' j hii]
    rcases hX with rfl | ⟨v, rfl | rfl⟩
    · exact (F4 i i' j hii).1
    · exact ((F4 i i' j hii).2 v).1
    · exact ((F4 i i' j hii).2 v).2

theorem D_lo (v : V) : D (fun u => if u = v then 1 else 0, 0) = ∅ := by
  apply Finset.filter_false_of_mem
  intro k _ h
  apply h
  show 1 * 0 ≤ sw (b01 (pt k)) (fun u => if u = v then 1 else 0)
  rw [sw_lo]
  unfold b01
  split_ifs <;> norm_num

theorem D_hi (v : V) : D (fun u => if u = v then -1 else 0, -1) = ∅ := by
  apply Finset.filter_false_of_mem
  intro k _ h
  apply h
  show 1 * -1 ≤ sw (b01 (pt k)) (fun u => if u = v then -1 else 0)
  rw [sw_hi]
  unfold b01
  split_ifs <;> norm_num

theorem test_lo (v : V) {X : V → ℤ} (hX : IsTest X) :
    holdW 2 X (fun u => if u = v then 1 else 0, 0) := by
  show 2 * 0 ≤ sw X (fun u => if u = v then 1 else 0)
  rw [sw_lo]
  rcases hX with rfl | ⟨w, rfl | rfl⟩
  · exact (F5 v).1.1
  · exact ((F5 v).2 w).1.1
  · exact ((F5 v).2 w).2.1

theorem test_hi (v : V) {X : V → ℤ} (hX : IsTest X) :
    holdW 2 X (fun u => if u = v then -1 else 0, -1) := by
  show 2 * -1 ≤ sw X (fun u => if u = v then -1 else 0)
  rw [sw_hi]
  rcases hX with rfl | ⟨w, rfl | rfl⟩
  · exact (F5 v).1.2
  · exact ((F5 v).2 w).1.2
  · exact ((F5 v).2 w).2.2

theorem D_add (e e' : Ln) : D (e.1 + e'.1, e.2 + e'.2) ⊆ D e ∪ D e' := by
  intro m hm
  simp only [D, Finset.mem_filter, Finset.mem_union] at hm ⊢
  by_contra hc
  apply hm.2
  apply holdW_add
  · by_contra h
    exact hc (Or.inl ⟨hm.1, h⟩)
  · by_contra h
    exact hc (Or.inr ⟨hm.1, h⟩)

theorem D_mul (e : Ln) (k : ℕ) : D ((k : ℤ) • e.1, (k : ℤ) * e.2) ⊆ D e := by
  intro m hm
  simp only [D, Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, fun h => hm.2 (holdW_mul k h)⟩

theorem D_div (e : Ln) (d : ℕ) (hd0 : 0 < d) (hdv : ∀ v, (d : ℤ) ∣ e.1 v) :
    D (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) ⊆ D e := by
  intro m hm
  simp only [D, Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, fun h => hm.2 (holdW_div d hd0 hdv h)⟩

theorem D_bot : D ((0 : V → ℤ), (1 : ℤ)) = Finset.range 45 := by
  apply Finset.filter_true_of_mem
  intro k _
  show ¬ (1 * 1 ≤ sw (b01 (pt k)) 0)
  rw [sw_zero]
  norm_num

/-! The rounding level. -/

def AllH (π : List Ln) : Prop := ∀ e ∈ π, ∀ X, IsTest X → holdW 2 X e

def SomeH (π : List Ln) : Prop := ∃ X, IsTest X ∧ ∀ e ∈ π, holdW 2 X e

open Classical in
/-- `0` when `P` holds, else `1`. -/
noncomputable def ind (P : Prop) : ℕ := if P then 0 else 1

theorem ind_le {P Q : Prop} (h : P → Q) : ind Q ≤ ind P := by
  unfold ind
  by_cases hq : Q
  · simp [hq]
  · have hp : ¬ P := fun p => hq (h p)
    simp [hq, hp]

theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  unfold ind
  split_ifs <;> simp

theorem ind_true {P : Prop} (h : P) : ind P = 0 := by
  unfold ind
  simp [h]

theorem ind_false {P : Prop} (h : ¬ P) : ind P = 1 := by
  unfold ind
  simp [h]

noncomputable def lvl (π : List Ln) : ℕ := ind (SomeH π) + ind (AllH π)

theorem lvl_nil : lvl [] = 0 := by
  have hS : SomeH [] := ⟨Xstar, Or.inl rfl, fun e he => by simp at he⟩
  have hA : AllH [] := fun e he => by simp at he
  unfold lvl
  rw [ind_true hS, ind_true hA]

theorem lvl_cons {π : List Ln} {new : Ln}
    (h : ∀ X, IsTest X → (∀ e ∈ π, holdW 2 X e) → holdW 2 X new) : lvl (new :: π) ≤ lvl π := by
  unfold lvl
  have h1 : ind (SomeH (new :: π)) ≤ ind (SomeH π) := ind_le (fun ⟨X, hX, hall⟩ =>
    ⟨X, hX, fun e he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact h X hX hall
      · exact hall e he⟩)
  have h2 : ind (AllH (new :: π)) ≤ ind (AllH π) := ind_le (fun hA e he X hX => by
    rcases List.mem_cons.mp he with rfl | he
    · exact h X hX (fun e' he' => hA e' he' X hX)
    · exact hA e he X hX)
  omega

theorem lvl_div {π : List Ln} {e : Ln} (he : e ∈ π) (d : ℕ) (hd0 : 0 < d)
    (hdv : ∀ v, (d : ℤ) ∣ e.1 v) :
    lvl ((fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) :: π) ≤ lvl π + 1 := by
  unfold lvl
  by_cases hA : AllH π
  · obtain ⟨X, hX, hR⟩ := div_key d hd0 hdv (fun X hX => hA e he X hX)
    have hS : SomeH ((fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) :: π) :=
      ⟨X, hX, fun e' he' => by
        rcases List.mem_cons.mp he' with rfl | he'
        · exact hR
        · exact hA e' he' X hX⟩
    rw [ind_true hS]
    have := ind_le_one (AllH ((fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) :: π))
    omega
  · rw [ind_false hA]
    have h1 := ind_le_one (SomeH ((fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) :: π))
    have h2 := ind_le_one (AllH ((fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) :: π))
    omega

theorem bot_fails (X : V → ℤ) : ¬ holdW 2 X ((0 : V → ℤ), (1 : ℤ)) := by
  show ¬ (2 * 1 ≤ sw X 0)
  rw [sw_zero]
  norm_num

theorem lvl_bot {π : List Ln} (h : ((0 : V → ℤ), (1 : ℤ)) ∈ π) : lvl π = 2 := by
  have hS : ¬ SomeH π := fun ⟨X, _, hall⟩ => bot_fails X (hall _ h)
  have hA : ¬ AllH π := fun hA => bot_fails Xstar (hA _ h Xstar (Or.inl rfl))
  unfold lvl
  rw [ind_false hS, ind_false hA]

/-! The joining count. -/

def blk (col : ℕ → ℕ) (s : Finset ℕ) : Prop := ∀ k ∈ s, ∀ k' ∈ s, col k = col k'

def cov : List Ln → Finset ℕ
  | [] => ∅
  | e :: π => D e ∪ cov π

theorem D_sub_cov {π : List Ln} {e : Ln} (h : e ∈ π) : D e ⊆ cov π := by
  induction π with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

theorem cov_sub (π : List Ln) : cov π ⊆ Finset.range 45 := by
  induction π with
  | nil => exact Finset.empty_subset _
  | cons x xs ih => exact Finset.union_subset (Finset.filter_subset _ _) ih

def Good (π : List Ln) : Prop :=
  ∃ col : ℕ → ℕ, (∀ e ∈ π, blk col (D e)) ∧
    2 * (cov π).card + lvl π ≤ π.length + ((cov π).image col).card

theorem keep {π : List Ln} {new : Ln} {col : ℕ → ℕ} (hb : ∀ e ∈ π, blk col (D e))
    (hn : blk col (D new)) (hs : D new ⊆ cov π)
    (hi : 2 * (cov π).card + lvl (new :: π) ≤ π.length + 1 + ((cov π).image col).card) :
    Good (new :: π) := by
  have hc : cov (new :: π) = cov π := Finset.union_eq_right.mpr hs
  refine ⟨col, fun e he => ?_, ?_⟩
  · rcases List.mem_cons.mp he with rfl | he
    · exact hn
    · exact hb e he
  · rw [hc, List.length_cons]
    exact hi

theorem fresh {π : List Ln} {new : Ln} {col : ℕ → ℕ} {kC : ℕ} (hD : D new = {kC})
    (hk : kC ∉ cov π) (hb : ∀ x ∈ π, blk col (D x))
    (hi : 2 * (cov π).card + lvl (new :: π) ≤ π.length + ((cov π).image col).card) :
    Good (new :: π) := by
  have hN : ((cov π).image col).sup id + 1 ∉ (cov π).image col := by
    intro h
    have := Finset.le_sup (f := id) h
    simp only [id] at this
    omega
  have hc : cov (new :: π) = insert kC (cov π) := by
    show D new ∪ cov π = insert kC (cov π)
    rw [hD, Finset.insert_eq]
  have hne : ∀ m ∈ cov π, m ≠ kC := fun m hm h => hk (h ▸ hm)
  refine ⟨Function.update col kC (((cov π).image col).sup id + 1), ?_, ?_⟩
  · intro x hx k hk1 k' hk2
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hD, Finset.mem_singleton] at hk1 hk2
      rw [hk1, hk2]
    · rw [Function.update_of_ne (hne k (D_sub_cov hx hk1)),
        Function.update_of_ne (hne k' (D_sub_cov hx hk2))]
      exact hb x hx k hk1 k' hk2
  · have himg : (cov π).image (Function.update col kC (((cov π).image col).sup id + 1)) =
        (cov π).image col :=
      Finset.image_congr (fun m hm => Function.update_of_ne (hne m hm) _ _)
    rw [hc, List.length_cons, Finset.card_insert_of_notMem hk, Finset.image_insert,
      Function.update_self, himg, Finset.card_insert_of_notMem hN]
    omega

/-- `c` with the label `a` renamed `b`. -/
def relabel (a b c : ℕ) : ℕ := if c = a then b else c

theorem merge {π : List Ln} {new e e' : Ln} {col : ℕ → ℕ} (he : e ∈ π) (he' : e' ∈ π)
    (hsub : D new ⊆ D e ∪ D e') (hb : ∀ x ∈ π, blk col (D x))
    (hi : 2 * (cov π).card + lvl (new :: π) ≤ π.length + ((cov π).image col).card) :
    Good (new :: π) := by
  have hs : D new ⊆ cov π := hsub.trans (Finset.union_subset (D_sub_cov he) (D_sub_cov he'))
  by_cases h1 : D e = ∅
  · rw [h1, Finset.empty_union] at hsub
    exact keep hb (fun k hk k' hk' => hb e' he' k (hsub hk) k' (hsub hk')) hs (by omega)
  by_cases h2 : D e' = ∅
  · rw [h2, Finset.union_empty] at hsub
    exact keep hb (fun k hk k' hk' => hb e he k (hsub hk) k' (hsub hk')) hs (by omega)
  obtain ⟨k1, hk1⟩ := Finset.nonempty_iff_ne_empty.mpr h1
  obtain ⟨k2, hk2⟩ := Finset.nonempty_iff_ne_empty.mpr h2
  have hc : cov (new :: π) = cov π := Finset.union_eq_right.mpr hs
  refine ⟨fun k => relabel (col k1) (col k2) (col k), ?_, ?_⟩
  · intro x hx k hk k' hk'
    rcases List.mem_cons.mp hx with rfl | hx
    · have hval : ∀ m ∈ D x, relabel (col k1) (col k2) (col m) = col k2 := by
        intro m hm
        rcases Finset.mem_union.mp (hsub hm) with hm | hm
        · have : col m = col k1 := hb e he m hm k1 hk1
          simp [relabel, this]
        · have : col m = col k2 := hb e' he' m hm k2 hk2
          simp [relabel, this]
      show relabel (col k1) (col k2) (col k) = relabel (col k1) (col k2) (col k')
      rw [hval k hk, hval k' hk']
    · show relabel (col k1) (col k2) (col k) = relabel (col k1) (col k2) (col k')
      rw [hb x hx k hk k' hk']
  · rw [hc, List.length_cons]
    have hsub2 : ((cov π).image col).erase (col k1) ⊆
        (cov π).image (fun k => relabel (col k1) (col k2) (col k)) := by
      intro c hc'
      rw [Finset.mem_erase] at hc'
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hc'.2
      exact Finset.mem_image.mpr ⟨m, hm, by simp [relabel, hc'.1]⟩
    have h3 := Finset.card_le_card hsub2
    have h4 := Finset.pred_card_le_card_erase (s := (cov π).image col) (a := col k1)
    omega

theorem good_of {π : List Ln} (h : IsCPDerivation (PHP (4 + 1) 4) π) : Good π := by
  induction h with
  | nil =>
    refine ⟨id, fun e he => by simp at he, ?_⟩
    rw [lvl_nil]
    simp [cov]
  | @ax π C hd hC ih =>
    obtain ⟨col, hb, hi⟩ := ih
    have hl := lvl_cons (new := clauseCP C) (π := π) (fun X hX _ => test_ax hC hX)
    obtain ⟨kC, hkC⟩ := D_ax hC
    by_cases hnew : kC ∈ D (clauseCP C) ∧ kC ∉ cov π
    · have hD : D (clauseCP C) = {kC} :=
        Finset.Subset.antisymm hkC (Finset.singleton_subset_iff.mpr hnew.1)
      exact fresh hD hnew.2 hb (by omega)
    · refine keep hb ?_ ?_ (by omega)
      · intro k hk k' hk'
        rw [Finset.mem_singleton.mp (hkC hk), Finset.mem_singleton.mp (hkC hk')]
      · intro k hk
        have hk2 := Finset.mem_singleton.mp (hkC hk)
        subst hk2
        by_contra hc
        exact hnew ⟨hk, hc⟩
  | @boolLo π v hd ih =>
    obtain ⟨col, hb, hi⟩ := ih
    have hl := lvl_cons (new := (fun u => if u = v then 1 else 0, 0)) (π := π)
      (fun X hX _ => test_lo v hX)
    refine keep hb ?_ ?_ (by omega)
    · rw [D_lo]
      intro k hk
      simp at hk
    · rw [D_lo]
      exact Finset.empty_subset _
  | @boolHi π v hd ih =>
    obtain ⟨col, hb, hi⟩ := ih
    have hl := lvl_cons (new := (fun u => if u = v then -1 else 0, -1)) (π := π)
      (fun X hX _ => test_hi v hX)
    refine keep hb ?_ ?_ (by omega)
    · rw [D_hi]
      intro k hk
      simp at hk
    · rw [D_hi]
      exact Finset.empty_subset _
  | @add π e e' hd he he' ih =>
    obtain ⟨col, hb, hi⟩ := ih
    have hl := lvl_cons (new := (e.1 + e'.1, e.2 + e'.2)) (π := π)
      (fun X hX hall => holdW_add (hall e he) (hall e' he'))
    exact merge he he' (D_add e e') hb (by omega)
  | @mul π e k hd he ih =>
    obtain ⟨col, hb, hi⟩ := ih
    have hl := lvl_cons (new := ((k : ℤ) • e.1, (k : ℤ) * e.2)) (π := π)
      (fun X hX hall => holdW_mul k (hall e he))
    refine keep hb ?_ ((D_mul e k).trans (D_sub_cov he)) (by omega)
    intro k1 hk1 k2 hk2
    exact hb e he k1 (D_mul e k hk1) k2 (D_mul e k hk2)
  | @div π e d hd he hd0 hdv ih =>
    obtain ⟨col, hb, hi⟩ := ih
    have hl := lvl_div he d hd0 hdv
    refine keep hb ?_ ((D_div e d hd0 hdv).trans (D_sub_cov he)) (by omega)
    intro k1 hk1 k2 hk2
    exact hb e he k1 (D_div e d hd0 hdv hk1) k2 (D_div e d hd0 hdv hk2)

theorem long (π : List Ln) (h : IsCPRefutation (PHP (4 + 1) 4) π) : 91 ≤ π.length := by
  obtain ⟨hd, hmem⟩ := h
  obtain ⟨col, hb, hi⟩ := good_of hd
  have hcov : cov π = Finset.range 45 := by
    apply Finset.Subset.antisymm (cov_sub π)
    rw [← D_bot]
    exact D_sub_cov hmem
  have hK : ((cov π).image col).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb'
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hb'
    rw [hcov, ← D_bot] at hk hk'
    exact hb _ hmem k hk k' hk'
  rw [lvl_bot hmem] at hi
  rw [hcov, Finset.card_range] at hi
  rw [hcov] at hK
  omega

end PEqualNP.Outside.L_meta_9687_aux

theorem PEqualNP.Outside.L_meta_9687 : ¬ (∃ π : List (PEqualNP.Search.CPLine (Fin (4 + 1) × Fin 4)), PEqualNP.Search.IsCPRefutation (PEqualNP.ProofComplexity.PHP (4 + 1) 4) π ∧ π.length ≤ 90) := by
  rintro ⟨π, h, hl⟩
  have := PEqualNP.Outside.L_meta_9687_aux.long π h
  omega
