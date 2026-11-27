import PEqualNP.Defs
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Linarith

namespace PEqualNP.Outside.L_gct_251

open Polynomial

-- The interval certificate follows the fixed-point method in L_gct_261.
-- The three-binomial seed is due to XXXLUMI, PR 14351.
def covers (s : ℕ) (b : ℕ × ℕ) (x : ℝ) : Prop :=
  (b.1 : ℝ) ≤ (s : ℝ) * x ∧ (s : ℝ) * x ≤ (b.2 : ℝ)

def boxMul (s : ℕ) (a b : ℕ × ℕ) : ℕ × ℕ :=
  (a.1 * b.1 / s, a.2 * b.2 / s + 1)

lemma boxMul_ok {s : ℕ} (hs : 0 < s) {a b : ℕ × ℕ} {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : covers s a x) (hb : covers s b y) :
    covers s (boxMul s a b) (x*y) := by
  have sp : 0 < (s : ℝ) := by exact_mod_cast hs
  have lower : (a.1 * b.1 / s) * s ≤ a.1 * b.1 := Nat.div_mul_le_self _ _
  have upper : a.2 * b.2 ≤ (a.2 * b.2 / s + 1) * s := by
    have h := Nat.mod_add_div (a.2 * b.2) s
    have hrem := Nat.mod_lt (a.2 * b.2) hs
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (a.2 * b.2 / s)]
    omega
  constructor
  · apply le_of_mul_le_mul_right (a := (s : ℝ)) _ sp
    calc
      ((a.1 * b.1 / s : ℕ) : ℝ) * s ≤ (a.1 : ℝ) * b.1 := by exact_mod_cast lower
      _ ≤ ((s : ℝ) * x) * ((s : ℝ) * y) :=
        mul_le_mul ha.1 hb.1 (by positivity) (mul_nonneg sp.le hx)
      _ = ((s : ℝ) * (x*y)) * s := by ring
  · apply le_of_mul_le_mul_right (a := (s : ℝ)) _ sp
    calc
      ((s : ℝ) * (x*y)) * s = ((s : ℝ) * x) * ((s : ℝ) * y) := by ring
      _ ≤ (a.2 : ℝ) * b.2 :=
        mul_le_mul ha.2 hb.2 (mul_nonneg sp.le hy) (by positivity)
      _ ≤ ((a.2 * b.2 / s + 1 : ℕ) : ℝ) * s := by exact_mod_cast upper

def powerBox (s base : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (s,s)
  | k+1, n =>
    let u := powerBox s base k (n/2)
    let v := boxMul s u u
    if n % 2 = 0 then v else boxMul s v (base,base)

lemma powerBox_ok {s b : ℕ} (hs : 0 < s) (k n : ℕ) (hn : n < 2^k) :
    covers s (powerBox s b k n) (((b : ℝ) / s)^n) := by
  have sp : 0 < (s : ℝ) := by exact_mod_cast hs
  have xp : 0 ≤ (b : ℝ)/s := by positivity
  have base : covers s (b,b) ((b : ℝ)/s) := by
    unfold covers
    rw [mul_div_cancel₀ _ sp.ne']
    exact ⟨le_rfl,le_rfl⟩
  induction k generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst n
    simp [powerBox,covers]
  | succ k ih =>
    have half : n / 2 < 2^k := by rw [pow_succ] at hn; omega
    have h := ih (n/2) half
    have sq := boxMul_ok hs (pow_nonneg xp _) (pow_nonneg xp _) h h
    rw [← pow_add] at sq
    by_cases even : n % 2 = 0
    · simp only [powerBox,even,ite_true]
      convert sq using 2; omega
    · simp only [powerBox,even,ite_false]
      have step := boxMul_ok hs (pow_nonneg xp _) xp sq base
      rw [← pow_succ] at step
      convert step using 2; omega

open Polynomial

def weightedBox (s b : ℕ) : List (ℕ × ℕ) → ℕ × ℕ
  | [] => (0,0)
  | t :: ts =>
    let z := powerBox s b 52 t.2
    let tail := weightedBox s b ts
    (t.1 * z.1 + tail.1, t.1 * z.2 + tail.2)

def weightedEval (x : ℝ) : List (ℕ × ℕ) → ℝ
  | [] => 0
  | t :: ts => (t.1 : ℝ) * x^t.2 + weightedEval x ts

lemma weighted_ok {s b : ℕ} (hs : 0 < s) (ts : List (ℕ × ℕ))
    (h : ∀ t ∈ ts, t.2 < 2^52) :
    covers s (weightedBox s b ts) (weightedEval ((b : ℝ)/s) ts) := by
  induction ts with
  | nil => simp [covers, weightedBox, weightedEval]
  | cons t ts ih =>
    have ht := powerBox_ok (b := b) hs 52 t.2 (h t (by simp))
    have hz := ih (fun u hu => h u (by simp [hu]))
    rcases ht with ⟨tl,tu⟩
    rcases hz with ⟨zl,zu⟩
    have coef : (0 : ℝ) ≤ t.1 := by positivity
    simp only [covers, weightedBox, weightedEval, Nat.cast_add, Nat.cast_mul]
    constructor
    · nlinarith only [mul_le_mul_of_nonneg_left tl coef,zl]
    · nlinarith only [mul_le_mul_of_nonneg_left tu coef,zu]


def boxesCheck (i : ℕ) (p n : ℕ × ℕ) : Bool :=
  if i%2 = 0 then decide (n.2 < p.1) else decide (p.2 < n.1)

lemma sign_from_boxes (i s : ℕ) (p n : ℕ × ℕ) (a b v d : ℝ)
    (hs : 0 < s) (hd : 0 < d) (hp : covers s p a) (hn : covers s n b)
    (hv : d * v = a - b) (hc : boxesCheck i p n = true) :
    if i%2=0 then 0<v else v<0 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  by_cases h : i%2 = 0
  · simp only [h,ite_true]
    simp only [boxesCheck,h,ite_true,decide_eq_true_eq] at hc
    have hR : (n.2 : ℝ) < p.1 := by exact_mod_cast hc
    have hba := (mul_lt_mul_iff_right₀ hsR).mp (hn.2.trans_lt (hR.trans_le hp.1))
    exact pos_of_mul_pos_right (hv.symm ▸ sub_pos.mpr hba) hd.le
  · simp only [h,ite_false]
    simp only [boxesCheck,h,ite_false,decide_eq_true_eq] at hc
    have hR : (p.2 : ℝ) < n.1 := by exact_mod_cast hc
    have hab := (mul_lt_mul_iff_right₀ hsR).mp (hp.2.trans_lt (hR.trans_le hn.1))
    exact neg_of_mul_neg_right (hv.symm ▸ sub_neg.mpr hab) hd.le

lemma rootsOfCrossings (count : ℕ) (P : Polynomial ℝ) (point : ℕ → ℝ)
    (hcount : 0 < count) (hpos : ∀ n ≤ count, 0 < point n)
    (hinc : ∀ n < count, point n < point (n + 1))
    (hcross : ∀ n < count, P.eval (point n) * P.eval (point (n + 1)) < 0) :
    count ≤ (P.roots.toFinset.filter (fun x : ℝ => 0 < x)).card := by
  classical
  have hp : P ≠ 0 := by
    intro hp
    have h := hcross 0 (by omega)
    simp [hp] at h
  have hz (n : ℕ) (hn : n < count) :
      ∃ x : ℝ, point n < x ∧ x < point (n + 1) ∧ P.eval x = 0 := by
    have hs := (mul_neg_iff.mp (hcross n hn))
    rcases hs with h | h
    · obtain ⟨x, hx, he⟩ := intermediate_value_Ioo' (hinc n hn).le P.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (P.eval (point (n + 1))) (P.eval (point n)) from ⟨h.2, h.1⟩)
      exact ⟨x, hx.1, hx.2, he⟩
    · obtain ⟨x, hx, he⟩ := intermediate_value_Ioo (hinc n hn).le P.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (P.eval (point n)) (P.eval (point (n + 1))) from ⟨h.1, h.2⟩)
      exact ⟨x, hx.1, hx.2, he⟩
  let root : Fin count → ℝ := fun i => Classical.choose (hz i.val i.isLt)
  have hroot (i : Fin count) :
      point i.val < root i ∧ root i < point (i.val + 1) ∧ P.eval (root i) = 0 :=
    Classical.choose_spec (hz i.val i.isLt)
  have hmono : StrictMonoOn point (Set.Iic count) :=
    strictMonoOn_Iic_of_lt_succ (by simpa using hinc)
  have hri : StrictMono root := by
    intro i j hij
    have hij' : i.val + 1 ≤ j.val := by omega
    have hh : point (i.val + 1) ≤ point j.val := by
      rcases eq_or_lt_of_le hij' with he | he
      · rw [he]
      · exact (hmono (by simp) (by simp) he).le
    exact lt_of_lt_of_le (hroot i).2.1 (le_trans hh (hroot j).1.le)
  have hcard : count ≤ (P.roots.toFinset.filter (fun x : ℝ => 0 < x)).card := by
    have hc := Finset.card_le_card_of_injOn root
      (s := Finset.univ)
      (t := P.roots.toFinset.filter (fun x : ℝ => 0 < x))
      (by
        intro i hi
        apply Finset.mem_filter.mpr
        constructor
        · apply Multiset.mem_toFinset.mpr
          exact (Polynomial.mem_roots hp).mpr (hroot i).2.2
        · exact lt_trans (hpos i.val (by omega)) (hroot i).1)
      (by
        intro i hi j hj h
        exact hri.injective h)
    simpa using hc
  omega


noncomputable def sparse : List (ℕ × ℝ) → Polynomial ℝ
  | [] => 0
  | (n, c) :: ts => monomial n c + sparse ts

lemma sparse_card (ts : List (ℕ × ℝ)) : (sparse ts).support.card ≤ ts.length := by
  induction ts with
  | nil => simp [sparse]
  | cons t ts ih =>
    obtain ⟨n, c⟩ := t
    have hmono : (monomial n c).support.card ≤ 1 := by
      simpa using Finset.card_le_card (support_monomial_subset n c)
    have hsum : (monomial n c + sparse ts).support.card ≤
        (monomial n c).support.card + (sparse ts).support.card :=
      (Finset.card_le_card support_add).trans (Finset.card_union_le _ _)
    simp only [sparse, List.length_cons]
    omega

noncomputable def list0 : List (ℕ × ℝ) := [(6402, 1),
    (12802, (-39 / 250000))]

noncomputable def part0 : Polynomial ℝ := sparse list0

noncomputable def list1 : List (ℕ × ℝ) := [(0, (39 / 250000)),
    (6400, (-1))]

noncomputable def part1 : Polynomial ℝ := sparse list1

noncomputable def list2 : List (ℕ × ℝ) := [(4353, (-1678911 / 20000000)),
    (8449, (1678911 / 20000000))]

noncomputable def part2 : Polynomial ℝ := sparse list2

noncomputable def list3 : List (ℕ × ℝ) := [(14497, (-10148405948902523 / 500000000000000000000)),
    (27119, (1471122985532201 / 20000000000000000000000000000))]

noncomputable def part3 : Polynomial ℝ := sparse list3

noncomputable def gs : Fin 4 → Polynomial ℝ := ![part0, part1, part2, part3]

noncomputable def P : Polynomial ℝ :=
  (Finset.univ : Finset (Fin 4)).sum fun i => C (1 : ℝ) * gs i ^ 3

lemma gs_card (i : Fin 4) : (gs i).support.card ≤ 2 := by
  fin_cases i
  · exact (sparse_card list0).trans (by decide)
  · exact (sparse_card list1).trans (by decide)
  · exact (sparse_card list2).trans (by decide)
  · exact (sparse_card list3).trans (by decide)

def count : ℕ := 14
def phase : ℕ := 0
def scale : ℕ := 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def den : ℕ := 8000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def samples : List ℕ := [9930000000000000000000000000000000000000000000000000000000000000000000000000000000000, 9990950000000000000000000000000000000000000000000000000000000000000000000000000000000, 9993650000000000000000000000000000000000000000000000000000000000000000000000000000000, 9995450000000000000000000000000000000000000000000000000000000000000000000000000000000, 9997300000000000000000000000000000000000000000000000000000000000000000000000000000000, 9999550000000000000000000000000000000000000000000000000000000000000000000000000000000, 10001850000000000000000000000000000000000000000000000000000000000000000000000000000000, 10003650000000000000000000000000000000000000000000000000000000000000000000000000000000, 10005500000000000000000000000000000000000000000000000000000000000000000000000000000000, 10006850000000000000000000000000000000000000000000000000000000000000000000000000000000, 10013450000000000000000000000000000000000000000000000000000000000000000000000000000000, 10014800000000000000000000000000000000000000000000000000000000000000000000000000000000, 10015250000000000000000000000000000000000000000000000000000000000000000000000000000000, 10015550000000000000000000000000000000000000000000000000000000000000000000000000000000, 10095000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def base (i : ℕ) : ℕ := samples.getD i 0

def posTerms : List (ℕ × ℕ) := [(30371328000000000000000000000000000000000000000000000000000000000000000000, 0),
    (3744000000000000000000000000000000000000000000000000000000000000000000000000000000, 12800),
    (14197251584851116093000000000000000000000000000000000000000000000000000000000000000, 17155),
    (8000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 19206),
    (4732417194950372031000000000000000000000000000000000000000000000000000000000000000, 25347),
    (584064000000000000000000000000000000000000000000000000000000000000000000000000, 32006),
    (727253602067318204384684697801503782611049436779200000000000000, 56113),
    (3183808541161381952608278290479045766915116601, 81357)]
def negTerms : List (ℕ × ℕ) := [(584064000000000000000000000000000000000000000000000000000000000000000000000000, 6400),
    (4732417194950372031000000000000000000000000000000000000000000000000000000000000000, 13059),
    (8000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 19200),
    (14197251584851116093000000000000000000000000000000000000000000000000000000000000000, 21251),
    (3744000000000000000000000000000000000000000000000000000000000000000000000000000000, 25606),
    (30371328000000000000000000000000000000000000000000000000000000000000000000, 38406),
    (66891890110834981878999323143834852031517729898688000000000000000000000, 43491),
    (2635585075378316389984145731957367095758204446760000000, 68735)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma eval_eq (x : ℝ) : (den : ℝ) * P.eval x =
    weightedEval x posTerms - weightedEval x negTerms := by
  simp only [P, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, gs, map_one, one_mul, part0, part1, part2, part3, list0, list1, list2, list3, sparse, eval_mul, eval_add,
    eval_pow, eval_zero, eval_one, eval_monomial, den, posTerms, negTerms, weightedEval,
    Nat.cast_ofNat, ← pow_add]
  ring
noncomputable def point (i : ℕ) : ℝ := (base i : ℝ) / scale

def checkPoint (i : ℕ) : Bool :=
  boxesCheck (i + phase) (weightedBox scale (base i) posTerms)
    (weightedBox scale (base i) negTerms)

lemma points_checked : ∀ i : Fin (count + 1), checkPoint i.val = true := by decide +kernel

lemma pos_size : ∀ t ∈ posTerms, t.2 < 2^52 := by decide
lemma neg_size : ∀ t ∈ negTerms, t.2 < 2^52 := by decide

lemma point_sign (i : ℕ) (hi : i < count + 1) :
    if (i + phase) % 2 = 0 then 0 < P.eval (point i)
    else P.eval (point i) < 0 :=
  sign_from_boxes (i + phase) scale _ _ _ _ _ den
    (by decide) (by norm_num [den])
    (weighted_ok (b := base i) (by decide : 0 < scale) posTerms pos_size)
    (weighted_ok (b := base i) (by decide : 0 < scale) negTerms neg_size)
    (eval_eq (point i)) (points_checked ⟨i, hi⟩)

lemma base_pos : ∀ i : Fin (count + 1), 0 < base i.val := by decide +kernel
lemma base_inc : ∀ i : Fin count, base i.val < base (i.val + 1) := by decide +kernel

lemma points_pos (i : ℕ) (hi : i ≤ count) : 0 < point i :=
  div_pos (by exact_mod_cast base_pos ⟨i, by omega⟩) (by norm_num [scale])

lemma points_inc (i : ℕ) (hi : i < count) : point i < point (i + 1) := by
  apply (div_lt_div_iff_of_pos_right (by norm_num [scale])).mpr
  exact_mod_cast base_inc ⟨i, hi⟩

lemma crossing (i : ℕ) (hi : i < count) : P.eval (point i) * P.eval (point (i + 1)) < 0 := by
  have h₁ := point_sign i (by omega)
  have h₂ := point_sign (i + 1) (by omega)
  by_cases h : (i + phase) % 2 = 0
  · have h' : ¬ (i + 1 + phase) % 2 = 0 := by omega
    rw [if_pos h] at h₁
    rw [if_neg h'] at h₂
    exact mul_neg_of_pos_of_neg h₁ h₂
  · have h' : (i + 1 + phase) % 2 = 0 := by omega
    rw [if_neg h] at h₁
    rw [if_pos h'] at h₂
    exact mul_neg_of_neg_of_pos h₁ h₂

lemma roots_lower : count ≤ (P.roots.toFinset.filter (fun x : ℝ => 0 < x)).card :=
  rootsOfCrossings count P point (by decide) points_pos points_inc crossing

end PEqualNP.Outside.L_gct_251

theorem PEqualNP.Outside.L_gct_251 :
    ¬ (∀ (s : Fin 4 → ℝ) (g : Fin 4 → Polynomial ℝ), (∀ i, s i = 1 ∨ s i = -1) → (∀ i, (g i).support.card ≤ 2) → ((((Finset.univ : Finset (Fin 4)).sum fun i => Polynomial.C (s i) * g i ^ 3)).roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ 13) := by
  intro h
  open PEqualNP.Outside.L_gct_251 in
  exact by
    have limit := h (fun _ => 1) gs (fun _ => Or.inl rfl) gs_card
    change (P.roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ 13 at limit
    have lower := roots_lower
    norm_num [count] at lower
    omega
