import PEqualNP.Defs
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Linarith

namespace PEqualNP.Outside.L_gct_273

open Polynomial

-- Fixed-point interval arithmetic adapted from L-gct-263 (#14768, k-sandhu)
-- and its source L-gct-261 (Apache-2.0).
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
    let z := powerBox s b 97 t.2
    let tail := weightedBox s b ts
    (t.1 * z.1 + tail.1, t.1 * z.2 + tail.2)

def weightedEval (x : ℝ) : List (ℕ × ℕ) → ℝ
  | [] => 0
  | t :: ts => (t.1 : ℝ) * x^t.2 + weightedEval x ts

lemma weighted_ok {s b : ℕ} (hs : 0 < s) (ts : List (ℕ × ℕ))
    (h : ∀ t ∈ ts, t.2 < 2^97) :
    covers s (weightedBox s b ts) (weightedEval ((b : ℝ)/s) ts) := by
  induction ts with
  | nil => simp [covers, weightedBox, weightedEval]
  | cons t ts ih =>
    have ht := powerBox_ok (b := b) hs 97 t.2 (h t (by simp))
    have hz := ih (fun u hu => h u (by simp [hu]))
    rcases ht with ⟨tl,tu⟩
    rcases hz with ⟨zl,zu⟩
    have coef : (0 : ℝ) ≤ t.1 := by positivity
    simp only [covers, weightedBox, weightedEval, Nat.cast_add, Nat.cast_mul]
    constructor
    · nlinarith only [mul_le_mul_of_nonneg_left tl coef,zl]
    · nlinarith only [mul_le_mul_of_nonneg_left tu coef,zu]


def boxesCheck (i : ℕ) (p n : ℕ × ℕ) : Bool :=
  if i % 2 = 0 then decide (n.2 < p.1) else decide (p.2 < n.1)

lemma sign_from_boxes (i s : ℕ) (p n : ℕ × ℕ) (a b v d : ℝ)
    (hs : 0 < s) (hd : 0 < d) (hp : covers s p a) (hn : covers s n b)
    (hv : d * v = a - b) (hc : boxesCheck i p n = true) :
    if i % 2=0 then 0<v else v<0 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  by_cases h : i % 2 = 0
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

noncomputable def list0 : List (ℕ × ℝ) := [(736947257748, 9999999999999999520750031327),
  (10000000000000000843964726088, -9999999999999999897203436485),
  (20000000000000000840708641308, 9999999999999999892821043077),
  (50000000000000001019758195019, 10000000000000000000000107226)]
noncomputable def part0 : Polynomial ℝ := sparse list0

noncomputable def list1 : List (ℕ × ℝ) := [(176925648818, 9999999999999999075897721119),
  (30000000000000000333225025960, -9999999999999999576347784655),
  (50000000000000000748085347185, -9999999999999999499547274779),
  (80000000000000001019758207912, 10000000000000000000000000000)]
noncomputable def part1 : Polynomial ℝ := sparse list1

noncomputable def list2 : List (ℕ × ℝ) := [(913872923701, 9999999999999999619624482554),
  (10000000000000001020873160529, -9999999999999999995979238534),
  (20000000000000001019746657289, 10000000000000000000064300966),
  (30000000000000001019758207912, -10000000000000000000000000000)]
noncomputable def part2 : Polynomial ℝ := sparse list2

noncomputable def list3 : List (ℕ × ℝ) := [(0, 9999999999999998977023413820),
  (40000000000000000487689254562, 9999999999999999956573374039),
  (90000000000000001019758207912, -10000000000000000000000000000),
  (100000000000000001019758207912, -10000000000000000000000000000)]
noncomputable def part3 : Polynomial ℝ := sparse list3

noncomputable def P : Polynomial ℝ := part0 * part1 - part2 * part3

def count : ℕ := 23
def phase : ℕ := 0
def scale : ℕ := 100000000000000000000000000000000000000000000000000000000000000000000
def den : ℕ := 1
def samples : List ℕ :=
  [99999999999999999999999999940000000000000000000000000018000000000000,
  99999999999999999999999999945217391304347826086956521754136105860113,
  99999999999999999999999999950434782608695652173913043490544423440454,
  99999999999999999999999999955652173913043478260869565227224952741021,
  99999999999999999999999999960869565217391304347826086964177693761815,
  99999999999999999999999999966086956521739130434782608701402646502836,
  99999999999999999999999999971304347826086956521739130438899810964083,
  99999999999999999999999999976521739130434782608695652176669187145558,
  99999999999999999999999999981739130434782608695652173914710775047259,
  99999999999999999999999999986956521739130434782608695653024574669187,
  99999999999999999999999999992173913043478260869565217391610586011342,
  99999999999999999999999999997391304347826086956521739130468809073724,
  100000000000000000000000000002608695652173913043478260869599243856333,
  100000000000000000000000000007826086956521739130434782609001890359168,
  100000000000000000000000000013043478260869565217391304348676748582231,
  100000000000000000000000000018260869565217391304347826088623818525520,
  100000000000000000000000000023478260869565217391304347828843100189036,
  100000000000000000000000000028695652173913043478260869569334593572779,
  100000000000000000000000000033913043478260869565217391310098298676749,
  100000000000000000000000000039130434782608695652173913051134215500945,
  100000000000000000000000000044347826086956521739130434792442344045369,
  100000000000000000000000000049565217391304347826086956534022684310019,
  100000000000000000000000000054782608695652173913043478275875236294896,
  100000000000000000000000000060000000000000000000000000018000000000000]
def base (i : ℕ) : ℕ := samples.getD i 0
def posTerms : List (ℕ × ℕ) := [(99999999999999985966477524460000442875988204367159494913, 913872906566),
  (99999999999999989730026523540000004113144838332772139880, 10000000000000001020873160529),
  (99999999999999989687187641960000099044318340632831643163, 20000000000000001017634290126),
  (99999999999999989770234138200000000000000000000000000000, 30000000000000001019758207912),
  (99999999999999994735512211400000043549991862982750137675, 40000000000000001177189752048),
  (99999999999999990758978283449999999999900912209044705894, 50000000000000001196683843837),
  (99999999999999999525526125730000000174608104262384018826, 50000000000000001508562415091),
  (99999999999999993967507112640000051444820354435368911815, 60000000000000001592050073273),
  (99999999999999999565733740390000000000000000000000000000, 70000000000000001507447462474),
  (99999999999999995207500313270000000000000000000000000000, 80000000000000001756705465660),
  (99999999999999996196244825540000000000000000000000000000, 90000000000000001933631131613),
  (99999999999999998928210430770000000000000000000000000000, 100000000000000001860466849220),
  (99999999999999996196244825540000000000000000000000000000, 100000000000000001933631131613),
  (100000000000000000000643009660000000000000000000000000000, 110000000000000002039504865201),
  (100000000000000000000643009660000000000000000000000000000, 120000000000000002039504865201),
  (100000000000000000000001072260000000000000000000000000000, 130000000000000002039516402931)]
def negTerms : List (ℕ × ℕ) := [(99999999999999985966478963740000389115248303360112496280, 913872923701),
  (99999999999999989731011576040000094994538605346959626715, 10000000000000001020890374906),
  (99999999999999989770877147859999999934221617313243750120, 20000000000000001019746657289),
  (99999999999999990970978159820000203035310932338299887185, 30000000000000001070172283708),
  (99999999999999995761978565930000016518425320849272015606, 40000000000000001401562178263),
  (99999999999999994691688277320000045406602538795274583435, 50000000000000001173933667268),
  (99999999999999990202973061060000239841952884481727001733, 50000000000000001485032604933),
  (99999999999999999566376750049999999997207626000587021674, 60000000000000001507435911851),
  (99999999999999993923683178560000053638001078459514654983, 70000000000000001588793988493),
  (99999999999999995763478918809999999999954573467557417030, 80000000000000001352983220979),
  (99999999999999998972034364850000000000000000000000000000, 90000000000000001863722934000),
  (99999999999999994995473820049999999999946338456085453054, 100000000000000001767843542204),
  (99999999999999999959792385340000000000000000000000000000, 100000000000000002040631368441),
  (99999999999999999959792385340000000000000000000000000000, 110000000000000002040631368441),
  (100000000000000000000000000000000000000000000000000000000, 120000000000000002039516415824),
  (100000000000000000000000000000000000000000000000000000000, 130000000000000002039516415824)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma eval_eq (x : ℝ) : (den : ℝ) * P.eval x =
    weightedEval x posTerms - weightedEval x negTerms := by
  simp only [P, part0, part1, part2, part3, list0, list1, list2, list3, sparse,
    eval_mul, eval_add, eval_sub, eval_zero, eval_monomial, den, posTerms, negTerms,
    weightedEval, Nat.cast_ofNat, Nat.cast_one, ← pow_add]
  ring

noncomputable def point (i : ℕ) : ℝ := (base i : ℝ) / scale

def checkPoint (i : ℕ) : Bool :=
  boxesCheck (i + phase) (weightedBox scale (base i) posTerms)
    (weightedBox scale (base i) negTerms)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma points_checked : ∀ i : Fin (count + 1), checkPoint i.val = true := by decide +kernel

lemma pos_size : ∀ t ∈ posTerms, t.2 < 2^97 := by decide
lemma neg_size : ∀ t ∈ negTerms, t.2 < 2^97 := by decide

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

end PEqualNP.Outside.L_gct_273

theorem PEqualNP.Outside.L_gct_273 : ¬ (∀ p q r s : Polynomial ℝ, (p.support.card ≤ 4 ∧ q.support.card ≤ 4 ∧ r.support.card ≤ 4 ∧ s.support.card ≤ 4) → ((p * q - r * s).roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ 22) := by
  intro bound
  open PEqualNP.Outside.L_gct_273 in
  exact by
    have limit := bound part0 part1 part2 part3
      ⟨(sparse_card list0).trans (by decide), (sparse_card list1).trans (by decide),
        (sparse_card list2).trans (by decide), (sparse_card list3).trans (by decide)⟩
    change (P.roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ 22 at limit
    have lower := roots_lower
    norm_num [count] at lower
    omega
