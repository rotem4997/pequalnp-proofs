import PEqualNP.Defs
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Linarith

namespace PEqualNP.Outside.L_gct_253

open Polynomial

-- The interval certificate uses the fixed-point and IVT proofs of L-gct-251 and L-gct-261.
-- The five binomials use an overlapping reflected pair of three-binomial seeds,
-- after perturbing the coefficients and exponents. The original three-binomial seed
-- is due to XXXLUMI, PR 14351. The twenty rational samples alternate in sign.
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

noncomputable def list0 : List (ℕ × ℝ) := [(100031250, 1), (200031250, (-39 / 250000))]
noncomputable def part0 : Polynomial ℝ := sparse list0

noncomputable def list1 : List (ℕ × ℝ) := [(1024047, (3709739 / 25000000000)), (100000949, (-49999609 / 50000000))]
noncomputable def part1 : Polynomial ℝ := sparse list1

noncomputable def list2 : List (ℕ × ℝ) := [(68279181, (-41143927 / 500000000)), (132014381, (42050547 / 500000000))]
noncomputable def part2 : Polynomial ℝ := sparse list2

noncomputable def list3 : List (ℕ × ℝ) := [(299038453, (-8380621 / 12500000000000000000000)), (200061551, (15517229 / 100000000000))]
noncomputable def part3 : Polynomial ℝ := sparse list3

noncomputable def list4 : List (ℕ × ℝ) := [(231783319, (49083659 / 1000000000000000)), (168048119, (-35730751 / 10000000000))]
noncomputable def part4 : Polynomial ℝ := sparse list4

noncomputable def gs : Fin 5 → Polynomial ℝ := ![part0, part1, part2, part3, part4]

noncomputable def P : Polynomial ℝ :=
  (Finset.univ : Finset (Fin 5)).sum fun i => C (1 : ℝ) * gs i ^ 3

lemma gs_card (i : Fin 5) : (gs i).support.card ≤ 2 := by
  fin_cases i
  · exact (sparse_card list0).trans (by decide)
  · exact (sparse_card list1).trans (by decide)
  · exact (sparse_card list2).trans (by decide)
  · exact (sparse_card list3).trans (by decide)

  · exact (sparse_card list4).trans (by decide)

def count : ℕ := 19
def phase : ℕ := 0
def scale : ℕ := 100000000000000000000000000000000000000000000000000000000000000
def den : ℕ := 1953125000000000000000000000000000000000000000000000000000000000000
def samples : List ℕ := [99999988000000719999971200000863999979264000414719992890514392, 99999993000000244999994283333433374998599416683006805392154168, 99999995900000084049998851316678440670736786499826403362941383, 99999996900000048049999503483337181337476142374289931066259670, 99999998100000018049999885683333876337497936584173200816787820, 99999999200000003199999991466666683733333306026666703075555513, 100000000800000003200000008533333350400000027306666703075555597, 100000001900000018050000114316667209670835396749173200816823291, 100000003100000048050000496516670514670857190959289931067351440, 100000004100000084050001148683345107337596546834826403370669727, 100000013431310003429836274196343347500243927420759186374801876, 100000014431310142742936996726875207840497363592257629064172877, 100000015631310323118658777496297375568566221398314719654150984, 100000016731310501113073299679155338589876406294129442075803639, 100000018331310781614045527363117263786725118191312025291887306, 100000019431310989308462256344674873934376543189531504372374657, 100000020631311229684198555901237802234229929980183271036142694, 100000021631311440997308900974806052998519455151799112237766276, 100000024531312110355352192347139954892438607877203988371160098, 100000029531313461920990457588757960448624635522877367552907182]
def base (i : ℕ) : ℕ := samples.getD i 0
def posTerms : List (ℕ × ℕ) := [(6381754308483618802375000000000000000000000000000000000, 3072141), (869456479666148307005531250000000000000000000000000000000000000, 201025945), (3336755705985826745482640625000000000000000000000000000000000000, 268572743), (1953125000000000000000000000000000000000000000000000000000000000000, 300093750), (1161809637235123109645671875000000000000000000000000000000000000, 396043143), (142593750000000000000000000000000000000000000000000000000000, 500093750), (3671745006192580658183144531250000000000000000000000000, 567879557), (7297473847366671874978515625000000000000000000000000000, 600184653), (230962158574750551094099609375000000000000000, 695349957), (408693601826408455795875000000000, 798138457)]
def negTerms : List (ℕ × ℕ) := [(129019273387526584629187500000000000000000000000000000000000, 102049043), (1088271481017946636546609375000000000000000000000000000000000000, 204837543), (1953079180045813909742640625000000000000000000000000000000000000000, 300002847), (3410282218371503257206703125000000000000000000000000000000000000, 332307943), (914062500000000000000000000000000000000000000000000000000000000, 400093750), (89095644201912872567873046875000000000000000000000000000000, 504144357), (7414875000000000000000000000000000000000000000000000000, 600093750), (50439096513507235645916601562500000000000000000000, 631614757), (94590129573560214930984375000000000000000000, 699161555), (588611309752454223061, 897115359)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma eval_eq (x : ℝ) : (den : ℝ) * P.eval x =
    weightedEval x posTerms - weightedEval x negTerms := by
  simp only [P, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, gs, map_one, one_mul, part0, part1, part2, part3, part4, list0, list1, list2, list3, list4, sparse, eval_mul, eval_add,
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

end PEqualNP.Outside.L_gct_253

theorem PEqualNP.Outside.L_gct_253 :
    ¬ (∀ (s : Fin 5 → ℝ) (g : Fin 5 → Polynomial ℝ), (∀ i, s i = 1 ∨ s i = -1) → (∀ i, (g i).support.card ≤ 2) → ((((Finset.univ : Finset (Fin 5)).sum fun i => Polynomial.C (s i) * g i ^ 3)).roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ 17) := by
  intro h
  open PEqualNP.Outside.L_gct_253 in
  exact by
    have limit := h (fun _ => 1) gs (fun _ => Or.inl rfl) gs_card
    change (P.roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ 17 at limit
    have lower := roots_lower
    norm_num [count] at lower
    omega
