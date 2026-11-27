import Mathlib

/-!
# Smolensky's degree bound for parity over `ZMod 3`, and the binomial tail

A block of the proof that parity is not in AC0 by the polynomial method (L-clb-007).
STATUS: helper statements and proofs; nothing here is a result until the checker accepts a
lemma that rests on it.

Conventions. A point of the cube is `x : Fin n → Bool`; it is read in `ZMod 3` as the 0/1
vector `embed x`. Parity is `OddWeight x`: the number of true coordinates is odd.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers.ParitySmol

open Finset

/-- The 0/1 vector of a point of the cube, in `ZMod 3`. -/
def embed {n : ℕ} (x : Fin n → Bool) : Fin n → ZMod 3 := fun i => if x i then 1 else 0

/-- The number of true coordinates of `x` is odd. -/
def OddWeight {n : ℕ} (x : Fin n → Bool) : Prop :=
  (Finset.univ.filter fun i => x i = true).card % 2 = 1

instance {n : ℕ} (x : Fin n → Bool) : Decidable (OddWeight x) := by
  unfold OddWeight; infer_instance

/-- Smolensky's bound. If a polynomial over `ZMod 3` of total degree at most `D` takes the
value 1 at the odd points and 0 at the even points of a set `A` of the cube, then `A` has at
most as many points as there are sets of at most `n / 2 + D` coordinates. -/
def StmtSmolensky : Prop :=
  ∀ (n D : ℕ) (P : MvPolynomial (Fin n) (ZMod 3)) (A : Finset (Fin n → Bool)),
    P.totalDegree ≤ D →
    (∀ x ∈ A, MvPolynomial.eval (embed x) P = if OddWeight x then 1 else 0) →
    A.card ≤ ∑ i ∈ Finset.range (n / 2 + D + 1), n.choose i

/-- The binomial tail: the sum of Smolensky's bound is at most half the cube plus `D + 1`
central coefficients. -/
def StmtBinomTail : Prop :=
  ∀ n D : ℕ, ∑ i ∈ Finset.range (n / 2 + D + 1), n.choose i ≤
    2 ^ (n - 1) + (D + 1) * n.choose (n / 2)

/-- The central coefficient is at most `2 ^ n / sqrt (n + 1)`, without division or roots. -/
def StmtCentral : Prop :=
  ∀ n : ℕ, n.choose (n / 2) ^ 2 * (n + 1) ≤ 4 ^ n

/-- The directly usable form: if `16 (D + 1)^2 ≤ n`, Smolensky's bound is at most three
quarters of the cube. -/
def StmtTailUsable : Prop :=
  ∀ n D : ℕ, 16 * (D + 1) ^ 2 ≤ n →
    4 * ∑ i ∈ Finset.range (n / 2 + D + 1), n.choose i ≤ 3 * 2 ^ n

/-! ## The binomial arithmetic -/

theorem central_sq (k : ℕ) : k.centralBinom ^ 2 * (2 * k + 1) ≤ 16 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Nat.succ_mul_centralBinom_succ k
    have hpos : 0 < (k + 1) ^ 2 := by positivity
    apply Nat.le_of_mul_le_mul_left _ hpos
    calc (k + 1) ^ 2 * ((k + 1).centralBinom ^ 2 * (2 * (k + 1) + 1))
        = ((k + 1) * (k + 1).centralBinom) ^ 2 * (2 * k + 3) := by ring
      _ = (2 * (2 * k + 1) * k.centralBinom) ^ 2 * (2 * k + 3) := by rw [h]
      _ = (k.centralBinom ^ 2 * (2 * k + 1)) * (4 * (2 * k + 1) * (2 * k + 3)) := by ring
      _ ≤ 16 ^ k * (16 * (k + 1) ^ 2) := by
          apply Nat.mul_le_mul ih; nlinarith
      _ = (k + 1) ^ 2 * 16 ^ (k + 1) := by ring

theorem central : StmtCentral := by
  intro n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h := central_sq k
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    have e : (2 * k) / 2 = k := by omega
    rw [e, pow_mul]; norm_num; exact h
  · have h := central_sq (k + 1)
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    have e : (2 * k + 1) / 2 = k := by omega
    have hc : (2 * (k + 1)).choose (k + 1) = 2 * (2 * k + 1).choose k := by
      have : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [this, Nat.choose_succ_succ', Nat.choose_symm_half]; ring
    rw [hc] at h
    rw [e]
    have e4 : (4 : ℕ) ^ (2 * k + 1) * 4 = 16 ^ (k + 1) := by
      rw [pow_succ, pow_mul]; norm_num; ring
    nlinarith [h, e4, Nat.zero_le ((2 * k + 1).choose k ^ 2)]

theorem half_sum (n : ℕ) :
    ∑ i ∈ Finset.range (n / 2 + 1), n.choose i ≤ 2 ^ (n - 1) + n.choose (n / 2) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have e : (2 * k) / 2 = k := by omega
    rw [e]
    cases k with
    | zero => simp
    | succ j =>
      have h1 := Nat.sum_range_choose_halfway j
      have h2 : ∑ i ∈ Finset.range (j + 2), (2 * j + 1).choose i =
          ∑ i ∈ Finset.range (j + 1), (2 * j + 1).choose (i + 1) + 1 := by
        rw [Finset.sum_range_succ']; simp
      have h3 : ∑ i ∈ Finset.range (j + 2), (2 * j + 1).choose i =
          4 ^ j + (2 * j + 1).choose (j + 1) := by
        rw [Finset.sum_range_succ, h1]
      have h4 : ∑ i ∈ Finset.range (j + 2), (2 * (j + 1)).choose i =
          ∑ i ∈ Finset.range (j + 1), (2 * j + 1).choose i +
            ∑ i ∈ Finset.range (j + 1), (2 * j + 1).choose (i + 1) + 1 := by
        rw [Finset.sum_range_succ', ← Finset.sum_add_distrib]
        have : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
        simp only [this, Nat.choose_succ_succ', Nat.choose_zero_right]
      have h5 : (2 * j + 1).choose (j + 1) ≤ (2 * (j + 1)).choose (j + 1) := by
        have : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
        rw [this]; exact Nat.choose_le_succ _ _
      have h6 : (2 : ℕ) ^ (2 * (j + 1) - 1) = 2 * 4 ^ j := by
        have : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
        rw [this, pow_succ, pow_mul]; norm_num; ring
      have h7 : j + 1 + 1 = j + 2 := rfl
      rw [h7, h4, h6]; omega
  · have e : (2 * k + 1) / 2 = k := by omega
    rw [e, Nat.sum_range_choose_halfway]
    have : (2 : ℕ) ^ (2 * k + 1 - 1) = 4 ^ k := by
      have : 2 * k + 1 - 1 = 2 * k := by omega
      rw [this, pow_mul]; norm_num
    omega

theorem binomTail : StmtBinomTail := by
  intro n D
  have h : n / 2 + D + 1 = (n / 2 + 1) + D := by ring
  rw [h, Finset.sum_range_add]
  have h2 : ∑ x ∈ Finset.range D, n.choose (n / 2 + 1 + x) ≤ D * n.choose (n / 2) := by
    calc ∑ x ∈ Finset.range D, n.choose (n / 2 + 1 + x)
        ≤ ∑ _x ∈ Finset.range D, n.choose (n / 2) :=
          Finset.sum_le_sum fun x _ => Nat.choose_le_middle _ _
      _ = D * n.choose (n / 2) := by simp
  have := half_sum n
  nlinarith

theorem tailUsable : StmtTailUsable := by
  intro n D hD
  have h1 := binomTail n D
  have hc := central n
  set c := n.choose (n / 2)
  have hsq : (4 * (D + 1) * c) ^ 2 ≤ (2 ^ n) ^ 2 := by
    have e : ((2 : ℕ) ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e]
    calc (4 * (D + 1) * c) ^ 2 = 16 * (D + 1) ^ 2 * c ^ 2 := by ring
      _ ≤ n * c ^ 2 := Nat.mul_le_mul_right _ hD
      _ ≤ c ^ 2 * (n + 1) := by nlinarith
      _ ≤ 4 ^ n := hc
  have h3 : 4 * (D + 1) * c ≤ 2 ^ n := by
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 hsq
  have hn : 1 ≤ n := by nlinarith
  have h4 : 4 * 2 ^ (n - 1) = 2 * 2 ^ n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]; ring
  nlinarith

/-! ## Smolensky's bound -/

section Smol

variable {n : ℕ}

/-- Functions on the cube with values in `ZMod 3`. -/
abbrev Fn (n : ℕ) := (Fin n → Bool) → ZMod 3

/-- The sign coordinate: `1` at false, `-1 = 2` at true. -/
def y (i : Fin n) : Fn n := fun x => if x i then 2 else 1

/-- The character of a set of coordinates. -/
def chi (U : Finset (Fin n)) : Fn n := ∏ i ∈ U, y i

/-- The span of the characters of sets of at most `d` coordinates. -/
def W (n d : ℕ) : Submodule (ZMod 3) (Fn n) :=
  Submodule.span (ZMod 3) (chi '' {U : Finset (Fin n) | U.card ≤ d})

theorem y_mul_y (i : Fin n) : y i * y i = 1 := by
  funext x
  simp only [Pi.mul_apply, y, Pi.one_apply]
  split_ifs <;> decide

theorem chi_mul_chi (U : Finset (Fin n)) : chi U * chi U = 1 := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => y_mul_y i

theorem W_mono {d e : ℕ} (h : d ≤ e) : W n d ≤ W n e :=
  Submodule.span_mono (Set.image_mono fun _ hU => le_trans hU h)

theorem chi_mem {d : ℕ} (U : Finset (Fin n)) (h : U.card ≤ d) : chi U ∈ W n d :=
  Submodule.subset_span ⟨U, h, rfl⟩

theorem y_mul_mem {d : ℕ} (i : Fin n) {w : Fn n} (hw : w ∈ W n d) : y i * w ∈ W n (d + 1) := by
  induction hw using Submodule.span_induction with
  | mem w h =>
    obtain ⟨U, hU, rfl⟩ := h
    have hU' : U.card ≤ d := hU
    by_cases hi : i ∈ U
    · have : y i * chi U = chi (U.erase i) := by
        unfold chi
        rw [← Finset.mul_prod_erase U _ hi, ← mul_assoc, y_mul_y, one_mul]
      rw [this]
      exact chi_mem _ (le_trans (Finset.card_erase_le) (by omega))
    · have : y i * chi U = chi (insert i U) := by
        unfold chi
        rw [Finset.prod_insert hi]
      rw [this]
      apply chi_mem
      rw [Finset.card_insert_of_notMem hi]
      omega
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha

/-- The 0/1 coordinate function. -/
def xf (i : Fin n) : Fn n := fun x => embed x i

theorem xf_eq (i : Fin n) : xf i = y i - 1 := by
  funext x
  simp only [xf, embed, y, Pi.sub_apply, Pi.one_apply]
  split_ifs <;> decide

theorem xf_mul_mem {d : ℕ} (i : Fin n) {w : Fn n} (hw : w ∈ W n d) :
    xf i * w ∈ W n (d + 1) := by
  rw [xf_eq, sub_mul, one_mul]
  exact sub_mem (y_mul_mem i hw) (W_mono (Nat.le_succ d) hw)

theorem lin_mul_mem {d : ℕ} (i : Fin n) (a b : ZMod 3) {w : Fn n} (hw : w ∈ W n d) :
    (a • (1 : Fn n) + b • y i) * w ∈ W n (d + 1) := by
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  exact add_mem (Submodule.smul_mem _ _ (W_mono (Nat.le_succ d) hw))
    (Submodule.smul_mem _ _ (y_mul_mem i hw))

theorem xpow_mul_mem {d : ℕ} (i : Fin n) (k : ℕ) {w : Fn n} (hw : w ∈ W n d) :
    xf i ^ k * w ∈ W n (d + k) := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    have : xf i ^ (k + 1) * w = xf i * (xf i ^ k * w) := by ring
    rw [this]
    exact xf_mul_mem i ih

theorem mono_mul_mem {d : ℕ} (e : Fin n → ℕ) (I : Finset (Fin n)) {w : Fn n}
    (hw : w ∈ W n d) : (∏ i ∈ I, xf i ^ e i) * w ∈ W n (d + ∑ i ∈ I, e i) := by
  induction I using Finset.induction_on with
  | empty => simpa using hw
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc]
    have := xpow_mul_mem a (e a) ih
    have h2 : d + ∑ i ∈ s, e i + e a = d + (e a + ∑ i ∈ s, e i) := by ring
    rw [h2] at this
    exact this

theorem linprod_mul_mem {d : ℕ} (a b : Fin n → ZMod 3) (I : Finset (Fin n)) {w : Fn n}
    (hw : w ∈ W n d) :
    (∏ i ∈ I, (a i • (1 : Fn n) + b i • y i)) * w ∈ W n (d + I.card) := by
  induction I using Finset.induction_on with
  | empty => simpa using hw
  | insert c s hc ih =>
    rw [Finset.prod_insert hc, Finset.card_insert_of_notMem hc, mul_assoc]
    exact lin_mul_mem c _ _ ih

theorem one_mem_W : (1 : Fn n) ∈ W n 0 := by
  have : (1 : Fn n) = chi ∅ := by simp [chi]
  rw [this]
  exact chi_mem _ (by simp)

theorem poly_mul_mem {d D : ℕ} (P : MvPolynomial (Fin n) (ZMod 3)) (hP : P.totalDegree ≤ D)
    {w : Fn n} (hw : w ∈ W n d) :
    (fun x => MvPolynomial.eval (embed x) P) * w ∈ W n (d + D) := by
  have h : (fun x => MvPolynomial.eval (embed x) P) =
      ∑ s ∈ P.support, P.coeff s • ∏ i, xf i ^ s i := by
    funext x
    rw [MvPolynomial.eval_eq']
    simp [Finset.sum_apply, Finset.prod_apply, xf]
  rw [h, Finset.sum_mul]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [smul_mul_assoc]
  refine Submodule.smul_mem _ _ ?_
  refine W_mono ?_ (mono_mul_mem (fun i => s i) Finset.univ hw)
  have := MvPolynomial.le_totalDegree hs
  have e : (s.sum fun _ k => k) = ∑ i, s i := Finsupp.sum_fintype _ _ (fun _ => rfl)
  omega

theorem delta_mem (a : Fin n → Bool) :
    (fun x => if x = a then (1 : ZMod 3) else 0) ∈ W n n := by
  have h : (fun x : Fin n → Bool => if x = a then (1 : ZMod 3) else 0) =
      (∏ i ∈ (Finset.univ : Finset (Fin n)),
        ((2 : ZMod 3) • (1 : Fn n) + (if a i then (1 : ZMod 3) else 2) • y i)) * 1 := by
    funext x
    have hf : ∀ i : Fin n, ((2 : ZMod 3) • (1 : Fn n) +
        (if a i then (1 : ZMod 3) else 2) • y i) x = if x i = a i then 1 else 0 := by
      intro i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, y, smul_eq_mul]
      cases x i <;> cases a i <;> decide
    rw [mul_one, Finset.prod_apply]
    simp only [hf]
    rw [Finset.prod_boole]
    simp [funext_iff]
  rw [h]
  have := linprod_mul_mem (fun _ => (2 : ZMod 3)) (fun i => if a i then (1 : ZMod 3) else 2)
    Finset.univ (one_mem_W (n := n))
  simpa using this

theorem all_mem (f : Fn n) : f ∈ W n n := by
  have h : f = ∑ a : Fin n → Bool, f a • (fun x => if x = a then (1 : ZMod 3) else 0) := by
    funext x
    simp [Finset.sum_apply]
  rw [h]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (delta_mem a)

theorem chi_univ_apply (x : Fin n → Bool) :
    chi (Finset.univ : Finset (Fin n)) x = if OddWeight x then 2 else 1 := by
  have h : chi (Finset.univ : Finset (Fin n)) x =
      (2 : ZMod 3) ^ (Finset.univ.filter fun i => x i = true).card := by
    simp only [chi, Finset.prod_apply, y]
    rw [Finset.prod_ite]
    simp
  rw [h]
  have h4 : (2 : ZMod 3) ^ 2 = 1 := by decide
  obtain ⟨k, hk⟩ : ∃ k, k = (Finset.univ.filter fun i => x i = true).card := ⟨_, rfl⟩
  have hd : k = 2 * (k / 2) + k % 2 := (Nat.div_add_mod k 2).symm
  rw [← hk]
  by_cases ho : OddWeight x
  · have ho' : k % 2 = 1 := by rw [hk]; exact ho
    rw [if_pos ho, hd, pow_add, pow_mul, h4, one_pow, one_mul, ho', pow_one]
  · have ho' : k % 2 = 0 := by
      have : ¬ k % 2 = 1 := by rw [hk]; exact ho
      omega
    rw [if_neg ho, hd, pow_add, pow_mul, h4, one_pow, one_mul, ho', pow_zero]

theorem finrank_W_le (m : ℕ) :
    Module.finrank (ZMod 3) (W n m) ≤ ∑ i ∈ Finset.range (m + 1), n.choose i := by
  classical
  let T : Finset (Finset (Fin n)) :=
    (Finset.range (m + 1)).biUnion fun i => Finset.powersetCard i Finset.univ
  have hT : (W n m) = Submodule.span (ZMod 3) ((T.image chi : Finset (Fn n)) : Set (Fn n)) := by
    unfold W
    congr 1
    ext f
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_image, Finset.mem_coe, T,
      Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ,
      true_and]
    constructor
    · rintro ⟨U, hU, rfl⟩
      exact ⟨U, ⟨U.card, by omega, rfl⟩, rfl⟩
    · rintro ⟨U, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨U, by omega, rfl⟩
  rw [hT]
  refine le_trans (finrank_span_finset_le_card _) ?_
  refine le_trans Finset.card_image_le ?_
  refine le_trans Finset.card_biUnion_le ?_
  simp

theorem smolensky : StmtSmolensky := by
  classical
  intro n D P A hP hA
  set m := n / 2 + D with hm
  let res : Fn n →ₗ[ZMod 3] (A → ZMod 3) :=
    LinearMap.funLeft (ZMod 3) (ZMod 3) (Subtype.val : A → (Fin n → Bool))
  have key : ∀ S : Finset (Fin n), res (chi S) ∈ (W n m).map res := by
    intro S
    by_cases hS : S.card ≤ m
    · exact Submodule.mem_map_of_mem (chi_mem S hS)
    · refine ⟨((1 : Fn n) + fun x => MvPolynomial.eval (embed x) P) * chi Sᶜ, ?_, ?_⟩
      · have hc : (Sᶜ).card ≤ n / 2 := by
          rw [Finset.card_compl, Fintype.card_fin]; omega
        have h1 : chi Sᶜ ∈ W n (Sᶜ).card := chi_mem _ le_rfl
        rw [add_mul, one_mul]
        refine add_mem (W_mono (by omega) h1) (W_mono (by omega) (poly_mul_mem P hP h1))
      · funext ⟨x, hx⟩
        have hu := chi_univ_apply x
        have hsplit : chi (Finset.univ : Finset (Fin n)) = chi S * chi Sᶜ := by
          unfold chi; rw [Finset.prod_mul_prod_compl]
        have hsq := congrFun (chi_mul_chi Sᶜ) x
        simp only [Pi.mul_apply, Pi.one_apply] at hsq
        have hval : (1 : ZMod 3) + MvPolynomial.eval (embed x) P = chi S x * chi Sᶜ x := by
          rw [hA x hx, ← Pi.mul_apply, ← hsplit, hu]
          split_ifs <;> decide
        show ((1 : Fn n) + fun x => MvPolynomial.eval (embed x) P) x * chi Sᶜ x = chi S x
        rw [Pi.add_apply, Pi.one_apply, hval, mul_assoc, hsq, mul_one]
  have surj : (W n m).map res = ⊤ := by
    rw [eq_top_iff]
    intro g _
    let f : Fn n := fun x => if h : x ∈ A then g ⟨x, h⟩ else 0
    have hf : res f = g := by
      funext ⟨x, hx⟩
      show f x = g ⟨x, hx⟩
      simp [f, hx]
    rw [← hf]
    have hle : (W n n).map res ≤ (W n m).map res := by
      show Submodule.map res (Submodule.span (ZMod 3) _) ≤ _
      rw [Submodule.map_span]
      apply Submodule.span_le.2
      rintro _ ⟨_, ⟨U, _, rfl⟩, rfl⟩
      exact key U
    exact hle (Submodule.mem_map_of_mem (all_mem f))
  have h1 : Module.finrank (ZMod 3) (A → ZMod 3) = A.card := by simp
  have h3 : Module.finrank (ZMod 3) ((W n m).map res) ≤ Module.finrank (ZMod 3) (W n m) :=
    Submodule.finrank_map_le _ _
  rw [surj, finrank_top, h1] at h3
  exact le_trans h3 (finrank_W_le m)

end Smol

end PEqualNP.CircuitLowerBounds.Helpers.ParitySmol
