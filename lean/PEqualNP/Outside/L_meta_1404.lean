import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1404

abbrev F := (Fin 15 → Bool) → Bool

-- Bit vectors from predicates.

def bitsOf (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => bitsOf f n + (if f n then 2 ^ n else 0)

theorem bitsOf_lt (f : Nat → Bool) (n : Nat) : bitsOf f n < 2 ^ n := by
  induction n with
  | zero => simp [bitsOf]
  | succ n ih =>
    simp only [bitsOf]
    have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; ring
    split <;> omega

theorem testBit_bitsOf (f : Nat → Bool) (n i : Nat) :
    (bitsOf f n).testBit i = (decide (i < n) && f i) := by
  induction n generalizing i with
  | zero => simp [bitsOf]
  | succ n ih =>
    simp only [bitsOf]
    have hl := bitsOf_lt f n
    by_cases hf : f n = true
    · simp only [hf, ite_true]
      rw [Nat.add_comm]
      rcases Nat.lt_trichotomy i n with h | h | h
      · rw [Nat.testBit_two_pow_add_gt h, ih]
        simp [h, show i < n + 1 by omega]
      · subst h
        rw [Nat.testBit_two_pow_add_eq, ih]
        simp [hf]
      · have hlt : 2 ^ n + bitsOf f n < 2 ^ i := by
          have : 2 ^ (n + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
          have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; ring
          omega
        rw [Nat.testBit_lt_two_pow hlt]
        simp [show ¬ (i < n + 1) by omega]
    · have hf' : f n = false := by simpa using hf
      simp only [hf', Bool.false_eq_true, ite_false, Nat.add_zero]
      rw [ih]
      by_cases h : i < n
      · simp [h, show i < n + 1 by omega]
      · by_cases h' : i = n
        · subst h'; simp [hf']
        · simp [h, show ¬ (i < n + 1) by omega]

theorem bitsOf_congr (f g : Nat → Bool) (n : Nat) (h : ∀ i, i < n → f i = g i) :
    bitsOf f n = bitsOf g n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitsOf, testBit_bitsOf]
  by_cases hi : i < n
  · simp [hi, h i hi]
  · simp [hi]

-- Number of true values below n.
def cntBits (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cntBits f n + (f n).toNat

theorem cntBits_le (f : Nat → Bool) (n : Nat) : cntBits f n ≤ n := by
  induction n with
  | zero => simp [cntBits]
  | succ n ih => simp only [cntBits]; cases f n <;> simp <;> omega

theorem cntBits_mono (f g : Nat → Bool) (n : Nat) (h : ∀ i, i < n → f i = true → g i = true) :
    cntBits f n ≤ cntBits g n := by
  induction n with
  | zero => simp [cntBits]
  | succ n ih =>
    simp only [cntBits]
    have := ih (fun i hi => h i (by omega))
    have hn := h n (by omega)
    cases hf : f n <;> cases hg : g n <;> simp_all <;> omega

theorem cntBits_or_le (f g : Nat → Bool) (n : Nat) :
    cntBits (fun i => f i || g i) n ≤ cntBits f n + cntBits g n := by
  induction n with
  | zero => simp [cntBits]
  | succ n ih =>
    simp only [cntBits]
    cases hf : f n <;> cases hg : g n <;> simp_all <;> omega

theorem cntBits_congr (f g : Nat → Bool) (n : Nat) (h : ∀ i, i < n → f i = g i) :
    cntBits f n = cntBits g n := by
  induction n with
  | zero => simp [cntBits]
  | succ n ih => simp only [cntBits]; rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem cntBits_eq_full (f : Nat → Bool) (n : Nat) (h : cntBits f n = n) : ∀ i, i < n → f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    simp only [cntBits] at h
    have hle := cntBits_le f n
    cases hf : f n
    · simp [hf] at h; omega
    · simp [hf] at h
      intro i hi
      rcases Nat.lt_or_ge i n with h1 | h1
      · exact ih h i h1
      · have : i = n := by omega
        subst this; exact hf

theorem cntBits_full (f : Nat → Bool) (n : Nat) (h : ∀ i, i < n → f i = true) : cntBits f n = n := by
  induction n with
  | zero => simp [cntBits]
  | succ n ih => simp only [cntBits]; rw [ih (fun i hi => h i (by omega)), h n (by omega)]; simp

-- The 180 boundary inputs: 45 minimal true inputs, then 135 maximal false inputs.
def ptsPack : Nat := 0xfd297e52f4e76d4afa95b73b4b5796ad3dead2dda5abce5e94fd297e72b6a76d4afbd4adb95b53bcb569ead2dde52f4e5e94ffe52bea5796b7694fd29db5b95a7ab4e5ef4e56dcad3d6af297e52beb53b4b7694fde94eda9da5bd5a72f4e56dea5796af297fea53f4a7ab5b7297e52ddada9cbd396af796a76d4e5eb4f52bea53f5a5b95b7297ef296ed2dcade9cb5796a76f4a7ab4f52bff4a5f94bd39db52bea56dced2d5e5ab4f7ab4b7696af397a53f4a5f9cada9db52bef52b6e56d4ef2d5a7ab4b7794bd397a53ff94afa95e5adda53f4a76d6e569ead397bd395b72b4f5abca5f94afad4ed2dda53f7a53b6a7696f569cbd395b7a95e5abca5fc6208c0308862184411806218c03088231c60184411886208c030886218441180630c60184411886208c030886218441180630c60184411886208c030886218441180630c60184411886208c03088621844118063

def ptAt (p : Nat) : Nat := Nat.land (Nat.shiftRight ptsPack (15 * p)) 32767
def inp (p : Nat) : Fin 15 → Bool := fun i => (ptAt p).testBit i

-- Truth vector of a Boolean function on the boundary.
def tv (g : F) : Nat := bitsOf (fun p => g (inp p)) 180

theorem testBit_tv (g : F) (p : Nat) : (tv g).testBit p = (decide (p < 180) && g (inp p)) :=
  testBit_bitsOf _ _ _

theorem tv_lt (g : F) : tv g < 2 ^ 180 := bitsOf_lt _ _

theorem tv_and (g h : F) : tv (fun y => g y && h y) = tv g &&& tv h := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_tv, testBit_tv, testBit_tv]
  cases decide (i < 180) <;> simp

theorem tv_or (g h : F) : tv (fun y => g y || h y) = tv g ||| tv h := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, testBit_tv, testBit_tv, testBit_tv]
  cases decide (i < 180) <;> simp

-- Exact depth sets.
def DF : Nat → Set F
  | 0 => {g | ∃ i : Fin 15, g = fun x => x i}
  | k + 1 => {g | ∃ a ∈ DF k, ∃ b ∈ DF k, g = (fun y => a y && b y) ∨ g = (fun y => a y || b y)}

theorem DF_mono (k : Nat) (g : F) (hg : g ∈ DF k) : g ∈ DF (k + 1) :=
  ⟨g, hg, g, hg, Or.inl (funext fun y => by simp)⟩

-- Variable substitution.
def act (σ : Fin 15 → Fin 15) (g : F) : F := fun x => g (fun i => x (σ i))

theorem act_DF (σ : Fin 15 → Fin 15) : ∀ (k : Nat) (g : F), g ∈ DF k → act σ g ∈ DF k
  | 0, g, ⟨i, hi⟩ => ⟨σ i, by subst hi; rfl⟩
  | k + 1, g, ⟨a, ha, b, hb, h⟩ => by
    refine ⟨act σ a, act_DF σ k a ha, act σ b, act_DF σ k b hb, ?_⟩
    rcases h with h | h <;> subst h
    · exact Or.inl rfl
    · exact Or.inr rfl

-- Point maps compatible with a variable map.
def Compat (σ : Fin 15 → Fin 15) (π : Nat → Nat) : Prop :=
  ∀ p, p < 180 → π p < 180 ∧ inp (π p) = fun i => inp p (σ i)

def permP (π : Nat → Nat) (t : Nat) : Nat := bitsOf (fun p => t.testBit (π p)) 180

theorem testBit_permP (π : Nat → Nat) (t p : Nat) :
    (permP π t).testBit p = (decide (p < 180) && t.testBit (π p)) := testBit_bitsOf _ _ _

theorem permP_lt (π : Nat → Nat) (t : Nat) : permP π t < 2 ^ 180 := bitsOf_lt _ _

theorem tv_act (σ : Fin 15 → Fin 15) (π : Nat → Nat) (h : Compat σ π) (g : F) :
    tv (act σ g) = permP π (tv g) := by
  apply bitsOf_congr
  intro p hp
  obtain ⟨h1, h2⟩ := h p hp
  rw [testBit_tv]
  simp only [h1, decide_true, Bool.true_and]
  simp only [act]
  rw [h2]

theorem permP_and (π : Nat → Nat) (s t : Nat) : permP π (s &&& t) = permP π s &&& permP π t := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_permP, testBit_permP, testBit_permP, Nat.testBit_and]
  cases decide (i < 180) <;> simp

theorem permP_or (π : Nat → Nat) (s t : Nat) : permP π (s ||| t) = permP π s ||| permP π t := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, testBit_permP, testBit_permP, testBit_permP, Nat.testBit_or]
  cases decide (i < 180) <;> simp

-- Packed fields: field i (width w) holds f i.
def pk (f : Nat → Nat) (w : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 ^ (w * n) * f n + pk f w n

def Fits (f : Nat → Nat) (w n : Nat) : Prop := ∀ i, i < n → f i < 2 ^ w

theorem pk_lt (f : Nat → Nat) (w n : Nat) (h : Fits f w n) : pk f w n < 2 ^ (w * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    simp only [pk]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 : f n + 1 ≤ 2 ^ w := h n (by omega)
    have h3 : 2 ^ (w * (n + 1)) = 2 ^ (w * n) * 2 ^ w := by rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    rw [h3]
    have h4 : 2 ^ (w * n) * (f n + 1) ≤ 2 ^ (w * n) * 2 ^ w := Nat.mul_le_mul_left _ h2
    rw [Nat.mul_add, Nat.mul_one] at h4
    omega

theorem testBit_pk (f : Nat → Nat) (w n : Nat) (h : Fits f w n) (i j : Nat) (hj : j < w) :
    (pk f w n).testBit (w * i + j) = (decide (i < n) && (f i).testBit j) := by
  induction n with
  | zero =>
    simp [pk]
  | succ n ih =>
    simp only [pk]
    have hl := pk_lt f w n (fun k hk => h k (by omega))
    rw [Nat.testBit_two_pow_mul_add _ hl]
    have hfn : f n < 2 ^ w := h n (by omega)
    rcases Nat.lt_trichotomy i n with hi | hi | hi
    · have : w * i + j < w * n := by
        have : w * (i + 1) ≤ w * n := Nat.mul_le_mul_left _ hi
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      simp only [this, ite_true]
      rw [ih (fun k hk => h k (by omega))]
      simp [hi, show i < n + 1 by omega]
    · subst hi
      have : ¬ (w * i + j < w * i) := by omega
      simp only [this, ite_false]
      simp [show w * i + j - w * i = j by omega]
    · have hge : w * (n + 1) ≤ w * i := Nat.mul_le_mul_left _ hi
      have : ¬ (w * i + j < w * n) := by
        rw [Nat.mul_add, Nat.mul_one] at hge; omega
      simp only [this, ite_false]
      have hb : w ≤ w * i + j - w * n := by rw [Nat.mul_add, Nat.mul_one] at hge; omega
      have hlt : f n < 2 ^ (w * i + j - w * n) :=
        lt_of_lt_of_le hfn (Nat.pow_le_pow_right (by norm_num) hb)
      rw [Nat.testBit_lt_two_pow hlt]
      simp [show ¬ (i < n + 1) by omega]

-- Every bit position, for w > 0.
theorem testBit_pk' (f : Nat → Nat) (w n : Nat) (hw : 0 < w) (h : Fits f w n) (k : Nat) :
    (pk f w n).testBit k = (decide (k / w < n) && (f (k / w)).testBit (k % w)) := by
  have hk : k = w * (k / w) + k % w := (Nat.div_add_mod k w).symm
  conv_lhs => rw [hk]
  exact testBit_pk f w n h (k / w) (k % w) (Nat.mod_lt k hw)

theorem pk_congr (f g : Nat → Nat) (w n : Nat) (h : ∀ i, i < n → f i = g i) : pk f w n = pk g w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pk]; rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem pk_add (f g : Nat → Nat) (w n : Nat) : pk f w n + pk g w n = pk (fun i => f i + g i) w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pk]; rw [← ih]; ring

theorem pk_sub (f g : Nat → Nat) (w n : Nat) (h : ∀ i, i < n → g i ≤ f i) :
    pk f w n - pk g w n = pk (fun i => f i - g i) w n := by
  have e := pk_add (fun i => f i - g i) g w n
  have e2 : pk (fun i => f i - g i + g i) w n = pk f w n := pk_congr _ _ _ _ (fun i hi => by have := h i hi; omega)
  omega

theorem pk_mul (c : Nat) (f : Nat → Nat) (w n : Nat) : c * pk f w n = pk (fun i => c * f i) w n := by
  induction n with
  | zero => simp [pk]
  | succ n ih => simp only [pk]; rw [← ih]; ring

theorem Fits_land (f g : Nat → Nat) (w n : Nat) (hg : Fits g w n) : Fits (fun i => f i &&& g i) w n :=
  fun i hi => Nat.and_lt_two_pow _ (hg i hi)

theorem pk_land (f g : Nat → Nat) (w n : Nat) (hw : 0 < w) (hf : Fits f w n) (hg : Fits g w n) :
    pk f w n &&& pk g w n = pk (fun i => f i &&& g i) w n := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, testBit_pk' f w n hw hf, testBit_pk' g w n hw hg,
    testBit_pk' _ w n hw (Fits_land f g w n hg), Nat.testBit_and]
  cases decide (k / w < n) <;> simp

theorem pk_lor (f g : Nat → Nat) (w n : Nat) (hw : 0 < w) (hf : Fits f w n) (hg : Fits g w n) :
    pk f w n ||| pk g w n = pk (fun i => f i ||| g i) w n := by
  apply Nat.eq_of_testBit_eq
  intro k
  have hfg : Fits (fun i => f i ||| g i) w n := fun i hi => Nat.or_lt_two_pow (hf i hi) (hg i hi)
  rw [Nat.testBit_or, testBit_pk' f w n hw hf, testBit_pk' g w n hw hg,
    testBit_pk' _ w n hw hfg, Nat.testBit_or]
  cases decide (k / w < n) <;> simp

theorem pk_xor (f g : Nat → Nat) (w n : Nat) (hw : 0 < w) (hf : Fits f w n) (hg : Fits g w n) :
    pk f w n ^^^ pk g w n = pk (fun i => f i ^^^ g i) w n := by
  apply Nat.eq_of_testBit_eq
  intro k
  have hfg : Fits (fun i => f i ^^^ g i) w n := fun i hi => Nat.xor_lt_two_pow (hf i hi) (hg i hi)
  rw [Nat.testBit_xor, testBit_pk' f w n hw hf, testBit_pk' g w n hw hg,
    testBit_pk' _ w n hw hfg, Nat.testBit_xor]
  cases decide (k / w < n) <;> simp

-- Shift inside fields, then mask: bits never cross field borders.
theorem pk_shr_mask (f : Nat → Nat) (w n s m : Nat) (hw : 0 < w) (hf : Fits f w n) (hm : m < 2 ^ (w - s)) :
    (pk f w n >>> s) &&& pk (fun _ => m) w n = pk (fun i => (f i >>> s) &&& m) w n := by
  have hmw : m < 2 ^ w := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
  have hm' : Fits (fun _ => m) w n := fun _ _ => hmw
  have hr : Fits (fun i => (f i >>> s) &&& m) w n := fun i _ => Nat.and_lt_two_pow _ hmw
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_pk' _ w n hw hm', testBit_pk' _ w n hw hr,
    Nat.testBit_and, Nat.testBit_shiftRight]
  by_cases hj : k % w < w - s
  · have hk : s + k = w * (k / w) + (s + k % w) := by
      have := Nat.div_add_mod k w; omega
    rw [hk, testBit_pk f w n hf (k / w) (s + k % w) (by omega)]
    cases decide (k / w < n) <;> simp
  · have : m.testBit (k % w) = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [this]

-- Shift by whole fields.
theorem pk_shr_fields (f : Nat → Nat) (w n t : Nat) (hw : 0 < w) (hf : Fits f w n) :
    pk f w n >>> (w * t) = pk (fun i => f (i + t)) w (n - t) := by
  have hr : Fits (fun i => f (i + t)) w (n - t) := fun i hi => hf (i + t) (by omega)
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_shiftRight, testBit_pk' _ w _ hw hr]
  have e : w * t + k = w * (k / w + t) + k % w := by
    have := Nat.div_add_mod k w; rw [Nat.mul_add]; omega
  rw [e, testBit_pk f w n hf _ _ (Nat.mod_lt k hw)]
  by_cases h : k / w + t < n
  · simp [h, show k / w < n - t by omega]
  · have h2 : ¬ (k / w < n - t) := by clear e; generalize k / w = q at *; omega
    simp [h, h2]

-- Field extraction.
theorem pk_field (f : Nat → Nat) (w n i : Nat) (hw : 0 < w) (hf : Fits f w n) (hi : i < n) :
    (pk f w n >>> (w * i)) % 2 ^ w = f i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hj : j < w
  · rw [testBit_pk f w n hf i j hj]; simp [hj, hi]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf i hi) (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [hj]

-- Count of set bits of x in [lo, lo + len).
def cntR (x lo : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cntR x lo n + (x.testBit (lo + n)).toNat

theorem cntR_le (x lo n : Nat) : cntR x lo n ≤ n := by
  induction n with
  | zero => simp [cntR]
  | succ n ih => simp only [cntR]; cases x.testBit (lo + n) <;> simp <;> omega

theorem cntR_add (x lo a b : Nat) : cntR x lo (a + b) = cntR x lo a + cntR x (lo + a) b := by
  induction b with
  | zero => simp [cntR]
  | succ b ih => rw [← Nat.add_assoc, cntR, ih, cntR, Nat.add_assoc lo a b]; ring

theorem cntR_one (x lo : Nat) : cntR x lo 1 = (x.testBit lo).toNat := by simp [cntR]

-- A number below 2^N is the packing of its bits.
theorem pk_bits (x N : Nat) (hx : x < 2 ^ N) : pk (fun i => cntR x i 1) 1 N = x := by
  apply Nat.eq_of_testBit_eq
  intro k
  have hf : Fits (fun i => cntR x i 1) 1 N := fun i _ => by
    have := cntR_le x i 1; simp only [Nat.pow_one]; omega
  rw [testBit_pk' _ 1 N (by norm_num) hf k]
  simp only [Nat.div_one, Nat.mod_one, cntR_one]
  by_cases hk : k < N
  · simp only [hk, decide_true, Bool.true_and]
    cases x.testBit k <;> simp
  · simp only [hk, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

-- Merging two adjacent fields into one of double width.
theorem pk_merge2 (f : Nat → Nat) (w n : Nat) :
    pk f w (2 * n) = pk (fun j => f (2 * j) + 2 ^ w * f (2 * j + 1)) (2 * w) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, pk, pk, ih, pk]
    have e1 : 2 ^ (w * (2 * n + 1)) = 2 ^ (2 * w * n) * 2 ^ w := by
      rw [← Nat.pow_add]; congr 1; ring
    have e2 : 2 ^ (w * (2 * n)) = 2 ^ (2 * w * n) := by congr 1; ring
    rw [e1, e2]
    ring

-- One step of the pairwise-sum popcount: fields of width w become fields of width 2w.
theorem pk_pairsum (x w n : Nat) (hw : 0 < w) :
    let X := pk (fun j => cntR x (w * j) w) w (2 * n)
    let M := pk (fun _ => 2 ^ w - 1) (2 * w) n
    (X &&& M) + ((X >>> w) &&& M) = pk (fun j => cntR x (2 * w * j) (2 * w)) (2 * w) n := by
  intro X M
  have hcnt : ∀ j, cntR x (w * j) w < 2 ^ w := fun j =>
    lt_of_le_of_lt (cntR_le x _ w) (Nat.lt_two_pow_self)
  have hX : X = pk (fun j => cntR x (w * (2 * j)) w + 2 ^ w * cntR x (w * (2 * j + 1)) w) (2 * w) n := by
    simp only [X]; rw [pk_merge2]
  have h2w : 0 < 2 * w := by omega
  have hfit : Fits (fun j => cntR x (w * (2 * j)) w + 2 ^ w * cntR x (w * (2 * j + 1)) w) (2 * w) n := by
    intro j _
    have a := hcnt (2 * j); have b := hcnt (2 * j + 1)
    have : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [← Nat.pow_add]; congr 1; ring
    rw [this]
    calc cntR x (w * (2 * j)) w + 2 ^ w * cntR x (w * (2 * j + 1)) w
        < 2 ^ w + 2 ^ w * cntR x (w * (2 * j + 1)) w := by omega
      _ = 2 ^ w * (cntR x (w * (2 * j + 1)) w + 1) := by ring
      _ ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_left _ (by omega)
  have hmf : Fits (fun _ => 2 ^ w - 1) (2 * w) n := fun _ _ => by
    show 2 ^ w - 1 < 2 ^ (2 * w)
    have : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.two_pow_pos w
    omega
  have hlo : X &&& M = pk (fun j => cntR x (w * (2 * j)) w) (2 * w) n := by
    rw [hX, pk_land _ _ _ _ h2w hfit hmf]
    apply pk_congr; intro j _
    rw [Nat.and_two_pow_sub_one_eq_mod]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hcnt _)]
  have hhi : (X >>> w) &&& M = pk (fun j => cntR x (w * (2 * j + 1)) w) (2 * w) n := by
    rw [hX, pk_shr_mask _ (2 * w) n w (2 ^ w - 1) h2w hfit (by
      rw [show 2 * w - w = w by omega]; have := Nat.two_pow_pos w; omega)]
    apply pk_congr; intro j _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt (hcnt _), Nat.zero_add]
    exact Nat.mod_eq_of_lt (hcnt _)
  rw [hlo, hhi, pk_add]
  apply pk_congr; intro j _
  rw [show 2 * w * j = w * (2 * j) by ring, show 2 * w = w + w by ring, cntR_add]
  congr 2

def pstep (X M w : Nat) : Nat := Nat.add (Nat.land X M) (Nat.land (Nat.shiftRight X w) M)

def Q1 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def Q2 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def Q4 : Nat := 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def Q8 : Nat := 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def Q16 : Nat := 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def Q32 : Nat := 0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def Q64 : Nat := 0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff
def Q128 : Nat := 0xffffffffffffffffffffffffffffffff

-- popcount of x < 2^256
def popc256 (x : Nat) : Nat :=
  pstep (pstep (pstep (pstep (pstep (pstep (pstep (pstep x Q1 1) Q2 2) Q4 4) Q8 8) Q16 16) Q32 32) Q64 64) Q128 128

set_option maxRecDepth 10000 in
theorem Q1_eq : Q1 = pk (fun _ => 2 ^ 1 - 1) (2 * 1) 128 := by decide +kernel
set_option maxRecDepth 10000 in
theorem Q2_eq : Q2 = pk (fun _ => 2 ^ 2 - 1) (2 * 2) 64 := by decide +kernel
set_option maxRecDepth 10000 in
theorem Q4_eq : Q4 = pk (fun _ => 2 ^ 4 - 1) (2 * 4) 32 := by decide +kernel
set_option maxRecDepth 10000 in
theorem Q8_eq : Q8 = pk (fun _ => 2 ^ 8 - 1) (2 * 8) 16 := by decide +kernel
set_option maxRecDepth 10000 in
theorem Q16_eq : Q16 = pk (fun _ => 2 ^ 16 - 1) (2 * 16) 8 := by decide +kernel
set_option maxRecDepth 10000 in
theorem Q32_eq : Q32 = pk (fun _ => 2 ^ 32 - 1) (2 * 32) 4 := by decide +kernel
set_option maxRecDepth 10000 in
theorem Q64_eq : Q64 = pk (fun _ => 2 ^ 64 - 1) (2 * 64) 2 := by decide +kernel
set_option maxRecDepth 10000 in
theorem Q128_eq : Q128 = pk (fun _ => 2 ^ 128 - 1) (2 * 128) 1 := by decide +kernel

theorem pstep_eq (x w n : Nat) (hw : 0 < w) (M : Nat) (hM : M = pk (fun _ => 2 ^ w - 1) (2 * w) n) :
    pstep (pk (fun j => cntR x (w * j) w) w (2 * n)) M w = pk (fun j => cntR x (2 * w * j) (2 * w)) (2 * w) n := by
  subst hM
  exact pk_pairsum x w n hw

theorem pk_one (f : Nat → Nat) (w : Nat) : pk f w 1 = f 0 := by simp [pk]

theorem popc256_eq (x : Nat) (hx : x < 2 ^ 256) : popc256 x = cntR x 0 256 := by
  have h0 : pk (fun j => cntR x (1 * j) 1) 1 (2 * 128) = x := by
    conv_rhs => rw [← pk_bits x 256 hx]
    exact pk_congr _ _ _ _ (fun i _ => by simp)
  unfold popc256
  conv_lhs => rw [← h0]
  rw [pstep_eq x 1 128 (by norm_num) Q1 Q1_eq]
  rw [show pk (fun j => cntR x (2 * 1 * j) (2 * 1)) (2 * 1) 128 = pk (fun j => cntR x (2 * j) 2) 2 (2 * 64) by rfl]
  rw [pstep_eq x 2 64 (by norm_num) Q2 Q2_eq]
  rw [show pk (fun j => cntR x (2 * 2 * j) (2 * 2)) (2 * 2) 64 = pk (fun j => cntR x (4 * j) 4) 4 (2 * 32) by rfl]
  rw [pstep_eq x 4 32 (by norm_num) Q4 Q4_eq]
  rw [show pk (fun j => cntR x (2 * 4 * j) (2 * 4)) (2 * 4) 32 = pk (fun j => cntR x (8 * j) 8) 8 (2 * 16) by rfl]
  rw [pstep_eq x 8 16 (by norm_num) Q8 Q8_eq]
  rw [show pk (fun j => cntR x (2 * 8 * j) (2 * 8)) (2 * 8) 16 = pk (fun j => cntR x (16 * j) 16) 16 (2 * 8) by rfl]
  rw [pstep_eq x 16 8 (by norm_num) Q16 Q16_eq]
  rw [show pk (fun j => cntR x (2 * 16 * j) (2 * 16)) (2 * 16) 8 = pk (fun j => cntR x (32 * j) 32) 32 (2 * 4) by rfl]
  rw [pstep_eq x 32 4 (by norm_num) Q32 Q32_eq]
  rw [show pk (fun j => cntR x (2 * 32 * j) (2 * 32)) (2 * 32) 4 = pk (fun j => cntR x (64 * j) 64) 64 (2 * 2) by rfl]
  rw [pstep_eq x 64 2 (by norm_num) Q64 Q64_eq]
  rw [show pk (fun j => cntR x (2 * 64 * j) (2 * 64)) (2 * 64) 2 = pk (fun j => cntR x (128 * j) 128) 128 (2 * 1) by rfl]
  rw [pstep_eq x 128 1 (by norm_num) Q128 Q128_eq]
  rw [pk_one]

theorem cntR_shift (x s lo n : Nat) : cntR (x >>> s) lo n = cntR x (s + lo) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [cntR, ih, Nat.testBit_shiftRight, Nat.add_assoc]

theorem cntR_zero_above (x lo n : Nat) (hx : x < 2 ^ lo) : cntR x lo n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cntR, ih]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rfl

-- Masks of the two sides.
def MA : Nat := 2 ^ 45 - 1
def MV : Nat := 2 ^ 180 - 2 ^ 45
def rect (t : Nat) : Nat := t ^^^ MV

-- Accepted minterms and rejected maxterms.
def cA (t : Nat) : Nat := cntR t 0 45
def cB (t : Nat) : Nat := cntR (rect t) 45 135

def popA (t : Nat) : Nat := popc256 (Nat.land t MA)
def popB (t : Nat) : Nat := popc256 (Nat.shiftRight (rect t) 45)

theorem cntR_congr (x y lo n : Nat) (h : ∀ i, lo ≤ i → i < lo + n → x.testBit i = y.testBit i) :
    cntR x lo n = cntR y lo n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [cntR]; rw [ih (fun i h1 h2 => h i h1 (by omega)), h (lo + n) (by omega) (by omega)]

theorem popA_eq (t : Nat) : popA t = cA t := by
  unfold popA cA
  have hlt : Nat.land t MA < 2 ^ 256 :=
    lt_of_lt_of_le (Nat.and_lt_two_pow t (show MA < 2 ^ 45 by unfold MA; omega)) (by norm_num)
  have hz : cntR (Nat.land t MA) (0 + 45) 211 = 0 :=
    cntR_zero_above _ _ _ (Nat.and_lt_two_pow t (show MA < 2 ^ 45 by unfold MA; omega))
  rw [popc256_eq _ hlt, show (256 : Nat) = 45 + 211 by rfl, cntR_add, hz, Nat.add_zero]
  apply cntR_congr
  intro i _ hi
  change (t &&& MA).testBit i = t.testBit i
  rw [Nat.testBit_and]
  have : MA.testBit i = true := by
    unfold MA
    rw [Nat.testBit_two_pow_sub_one]; simp; omega
  simp [this]

theorem popB_eq (t : Nat) (ht : t < 2 ^ 180) : popB t = cB t := by
  unfold popB cB
  have hr : rect t < 2 ^ 180 := Nat.xor_lt_two_pow ht (by unfold MV; omega)
  have hs : Nat.shiftRight (rect t) 45 < 2 ^ 256 := by
    show rect t >>> 45 < 2 ^ 256
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le hr (by norm_num))
  rw [popc256_eq _ hs]
  show cntR (rect t >>> 45) 0 256 = cntR (rect t) 45 135
  have hz : cntR (rect t) (45 + 135) 121 = 0 := cntR_zero_above _ _ _ (show rect t < 2 ^ (45 + 135) from hr)
  rw [cntR_shift, show (256 : Nat) = 135 + 121 by rfl, cntR_add, Nat.add_zero, hz, Nat.add_zero]

-- The 19 symmetry stages: reflection, rotations by 1, 2, 4, and three local transpositions per vertex.
def genVpack : Nat := 0xedcba48765932109dcbae876543210edcba4876593210edcba9376548210e8cba9d76543210edcba9376548210edcba9826543710ed7ba98c6543210edcba9826543710edcba9871543260edc6a987b543210edcba9871543260edcba9876043215edcb59876a43210edcba9876043215dcbae8765932104baedc6598710432aedcb5987604321bcdea6789512340
def genPpack : Nat := 0xb3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7b7c7a7879777576747273716f706e6c6d6b696a6866676563646260615f5d5e5c5a5b595758565455535152504e4f4d4b4c4a4849474546444243413f403e3c3d3b393a3836373533343230312f2d2e2928272c2b2a2625242223211f201e1c1d1b1a191817161514131211100f0e0d0c0b0a09080706050403020100b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7c7d7b797a7876777573747270716f6d6e6c6a6b696768666465636162605e5f5d5b5c5a5859575556545253514f504e4c4d4b494a4846474543444240413f3d3e3c3a3b393738363435333132302e2f2d2c2b2a262524292827232122201e1f1d1b1c1a191817161514131211100f0e0d0c0b0a09080706050403020100b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7b7c7a7879777576747273716f706e6c6d6b696a6866676563646260615f5d5e5c5a5b595758565455535152504e4f4d4b4c4a4849474546444243413f403e3c3d3b393a3836373533343230312f2d2e2928272c2b2a2625242223211f201e1c1d1b1a191817161514131211100f0e0d0c0b0a09080706050403020100b3b1b2b0aeafadabacaaa8a9a7a5a6a4a2a3a19fa09e9c9d9b999a9896979593949290918f8d8e8c8a8b898788868485838182807e7f7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464541403f4443423e3d3c3837363b3a393534332f2e2d3231302c2b2a292827262524201f1e2322211d1c1b191a1816171513141211100f0e0d0c0b0a09080706050403020100b2b3b1afb0aeacadaba9aaa8a6a7a5a3a4a2a0a19f9d9e9c9a9b999798969495939192908e8f8d8b8c8a8889878586848283817f807e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494844434247464541403f3b3a393e3d3c3837363231303534332f2e2d2c2b2a2928272625242322211d1c1b201f1e1a181917151614121311100f0e0d0c0b0a09080706050403020100b3b1b2b0aeafadabacaaa8a9a7a5a6a4a2a3a19fa09e9c9d9b999a9896979593949290918f8d8e8c8a8b898788868485838182807e7f7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464541403f4443423e3d3c3837363b3a393534332f2e2d3231302c2b2a292827262524201f1e2322211d1c1b191a1816171513141211100f0e0d0c0b0a09080706050403020100b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969291909594938f8e8d8988878c8b8a868584807f7e8382817d7c7b7776757a79787473726e6d6c71706f6b6a696564636867666261605c5b5a5f5e5d595857535251565554504f4e4a49484d4c4b47464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1716151a191814131210110f0d0e0c0a0b09080706050403020100b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999594939897969291908c8b8a8f8e8d898887838281868584807f7e7a79787d7c7b77767571706f7473726e6d6c6867666b6a696564635f5e5d6261605c5b5a5655545958575352514d4c4b504f4e4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a1918141312171615110f100e0c0d0b090a080706050403020100b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969291909594938f8e8d8988878c8b8a868584807f7e8382817d7c7b7776757a79787473726e6d6c71706f6b6a696564636867666261605c5b5a5f5e5d595857535251565554504f4e4a49484d4c4b47464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1716151a191814131210110f0d0e0c0a0b09080706050403020100b3b2b1adacabb0afaeaaa9a8a4a3a2a7a6a5a1a09f9b9a999e9d9c9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a504f4e4d4c4b4a494859585756555453525147464544434241403f3534333231302f2e2d3e3d3c3b3a393837362c2b2a292827262524232221201f1e1d1c1b1a19181716151413120e0d0c11100f0b0a09070806040503010200b0afaeb3b2b1adacaba7a6a5aaa9a8a4a3a29e9d9ca1a09f9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564635958575655545352516261605f5e5d5c5b5a504f4e4d4c4b4a49483e3d3c3b3a3938373647464544434241403f3534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0b0a090e0d0c080607050304020001b3b2b1adacabb0afaeaaa9a8a4a3a2a7a6a5a1a09f9b9a999e9d9c9897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a504f4e4d4c4b4a494859585756555453525147464544434241403f3534333231302f2e2d3e3d3c3b3a393837362c2b2a292827262524232221201f1e1d1c1b1a19181716151413120e0d0c11100f0b0a09070806040503010200b3b2b1b0afaeadacaba1a09f9e9d9c9b9a99aaa9a8a7a6a5a4a3a2989796959493929190868584838281807f7e8f8e8d8c8b8a8988877d7c7b7a79787776756b6a6968676665646374737271706f6e6d6c6261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2b2c2a282927252624232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09050403080706020100aaa9a8a7a6a5a4a3a2b3b2b1b0afaeadacaba1a09f9e9d9c9b9a998f8e8d8c8b8a898887989796959493929190868584838281807f7e74737271706f6e6d6c7d7c7b7a79787776756b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2a2b292728262425232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706020100050403b3b2b1b0afaeadacaba1a09f9e9d9c9b9a99aaa9a8a7a6a5a4a3a2989796959493929190868584838281807f7e8f8e8d8c8b8a8988877d7c7b7a79787776756b6a6968676665646374737271706f6e6d6c6261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2b2c2a282927252624232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090504030807060201006261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2db3aaa1b2a9a0b1a89fb0a79eafa69daea59cada49baca39aaba299988f86978e85968d84958c83948b82938a8192898091887f90877e7d746b7c736a7b72697a7168797067786f66776e65766d64756c630807060504030201002c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09473e35463d34453c33443b32433a3142393041382f40372e3f362db3b0adaaa7a4a19e9bb2afaca9a6a3a09d9ab1aeaba8a5a29f9c999895928f8c898683809794918e8b8885827f9693908d8a8784817e7d7a7774716e6b68657c797673706d6a67647b7875726f6c696663625f5c595653504d4a615e5b5855524f4c49605d5a5754514e4b481a191817161514131211100f0e0d0c0b0a090807060504030201002c2b2a292827262524232221201f1e1d1c1b7d7a7774716e6b68657c797673706d6a67647b7875726f6c696663625f5c595653504d4a615e5b5855524f4c49605d5a5754514e4b484744413e3b3835322f4643403d3a3734312e45423f3c393633302db3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201002c2b2a2928272625247d7a777c79767b787574716e73706d726f6c6b68656a67646966639895929794919693908f8c898e8b888d8a8786838085827f84817eb3b0adb2afacb1aeabaaa7a4a9a6a3a8a5a2a19e9ba09d9a9f9c99473e35443b3241382f463d34433a3140372e453c334239303f362d6259505f564d5c534a61584f5e554c5b524960574e5d544b5a5148080502070401060300110e0b100d0a0f0c091a171419161318151223201d221f1c211e1b2c29262b28252a2724

def gV (k i : Nat) : Nat := Nat.land (Nat.shiftRight genVpack (60 * k + 4 * i)) 15
def gP (k p : Nat) : Nat := Nat.land (Nat.shiftRight genPpack (1440 * k + 8 * p)) 255

def genV (k : Nat) : Fin 15 → Fin 15 := fun i => if k < 19 then ⟨gV k i.val % 15, Nat.mod_lt _ (by norm_num)⟩ else i
def genP (k : Nat) : Nat → Nat := fun p => if k < 19 then gP k p else p

def pull (k z : Nat) : Nat := bitsOf (fun i => z.testBit (gV k i)) 15

def allBelow (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j acc => acc && p j) n

theorem allBelow_spec (n : Nat) (p : Nat → Bool) (h : allBelow n p = true) : ∀ j, j < n → p j = true := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    intro j hj
    rcases Nat.lt_or_ge j n with h1 | h1
    · exact ih h.1 j h1
    · have : j = n := by omega
      subst this; exact h.2

def genCheck : Bool :=
  allBelow 19 (fun k => allBelow 180 (fun p =>
    Nat.blt (gP k p) 180 && (Nat.blt p 45 == Nat.blt (gP k p) 45) && (gV k 0 < 15 && gV k 1 < 15 && gV k 2 < 15 &&
      gV k 3 < 15 && gV k 4 < 15 && gV k 5 < 15 && gV k 6 < 15 && gV k 7 < 15 && gV k 8 < 15 && gV k 9 < 15 &&
      gV k 10 < 15 && gV k 11 < 15 && gV k 12 < 15 && gV k 13 < 15 && gV k 14 < 15) &&
    (ptAt (gP k p) == pull k (ptAt p))))

set_option maxRecDepth 100000 in
theorem genCheck_ok : genCheck = true := by decide +kernel

theorem gV_lt (k : Nat) (hk : k < 19) (i : Nat) (hi : i < 15) : gV k i < 15 := by
  have h := allBelow_spec _ _ (allBelow_spec _ _ genCheck_ok k hk) 0 (by norm_num)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  interval_cases i <;> simp_all

theorem genP_lt (k : Nat) (p : Nat) (hp : p < 180) : genP k p < 180 := by
  unfold genP
  by_cases hk : k < 19
  · have h := allBelow_spec _ _ (allBelow_spec _ _ genCheck_ok k hk) p hp
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    simp only [hk, if_true]; exact h.1.1.1
  · simp only [hk, if_false]; exact hp

theorem genP_side (k : Nat) (p : Nat) (hp : p < 180) : (p < 45 ↔ genP k p < 45) := by
  unfold genP
  by_cases hk : k < 19
  · have h := allBelow_spec _ _ (allBelow_spec _ _ genCheck_ok k hk) p hp
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have h2 : Nat.blt p 45 = Nat.blt (gP k p) 45 := h.1.1.2
    have e1 : (Nat.blt p 45 = true) ↔ p < 45 := by rw [Nat.blt_eq]
    have e2 : (Nat.blt (gP k p) 45 = true) ↔ gP k p < 45 := by rw [Nat.blt_eq]
    simp only [hk, if_true]; rw [← e1, ← e2, h2]
  · simp only [hk, if_false]

theorem gen_compat (k : Nat) : Compat (genV k) (genP k) := by
  intro p hp
  refine ⟨genP_lt k p hp, ?_⟩
  by_cases hk : k < 19
  · have h := allBelow_spec _ _ (allBelow_spec _ _ genCheck_ok k hk) p hp
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have he := h.2
    funext i
    simp only [inp, genP, genV, hk, if_true]
    rw [he, pull, testBit_bitsOf]
    have hi := i.isLt
    simp only [hi, decide_true, Bool.true_and]
    rw [Nat.mod_eq_of_lt (gV_lt k hk i.val hi)]
  · funext i
    simp only [genP, genV, hk, if_false]
-- Words of generators, applied left to right.
def actW : List Nat → F → F
  | [], g => g
  | k :: w, g => actW w (act (genV k) g)

def permW : List Nat → Nat → Nat
  | [], t => t
  | k :: w, t => permW w (permP (genP k) t)

theorem tv_actW (w : List Nat) (g : F) : tv (actW w g) = permW w (tv g) := by
  induction w generalizing g with
  | nil => rfl
  | cons k w ih => simp only [actW, permW]; rw [ih, tv_act _ _ (gen_compat k)]

theorem actW_DF (w : List Nat) (k : Nat) (g : F) (hg : g ∈ DF k) : actW w g ∈ DF k := by
  induction w generalizing g with
  | nil => exact hg
  | cons a w ih => exact ih _ (act_DF _ _ _ hg)

theorem permW_and (w : List Nat) (s t : Nat) : permW w (s &&& t) = permW w s &&& permW w t := by
  induction w generalizing s t with
  | nil => rfl
  | cons k w ih => simp only [permW]; rw [permP_and, ih]

theorem permW_or (w : List Nat) (s t : Nat) : permW w (s ||| t) = permW w s ||| permW w t := by
  induction w generalizing s t with
  | nil => rfl
  | cons k w ih => simp only [permW]; rw [permP_or, ih]

theorem permW_append (w1 w2 : List Nat) (t : Nat) : permW (w1 ++ w2) t = permW w2 (permW w1 t) := by
  induction w1 generalizing t with
  | nil => rfl
  | cons k w ih => simp only [List.cons_append, permW]; rw [ih]

theorem permW_lt (w : List Nat) (t : Nat) (ht : t < 2 ^ 180) : permW w t < 2 ^ 180 := by
  induction w generalizing t with
  | nil => exact ht
  | cons k w ih => simp only [permW]; exact ih _ (permP_lt _ _)

theorem testBit_permW_ge (w : List Nat) (t : Nat) (ht : t < 2 ^ 180) (p : Nat) (hp : 180 ≤ p) :
    (permW w t).testBit p = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (permW_lt w t ht) (Nat.pow_le_pow_right (by norm_num) hp))

-- Domination of rectangles, stated on truth vectors.
def dom (t s : Nat) : Prop :=
  ∀ p, p < 180 → (p < 45 → t.testBit p = true → s.testBit p = true) ∧ (45 ≤ p → s.testBit p = true → t.testBit p = true)

theorem dom_refl (t : Nat) : dom t t := fun _ _ => ⟨fun _ h => h, fun _ h => h⟩

theorem dom_trans {t s u : Nat} (h1 : dom t s) (h2 : dom s u) : dom t u := fun p hp =>
  ⟨fun hl ht => (h2 p hp).1 hl ((h1 p hp).1 hl ht), fun hl hu => (h1 p hp).2 hl ((h2 p hp).2 hl hu)⟩

theorem dom_and {t1 s1 t2 s2 : Nat} (h1 : dom t1 s1) (h2 : dom t2 s2) : dom (t1 &&& t2) (s1 &&& s2) := by
  intro p hp
  simp only [Nat.testBit_and, Bool.and_eq_true]
  exact ⟨fun hl ht => ⟨(h1 p hp).1 hl ht.1, (h2 p hp).1 hl ht.2⟩, fun hl hs => ⟨(h1 p hp).2 hl hs.1, (h2 p hp).2 hl hs.2⟩⟩

theorem dom_or {t1 s1 t2 s2 : Nat} (h1 : dom t1 s1) (h2 : dom t2 s2) : dom (t1 ||| t2) (s1 ||| s2) := by
  intro p hp
  simp only [Nat.testBit_or, Bool.or_eq_true]
  refine ⟨fun hl ht => ?_, fun hl hs => ?_⟩
  · rcases ht with ht | ht
    · exact Or.inl ((h1 p hp).1 hl ht)
    · exact Or.inr ((h2 p hp).1 hl ht)
  · rcases hs with hs | hs
    · exact Or.inl ((h1 p hp).2 hl hs)
    · exact Or.inr ((h2 p hp).2 hl hs)

-- Index map of a word: bit p of permW w t is bit (idxW w p) of t.
def idxW : List Nat → Nat → Nat
  | [], p => p
  | k :: w, p => genP k (idxW w p)

theorem idxW_lt (w : List Nat) (p : Nat) (hp : p < 180) : idxW w p < 180 := by
  induction w with
  | nil => exact hp
  | cons k w ih => exact genP_lt k _ ih

theorem idxW_side (w : List Nat) (p : Nat) (hp : p < 180) : (p < 45 ↔ idxW w p < 45) := by
  induction w with
  | nil => exact Iff.rfl
  | cons k w ih => exact ih.trans (genP_side k _ (idxW_lt w p hp))

theorem testBit_permW (w : List Nat) (t p : Nat) (hp : p < 180) :
    (permW w t).testBit p = t.testBit (idxW w p) := by
  induction w generalizing t with
  | nil => rfl
  | cons k w ih =>
    simp only [permW, idxW]
    rw [ih, testBit_permP]
    simp [idxW_lt w p hp]

theorem dom_permW (w : List Nat) {t s : Nat} (h : dom t s) : dom (permW w t) (permW w s) := by
  intro p hp
  rw [testBit_permW w t p hp, testBit_permW w s p hp]
  have hq := idxW_lt w p hp
  have hs := idxW_side w p hp
  exact ⟨fun hl ht => (h _ hq).1 (hs.1 hl) ht, fun hl h2 => (h _ hq).2 (by have := hs.2; omega) h2⟩

theorem permW_ext (w1 w2 : List Nat) (t : Nat) (ht : t < 2 ^ 180)
    (h : ∀ p, p < 180 → idxW w1 p = idxW w2 p) : permW w1 t = permW w2 t := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 180
  · rw [testBit_permW _ _ _ hp, testBit_permW _ _ _ hp, h p hp]
  · rw [testBit_permW_ge _ _ ht p (by omega), testBit_permW_ge _ _ ht p (by omega)]

theorem permW_id (w : List Nat) (t : Nat) (ht : t < 2 ^ 180) (h : ∀ p, p < 180 → idxW w p = p) :
    permW w t = t := by
  exact permW_ext w [] t ht h

-- Inverse words.
def invG (k : Nat) : List Nat :=
  if k = 1 then [3] else if k = 2 then [1, 2] else if k = 3 then [1] else [k]

def invW : List Nat → List Nat
  | [] => []
  | k :: w => invW w ++ invG k

theorem idxW_append (w1 w2 : List Nat) (p : Nat) : idxW (w1 ++ w2) p = idxW w1 (idxW w2 p) := by
  induction w1 with
  | nil => rfl
  | cons k w ih => simp only [List.cons_append, idxW, ih]

set_option maxRecDepth 100000 in
theorem invChk_ok : allBelow 19 (fun k => allBelow 180 (fun p => idxW ([k] ++ invG k) p == p && idxW (invG k ++ [k]) p == p)) = true := by
  decide +kernel

theorem idxW_invG (k p : Nat) (hp : p < 180) : idxW ([k] ++ invG k) p = p := by
  by_cases hk : k < 19
  · have := allBelow_spec _ _ (allBelow_spec _ _ invChk_ok k hk) p hp
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  · simp [invG, idxW, genP, show ¬ k = 1 by omega, show ¬ k = 2 by omega, show ¬ k = 3 by omega, hk]

theorem idxW_invG' (k p : Nat) (hp : p < 180) : idxW (invG k ++ [k]) p = p := by
  by_cases hk : k < 19
  · have := allBelow_spec _ _ (allBelow_spec _ _ invChk_ok k hk) p hp
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.2
  · simp [invG, idxW, genP, show ¬ k = 1 by omega, show ¬ k = 2 by omega, show ¬ k = 3 by omega, hk]

theorem idxW_inv (w : List Nat) (p : Nat) (hp : p < 180) : idxW (w ++ invW w) p = p := by
  induction w generalizing p with
  | nil => rfl
  | cons k w ih =>
    simp only [invW, List.cons_append]
    rw [idxW, ← List.append_assoc, idxW_append, ih _ (idxW_lt _ p hp)]
    have := idxW_invG k p hp
    simpa [idxW] using this

theorem permW_inv (w : List Nat) (t : Nat) (ht : t < 2 ^ 180) : permW (invW w) (permW w t) = t := by
  rw [← permW_append]
  exact permW_id _ _ ht (fun p hp => idxW_inv w p hp)
theorem idxW_inv' (w : List Nat) (p : Nat) (hp : p < 180) : idxW (invW w ++ w) p = p := by
  induction w generalizing p with
  | nil => rfl
  | cons k w ih =>
    simp only [invW]
    rw [show invW w ++ invG k ++ k :: w = invW w ++ (invG k ++ [k]) ++ w by simp]
    rw [idxW_append, idxW_append, idxW_invG' k _ (idxW_lt w p hp), ← idxW_append, ih p hp]

theorem cntR_card (x lo n : Nat) :
    cntR x lo n = ((Finset.range n).filter (fun i => x.testBit (lo + i) = true)).card := by
  induction n with
  | zero => simp [cntR]
  | succ n ih =>
    rw [cntR, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : x.testBit (lo + n) = true
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
      simp [h]
    · rw [if_neg h]
      have : x.testBit (lo + n) = false := by simpa using h
      simp [this]

-- Counting is invariant under a bijection of index ranges.
theorem cntR_bij (x y lo1 lo2 n : Nat) (f g : Nat → Nat)
    (hf : ∀ i, i < n → lo2 ≤ f (lo1 + i) ∧ f (lo1 + i) < lo2 + n)
    (hg : ∀ i, i < n → lo1 ≤ g (lo2 + i) ∧ g (lo2 + i) < lo1 + n)
    (hgf : ∀ i, i < n → g (f (lo1 + i)) = lo1 + i)
    (hfg : ∀ i, i < n → f (g (lo2 + i)) = lo2 + i)
    (hxy : ∀ i, i < n → x.testBit (lo1 + i) = y.testBit (f (lo1 + i))) :
    cntR x lo1 n = cntR y lo2 n := by
  rw [cntR_card, cntR_card]
  apply Finset.card_bij' (fun i _ => f (lo1 + i) - lo2) (fun j _ => g (lo2 + j) - lo1)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    have := hf i hi.1
    refine ⟨by omega, ?_⟩
    rw [show lo2 + (f (lo1 + i) - lo2) = f (lo1 + i) by omega, ← hxy i hi.1]; exact hi.2
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    have := hg j hj.1
    refine ⟨by omega, ?_⟩
    rw [show lo1 + (g (lo2 + j) - lo1) = g (lo2 + j) by omega]
    have e := hxy (g (lo2 + j) - lo1) (by omega)
    rw [show lo1 + (g (lo2 + j) - lo1) = g (lo2 + j) by omega, hfg j hj.1] at e
    rw [e]; exact hj.2
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have := hf i hi.1
    rw [show lo2 + (f (lo1 + i) - lo2) = f (lo1 + i) by omega, hgf i hi.1]; omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    have := hg j hj.1
    rw [show lo1 + (g (lo2 + j) - lo1) = g (lo2 + j) by omega, hfg j hj.1]; omega

theorem cA_permW (w : List Nat) (t : Nat) : cA (permW w t) = cA t := by
  unfold cA
  apply cntR_bij _ _ 0 0 45 (idxW w) (idxW (invW w))
  · intro i hi
    simp only [Nat.zero_add]
    have := (idxW_side w i (by omega)).1 (by omega); omega
  · intro i hi
    simp only [Nat.zero_add]
    have := (idxW_side (invW w) i (by omega)).1 (by omega); omega
  · intro i hi; simp only [Nat.zero_add]; rw [← idxW_append]; exact idxW_inv' w i (by omega)
  · intro i hi; simp only [Nat.zero_add]; rw [← idxW_append]; exact idxW_inv w i (by omega)
  · intro i hi; simp only [Nat.zero_add]; exact testBit_permW w t i (by omega)

theorem testBit_MV (p : Nat) : MV.testBit p = (decide (45 ≤ p) && decide (p < 180)) := by
  unfold MV
  have : (2 : Nat) ^ 180 - 2 ^ 45 = 2 ^ 45 * (2 ^ 135 - 1) := by norm_num
  rw [this, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
  by_cases h1 : 45 ≤ p
  · by_cases h2 : p < 180
    · simp [h1, h2, show p - 45 < 135 by omega]
    · simp [h1, h2, show ¬ (p - 45 < 135) by omega]
  · simp [h1]

theorem cB_permW (w : List Nat) (t : Nat) : cB (permW w t) = cB t := by
  unfold cB
  apply cntR_bij _ _ 45 45 135 (idxW w) (idxW (invW w))
  · intro i hi
    have h1 := idxW_lt w (45 + i) (by omega)
    have := (idxW_side w (45 + i) (by omega)); omega
  · intro i hi
    have h1 := idxW_lt (invW w) (45 + i) (by omega)
    have := (idxW_side (invW w) (45 + i) (by omega)); omega
  · intro i hi; rw [← idxW_append]; exact idxW_inv' w _ (by omega)
  · intro i hi; rw [← idxW_append]; exact idxW_inv w _ (by omega)
  · intro i hi
    have hq := idxW_lt w (45 + i) (by omega)
    have hs := idxW_side w (45 + i) (by omega)
    simp only [rect, Nat.testBit_xor, testBit_MV]
    rw [testBit_permW w t _ (by omega)]
    simp [show 45 ≤ 45 + i by omega, show 45 + i < 180 by omega, hq, show 45 ≤ idxW w (45 + i) by omega]

theorem cA_mono {t s : Nat} (h : dom t s) : cA t ≤ cA s := by
  unfold cA
  rw [cntR_card, cntR_card]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_add] at hi ⊢
  exact ⟨hi.1, (h i (by omega)).1 hi.1 hi.2⟩

theorem cB_mono {t s : Nat} (h : dom t s) : cB t ≤ cB s := by
  unfold cB
  rw [cntR_card, cntR_card]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  refine ⟨hi.1, ?_⟩
  have hd := (h (45 + i) (by omega)).2 (by omega)
  simp only [rect, Nat.testBit_xor, testBit_MV] at hi ⊢
  simp only [show 45 ≤ 45 + i by omega, show 45 + i < 180 by omega, decide_true, Bool.and_self,
    Bool.xor_true, Bool.not_eq_true'] at hi ⊢
  cases hs : s.testBit (45 + i)
  · rfl
  · rw [hd hs] at hi; exact absurd hi (by simp)

-- ===== primitive helpers for kernel computations =====
def tb (x i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight x i) 1) 1

theorem tb_eq (x i : Nat) : tb x i = x.testBit i := by
  have h : Nat.land (Nat.shiftRight x i) 1 = (x >>> i) % 2 := Nat.and_one_is_mod _
  have e : x.testBit i = (x >>> i).testBit 0 := by simp
  unfold tb
  rw [h, e, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one (x >>> i) with h2 | h2 <;> rw [h2] <;> rfl

def fld (P w i : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.mul w i)) (Nat.sub (Nat.shiftLeft 1 w) 1)

theorem fld_eq (P w i : Nat) : fld P w i = (P >>> (w * i)) % 2 ^ w := by
  unfold fld
  rw [show Nat.shiftLeft 1 w = 2 ^ w by simp [Nat.shiftLeft_eq]]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem fld_pk (f : Nat → Nat) (w n i : Nat) (hw : 0 < w) (hf : Fits f w n) (hi : i < n) :
    fld (pk f w n) w i = f i := by
  rw [fld_eq]; exact pk_field f w n i hw hf hi

theorem fld_lt (P w i : Nat) : fld P w i < 2 ^ w := by
  rw [fld_eq]; exact Nat.mod_lt _ (by positivity)

-- ===== gates and formulas =====
def gate (b : Bool) (x y : Nat) : Nat := cond b (Nat.lor x y) (Nat.land x y)
def bop (b : Bool) (x y : Bool) : Bool := cond b (x || y) (x && y)
def fv (x : Nat) : Fin 15 := ⟨x % 15, Nat.mod_lt _ (by norm_num)⟩

theorem testBit_gate (b : Bool) (x y p : Nat) : (gate b x y).testBit p = bop b (x.testBit p) (y.testBit p) := by
  cases b
  · show (x &&& y).testBit p = (x.testBit p && y.testBit p); exact Nat.testBit_and _ _ _
  · show (x ||| y).testBit p = (x.testBit p || y.testBit p); exact Nat.testBit_or _ _ _

theorem bop_ff (b : Bool) : bop b false false = false := by cases b <;> rfl

theorem tv_bop (b : Bool) (g h : F) : tv (fun z => bop b (g z) (h z)) = gate b (tv g) (tv h) := by
  cases b
  · exact tv_and g h
  · exact tv_or g h

theorem bop_DF (b : Bool) (k : Nat) (g h : F) (hg : g ∈ DF k) (hh : h ∈ DF k) :
    (fun z => bop b (g z) (h z)) ∈ DF (k + 1) := by
  refine ⟨g, hg, h, hh, ?_⟩
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem gate_lt (b : Bool) (x y : Nat) (hx : x < 2 ^ 180) (hy : y < 2 ^ 180) : gate b x y < 2 ^ 180 := by
  cases b
  · exact lt_of_le_of_lt Nat.and_le_left hx
  · exact Nat.or_lt_two_pow hx hy

theorem dom_gate (b : Bool) {t1 s1 t2 s2 : Nat} (h1 : dom t1 s1) (h2 : dom t2 s2) :
    dom (gate b t1 t2) (gate b s1 s2) := by
  cases b
  · exact dom_and h1 h2
  · exact dom_or h1 h2

theorem permW_gate (w : List Nat) (b : Bool) (s t : Nat) : permW w (gate b s t) = gate b (permW w s) (permW w t) := by
  cases b
  · exact permW_and w s t
  · exact permW_or w s t

-- variable columns
def VP : Nat := pk (fun x => bitsOf (fun p => (ptAt p).testBit x) 180) 180 15
def mask180 : Nat := Nat.sub (Nat.shiftLeft 1 180) 1
def varAt (x : Nat) : Nat := Nat.land (Nat.shiftRight VP (Nat.mul 180 (Nat.mod x 15))) mask180

theorem tv_var (x : Nat) : tv (fun z => z (fv x)) = varAt x := by
  have h1 : varAt x = fld VP 180 (x % 15) := rfl
  rw [h1, VP, fld_pk _ _ _ _ (by norm_num) (fun i _ => bitsOf_lt _ _) (Nat.mod_lt _ (by norm_num))]
  rfl

-- four-leaf formulas (depth two)
def F2 (code : Nat) (lf : Nat → Nat) : F := fun z =>
  bop (tb code 0) (bop (tb code 1) (z (fv (lf 0))) (z (fv (lf 1)))) (bop (tb code 2) (z (fv (lf 2))) (z (fv (lf 3))))

def evalT2 (code : Nat) (lf : Nat → Nat) : Nat :=
  gate (tb code 0) (gate (tb code 1) (varAt (lf 0)) (varAt (lf 1))) (gate (tb code 2) (varAt (lf 2)) (varAt (lf 3)))

theorem tv_F2 (code : Nat) (lf : Nat → Nat) : tv (F2 code lf) = evalT2 code lf := by
  apply Nat.eq_of_testBit_eq; intro p
  simp only [evalT2, testBit_gate, ← tv_var, testBit_tv]
  by_cases hp : p < 180
  · simp only [hp, decide_true, Bool.true_and]; rfl
  · simp only [hp, decide_false, Bool.false_and, bop_ff]

theorem var_DF (x : Nat) : (fun z : Fin 15 → Bool => z (fv x)) ∈ DF 0 := ⟨fv x, rfl⟩

theorem F2_DF (code : Nat) (lf : Nat → Nat) : F2 code lf ∈ DF 2 :=
  bop_DF _ _ _ _ (bop_DF _ _ _ _ (var_DF _) (var_DF _)) (bop_DF _ _ _ _ (var_DF _) (var_DF _))

-- eight-leaf formulas (depth three)
def FH (code : Nat) (lf : Nat → Nat) : F := fun z =>
  bop (tb code 0)
    (bop (tb code 1) (bop (tb code 3) (z (fv (lf 0))) (z (fv (lf 1)))) (bop (tb code 4) (z (fv (lf 2))) (z (fv (lf 3)))))
    (bop (tb code 2) (bop (tb code 5) (z (fv (lf 4))) (z (fv (lf 5)))) (bop (tb code 6) (z (fv (lf 6))) (z (fv (lf 7)))))

def evalHv (code : Nat) (col : Nat → Nat) : Nat :=
  gate (tb code 0)
    (gate (tb code 1) (gate (tb code 3) (col 0) (col 1)) (gate (tb code 4) (col 2) (col 3)))
    (gate (tb code 2) (gate (tb code 5) (col 4) (col 5)) (gate (tb code 6) (col 6) (col 7)))

theorem tv_FH (code : Nat) (lf : Nat → Nat) : tv (FH code lf) = evalHv code (fun j => varAt (lf j)) := by
  apply Nat.eq_of_testBit_eq; intro p
  simp only [evalHv, testBit_gate, ← tv_var, testBit_tv]
  by_cases hp : p < 180
  · simp only [hp, decide_true, Bool.true_and]; rfl
  · simp only [hp, decide_false, Bool.false_and, bop_ff]

theorem FH_DF (code : Nat) (lf : Nat → Nat) : FH code lf ∈ DF 3 :=
  bop_DF _ _ _ _ (bop_DF _ _ _ _ (bop_DF _ _ _ _ (var_DF _) (var_DF _)) (bop_DF _ _ _ _ (var_DF _) (var_DF _)))
    (bop_DF _ _ _ _ (bop_DF _ _ _ _ (var_DF _) (var_DF _)) (bop_DF _ _ _ _ (var_DF _) (var_DF _)))

-- renaming leaves
theorem fv_val (i : Fin 15) : fv i.val = i := by
  apply Fin.ext; simp [fv, Nat.mod_eq_of_lt i.isLt]

theorem act_F2 (s : Nat → Nat) (code : Nat) (lf : Nat → Nat) (h : ∀ j, j < 4 → lf j < 15) :
    act (fun i => fv (s i.val)) (F2 code lf) = F2 code (fun j => s (lf j)) := by
  funext z
  simp only [act, F2, fv, Nat.mod_eq_of_lt (h 0 (by norm_num)), Nat.mod_eq_of_lt (h 1 (by norm_num)),
    Nat.mod_eq_of_lt (h 2 (by norm_num)), Nat.mod_eq_of_lt (h 3 (by norm_num))]

theorem act_FH (s : Nat → Nat) (code : Nat) (lf : Nat → Nat) (h : ∀ j, j < 8 → lf j < 15) :
    act (fun i => fv (s i.val)) (FH code lf) = FH code (fun j => s (lf j)) := by
  funext z
  simp only [act, FH, fv, Nat.mod_eq_of_lt (h 0 (by norm_num)), Nat.mod_eq_of_lt (h 1 (by norm_num)),
    Nat.mod_eq_of_lt (h 2 (by norm_num)), Nat.mod_eq_of_lt (h 3 (by norm_num)),
    Nat.mod_eq_of_lt (h 4 (by norm_num)), Nat.mod_eq_of_lt (h 5 (by norm_num)),
    Nat.mod_eq_of_lt (h 6 (by norm_num)), Nat.mod_eq_of_lt (h 7 (by norm_num))]

-- ===== group elements as variable maps =====
def gVf (k x : Nat) : Nat := if k < 19 then gV k x % 15 else x

def sig : List Nat → Nat → Nat
  | [], x => x
  | k :: w, x => sig w (gVf k x)

theorem gVf_lt (k x : Nat) (hx : x < 15) : gVf k x < 15 := by
  unfold gVf; split
  · exact Nat.mod_lt _ (by norm_num)
  · exact hx

theorem sig_lt (w : List Nat) (x : Nat) (hx : x < 15) : sig w x < 15 := by
  induction w generalizing x with
  | nil => exact hx
  | cons k w ih => exact ih _ (gVf_lt k x hx)

theorem sig_append (w1 w2 : List Nat) (x : Nat) : sig (w1 ++ w2) x = sig w2 (sig w1 x) := by
  induction w1 generalizing x with
  | nil => rfl
  | cons k w ih => simp only [List.cons_append, sig]; rw [ih]

theorem genV_val (k : Nat) (i : Fin 15) : (genV k i).val = gVf k i.val := by
  unfold genV gVf; split <;> rfl

theorem actW_sig (w : List Nat) (g : F) : actW w g = act (fun i => fv (sig w i.val)) g := by
  induction w generalizing g with
  | nil => funext z; simp only [actW, act, sig, fv_val]
  | cons k w ih =>
    simp only [actW]; rw [ih]
    funext z
    simp only [act, sig, genV_val]

theorem act_congr (s1 s2 : Nat → Nat) (h : ∀ x, x < 15 → s1 x = s2 x) (g : F) :
    act (fun i => fv (s1 i.val)) g = act (fun i => fv (s2 i.val)) g := by
  funext z; simp only [act]; congr 1; funext i; rw [h i.val i.isLt]

-- ===== dihedral-local normal form =====
def permTab : Nat := 36 + (24 <<< 6) + (33 <<< 12) + (9 <<< 18) + (18 <<< 24) + (6 <<< 30)
def permAt (p k : Nat) : Nat := Nat.land (Nat.shiftRight permTab (Nat.mul 2 (Nat.add (Nat.mul 3 p) k))) 3
def dmapC (d v : Nat) : Nat := cond (Nat.blt d 5) (Nat.mod (Nat.sub (Nat.add d 5) v) 5) (Nat.mod (Nat.sub (Nat.add v d) 5) 5)
def lam (d : Nat) (p : Nat → Nat) (x : Nat) : Nat :=
  Nat.add (dmapC d (Nat.mod x 5)) (Nat.mul 5 (permAt (p (Nat.mod x 5)) (Nat.div x 5)))

theorem dmapC_lt (d v : Nat) : dmapC d v < 5 := by
  unfold dmapC; cases Nat.blt d 5 <;> exact Nat.mod_lt _ (by norm_num)

theorem permAt_lt (p k : Nat) (hp : p < 6) (hk : k < 3) : permAt p k < 3 := by
  interval_cases p <;> interval_cases k <;> decide

theorem lam_lt (d : Nat) (p : Nat → Nat) (x : Nat) (hx : x < 15) (hp : p (x % 5) < 6) : lam d p x < 15 := by
  have h1 := dmapC_lt d (x % 5)
  have h2 := permAt_lt (p (x % 5)) (x / 5) hp (by omega)
  show dmapC d (x % 5) + 5 * permAt (p (x % 5)) (x / 5) < 15
  omega

theorem lam_mod (d : Nat) (p : Nat → Nat) (x : Nat) (hx : x < 15) (hp : p (x % 5) < 6) :
    lam d p x % 5 = dmapC d (x % 5) := by
  have h1 := dmapC_lt d (x % 5)
  show (dmapC d (x % 5) + 5 * permAt (p (x % 5)) (x / 5)) % 5 = dmapC d (x % 5)
  omega

theorem lam_div (d : Nat) (p : Nat → Nat) (x : Nat) (hx : x < 15) (hp : p (x % 5) < 6) :
    lam d p x / 5 = permAt (p (x % 5)) (x / 5) := by
  have h1 := dmapC_lt d (x % 5)
  show (dmapC d (x % 5) + 5 * permAt (p (x % 5)) (x / 5)) / 5 = permAt (p (x % 5)) (x / 5)
  omega

def srch (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => cond (P k) k (srch P k)

def dc (d d' : Nat) : Nat := srch (fun e => allBelow 5 (fun v => Nat.beq (dmapC e v) (dmapC d (dmapC d' v)))) 10
def pcomp (a b : Nat) : Nat := srch (fun c => allBelow 3 (fun k => Nat.beq (permAt c k) (permAt a (permAt b k)))) 6

def dcCheck : Bool :=
  allBelow 10 (fun d => allBelow 10 (fun d' => Nat.blt (dc d d') 10 &&
    allBelow 5 (fun v => Nat.beq (dmapC (dc d d') v) (dmapC d (dmapC d' v)))))

def pcCheck : Bool :=
  allBelow 6 (fun a => allBelow 6 (fun b => Nat.blt (pcomp a b) 6 &&
    allBelow 3 (fun k => Nat.beq (permAt (pcomp a b) k) (permAt a (permAt b k)))))

set_option maxRecDepth 10000 in
theorem dcCheck_ok : dcCheck = true := by decide +kernel

set_option maxRecDepth 10000 in
theorem pcCheck_ok : pcCheck = true := by decide +kernel

theorem dc_spec (d d' v : Nat) (hd : d < 10) (hd' : d' < 10) (hv : v < 5) :
    dc d d' < 10 ∧ dmapC (dc d d') v = dmapC d (dmapC d' v) := by
  have h1 := allBelow_spec _ _ (allBelow_spec _ _ dcCheck_ok d hd) d' hd'
  simp only [Bool.and_eq_true, Nat.blt_eq] at h1
  exact ⟨h1.1, Nat.eq_of_beq_eq_true (allBelow_spec _ _ h1.2 v hv)⟩

theorem pcomp_spec (a b k : Nat) (ha : a < 6) (hb : b < 6) (hk : k < 3) :
    pcomp a b < 6 ∧ permAt (pcomp a b) k = permAt a (permAt b k) := by
  have h1 := allBelow_spec _ _ (allBelow_spec _ _ pcCheck_ok a ha) b hb
  simp only [Bool.and_eq_true, Nat.blt_eq] at h1
  exact ⟨h1.1, Nat.eq_of_beq_eq_true (allBelow_spec _ _ h1.2 k hk)⟩

theorem lam_comp (d d' : Nat) (p p' : Nat → Nat) (hd : d < 10) (hd' : d' < 10)
    (hp : ∀ v, v < 5 → p v < 6) (hp' : ∀ v, v < 5 → p' v < 6) (x : Nat) (hx : x < 15) :
    lam d p (lam d' p' x) = lam (dc d d') (fun v => pcomp (p (dmapC d' v)) (p' v)) x := by
  have hv : x % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hl : x / 5 < 3 := by omega
  have e1 := lam_mod d' p' x hx (hp' _ hv)
  have e2 := lam_div d' p' x hx (hp' _ hv)
  have hw := dmapC_lt d' (x % 5)
  have hq := hp _ hw
  have hr := hp' _ hv
  have hc := (dc_spec d d' (x % 5) hd hd' hv).2
  have hpc := (pcomp_spec _ _ (x / 5) hq hr hl).2
  show dmapC d (lam d' p' x % 5) + 5 * permAt (p (lam d' p' x % 5)) (lam d' p' x / 5) =
    dmapC (dc d d') (x % 5) + 5 * permAt (pcomp (p (dmapC d' (x % 5))) (p' (x % 5))) (x / 5)
  rw [e1, e2, hc, hpc]

-- generators in normal form
def gd (k : Nat) : Nat := srch (fun d => allBelow 5 (fun v => Nat.beq (gVf k v % 5) (dmapC d v))) 10
def gp (k v : Nat) : Nat := srch (fun c => allBelow 3 (fun l => Nat.beq (gVf k (v + 5 * l) / 5) (permAt c l))) 6

def genForm : Bool :=
  allBelow 19 (fun k => Nat.blt (gd k) 10 && allBelow 5 (fun v => Nat.blt (gp k v) 6) &&
    allBelow 15 (fun x => Nat.beq (gVf k x) (lam (gd k) (gp k) x)))

set_option maxRecDepth 10000 in
theorem genForm_ok : genForm = true := by decide +kernel

theorem lam_id (x : Nat) (hx : x < 15) : lam 5 (fun _ => 0) x = x := by
  interval_cases x <;> rfl

theorem gen_nf (k : Nat) : ∃ d p, d < 10 ∧ (∀ v, v < 5 → p v < 6) ∧ ∀ x, x < 15 → gVf k x = lam d p x := by
  by_cases hk : k < 19
  · have h := allBelow_spec _ _ genForm_ok k hk
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    refine ⟨gd k, gp k, h.1.1, fun v hv => allBelow_spec _ _ h.1.2 v hv |> (by simpa [Nat.blt_eq] using ·), ?_⟩
    intro x hx
    have := allBelow_spec _ _ h.2 x hx
    simpa [Nat.beq_eq_true_eq] using this
  · refine ⟨5, fun _ => 0, by norm_num, fun _ _ => by norm_num, ?_⟩
    intro x hx
    rw [lam_id x hx]; unfold gVf; simp [hk]

theorem sig_nf (w : List Nat) :
    ∃ d p, d < 10 ∧ (∀ v, v < 5 → p v < 6) ∧ ∀ x, x < 15 → sig w x = lam d p x := by
  induction w with
  | nil => exact ⟨5, fun _ => 0, by norm_num, fun _ _ => by norm_num, fun x hx => (lam_id x hx).symm⟩
  | cons k w ih =>
    obtain ⟨d, p, hd, hp, he⟩ := ih
    obtain ⟨dk, pk', hdk, hpk, hek⟩ := gen_nf k
    refine ⟨dc d dk, fun v => pcomp (p (dmapC dk v)) (pk' v), (dc_spec d dk 0 hd hdk (by norm_num)).1, ?_, ?_⟩
    · intro v hv
      exact (pcomp_spec _ _ 0 (hp _ (dmapC_lt _ _)) (hpk v hv) (by norm_num)).1
    · intro x hx
      show sig w (gVf k x) = _
      rw [he _ (gVf_lt k x hx), hek x hx, lam_comp d dk p pk' hd hdk hp hpk x hx]

-- realization of normal forms by words
def wDih (d : Nat) : List Nat :=
  cond (Nat.beq d 0) [0] (cond (Nat.beq d 1) [0, 1] (cond (Nat.beq d 2) [0, 2] (cond (Nat.beq d 3) [0, 1, 2]
  (cond (Nat.beq d 4) [0, 3] (cond (Nat.beq d 5) [] (cond (Nat.beq d 6) [1] (cond (Nat.beq d 7) [2]
  (cond (Nat.beq d 8) [1, 2] [3]))))))))

def wLv (v c : Nat) : List Nat :=
  cond (Nat.beq c 0) [] (cond (Nat.beq c 1) [5 + 3 * v] (cond (Nat.beq c 2) [4 + 3 * v]
  (cond (Nat.beq c 3) [5 + 3 * v, 6 + 3 * v] (cond (Nat.beq c 4) [4 + 3 * v, 5 + 3 * v] [4 + 3 * v, 5 + 3 * v, 6 + 3 * v]))))

def lamL (v c x : Nat) : Nat := if x % 5 = v then v + 5 * permAt c (x / 5) else x

def wordCheck : Bool :=
  allBelow 10 (fun d => allBelow 15 (fun x => Nat.beq (sig (wDih d) x) (lam d (fun _ => 0) x))) &&
  allBelow 5 (fun v => allBelow 6 (fun c => allBelow 15 (fun x => Nat.beq (sig (wLv v c) x) (lamL v c x))))

set_option maxRecDepth 10000 in
theorem wordCheck_ok : wordCheck = true := by decide +kernel

theorem sig_wDih (d x : Nat) (hd : d < 10) (hx : x < 15) : sig (wDih d) x = lam d (fun _ => 0) x := by
  have h := wordCheck_ok
  simp only [wordCheck, Bool.and_eq_true] at h
  have := allBelow_spec _ _ (allBelow_spec _ _ h.1 d hd) x hx
  simpa [Nat.beq_eq_true_eq] using this

theorem sig_wLv (v c x : Nat) (hv : v < 5) (hc : c < 6) (hx : x < 15) : sig (wLv v c) x = lamL v c x := by
  have h := wordCheck_ok
  simp only [wordCheck, Bool.and_eq_true] at h
  have := allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ h.2 v hv) c hc) x hx
  simpa [Nat.beq_eq_true_eq] using this

theorem lamL_lt (v c x : Nat) (hv : v < 5) (hc : c < 6) (hx : x < 15) : lamL v c x < 15 := by
  unfold lamL; split
  · have := permAt_lt c (x / 5) hc (by omega); omega
  · exact hx

def wLoc (p : Nat → Nat) : List Nat := wLv 0 (p 0) ++ (wLv 1 (p 1) ++ (wLv 2 (p 2) ++ (wLv 3 (p 3) ++ wLv 4 (p 4))))

theorem lamL_chain (p : Nat → Nat) (x : Nat) (hx : x < 15) :
    lamL 4 (p 4) (lamL 3 (p 3) (lamL 2 (p 2) (lamL 1 (p 1) (lamL 0 (p 0) x)))) = lam 5 p x := by
  interval_cases x <;> simp [lamL, lam, dmapC, Nat.add_mul_mod_self_left] <;> rfl

theorem sig_wLoc (p : Nat → Nat) (hp : ∀ v, v < 5 → p v < 6) (x : Nat) (hx : x < 15) :
    sig (wLoc p) x = lam 5 p x := by
  have h0 := lamL_lt 0 (p 0) x (by norm_num) (hp 0 (by norm_num)) hx
  have h1 := lamL_lt 1 (p 1) _ (by norm_num) (hp 1 (by norm_num)) h0
  have h2 := lamL_lt 2 (p 2) _ (by norm_num) (hp 2 (by norm_num)) h1
  have h3 := lamL_lt 3 (p 3) _ (by norm_num) (hp 3 (by norm_num)) h2
  simp only [wLoc, sig_append]
  rw [sig_wLv 0 _ _ (by norm_num) (hp 0 (by norm_num)) hx, sig_wLv 1 _ _ (by norm_num) (hp 1 (by norm_num)) h0,
    sig_wLv 2 _ _ (by norm_num) (hp 2 (by norm_num)) h1, sig_wLv 3 _ _ (by norm_num) (hp 3 (by norm_num)) h2,
    sig_wLv 4 _ _ (by norm_num) (hp 4 (by norm_num)) h3]
  exact lamL_chain p x hx

theorem lam_split (d : Nat) (p : Nat → Nat) (x : Nat) (hx : x < 15) (hp : p (x % 5) < 6) :
    lam d (fun _ => 0) (lam 5 p x) = lam d p x := by
  have hv : x % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have e1 := lam_mod 5 p x hx hp
  have e2 := lam_div 5 p x hx hp
  have h5 : dmapC 5 (x % 5) = x % 5 := by interval_cases (x % 5) <;> rfl
  have hl := permAt_lt (p (x % 5)) (x / 5) hp (by omega)
  have h0 : permAt 0 (permAt (p (x % 5)) (x / 5)) = permAt (p (x % 5)) (x / 5) := by
    generalize permAt (p (x % 5)) (x / 5) = m at hl ⊢
    interval_cases m <;> rfl
  show dmapC d (lam 5 p x % 5) + 5 * permAt 0 (lam 5 p x / 5) = dmapC d (x % 5) + 5 * permAt (p (x % 5)) (x / 5)
  rw [e1, e2, h5, h0]

theorem lam_real (d : Nat) (p : Nat → Nat) (hd : d < 10) (hp : ∀ v, v < 5 → p v < 6) :
    ∃ w : List Nat, ∀ x, x < 15 → sig w x = lam d p x := by
  refine ⟨wLoc p ++ wDih d, fun x hx => ?_⟩
  have hv : x % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rw [sig_append, sig_wLoc p hp x hx, sig_wDih d _ hd (lam_lt 5 p x hx (hp _ hv)), lam_split d p x hx (hp _ hv)]

-- truth vectors of renamed functions
theorem tv_act_lam (d : Nat) (p : Nat → Nat) (hd : d < 10) (hp : ∀ v, v < 5 → p v < 6) :
    ∃ w : List Nat, ∀ g : F, tv (act (fun i => fv (lam d p i.val)) g) = permW w (tv g) := by
  obtain ⟨w, hw⟩ := lam_real d p hd hp
  refine ⟨w, fun g => ?_⟩
  rw [← tv_actW, actW_sig, act_congr _ _ hw]

def packList : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, w => Nat.lor x (Nat.shiftLeft (packList xs w) w)

def hCodes : List Nat := [0x224f08b5f3, 0x248f0ca736, 0xdcf118b07, 0x224f0935e3, 0xb5d8b4f63, 0x8b5a24f79, 0x2d35a24f53, 0xb2580922e, 0x135a24f53, 0x224f010f79, 0xa35822d56, 0xa35823e56, 0xa4f022d56, 0xca72d074e, 0xb5a24f33, 0x24f700a4e3, 0x35be224f33, 0xa35922d56, 0x11c6a24f33, 0xa35923e56, 0x935a24f33, 0x24f70924e3, 0xa35812d56, 0xb5a24f39, 0x935a24f39, 0x2b55a24f19, 0x33de224f19, 0x224f24f74e, 0x224f2c56fa, 0x24f71a2d2e, 0xd35a22d39, 0xa2d00cf6a, 0x1a46a22d39, 0x224f2d46d6, 0x24f0911a3, 0x24f008923, 0x130d890223, 0xb96090223, 0x224f01c6d6, 0x224f01c6f2, 0x24cf01a778]
def hRanks : List Nat := [0x104, 0x4, 0x154, 0x114, 0x100, 0x104, 0x105, 0x119, 0x115, 0x215, 0x105, 0x115, 0x105, 0x205, 0x105, 0x5, 0x114, 0x115, 0x150, 0x114, 0x114, 0x14, 0x115, 0x105, 0x114, 0x105, 0x114, 0x0, 0x141, 0x241, 0x106, 0x105, 0x141, 0x141, 0x155, 0x115, 0x115, 0x115, 0x141, 0x141, 0x41]

def hPack : Nat := packList hCodes 39
def hCode (s : Nat) : Nat := fld hPack 39 s
def hLeaf (code j : Nat) : Nat := Nat.land (Nat.shiftRight code (Nat.add 7 (Nat.mul 4 j))) 15
def hRankPack : Nat := packList hRanks 10
def rankOf (s v : Nat) : Nat := Nat.land (Nat.shiftRight (fld hRankPack 10 s) (Nat.mul 2 v)) 3
def locOpt (r j : Nat) : Nat := cond (Nat.beq r 0) 0 (cond (Nat.beq r 1) (Nat.land (Nat.shiftRight 0x430 (Nat.mul 4 j)) 15) j)
def locLen (r : Nat) : Nat := cond (Nat.beq r 0) 1 (cond (Nat.beq r 1) 3 6)
def nImg (s : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 1 (fun u acc => Nat.mul acc (locLen (rankOf s u))) 5
def divOf (s v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun u acc => cond (Nat.ble u v) acc (Nat.mul acc (locLen (rankOf s u)))) 5
def outOf (s v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun u acc => cond (Nat.blt u v) (Nat.mul acc (locLen (rankOf s u))) acc) 5
def digit (s v i : Nat) : Nat := Nat.mod (Nat.div i (divOf s v)) (locLen (rankOf s v))
def cvec (s i v : Nat) : Nat := locOpt (rankOf s v) (digit s v i)
def hImg (s d x c : Nat) : Nat :=
  Nat.add (dmapC d (Nat.mod x 5)) (Nat.mul 5 (permAt (locOpt (rankOf s (Nat.mod x 5)) c) (Nat.div x 5)))
def imgLf (s d i j : Nat) : Nat := hImg s d (hLeaf (hCode s) j) (digit s (Nat.mod (hLeaf (hCode s) j) 5) i)

def HF (s : Nat) : F := FH (hCode s) (hLeaf (hCode s))
def imgF (s d i : Nat) : F := FH (hCode s) (imgLf s d i)

-- data sanity: leaves below 15 and ranks below 3
def hDataCheck : Bool :=
  allBelow 41 (fun s => allBelow 8 (fun j => Nat.blt (hLeaf (hCode s) j) 15) && allBelow 5 (fun v => Nat.blt (rankOf s v) 3))

set_option maxRecDepth 10000 in
theorem hDataCheck_ok : hDataCheck = true := by decide +kernel

theorem hLeaf_lt (s j : Nat) (hs : s < 41) (hj : j < 8) : hLeaf (hCode s) j < 15 := by
  have h := allBelow_spec _ _ hDataCheck_ok s hs
  simp only [Bool.and_eq_true] at h
  exact (Nat.blt_eq).mp (allBelow_spec _ _ h.1 j hj)

theorem rankOf_lt (s v : Nat) (hs : s < 41) (hv : v < 5) : rankOf s v < 3 := by
  have h := allBelow_spec _ _ hDataCheck_ok s hs
  simp only [Bool.and_eq_true] at h
  exact (Nat.blt_eq).mp (allBelow_spec _ _ h.2 v hv)

-- local factorization: every permutation = (representative) after (stabilizer element)
def stabR (r t : Nat) : Bool := cond (Nat.beq r 0) true (cond (Nat.beq r 1) (Nat.beq (permAt t 0) 0) (Nat.beq t 0))
def fI (r a : Nat) : Nat := cond (Nat.beq r 0) 0 (cond (Nat.beq r 1) (permAt a 0) a)
def fT (r a : Nat) : Nat :=
  srch (fun t => allBelow 3 (fun k => Nat.beq (permAt a k) (permAt (locOpt r (fI r a)) (permAt t k)))) 6

def allowedR (r v k : Nat) : Bool :=
  (Nat.beq k (5 + 3 * v) && Nat.ble r 1) || ((Nat.beq k (4 + 3 * v) || Nat.beq k (6 + 3 * v)) && Nat.beq r 0)

def factCheck : Bool :=
  allBelow 3 (fun r => allBelow 6 (fun a => Nat.blt (fI r a) (locLen r) && Nat.blt (fT r a) 6 && stabR r (fT r a) &&
    allBelow 3 (fun k => Nat.beq (permAt a k) (permAt (locOpt r (fI r a)) (permAt (fT r a) k))))) &&
  allBelow 3 (fun r => allBelow 6 (fun t => !stabR r t || allBelow 5 (fun v => (wLv v t).all (allowedR r v)))) &&
  allBelow 3 (fun r => allBelow 6 (fun j => Nat.blt (locOpt r j) 6))

set_option maxRecDepth 10000 in
theorem factCheck_ok : factCheck = true := by decide +kernel

theorem fact_spec (r a : Nat) (hr : r < 3) (ha : a < 6) :
    fI r a < locLen r ∧ fT r a < 6 ∧ stabR r (fT r a) = true ∧
    ∀ k, k < 3 → permAt a k = permAt (locOpt r (fI r a)) (permAt (fT r a) k) := by
  have h := factCheck_ok
  simp only [factCheck, Bool.and_eq_true] at h
  have h1 := allBelow_spec _ _ (allBelow_spec _ _ h.1.1 r hr) a ha
  simp only [Bool.and_eq_true, Nat.blt_eq] at h1
  exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, fun k hk => Nat.eq_of_beq_eq_true (allBelow_spec _ _ h1.2 k hk)⟩

theorem stab_words (r t v : Nat) (hr : r < 3) (ht : t < 6) (hv : v < 5) (hs : stabR r t = true) :
    (wLv v t).all (allowedR r v) = true := by
  have h := factCheck_ok
  simp only [factCheck, Bool.and_eq_true] at h
  have h1 := allBelow_spec _ _ (allBelow_spec _ _ h.1.2 r hr) t ht
  simp only [hs, Bool.not_true, Bool.false_or] at h1
  exact allBelow_spec _ _ h1 v hv

theorem locOpt_lt (r j : Nat) (hr : r < 3) (hj : j < 6) : locOpt r j < 6 := by
  have h := factCheck_ok
  simp only [factCheck, Bool.and_eq_true] at h
  exact (Nat.blt_eq).mp (allBelow_spec _ _ (allBelow_spec _ _ h.2 r hr) j hj)

-- stabilizer generators fix the boundary rectangle of each high formula
def stabCheck : Bool :=
  allBelow 41 (fun s => allBelow 5 (fun v => allBelow 3 (fun e =>
    let k := 4 + 3 * v + e
    !allowedR (rankOf s v) v k ||
      Nat.beq (evalHv (hCode s) (fun j => varAt (gVf k (hLeaf (hCode s) j)))) (evalHv (hCode s) (fun j => varAt (hLeaf (hCode s) j))))))

set_option maxRecDepth 10000 in
theorem stabCheck_ok : stabCheck = true := by decide +kernel

theorem FH_congr (code : Nat) (lf lf' : Nat → Nat) (h : ∀ j, j < 8 → lf j = lf' j) : FH code lf = FH code lf' := by
  funext z
  simp only [FH, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num)]

theorem sig_one (k x : Nat) : sig [k] x = gVf k x := rfl

theorem permW_gen_fix (s k : Nat) (hs : s < 41) (v : Nat) (hv : v < 5) (hk : 4 + 3 * v ≤ k ∧ k < 7 + 3 * v)
    (ha : allowedR (rankOf s v) v k = true) : permW [k] (tv (HF s)) = tv (HF s) := by
  have h := allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ stabCheck_ok s hs) v hv) (k - (4 + 3 * v)) (by omega)
  simp only [show 4 + 3 * v + (k - (4 + 3 * v)) = k by omega, ha, Bool.not_true, Bool.false_or] at h
  have e := Nat.eq_of_beq_eq_true h
  rw [← tv_actW, actW_sig, HF, act_FH _ _ _ (fun j hj => hLeaf_lt s j hs hj), tv_FH, tv_FH]
  exact e

def allowedS (s k : Nat) : Bool := Nat.ble 4 k && Nat.blt k 19 && allowedR (rankOf s ((k - 4) / 3)) ((k - 4) / 3) k

theorem permW_allowed_fix (s : Nat) (hs : s < 41) (w : List Nat) (hw : w.all (allowedS s) = true) :
    permW w (tv (HF s)) = tv (HF s) := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hw
    have h1 := hw.1
    simp only [allowedS, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h1
    have hv : (k - 4) / 3 < 5 := by omega
    have e1 : permW [k] (tv (HF s)) = tv (HF s) :=
      permW_gen_fix s k hs ((k - 4) / 3) hv (by omega) h1.2
    show permW w (permP (genP k) (tv (HF s))) = tv (HF s)
    have e2 : permP (genP k) (tv (HF s)) = permW [k] (tv (HF s)) := rfl
    rw [e2, e1, ih hw.2]

theorem wLv_allowedS (s v c : Nat) (hs : s < 41) (hv : v < 5) (hc : c < 6) (hst : stabR (rankOf s v) c = true) :
    (wLv v c).all (allowedS s) = true := by
  have h := stab_words (rankOf s v) c v (rankOf_lt s v hs hv) hc hv hst
  rw [List.all_eq_true] at h ⊢
  intro k hk
  have hk2 := h k hk
  have hmem : k = 4 + 3 * v ∨ k = 5 + 3 * v ∨ k = 6 + 3 * v := by
    interval_cases c <;> simp [wLv] at hk <;> omega
  have hq : (k - 4) / 3 = v := by omega
  simp only [allowedS, hq, hk2, Bool.and_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
  omega

theorem stab_fix (s : Nat) (hs : s < 41) (t : Nat → Nat) (ht : ∀ v, v < 5 → t v < 6)
    (hst : ∀ v, v < 5 → stabR (rankOf s v) (t v) = true) :
    tv (FH (hCode s) (fun j => lam 5 t (hLeaf (hCode s) j))) = tv (HF s) := by
  have hw : (wLoc t).all (allowedS s) = true := by
    simp only [wLoc, List.all_append, Bool.and_eq_true]
    exact ⟨wLv_allowedS s 0 _ hs (by norm_num) (ht 0 (by norm_num)) (hst 0 (by norm_num)),
      wLv_allowedS s 1 _ hs (by norm_num) (ht 1 (by norm_num)) (hst 1 (by norm_num)),
      wLv_allowedS s 2 _ hs (by norm_num) (ht 2 (by norm_num)) (hst 2 (by norm_num)),
      wLv_allowedS s 3 _ hs (by norm_num) (ht 3 (by norm_num)) (hst 3 (by norm_num)),
      wLv_allowedS s 4 _ hs (by norm_num) (ht 4 (by norm_num)) (hst 4 (by norm_num))⟩
  rw [← act_FH _ _ _ (fun j hj => hLeaf_lt s j hs hj), act_congr _ _ (fun x hx => (sig_wLoc t ht x hx).symm),
    ← actW_sig, tv_actW]
  exact permW_allowed_fix s hs _ hw

-- mixed radix enumeration of the local representatives
def encR (s : Nat) (idx : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun v acc => Nat.add acc (Nat.mul (idx v) (divOf s v))) 5

def radixCheck : Bool :=
  allBelow 41 (fun s => allBelow (locLen (rankOf s 0)) (fun i0 => allBelow (locLen (rankOf s 1)) (fun i1 =>
    allBelow (locLen (rankOf s 2)) (fun i2 => allBelow (locLen (rankOf s 3)) (fun i3 =>
    allBelow (locLen (rankOf s 4)) (fun i4 =>
      let idx := fun v => cond (Nat.beq v 0) i0 (cond (Nat.beq v 1) i1 (cond (Nat.beq v 2) i2 (cond (Nat.beq v 3) i3 i4)))
      let e := encR s idx
      Nat.blt e (nImg s) && allBelow 5 (fun v => Nat.beq (digit s v e) (idx v))))))))

set_option maxRecDepth 10000 in
theorem radixCheck_ok : radixCheck = true := by decide +kernel

theorem radix_spec (s : Nat) (hs : s < 41) (idx : Nat → Nat) (hi : ∀ v, v < 5 → idx v < locLen (rankOf s v)) :
    ∃ i, i < nImg s ∧ ∀ v, v < 5 → digit s v i = idx v := by
  have h := allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _
    (allBelow_spec _ _ radixCheck_ok s hs) (idx 0) (hi 0 (by norm_num))) (idx 1) (hi 1 (by norm_num)))
    (idx 2) (hi 2 (by norm_num))) (idx 3) (hi 3 (by norm_num))) (idx 4) (hi 4 (by norm_num))
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  have hidx : ∀ v, v < 5 → (cond (Nat.beq v 0) (idx 0) (cond (Nat.beq v 1) (idx 1) (cond (Nat.beq v 2) (idx 2)
      (cond (Nat.beq v 3) (idx 3) (idx 4))))) = idx v := by
    intro v hv; interval_cases v <;> rfl
  refine ⟨_, h.1, fun v hv => ?_⟩
  have := Nat.eq_of_beq_eq_true (allBelow_spec _ _ h.2 v hv)
  rw [this, hidx v hv]

theorem locLen_le (r : Nat) : locLen r ≤ 6 := by
  unfold locLen; cases Nat.beq r 0 <;> cases Nat.beq r 1 <;> simp

-- the completeness of the generated images of each high formula
theorem imgLf_eq (s d i j : Nat) (hs : s < 41) (hj : j < 8) :
    imgLf s d i j = lam d (cvec s i) (hLeaf (hCode s) j) := rfl

theorem img_complete (s : Nat) (hs : s < 41) (w : List Nat) :
    ∃ d i, d < 10 ∧ i < nImg s ∧ permW w (tv (HF s)) = tv (imgF s d i) := by
  obtain ⟨d, p, hd, hp, he⟩ := sig_nf w
  have hr := fun v (hv : v < 5) => rankOf_lt s v hs hv
  obtain ⟨i, hi, hdig⟩ := radix_spec s hs (fun v => fI (rankOf s v) (p v))
    (fun v hv => (fact_spec _ _ (hr v hv) (hp v hv)).1)
  let t := fun v => fT (rankOf s v) (p v)
  have ht : ∀ v, v < 5 → t v < 6 := fun v hv => (fact_spec _ _ (hr v hv) (hp v hv)).2.1
  have hst : ∀ v, v < 5 → stabR (rankOf s v) (t v) = true := fun v hv => (fact_spec _ _ (hr v hv) (hp v hv)).2.2.1
  have hc : ∀ v, v < 5 → cvec s i v < 6 := fun v hv => locOpt_lt _ _ (hr v hv) (by
    have h1 := (fact_spec _ _ (hr v hv) (hp v hv)).1
    have h2 : locLen (rankOf s v) ≤ 6 := locLen_le _
    unfold digit; exact lt_of_lt_of_le (Nat.mod_lt _ (by omega)) h2)
  have hlam : ∀ x, x < 15 → lam d p x = lam d (cvec s i) (lam 5 t x) := by
    intro x hx
    have hv : x % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have e1 := lam_mod 5 t x hx (ht _ hv)
    have e2 := lam_div 5 t x hx (ht _ hv)
    have h5 : dmapC 5 (x % 5) = x % 5 := by interval_cases (x % 5) <;> rfl
    have hf := (fact_spec _ _ (hr _ hv) (hp _ hv)).2.2.2 (x / 5) (by omega)
    show dmapC d (x % 5) + 5 * permAt (p (x % 5)) (x / 5) =
      dmapC d (lam 5 t x % 5) + 5 * permAt (cvec s i (lam 5 t x % 5)) (lam 5 t x / 5)
    rw [e1, e2, h5, hf]
    simp only [cvec, hdig _ hv]; rfl
  obtain ⟨wc, hwc⟩ := tv_act_lam d (cvec s i) hd hc
  have hl := fun j (hj : j < 8) => hLeaf_lt s j hs hj
  have hl5 : ∀ j, j < 8 → lam 5 t (hLeaf (hCode s) j) < 15 := fun j hj =>
    lam_lt 5 t _ (hl j hj) (ht _ (Nat.mod_lt _ (by norm_num)))
  refine ⟨d, i, hd, hi, ?_⟩
  rw [← tv_actW, actW_sig, act_congr _ _ he, HF, act_FH _ _ _ hl]
  rw [FH_congr _ _ (fun j => lam d (cvec s i) (lam 5 t (hLeaf (hCode s) j))) (fun j hj => hlam _ (hl j hj))]
  rw [← act_FH (lam d (cvec s i)) _ _ hl5, hwc, stab_fix s hs t ht hst, ← hwc, HF, act_FH _ _ _ hl]
  rfl

def tplCodes : List Nat := [0xa830, 0xb5a, 0x10b4, 0x2b5a, 0x8b5a, 0x8812, 0x35a, 0x919, 0x5d8b1, 0x9031, 0xb059, 0x9c1, 0xb1c1, 0xa831, 0x939, 0x135e, 0x2b5e, 0x109e, 0x89a1, 0x89c1, 0xb1db, 0xb5e, 0x8919, 0x10be, 0x9825, 0x1c35b, 0x1a35b, 0x45b6f, 0x231df, 0x11b5b, 0x9a4d, 0x22093, 0x2315f, 0xb139, 0x924d, 0xb15b, 0x936, 0x8939, 0x933e, 0x13b5b, 0x3db67]
def ncCodes : List Nat := [0x0, 0x500, 0x100, 0x200, 0x50, 0x550, 0xa50, 0x150, 0x250, 0x10, 0x510, 0x110, 0x610, 0x210, 0x310, 0x410, 0x20, 0x520, 0x120, 0x220, 0x720, 0x320, 0x420, 0x5, 0x505, 0xa05, 0x105, 0x205, 0x55, 0x555, 0xa55, 0x155, 0x255, 0xa5, 0x5a5, 0xaa5, 0x1a5, 0x2a5, 0x15, 0x515, 0xa15, 0x115, 0x615, 0x215, 0x315, 0x415, 0x25, 0x525, 0xa25, 0x125, 0x225, 0x725, 0x325, 0x425, 0x1, 0x501, 0x101, 0x601, 0x201, 0x301, 0x401, 0x51, 0x551, 0xa51, 0x151, 0x651, 0x251, 0x351, 0x451, 0x11, 0x511, 0x111, 0x611, 0x211, 0x311, 0x411, 0x61, 0x561, 0x161, 0x661, 0xb61, 0x261, 0x361, 0x461, 0x21, 0x521, 0x121, 0x621, 0x221, 0x721, 0x321, 0x421, 0x31, 0x531, 0x131, 0x631, 0x231, 0x331, 0x831, 0x431, 0x41, 0x541, 0x141, 0x641, 0x241, 0x341, 0x441, 0x941, 0x2, 0x502, 0x102, 0x202, 0x702, 0x302, 0x402, 0x52, 0x552, 0xa52, 0x152, 0x252, 0x752, 0x352, 0x452, 0x12, 0x512, 0x112, 0x612, 0x212, 0x712, 0x312, 0x412, 0x22, 0x522, 0x122, 0x222, 0x722, 0x322, 0x422, 0x72, 0x572, 0x172, 0x272, 0x772, 0xc72, 0x372, 0x472, 0x32, 0x532, 0x132, 0x232, 0x732, 0x332, 0x832, 0x432, 0x42, 0x542, 0x142, 0x242, 0x742, 0x342, 0x442, 0x942]
def wit2 : Nat := 0x4110002001800c01000003f00006f000000400000800003f00002f800090400000800003f00002f800090400000800003f00001f800001c00007e00003f00006c00000fc00020200003f00406e000002c00432800003f00306a00000fc00007e00003f00002f800064800c32800003f00306a00000fc00007e00003f00001f800024400c12800003f00306a00000fc00007e00003f00403000001100080c400003f00312a000090400848200003f00002f80001100000c400003f00306a000090400048200003f00001f800001c00007e00003f00006c00000fc00020200003f004090002071800421000003f00012f000070400020800003f0000cf800070400020800003f0000cf800070400020800003f0040d0000031004024400003f00306a000030400138200003f0000cf800031000034400003f00306a000070400038200003f00001f800054400c2a800003f00306a00000fc00007e00003f00402e000072c20c3a800003f00306a00000fc00007e00003f0000cf800014800c3a800003f00306a00000fc00007e00003f00406e000002c00432800003f00306a00000fc00007e00003f0040d0000031004024400003f00306a000030400138200003f00001f800031000019000003f00306a00000fc00818800003f00306a000031000818800003f00306a000031000818800003f00306a000031000c19000003f00306a000031000018800003f00001f800055c0081c400003f00306a000060400110200003f10412d80003302041a800003f00306a00000fc00007e00003f00306a000094c0041a800003f00306a00000fc00007e00003f00002f800064800c32800003f00306a00000fc00007e00003f0000cf800031000034400003f00306a000070400038200003f00306a000031000c19000003f00306a000031000018800003f00306a000031000018800003f00306a000031000018800003f00001f80003580002c400003f00306a000020400010200003f00312a000034c20c1a800003f00306a00000fc00007e00003f00306a001835000c1a800003f00306a00000fc00007e00003f00001f800024400c12800003f00306a00000fc00007e00003f00001f800054400c2a800003f00306a00000fc00007e00003f00001f800055c0081c400003f00306a000060400110200003f00001f80003580002c400003f00306a000020400010200003f00001f802023c00411000003f00001f800050800010800003f00001f800051400010800003f00001f800051400010800003f00001f800025c04014400003f00312a000010400128200003f00001f800095800014400003f00306a000050400028200003f00403000001100080c400003f00312a000090400848200003f00402e000072c20c3a800003f00306a00000fc00007e00003f10412d80003302041a800003f00306a00000fc00007e00003f00312a000034c20c1a800003f00306a00000fc00007e00003f00001f800025c04014400003f00312a000010400128200003f00001f800011000409000003f00312a00000fc00808800003f00312a000011000808800003f00312a000011000808800003f00312a000011000409000003f00306a000011000008800003f00002f80001100000c400003f00306a000090400048200003f0000cf800014800c3a800003f00306a00000fc00007e00003f00306a000094c0041a800003f00306a00000fc00007e00003f00306a001835000c1a800003f00306a00000fc00007e00003f00001f800095800014400003f00306a000050400028200003f00312a000011000409000003f00306a000011000008800003f00306a000011000008800003f00306a000011000008800003f00001f802001801043a00003f00001f800000400009c00003f00001f800090400042c00003f00001f800090400042c00003f00001f800090400003e00003f00004f80000fc00008e00003f00001f800021c00033000003f00001f80000fc00028200003f00001f808095c00412800014100005100000fc00028200003f00001f800025800c12800014100005100000fc00028200003f00001f800019000c0c6000041001131800090400049200003f00001f80001100000c4000141000051000090400008a00003f00001f800090400003e00003f00004f80000fc00008e00003f00408e00000fc01023400003f00005100000fc00029600003f00004f80000fc0003a400003f00004f80000fc0003a400003f00001f800020400033e00003f00004f80000fc00028e00003f00405000102100042a800014100005100000fc00028200003f00004f800021000c2a800014100005100000fc00028200003f00413000101100040a800004100005100000fc00028200003f00004f800011000c3a800014100005100000fc00028200003f00001f800021c00033000003f00001f80000fc00028200003f00001f800020400033e00003f00004f80000fc00028e00003f00001f80206180101ba00003f00001f800060400029c00003f00001f80002040001ac00003f00001f80002040001ac00003f00001f80005900042c6000141003051800020400011200003f00001f80002100002c4000141000051000020400028a00003f00001f808025c00c4a800004100005100000fc00028200003f00001f800095800c1a800014100005100000fc00028200003f00001f808095c00412800014100005100000fc00028200003f00405000102100042a800014100005100000fc00028200003f00001f80005900042c6000141003051800020400011200003f00001f8000554000110000141003051801050400c29400003f00305180102100041100001410030518010210004110000141003051801822000411000014100005100002100001080001410240540000298044146000141003051801250400129a0001400030518000994008144000141000051001050401028c00014100001f800025800c12800014100005100000fc00028200003f00004f800021000c2a800014100005100000fc00028200003f00001f80002100002c4000141000051000020400028a00003f00305180182200041100001410000510000210000108000141000051000021000010800014100005100002100001080001410011318000294040144000141000051000250401008c0000410000510000288000144000141000051000050400028200014100001f800019000c0c6000041001131800090400049200003f00413000101100040a800004100005100000fc00028200003f00001f808025c00c4a800004100005100000fc00028200003f0240540000298044146000141003051801250400129a0001400011318000294040144000141000051000250401008c00004100001f8000154004090000041003131801010400c09400003f001131801011000409000004100113180101100040900000410011318018120004090000141000051000011000008800004100001f80001100000c4000141000051000090400008a00003f00004f800011000c3a800014100005100000fc00028200003f00001f800095800c1a800014100005100000fc00028200003f0030518000994008144000141000051001050401028c000141000051000028800014400014100005100005040002820001410011318018120004090000141000051000011000008800004100005100001100000880001410000510000110000088000141004030002091800033c00024100102400000fc00008800003f00402e00000fc00034400003f00402d00000fc00039600003f10412d80000fc0101b200003f00412c80000fc00019800003f00312a00000fc0001a600003f00312a00000fc0001a600003f00001f802011800007e00004100412e80000fc00011c00003f00001f80201100004a800003f00102400000fc00008800003f00312a001011020c1a800004400102400000fc00008800003f00312a000011000c1a800004400102400000fc00008800003f00001f802013c00007e00004200102400000fc00008800003f004130002011800023c00004100102400000fc00008800003f00001f802011800007e00004100412e80000fc00011c00003f024054002014001014e008143004133802010c000142000140001131802011800014a000041001131802011800014a00004100001f80201540004c6000041001024002010400009400003f001131800812004014400004400102400025040080880000410011318018120000144000044001024000050400008800004100001f80201100004a800003f00102400000fc00008800003f00001f80201540004c6000041001024002010400009400003f00001f802011000009000003f00001f802011000009000003f00001f8008120004090000044001024001011000808800003f00001f801812000c090000044001024000011000008800003f00312a001011020c1a800004400102400000fc00008800003f0011318008120040144000044001024000250400808800004100001f8008120004090000044001024001011000808800003f001024001011000808800004400102400101100080880000440010240008120004090000044001024000011000008800004400312a000011000c1a800004400102400000fc00008800003f0011318018120000144000044001024000050400008800004100001f801812000c090000044001024000011000008800003f001024000812000409000004400102400001100000880000440010240000110000088000044001024000011000008800004400002f80009040000be00024100002200000fc00008800003f0000cf80000fc00033e00003f00002900000fc0000a400003f00306a00000fc00c1a800003f00012980000fc0004a600003f00306a00000fc00c1a800003f00306a00000fc00c1a800003f00001f800050400007e00014100012b00000fc0004ac00003f00312a000011000c4a800004400002200000fc00008800003f00306a000011000c1a800004400002200000fc00008800003f00001f800011400007e00004500002200000fc00008800003f00004f800050400013e00014100002200000fc00008800003f00001f800050400007e00014100012b00000fc0004ac00003f003051802051800c14600814600013280005040004ca0001410000510000504000144000141000051000050400014400014100113180001100044c6000044003024000010400c0900000410000510000110000144000044000022000050400008800014100312a000011000c4a800004400002200000fc00008800003f00113180001100044c6000044003024000010400c09000004100001f800011000007e00004400302400000fc00c09000003f001024000011000409000004400102400001100040900000440010240000110004090000044000022000011000008800004400306a000011000c1a800004400002200000fc00008800003f000051000011000014400004400002200005040000880001410010240000110004090000044000022000011000008800004400002200001100000880000440000220000110000088000044

def tplPack : Nat := packList tplCodes 20
def tplAt (i : Nat) : Nat := fld tplPack 20 i
def leafOf (code t : Nat) : Nat := Nat.land (Nat.shiftRight code (Nat.add 3 (Nat.mul 4 t))) 15
def TF (j : Nat) : F := F2 (tplAt j) (leafOf (tplAt j))

def ncPack : Nat := packList ncCodes 12
def ncAt (i : Nat) : Nat := fld ncPack 12 i
def ncLeaf (c t : Nat) : Nat := cond (Nat.beq t 0) 0 (Nat.land (Nat.shiftRight c (Nat.mul 4 (Nat.sub t 1))) 15)
def ncMaskN (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (ncAt i))) n
def ncMask : Nat := ncMaskN 162

theorem ncMask_spec (c : Nat) (h : tb ncMask c = true) : ∃ i, i < 162 ∧ ncAt i = c := by
  rw [tb_eq] at h
  suffices H : ∀ n, (ncMaskN n).testBit c = true → ∃ i, i < n ∧ ncAt i = c by
    obtain ⟨i, hi, he⟩ := H 162 h; exact ⟨i, hi, he⟩
  intro n
  induction n with
  | zero => intro h0; simp [ncMaskN] at h0
  | succ n ih =>
    intro h1
    have e : ncMaskN (n + 1) = ncMaskN n ||| (1 <<< ncAt n) := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · obtain ⟨i, hi, he⟩ := ih h1; exact ⟨i, by omega, he⟩
    · rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at h1
      exact ⟨n, by omega, by simpa using h1⟩

-- rectangle tests
def domB (t s : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.land t (Nat.xor s mask180)) MA) 0 && Nat.beq (Nat.land (Nat.land s (Nat.xor t mask180)) MV) 0
def improperB (t : Nat) : Bool := Nat.beq (Nat.land t MA) 0 || Nat.beq (Nat.land t MV) MV

theorem testBit_mask180 (p : Nat) : mask180.testBit p = decide (p < 180) := by
  show (2 ^ 180 - 1).testBit p = _
  rw [Nat.testBit_two_pow_sub_one]

theorem testBit_MA (p : Nat) : MA.testBit p = decide (p < 45) := by
  show (2 ^ 45 - 1).testBit p = _
  rw [Nat.testBit_two_pow_sub_one]

theorem domB_spec (t s : Nat) (h : domB t s = true) : dom t s := by
  simp only [domB, Bool.and_eq_true] at h
  have h1 := Nat.eq_of_beq_eq_true h.1
  have h2 := Nat.eq_of_beq_eq_true h.2
  intro p hp
  constructor
  · intro hpa ht
    have := congrArg (fun x => x.testBit p) h1
    simp only [Nat.zero_testBit] at this
    change ((t &&& (s ^^^ mask180)) &&& MA).testBit p = false at this
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, testBit_mask180, testBit_MA] at this
    simp only [hp, hpa, decide_true, ht, Bool.true_and, Bool.and_true] at this
    cases hs : s.testBit p <;> simp_all
  · intro hpa hs
    have := congrArg (fun x => x.testBit p) h2
    simp only [Nat.zero_testBit] at this
    change ((s &&& (t ^^^ mask180)) &&& MV).testBit p = false at this
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, testBit_mask180, testBit_MV] at this
    simp only [hp, hpa, decide_true, hs, Bool.true_and, Bool.and_true] at this
    cases ht : t.testBit p <;> simp_all

theorem improperB_spec (t : Nat) (ht : t < 2 ^ 180) (h : improperB t = true) : cA t = 0 ∨ cB t = 0 := by
  simp only [improperB, Bool.or_eq_true] at h
  rcases h with h | h
  · left
    rw [← popA_eq]; unfold popA
    rw [show Nat.land t MA = 0 from Nat.eq_of_beq_eq_true h]; rfl
  · right
    have h1 : Nat.land t MV = MV := Nat.eq_of_beq_eq_true h
    rw [← popB_eq t ht]; unfold popB
    have h2 : rect t >>> 45 = 0 := by
      apply Nat.eq_of_testBit_eq; intro p
      rw [Nat.testBit_shiftRight, Nat.zero_testBit]
      unfold rect
      rw [Nat.testBit_xor, testBit_MV]
      by_cases hp : 45 + p < 180
      · have := congrArg (fun x => x.testBit (45 + p)) h1
        change (t &&& MV).testBit (45 + p) = MV.testBit (45 + p) at this
        rw [Nat.testBit_and, testBit_MV] at this
        simp only [show 45 ≤ 45 + p by omega, hp, decide_true, Bool.and_true] at this
        simp [this, hp]
      · have : t.testBit (45 + p) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [this, hp]
    rw [show Nat.shiftRight (rect t) 45 = 0 from h2]; rfl

-- witness records: template (6 bits, 63 = improper), dihedral (4 bits), five local permutations (3 bits each)
def w2At (k : Nat) : Nat := fld wit2 25 k
def wT (r : Nat) : Nat := Nat.land r 63
def wD (r : Nat) : Nat := Nat.land (Nat.shiftRight r 6) 15
def wP (r v : Nat) : Nat := Nat.land (Nat.shiftRight r (Nat.add 10 (Nat.mul 3 v))) 7

def wit2Check : Bool :=
  allBelow 162 (fun i => allBelow 8 (fun op =>
    let r := w2At (Nat.add (Nat.mul 8 i) op)
    let src := evalT2 op (ncLeaf (ncAt i))
    cond (Nat.beq (wT r) 63) (improperB src)
      (Nat.blt (wT r) 41 && Nat.blt (wD r) 10 && allBelow 5 (fun v => Nat.blt (wP r v) 6) &&
        domB src (evalT2 (tplAt (wT r)) (fun t => lam (wD r) (wP r) (leafOf (tplAt (wT r)) t))))))

set_option maxRecDepth 10000 in
theorem wit2Check_ok : wit2Check = true := by decide +kernel

-- stage A: dihedral normalization of the vertex sequence
def vec4 (a b c d t : Nat) : Nat := cond (Nat.beq t 0) a (cond (Nat.beq t 1) b (cond (Nat.beq t 2) c d))
def aR (vs : Nat → Nat) (t : Nat) : Nat := Nat.mod (Nat.sub (Nat.add (vs t) 5) (vs 0)) 5
def fR (us : Nat → Nat) : Nat := cond (Nat.beq (us 1) 0) (cond (Nat.beq (us 2) 0) (us 3) (us 2)) (us 1)
def rF (vs : Nat → Nat) : Bool := Nat.ble 3 (fR (aR vs))
def eA (vs : Nat → Nat) : Nat := cond (rF vs) (vs 0) (Nat.add 5 (vs 0))
def uA (vs : Nat → Nat) (t : Nat) : Nat := cond (rF vs) (Nat.mod (Nat.sub (Nat.add (vs 0) 5) (vs t)) 5) (aR vs t)
def NV (us : Nat → Nat) : Bool := Nat.beq (us 0) 0 && Nat.blt (fR us) 3

def stageA : Bool :=
  allBelow 5 (fun a => allBelow 5 (fun b => allBelow 5 (fun c => allBelow 5 (fun d =>
    let vs := vec4 a b c d
    NV (uA vs) && Nat.blt (eA vs) 10 &&
      allBelow 4 (fun t => Nat.blt (uA vs t) 5 && Nat.beq (dmapC (eA vs) (uA vs t)) (vs t))))))

set_option maxRecDepth 10000 in
theorem stageA_ok : stageA = true := by decide +kernel

-- stage B: local first-appearance normalization
def firstL (us ls : Nat → Nat) (w : Nat) : Nat :=
  cond (Nat.beq (us 0) w) (ls 0) (cond (Nat.beq (us 1) w) (ls 1) (cond (Nat.beq (us 2) w) (ls 2) (cond (Nat.beq (us 3) w) (ls 3) 0)))
def secondL (us ls : Nat → Nat) (w a : Nat) : Nat :=
  let ok := fun t => Nat.beq (us t) w && !Nat.beq (ls t) a
  cond (ok 0) (ls 0) (cond (ok 1) (ls 1) (cond (ok 2) (ls 2) (cond (ok 3) (ls 3) (Nat.mod (Nat.add a 1) 3))))
def PI (a b : Nat) : Nat := fld 0x054302100 4 (Nat.add (Nat.mul 3 a) b)
def invP (p : Nat) : Nat := fld 0x534210 4 p
def Pw (us ls : Nat → Nat) (w : Nat) : Nat := PI (firstL us ls w) (secondL us ls w (firstL us ls w))
def zB (us ls : Nat → Nat) (t : Nat) : Nat := Nat.add (us t) (Nat.mul 5 (permAt (invP (Pw us ls (us t))) (ls t)))
def zCode (us ls : Nat → Nat) : Nat := Nat.add (zB us ls 1) (Nat.add (Nat.mul 16 (zB us ls 2)) (Nat.mul 256 (zB us ls 3)))

def stageB : Bool :=
  allBelow 5 (fun b => allBelow 5 (fun c => allBelow 5 (fun d =>
    let us := vec4 0 b c d
    cond (NV us) (allBelow 3 (fun l0 => allBelow 3 (fun l1 => allBelow 3 (fun l2 => allBelow 3 (fun l3 =>
      let ls := vec4 l0 l1 l2 l3
      allBelow 5 (fun w => Nat.blt (Pw us ls w) 6) && Nat.beq (zB us ls 0) 0 && tb ncMask (zCode us ls) &&
        allBelow 4 (fun t => Nat.blt (zB us ls t) 15 &&
          Nat.beq (lam 5 (Pw us ls) (zB us ls t)) (Nat.add (us t) (Nat.mul 5 (ls t))))))))) true)))

set_option maxRecDepth 10000 in
theorem stageB_ok : stageB = true := by decide +kernel

def tplCheck : Bool := allBelow 41 (fun j => allBelow 4 (fun t => Nat.blt (leafOf (tplAt j) t) 15))

set_option maxRecDepth 10000 in
theorem tplCheck_ok : tplCheck = true := by decide +kernel

theorem tplLeaf_lt (j t : Nat) (hj : j < 41) (ht : t < 4) : leafOf (tplAt j) t < 15 :=
  (Nat.blt_eq).mp (allBelow_spec _ _ (allBelow_spec _ _ tplCheck_ok j hj) t ht)

theorem F2_congr (code code' : Nat) (lf lf' : Nat → Nat) (hc : ∀ k, k < 3 → tb code k = tb code' k)
    (hl : ∀ t, t < 4 → lf t = lf' t) : F2 code lf = F2 code' lf' := by
  funext z
  simp only [F2, hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), hl 0 (by norm_num),
    hl 1 (by norm_num), hl 2 (by norm_num), hl 3 (by norm_num)]

theorem tb_mod8 (code k : Nat) (hk : k < 3) : tb code k = tb (code % 8) k := by
  rw [tb_eq, tb_eq, show (8 : Nat) = 2 ^ 3 by norm_num, Nat.testBit_mod_two_pow]
  simp [hk]

theorem vec4_eq (f : Nat → Nat) (t : Nat) (ht : t < 4) : vec4 (f 0) (f 1) (f 2) (f 3) t = f t := by
  interval_cases t <;> rfl

theorem dom_permW_append (w1 w2 : List Nat) (t s : Nat) (h : dom t (permW w2 (permW w1 s))) :
    dom t (permW (w1 ++ w2) s) := by rw [permW_append]; exact h

theorem d2_cover (code : Nat) (lf : Nat → Nat) (hlf : ∀ t, t < 4 → lf t < 15)
    (hA : cA (tv (F2 code lf)) ≠ 0) (hB : cB (tv (F2 code lf)) ≠ 0) :
    ∃ w j, j < 41 ∧ dom (tv (F2 code lf)) (permW w (tv (TF j))) := by
  -- stage A
  let v := fun t => lf t % 5
  have hv : ∀ t, v t < 5 := fun t => Nat.mod_lt _ (by norm_num)
  have hA0 := allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ stageA_ok
    (v 0) (hv 0)) (v 1) (hv 1)) (v 2) (hv 2)) (v 3) (hv 3)
  simp only [Bool.and_eq_true, Nat.blt_eq] at hA0
  obtain ⟨⟨hnv, he⟩, hut⟩ := hA0
  let vs := vec4 (v 0) (v 1) (v 2) (v 3)
  let us := uA vs
  let e := eA vs
  have hus : ∀ t, t < 4 → us t < 5 ∧ dmapC e (us t) = v t := by
    intro t ht
    have h1 := allBelow_spec _ _ hut t ht
    simp only [Bool.and_eq_true, Nat.blt_eq] at h1
    exact ⟨h1.1, (Nat.eq_of_beq_eq_true h1.2).trans (vec4_eq v t ht)⟩
  have hnv' : NV us = true := hnv
  have hu0 : us 0 = 0 := by
    simp only [NV, Bool.and_eq_true] at hnv'; exact Nat.eq_of_beq_eq_true hnv'.1
  -- stage B
  let us' := vec4 0 (us 1) (us 2) (us 3)
  have hus' : ∀ t, t < 4 → us' t = us t := by
    intro t ht; interval_cases t
    · exact hu0.symm
    all_goals rfl
  have hnvB : NV us' = true := by
    have e1 : NV us' = NV us := by
      simp only [NV, fR, hus' 0 (by norm_num), hus' 1 (by norm_num), hus' 2 (by norm_num), hus' 3 (by norm_num)]
    rw [e1]; exact hnv'
  let l := fun t => lf t / 5
  have hl : ∀ t, t < 4 → l t < 3 := fun t ht => by have := hlf t ht; show lf t / 5 < 3; omega
  have hB0 := allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ stageB_ok
    (us 1) (hus 1 (by norm_num)).1) (us 2) (hus 2 (by norm_num)).1) (us 3) (hus 3 (by norm_num)).1
  simp only [] at hB0
  rw [show vec4 0 (us 1) (us 2) (us 3) = us' from rfl, hnvB, cond_true] at hB0
  have hB1 := allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ hB0
    (l 0) (hl 0 (by norm_num))) (l 1) (hl 1 (by norm_num))) (l 2) (hl 2 (by norm_num))) (l 3) (hl 3 (by norm_num))
  simp only [Bool.and_eq_true] at hB1
  obtain ⟨⟨⟨hP, hz0⟩, hmask⟩, hzt⟩ := hB1
  let ls := vec4 (l 0) (l 1) (l 2) (l 3)
  let P := Pw us' ls
  have hP' : ∀ w, w < 5 → P w < 6 := fun w hw => (Nat.blt_eq).mp (allBelow_spec _ _ hP w hw)
  have hz : ∀ t, t < 4 → zB us' ls t < 15 ∧ lam 5 P (zB us' ls t) = us' t + 5 * ls t := by
    intro t ht
    have h1 := allBelow_spec _ _ hzt t ht
    simp only [Bool.and_eq_true, Nat.blt_eq] at h1
    exact ⟨h1.1, Nat.eq_of_beq_eq_true h1.2⟩
  obtain ⟨i, hi, hci⟩ := ncMask_spec _ hmask
  let c := ncAt i
  have hleaf : ∀ t, t < 4 → ncLeaf c t = zB us' ls t := by
    have z0 : zB us' ls 0 = 0 := Nat.eq_of_beq_eq_true hz0
    have z1 := (hz 1 (by norm_num)).1
    have z2 := (hz 2 (by norm_num)).1
    have z3 := (hz 3 (by norm_num)).1
    have hc : c = zB us' ls 1 + 16 * zB us' ls 2 + 256 * zB us' ls 3 := by
      show ncAt i = _; rw [hci]; show zB us' ls 1 + (16 * zB us' ls 2 + 256 * zB us' ls 3) = _; omega
    intro t ht
    interval_cases t
    · exact z0.symm
    all_goals
      show Nat.land (Nat.shiftRight c _) 15 = _
      rw [show (15 : Nat) = 2 ^ 4 - 1 by norm_num]
      first
      | (change (c >>> 0) &&& (2 ^ 4 - 1) = _; rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]; omega)
      | (change (c >>> 4) &&& (2 ^ 4 - 1) = _; rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]; omega)
      | (change (c >>> 8) &&& (2 ^ 4 - 1) = _; rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]; omega)
  have hlt : ∀ t, t < 4 → ncLeaf c t < 15 := fun t ht => by rw [hleaf t ht]; exact (hz t ht).1
  have hlam : ∀ t, t < 4 → lf t = lam e P (ncLeaf c t) := by
    intro t ht
    rw [hleaf t ht]
    have hzt' := hz t ht
    have hzm : P (zB us' ls t % 5) < 6 := hP' _ (Nat.mod_lt _ (by norm_num))
    rw [← lam_split e P _ hzt'.1 hzm, hzt'.2, hus' t ht, (show ls t = l t from vec4_eq l t ht)]
    have hu := hus t ht
    have hlt3 := hl t ht
    show lf t = dmapC e ((us t + 5 * l t) % 5) + 5 * permAt 0 ((us t + 5 * l t) / 5)
    have m1 : (us t + 5 * l t) % 5 = us t := by omega
    have m2 : (us t + 5 * l t) / 5 = l t := by omega
    have m3 : permAt 0 (l t) = l t := by interval_cases (l t) <;> rfl
    rw [m1, m2, m3, hu.2]
    show lf t = lf t % 5 + 5 * (lf t / 5)
    omega
  have he10 : e < 10 := he
  -- rename the normalized formula
  let op := code % 8
  have hF : F2 code lf = act (fun x => fv (lam e P x.val)) (F2 op (ncLeaf c)) := by
    rw [act_F2 _ _ _ hlt]
    exact F2_congr _ _ _ _ (fun k hk => tb_mod8 code k hk) hlam
  obtain ⟨wE, hwE⟩ := tv_act_lam e P he10 hP'
  have htv : tv (F2 code lf) = permW wE (tv (F2 op (ncLeaf c))) := by rw [hF, hwE]
  -- witness
  have hop : op < 8 := Nat.mod_lt _ (by norm_num)
  have hW := allBelow_spec _ _ (allBelow_spec _ _ wit2Check_ok i hi) op hop
  simp only [] at hW
  generalize hr : w2At (8 * i + op) = r at hW
  by_cases h63 : Nat.beq (wT r) 63 = true
  · rw [h63, cond_true] at hW
    exfalso
    have hsrc := improperB_spec _ (by rw [← tv_F2]; exact tv_lt _) hW
    rw [← tv_F2] at hsrc
    rw [htv, cA_permW] at hA
    rw [htv, cB_permW] at hB
    rcases hsrc with h | h
    · exact hA h
    · exact hB h
  · rw [Bool.not_eq_true] at h63
    rw [h63, cond_false] at hW
    simp only [Bool.and_eq_true, Nat.blt_eq] at hW
    obtain ⟨⟨⟨hj, hd⟩, hpv⟩, hdom⟩ := hW
    have hpv' : ∀ v, v < 5 → wP r v < 6 := fun v hv => (Nat.blt_eq).mp (allBelow_spec _ _ hpv v hv)
    obtain ⟨wW, hwW⟩ := tv_act_lam (wD r) (wP r) hd hpv'
    have himg : tv (F2 (tplAt (wT r)) (fun t => lam (wD r) (wP r) (leafOf (tplAt (wT r)) t))) =
        permW wW (tv (TF (wT r))) := by
      rw [← hwW, TF, act_F2 _ _ _ (fun t ht => tplLeaf_lt _ t hj ht)]
    have hd1 := domB_spec _ _ hdom
    rw [← tv_F2, ← tv_F2, himg] at hd1
    refine ⟨wW ++ wE, wT r, hj, ?_⟩
    rw [htv, permW_append]
    exact dom_permW wE hd1

def tableRows : List Nat := [0xffeafcf8ffeeffff, 0xfce8ffeefcf80000, 0xeefcea00eeffee00, 0xeaf8eeffea000000, 0xf8ffe800f800f800, 0xe8eef800e8000000]

-- ===== loops accumulating bits =====
def accRec (P : Nat → Bool) (g : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun t acc => cond (P t) (Nat.lor acc (g t)) acc) n

theorem accRec_mem (P : Nat → Bool) (g : Nat → Nat) (n t b : Nat) (ht : t < n) (hP : P t = true)
    (hg : (g t).testBit b = true) : (accRec P g n).testBit b = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have e : accRec P g (n + 1) = cond (P n) (accRec P g n ||| g n) (accRec P g n) := rfl
    rw [e]
    rcases Nat.lt_or_ge t n with h | h
    · have := ih h
      cases hPn : P n
      · simpa using this
      · simp [Nat.testBit_or, this]
    · have : t = n := by omega
      subst this
      simp [hP, Nat.testBit_or, hg]

def tablePack : Nat := packList tableRows 64
def usedAt (c v : Nat) : Nat :=
  accRec (fun t => Nat.beq (Nat.mod (leafOf c t) 5) v) (fun t => Nat.shiftLeft 1 (Nat.div (leafOf c t) 5)) 4
def usedPlaced (c D v : Nat) : Nat :=
  accRec (fun t => Nat.beq (dmapC D (Nat.mod (leafOf c t) 5)) v) (fun t => Nat.shiftLeft 1 (Nat.div (leafOf c t) 5)) 4
def choiceMask (s t : Nat) : Nat :=
  accRec (fun p => tb tablePack (Nat.add (Nat.mul 64 p) (Nat.lor s (Nat.shiftLeft t 3)))) (fun p => Nat.shiftLeft 1 p) 6

theorem usedAt_mem (c t : Nat) (ht : t < 4) : tb (usedAt c (leafOf c t % 5)) (leafOf c t / 5) = true := by
  rw [tb_eq]
  apply accRec_mem _ _ 4 t _ ht
  · simp [Nat.beq_eq_true_eq]; rfl
  · show (1 <<< (leafOf c t / 5)).testBit (leafOf c t / 5) = true
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]; simp

theorem usedPlaced_mem (c D t : Nat) (ht : t < 4) :
    tb (usedPlaced c D (dmapC D (leafOf c t % 5))) (leafOf c t / 5) = true := by
  rw [tb_eq]
  apply accRec_mem _ _ 4 t _ ht
  · simp [Nat.beq_eq_true_eq]; rfl
  · show (1 <<< (leafOf c t / 5)).testBit (leafOf c t / 5) = true
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]; simp

-- ===== rows of the depth-three list =====
def pvF (pv w : Nat) : Nat := Nat.land (Nat.shiftRight pv (Nat.mul 3 w)) 7
def placeL (cc D pv t : Nat) : Nat :=
  Nat.add (dmapC D (Nat.mod (leafOf cc t) 5))
    (Nat.mul 5 (permAt (pvF pv (dmapC D (Nat.mod (leafOf cc t) 5))) (Nat.div (leafOf cc t) 5)))
def RowF (i D c pv : Nat) (op : Bool) : F := fun z => bop op (TF i z) (F2 (tplAt c) (placeL (tplAt c) D pv) z)
def choiceOK (i D c pv : Nat) : Prop :=
  ∀ w, w < 5 → pvF pv w < 6 ∧ tb (choiceMask (usedAt (tplAt i) w) (usedPlaced (tplAt c) D w)) (pvF pv w) = true

theorem RowF_DF (i D c pv : Nat) (op : Bool) : RowF i D c pv op ∈ DF 3 :=
  bop_DF _ _ _ _ (F2_DF _ _) (F2_DF _ _)

-- ===== the local placement table =====
def stabPt (U s : Nat) : Bool := allBelow 3 (fun m => !tb U m || Nat.beq (permAt s m) m)
def tFac (s r q : Nat) : Nat := pcomp (invP r) (pcomp (invP s) q)
def facOK (Ui Uc q k : Nat) : Bool :=
  let s := Nat.div k 6
  let r := Nat.mod k 6
  let t := tFac s r q
  stabPt Ui s && tb (choiceMask Ui Uc) r && stabPt Uc t && Nat.blt t 6 &&
    allBelow 3 (fun l => Nat.beq (permAt q l) (permAt s (permAt r (permAt t l))))
def tSearch (Ui Uc q : Nat) : Nat := srch (facOK Ui Uc q) 36

def tableCheck : Bool :=
  allBelow 8 (fun Ui => allBelow 8 (fun Uc => allBelow 6 (fun q => facOK Ui Uc q (tSearch Ui Uc q) && Nat.blt (tSearch Ui Uc q) 36)))

set_option maxRecDepth 10000 in
theorem tableCheck_ok : tableCheck = true := by decide +kernel

def dinv (D w : Nat) : Nat := srch (fun v => Nat.beq (dmapC D v) w) 5

def dinvCheck : Bool := allBelow 10 (fun D => allBelow 5 (fun v => Nat.beq (dinv D (dmapC D v)) v))

set_option maxRecDepth 10000 in
theorem dinvCheck_ok : dinvCheck = true := by decide +kernel

theorem dinv_spec (D v : Nat) (hD : D < 10) (hv : v < 5) : dinv D (dmapC D v) = v :=
  Nat.eq_of_beq_eq_true (allBelow_spec _ _ (allBelow_spec _ _ dinvCheck_ok D hD) v hv)

theorem table_spec (Ui Uc q : Nat) (hUi : Ui < 8) (hUc : Uc < 8) (hq : q < 6) :
    let k := tSearch Ui Uc q
    k / 6 < 6 ∧ k % 6 < 6 ∧ tFac (k / 6) (k % 6) q < 6 ∧ stabPt Ui (k / 6) = true ∧
    tb (choiceMask Ui Uc) (k % 6) = true ∧ stabPt Uc (tFac (k / 6) (k % 6) q) = true ∧
    ∀ l, l < 3 → permAt q l = permAt (k / 6) (permAt (k % 6) (permAt (tFac (k / 6) (k % 6) q) l)) := by
  intro k
  have h := allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ tableCheck_ok Ui hUi) Uc hUc) q hq
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hf, hk⟩ := h
  simp only [facOK, Bool.and_eq_true, Nat.blt_eq] at hf
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hf
  refine ⟨by omega, Nat.mod_lt _ (by norm_num), h4, h1, h2, h3, fun l hl => Nat.eq_of_beq_eq_true (allBelow_spec _ _ h5 l hl)⟩

theorem stabPt_fix (U s m : Nat) (h : stabPt U s = true) (hm : m < 3) (hU : tb U m = true) : permAt s m = m := by
  have := allBelow_spec _ _ h m hm
  simp only [hU, Bool.not_true, Bool.false_or] at this
  exact Nat.eq_of_beq_eq_true this

theorem accRec_lt (P : Nat → Bool) (g : Nat → Nat) (n k : Nat) (h : ∀ t, t < n → g t < 2 ^ k) :
    accRec P g n < 2 ^ k := by
  induction n with
  | zero => exact Nat.two_pow_pos k
  | succ n ih =>
    have e : accRec P g (n + 1) = cond (P n) (accRec P g n ||| g n) (accRec P g n) := rfl
    rw [e]
    have ih' := ih (fun t ht => h t (by omega))
    cases P n
    · exact ih'
    · exact Nat.or_lt_two_pow ih' (h n (by omega))

theorem shl_lt8 (c t : Nat) (hc : leafOf c t < 15) : Nat.shiftLeft 1 (Nat.div (leafOf c t) 5) < 2 ^ 3 := by
  show 1 <<< (leafOf c t / 5) < 2 ^ 3
  rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem usedAt_lt (c v : Nat) (hc : ∀ t, t < 4 → leafOf c t < 15) : usedAt c v < 8 :=
  accRec_lt _ _ 4 3 (fun t ht => shl_lt8 c t (hc t ht))

theorem usedPlaced_lt (c D v : Nat) (hc : ∀ t, t < 4 → leafOf c t < 15) : usedPlaced c D v < 8 :=
  accRec_lt _ _ 4 3 (fun t ht => shl_lt8 c t (hc t ht))
def invPCheck : Bool := allBelow 6 (fun a => Nat.blt (invP a) 6)

set_option maxRecDepth 10000 in
theorem invPCheck_ok : invPCheck = true := by decide +kernel

-- ===== forms of the exact depth sets =====
theorem DF1_form (a : F) (ha : a ∈ DF 1) :
    ∃ b x y, x < 15 ∧ y < 15 ∧ a = fun z => bop b (z (fv x)) (z (fv y)) := by
  obtain ⟨a0, ⟨i, rfl⟩, a1, ⟨j, rfl⟩, h⟩ := ha
  rcases h with rfl | rfl
  · exact ⟨false, i.val, j.val, i.isLt, j.isLt, by funext z; simp [bop, fv_val]⟩
  · exact ⟨true, i.val, j.val, i.isLt, j.isLt, by funext z; simp [bop, fv_val]⟩

theorem DF2_form (a : F) (ha : a ∈ DF 2) : ∃ code lf, (∀ t, t < 4 → lf t < 15) ∧ a = F2 code lf := by
  obtain ⟨a1, h1, a2, h2, h⟩ := ha
  obtain ⟨b1, x1, y1, hx1, hy1, rfl⟩ := DF1_form a1 h1
  obtain ⟨b2, x2, y2, hx2, hy2, rfl⟩ := DF1_form a2 h2
  have hlf : ∀ t, t < 4 → vec4 x1 y1 x2 y2 t < 15 := by
    intro t ht; interval_cases t <;> assumption
  rcases h with rfl | rfl <;> cases b1 <;> cases b2
  all_goals first
    | exact ⟨0, vec4 x1 y1 x2 y2, hlf, rfl⟩ | exact ⟨1, vec4 x1 y1 x2 y2, hlf, rfl⟩
    | exact ⟨2, vec4 x1 y1 x2 y2, hlf, rfl⟩ | exact ⟨3, vec4 x1 y1 x2 y2, hlf, rfl⟩
    | exact ⟨4, vec4 x1 y1 x2 y2, hlf, rfl⟩ | exact ⟨5, vec4 x1 y1 x2 y2, hlf, rfl⟩
    | exact ⟨6, vec4 x1 y1 x2 y2, hlf, rfl⟩ | exact ⟨7, vec4 x1 y1 x2 y2, hlf, rfl⟩

theorem DF3_form (g : F) (hg : g ∈ DF 3) :
    ∃ op a b, a ∈ DF 2 ∧ b ∈ DF 2 ∧ g = fun z => bop op (a z) (b z) := by
  obtain ⟨a, ha, b, hb, h⟩ := hg
  rcases h with rfl | rfl
  · exact ⟨false, a, b, ha, hb, rfl⟩
  · exact ⟨true, a, b, ha, hb, rfl⟩

-- ===== empty sides =====
def proper (t : Nat) : Prop := cA t ≠ 0 ∧ cB t ≠ 0

theorem cA_zero (t : Nat) (h : cA t = 0) (p : Nat) (hp : p < 45) : t.testBit p = false := by
  unfold cA at h
  rw [cntR_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hp)
  simpa using this

theorem cB_zero (t : Nat) (h : cB t = 0) (p : Nat) (hp1 : 45 ≤ p) (hp2 : p < 180) : t.testBit p = true := by
  unfold cB at h
  rw [cntR_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr (show p - 45 < 135 by omega))
  rw [show 45 + (p - 45) = p by omega] at this
  simp only [rect, Nat.testBit_xor, testBit_MV, hp1, hp2, decide_true, Bool.true_and] at this
  cases ht : t.testBit p <;> simp_all

theorem improper_child (op : Bool) (ta tb' : Nat) (hg : proper (gate op ta tb')) (hb : ¬ proper tb') :
    dom (gate op ta tb') ta ∧ proper ta := by
  have hdom : dom (gate op ta tb') ta := by
    unfold proper at hb hg
    rw [not_and_or] at hb
    intro p hp
    cases op
    · -- AND
      rcases hb with hb | hb
      · exfalso; apply hg.1
        have hz := cA_zero tb' (by omega)
        unfold cA; rw [cntR_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i hi
        rw [Finset.mem_range] at hi
        show ¬ (Nat.land ta tb').testBit (0 + i) = true
        change ¬ (ta &&& tb').testBit (0 + i) = true
        rw [Nat.testBit_and, hz _ (by omega)]; simp
      · have hz := cB_zero tb' (by omega)
        constructor
        · intro _ h1
          change (ta &&& tb').testBit p = true at h1
          rw [Nat.testBit_and, Bool.and_eq_true] at h1; exact h1.1
        · intro hp45 h1
          change (ta &&& tb').testBit p = true
          rw [Nat.testBit_and, h1, hz p hp45 hp]; rfl
    · -- OR
      rcases hb with hb | hb
      · have hz := cA_zero tb' (by omega)
        constructor
        · intro hp45 h1
          change (ta ||| tb').testBit p = true at h1
          rw [Nat.testBit_or, hz p hp45, Bool.or_false] at h1; exact h1
        · intro _ h1
          change (ta ||| tb').testBit p = true
          rw [Nat.testBit_or, h1]; rfl
      · exfalso; apply hg.2
        have hz := cB_zero tb' (by omega)
        unfold cB; rw [cntR_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i hi
        rw [Finset.mem_range] at hi
        simp only [rect, Nat.testBit_xor, testBit_MV, show 45 ≤ 45 + i by omega, show 45 + i < 180 by omega,
          decide_true, Bool.true_and]
        change ¬ (!(ta ||| tb').testBit (45 + i)) = true
        rw [Nat.testBit_or, hz (45 + i) (by omega) (by omega)]; simp
  refine ⟨hdom, ?_, ?_⟩
  · have := cA_mono hdom; have := hg.1; omega
  · have := cB_mono hdom; have := hg.2; omega

theorem gate_comm (op : Bool) (x y : Nat) : gate op x y = gate op y x := by
  cases op
  · exact Nat.land_comm x y
  · exact Nat.lor_comm x y

theorem permW_inv' (w : List Nat) (t : Nat) (ht : t < 2 ^ 180) : permW w (permW (invW w) t) = t := by
  rw [← permW_append]
  exact permW_id _ _ ht (fun p hp => idxW_inv' w p hp)

-- ===== the depth-three cover =====
theorem pvF_pack (r : Nat → Nat) (hr : ∀ w, w < 5 → r w < 6) (w : Nat) (hw : w < 5) :
    pvF (r 0 + 8 * r 1 + 64 * r 2 + 512 * r 3 + 4096 * r 4) w = r w := by
  have h0 := hr 0 (by norm_num); have h1 := hr 1 (by norm_num); have h2 := hr 2 (by norm_num)
  have h3 := hr 3 (by norm_num); have h4 := hr 4 (by norm_num)
  unfold pvF
  change (_ >>> (3 * w)) &&& (2 ^ 3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  interval_cases w <;> simp <;> omega

theorem srch_le (P : Nat → Bool) (n : Nat) : srch P (n + 1) ≤ n := by
  induction n with
  | zero => show cond (P 0) 0 0 ≤ 0; cases P 0 <;> simp
  | succ n ih =>
    show cond (P (n + 1)) (n + 1) (srch P (n + 1)) ≤ n + 1
    cases P (n + 1)
    · exact Nat.le_succ_of_le ih
    · exact le_rfl

-- ===== which order of a pair of templates is checked =====
def orPack : Nat := 0x1a83bffec7e7ee7d7e8f8d2554140010c08075222f74c43221a41f40401cbcd9405489023ec4723a4e53baf05442cb36109dc5843d0c32128df9dc3b0048bff6cac8143f6dc0e08a4bb369040f0f80dcf047c38b3370e103af0c455c43efb71006bc9ff1dbf198c95ef564d02fc7ac1eac0fa6233034c96d9ff974a3c54cd46ef2e82acc0951f39f234859c6fe8fed01557bd795957bb72afcf6beafb9b3bfbfbf8f937ef47f7356514b79f8460e39d7ff0bc5e4c83378e3485560e3a8bd797c8b39d6a3b06728111bb7b7472fd57bfb8e527
def ocheck (i c : Nat) : Bool := tb orPack (Nat.add (Nat.mul 41 i) c)
def orientCheck : Bool := allBelow 41 (fun i => allBelow 41 (fun c => ocheck i c || ocheck c i))

set_option maxRecDepth 100000 in
theorem orientCheck_ok : orientCheck = true := by decide +kernel

theorem orient (i c : Nat) (hi : i < 41) (hc : c < 41) : ocheck i c = true ∨ ocheck c i = true := by
  have h := allBelow_spec _ _ (allBelow_spec _ _ orientCheck_ok i hi) c hc
  simp only [Bool.or_eq_true] at h
  exact h

-- ===== reflections fixing a template, where there is one =====
def dTPack : Nat := 0x3f3f2f33f3ff242f4fffff2312f141f223f22f2f1
def pTPack : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000000000000023000000000000000000000000080000000000000000000000000000000000
def dT (i : Nat) : Nat := fld dTPack 4 i
def pT (i v : Nat) : Nat := fld (fld pTPack 15 i) 3 v
def symOK (i : Nat) : Bool := Nat.blt (dT i) 10 && allBelow 5 (fun v => Nat.blt (pT i v) 6) &&
  Nat.beq (evalT2 (tplAt i) (fun t => lam (dT i) (pT i) (leafOf (tplAt i) t))) (evalT2 (tplAt i) (leafOf (tplAt i)))
def dcPack : Nat := 0x8765932104765982104365987104325987604321987654321001234567894012395678340128956723401789561234067895
def dcT (d e : Nat) : Nat := fld dcPack 4 (Nat.add (Nat.mul 10 d) e)
def dcTCheck : Bool := allBelow 10 (fun d => allBelow 10 (fun e => Nat.beq (dcT d e) (dc d e)))
def rep2Pack : Nat := 0xd07c0d07c0707c0d0341f0341f07c0702c0707c0b07c1f07c1f07c070340701c1f01c0b01c1f01c070341f01c0707c0707c0707fff07fff07fff07c1fffc1ffffff07c1f07fff07fffffffffffff07c1f07c1fffc1f07c1fffc1f07c1fffc1f07fff07fff07c0d07c0d07c0707c0d0341f0341f07c0702c0707c0b07c1f07c1f07c070340701c1f01c0b01c1f01c070341f01c0707c0707c0707fff07fff07fff07c1fffc1ffffff07c1f07fff07fffffffffffff07c1f07c1fffc1f07c1fffc1f07c1fffc1f07fff07fff07c0707c0707c0707c0701c1f01c1f07c070340707c0d07c1f07c1f07c0701c1301c1f04c0d04c1f01c0701c1f01c0707c0707c1307fff07fff07fff07c1fffc1ffffff07c1f07fff07fffffffffffff07c1f07c1fffc1f07c1fffc1f07c1fffc1f07fff07fff07c0d07c0d07c0707c0d0341f0341f07c0702c0707c0b07c1f07c1f07c070340701c1f01c0b01c1f01c070341f01c0707c0707c070341f0341f01c1f0340d07c0d07c1f01c0b01c1f02c1f07c1f07c1f01c0d01c0707c0702c0707c0701c0d07c0701c1f01c1f01c1fffc1fffc1fffc1f07fff07fffffc1f07c1fffc1fffffffffffffc1f07c1f07fff07c1f07fff07c1f07fff07c1fffc1fffc1f0341f0341f01c1f0340d07c0d07c1f01c0b01c1f02c1f07c1f07c1f01c0d01c0707c0702c0707c0701c0d07c0701c1f01c1f01c1fffc1fffc1fffc1f07fff07fffffc1f07c1fffc1fffffffffffffc1f07c1f07fff07c1f07fff07c1f07fff07c1fffc1fffc1f07fff07fff07fff07c1fffc1ffffff07c1f07fff07fffffffffffff07c1f07c1fffc1f07c1fffc1f07c1fffc1f07fff07fff07c0707c0707c0707c0701c1f01c1f07c070340707c0d07c1f07c1f07c0701c1301c1f04c0d04c1f01c0701c1f01c0707c0707c1302c1f02c1f0341f02c0b07c0b07c1f034130341f04c1f07c1f07c1f0340b01c0d07c0704c0707c0d0340b07c0d0341f0341f01c0707c0707c0707c0701c1f01c1f07c070340707c0d07c1f07c1f07c0701c1301c1f04c0d04c1f01c0701c1f01c0707c0707c1307fff07fff07fff07c1fffc1ffffff07c1f07fff07fffffffffffff07c1f07c1fffc1f07c1fffc1f07c1fffc1f07fff07fff07c0b07c0b07c0d07c0b02c1f02c1f07c0d04c0d07c1307c1f07c1f07c0d02c070341f01c1301c1f0340d02c1f0340d07c0d07c0707fff07fff07fff07c1fffc1ffffff07c1f07fff07fffffffffffff07c1f07c1fffc1f07c1fffc1f07c1fffc1f07fff07fff07c1fffc1fffc1fffc1f07fff07fffffc1f07c1fffc1fffffffffffffc1f07c1f07fff07c1f07fff07c1f07fff07c1fffc1fffc1f07fff07fff07fff07c1fffc1ffffff07c1f07fff07fffffffffffff07c1f07c1fffc1f07c1fffc1f07c1fffc1f07fff07fff07c1fffc1fffc1fffc1f07fff07fffffc1f07c1fffc1fffffffffffffc1f07c1f07fff07c1f07fff07c1f07fff07c1fffc1fffc1f07fff07fff07fff07c1fffc1ffffff07c1f07fff07fffffffffffff07c1f07c1fffc1f07c1fffc1f07c1fffc1f07fff07fff07c0707c0707c0707c0701c1f01c1f07c070340707c0d07c1f07c1f07c0701c1301c1f04c0d04c1f01c0701c1f01c0707c0707c130341f0341f01c1f0340d07c0d07c1f01c0b01c1f02c1f07c1f07c1f01c0d01c0707c0702c0707c0701c0d07c0701c1f01c1f01c0707c0707c1307c0701c1f01c1f07c1301c1307c0707c1f07c1f07c1301c0b04c1f02c0702c1f04c1301c1f04c1307c1307c0b01c1f01c1f01c1f01c0707c0707c1f01c0d01c1f0341f07c1f07c1f01c0704c0707c130341307c0701c0707c0701c1f01c1f04c1fffc1fffc1fffc1f07fff07fffffc1f07c1fffc1fffffffffffffc1f07c1f07fff07c1f07fff07c1f07fff07c1fffc1fffc1f01c1f01c1f04c1f01c0707c0707c1f04c0704c1f01c1f07c1f07c1f04c0702c1307c0b01c0b07c1304c0707c1304c1f04c1f02c0b07c0b07c0d07c0b02c1f02c1f07c0d04c0d07c1307c1f07c1f07c0d02c070341f01c1301c1f0340d02c1f0340d07c0d07c0701c1f01c1f04c1f01c0707c0707c1f04c0704c1f01c1f07c1f07c1f04c0702c1307c0b01c0b07c1304c0707c1304c1f04c1f02c1fffc1fffc1fffc1f07fff07fffffc1f07c1fffc1fffffffffffffc1f07c1f07fff07c1f07fff07c1f07fff07c1fffc1fffc1f01c1f01c1f01c1f01c0707c0707c1f01c0d01c1f0341f07c1f07c1f01c0704c0707c130341307c0701c0707c0701c1f01c1f04c0707c0707c0707c0701c1f01c1f07c070340707c0d07c1f07c1f07c0701c1301c1f04c0d04c1f01c0701c1f01c0707c0707c130341f0341f01c1f0340d07c0d07c1f01c0b01c1f02c1f07c1f07c1f01c0d01c0707c0702c0707c0701c0d07c0701c1f01c1f01c1fffc1fffc1fffc1f07fff07fffffc1f07c1fffc1fffffffffffffc1f07c1f07fff07c1f07fff07c1f07fff07c1fffc1fffc1f01c1f01c1f01c1f01c0707c0707c1f01c0d01c1f0341f07c1f07c1f01c0704c0707c130341307c0701c0707c0701c1f01c1f04c0707c0707c0707c0701c1f01c1f07c070340707c0d07c1f07c1f07c0701c1301c1f04c0d04c1f01c0701c1f01c0707c0707c1307fff07fff07fff07c1fffc1ffffff07c1f07fff07fffffffffffff07c1f07c1fffc1f07c1fffc1f07c1fffc1f07fff07fff07c0707c0707c0707c0701c1f01c1f07c070340707c0d07c1f07c1f07c0701c1301c1f04c0d04c1f01c0701c1f01c0707c0707c1307fff07fff07fff07c1fffc1ffffff07c1f07fff07fffffffffffff07c1f07c1fffc1f07c1fffc1f07c1fffc1f07fff07fff07c0707c0707c1307c0701c1f01c1f07c1301c1307c0707c1f07c1f07c1301c0b04c1f02c0702c1f04c1301c1f04c1307c1307c0b
def repOK2 (i c D : Nat) : Bool := tb (fld rep2Pack 10 (Nat.add (Nat.mul 41 i) c)) D
def symCheck : Bool := allBelow 41 (fun i => allBelow 41 (fun c => !ocheck i c || allBelow 10 (fun D =>
  repOK2 i c D || (symOK i && repOK2 i c (dcT (dT i) D)) || (symOK c && repOK2 i c (dcT D (dT c))) ||
  (symOK i && symOK c && repOK2 i c (dcT (dcT (dT i) D) (dT c))))))

set_option maxRecDepth 100000 in
theorem dcTCheck_ok : dcTCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem symCheck_ok : symCheck = true := by decide +kernel

theorem dcT_eq (d e : Nat) (hd : d < 10) (he : e < 10) : dcT d e = dc d e :=
  Nat.eq_of_beq_eq_true (allBelow_spec _ _ (allBelow_spec _ _ dcTCheck_ok d hd) e he)

theorem sym_valid (i : Nat) (hi : i < 41) (h : symOK i = true) :
    dT i < 10 ∧ (∀ v, v < 5 → pT i v < 6) ∧
    ∃ t : List Nat, (∀ x, x < 15 → sig t x = lam (dT i) (pT i) x) ∧ permW t (tv (TF i)) = tv (TF i) := by
  simp only [symOK, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨h1, h3⟩, h4⟩ := h
  have hp : ∀ v, v < 5 → pT i v < 6 := fun v hv => by
    have := allBelow_spec _ _ h3 v hv; simpa [Nat.blt_eq] using this
  refine ⟨h1, hp, ?_⟩
  obtain ⟨t, ht⟩ := lam_real (dT i) (pT i) h1 hp
  refine ⟨t, ht, ?_⟩
  have hl : ∀ j, j < 4 → leafOf (tplAt i) j < 15 := fun j hj => tplLeaf_lt i j hi hj
  rw [← tv_actW, actW_sig, act_congr _ _ ht, TF, act_F2 _ _ _ hl, tv_F2, tv_F2]
  exact Nat.eq_of_beq_eq_true h4
theorem d3_core0 (a b : F) (op : Bool) (w1 u : List Nat) (i : Nat) (hi : i < 41) (hd1 : dom (tv a) (permW w1 (tv (TF i))))
    (c : Nat) (hc : c < 41) (hd2 : dom (tv b) (permW w1 (permW u (tv (TF c)))))
    (D : Nat) (p : Nat → Nat) (hD : D < 10) (hp : ∀ v, v < 5 → p v < 6) (hsig : ∀ x, x < 15 → sig u x = lam D p x) :
    ∃ w pv, choiceOK i D c pv ∧ dom (tv (fun z => bop op (a z) (b z))) (permW w (tv (RowF i D c pv op))) := by
  let ci := tplAt i
  let cc := tplAt c
  have hlI : ∀ t, t < 4 → leafOf ci t < 15 := fun t ht => tplLeaf_lt i t hi ht
  have hlC : ∀ t, t < 4 → leafOf cc t < 15 := fun t ht => tplLeaf_lt c t hc ht
  -- permuted second template
  have hY : permW u (tv (TF c)) = tv (F2 cc (fun t => lam D p (leafOf cc t))) := by
    rw [← tv_actW, actW_sig, act_congr _ _ hsig, TF, act_F2 _ _ _ hlC]
  -- factorization per target vertex
  let q := fun w => p (dinv D w)
  let k := fun w => tSearch (usedAt ci w) (usedPlaced cc D w) (q w)
  let s := fun w => k w / 6
  let r := fun w => k w % 6
  let tt := fun w => tFac (s w) (r w) (q w)
  have hq : ∀ w, w < 5 → q w < 6 := by
    intro w hw
    have : dinv D w < 5 := Nat.lt_of_le_of_lt (srch_le _ 4) (by norm_num)
    exact hp _ this
  have hT := fun w (hw : w < 5) => table_spec (usedAt ci w) (usedPlaced cc D w) (q w)
    (usedAt_lt _ _ hlI) (usedPlaced_lt _ _ _ hlC) (hq w hw)
  have hs : ∀ w, w < 5 → s w < 6 := fun w hw => (hT w hw).1
  have hr : ∀ w, w < 5 → r w < 6 := fun w hw => (hT w hw).2.1
  let pv := r 0 + 8 * r 1 + 64 * r 2 + 512 * r 3 + 4096 * r 4
  have hpv : ∀ w, w < 5 → pvF pv w = r w := fun w hw => pvF_pack r hr w hw
  have hchoice : choiceOK i D c pv := by
    intro w hw
    rw [hpv w hw]
    exact ⟨hr w hw, (hT w hw).2.2.2.2.1⟩
  -- leaf equations
  have hE1 : ∀ t, t < 4 → lam D p (leafOf cc t) = lam 5 s (placeL cc D pv t) := by
    intro t ht
    have hx := hlC t ht
    have hv : leafOf cc t % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have hl : leafOf cc t / 5 < 3 := by omega
    let w := dmapC D (leafOf cc t % 5)
    have hw : w < 5 := dmapC_lt _ _
    have hqw : q w = p (leafOf cc t % 5) := by show p (dinv D w) = _; rw [dinv_spec D _ hD hv]
    have hfac0 := (hT w hw).2.2.2.2.2.2 (leafOf cc t / 5) hl
    have hU := usedPlaced_mem cc D t ht
    have hfix := stabPt_fix _ _ _ (hT w hw).2.2.2.2.2.1 hl hU
    have hfac : permAt (q w) (leafOf cc t / 5) = permAt (s w) (permAt (r w) (leafOf cc t / 5)) := by
      rw [hfix] at hfac0; exact hfac0
    have hrl := permAt_lt (r w) (leafOf cc t / 5) (hr w hw) hl
    have e1 : placeL cc D pv t = w + 5 * permAt (r w) (leafOf cc t / 5) := by
      show dmapC D (leafOf cc t % 5) + 5 * permAt (pvF pv (dmapC D (leafOf cc t % 5))) (leafOf cc t / 5) = _
      rw [hpv w hw]
    have hy : (w + 5 * permAt (r w) (leafOf cc t / 5)) % 5 = w := by omega
    have hy2 : (w + 5 * permAt (r w) (leafOf cc t / 5)) / 5 = permAt (r w) (leafOf cc t / 5) := by omega
    have h5 : dmapC 5 w = w := by interval_cases w <;> rfl
    rw [e1]
    show dmapC D (leafOf cc t % 5) + 5 * permAt (p (leafOf cc t % 5)) (leafOf cc t / 5) =
      dmapC 5 ((w + 5 * permAt (r w) (leafOf cc t / 5)) % 5) +
        5 * permAt (s ((w + 5 * permAt (r w) (leafOf cc t / 5)) % 5)) ((w + 5 * permAt (r w) (leafOf cc t / 5)) / 5)
    rw [hy, hy2, h5, ← hqw, hfac]
  have hE2 : ∀ t, t < 4 → lam 5 s (leafOf ci t) = leafOf ci t := by
    intro t ht
    have hx := hlI t ht
    have hv : leafOf ci t % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have hl : leafOf ci t / 5 < 3 := by omega
    have hU := usedAt_mem ci t ht
    have hfix := stabPt_fix _ _ _ (hT _ hv).2.2.2.1 hl hU
    have h5 : dmapC 5 (leafOf ci t % 5) = leafOf ci t % 5 := by interval_cases (leafOf ci t % 5) <;> rfl
    show dmapC 5 (leafOf ci t % 5) + 5 * permAt (s (leafOf ci t % 5)) (leafOf ci t / 5) = leafOf ci t
    rw [h5, hfix]; omega
  have hpl : ∀ t, t < 4 → placeL cc D pv t < 15 := by
    intro t ht
    have hx := hlC t ht
    have hw := dmapC_lt D (leafOf cc t % 5)
    have hpw : pvF pv (dmapC D (leafOf cc t % 5)) < 6 := by rw [hpv _ hw]; exact hr _ hw
    have := permAt_lt _ (leafOf cc t / 5) hpw (by omega)
    show dmapC D (leafOf cc t % 5) + 5 * permAt (pvF pv (dmapC D (leafOf cc t % 5))) (leafOf cc t / 5) < 15
    omega
  -- the row renamed by the stabilizer element
  obtain ⟨ws, hws⟩ := tv_act_lam 5 s (by norm_num) hs
  have hrow : gate op (tv (TF i)) (permW u (tv (TF c))) = permW ws (tv (RowF i D c pv op)) := by
    rw [← hws, hY]
    have e : act (fun x => fv (lam 5 s x.val)) (RowF i D c pv op) =
        fun z => bop op (F2 ci (fun t => lam 5 s (leafOf ci t)) z) (F2 cc (fun t => lam 5 s (placeL cc D pv t)) z) := by
      rw [← act_F2 _ _ _ hlI, ← act_F2 _ _ _ hpl]; rfl
    rw [e, tv_bop, TF]
    rw [F2_congr ci ci (leafOf ci) (fun t => lam 5 s (leafOf ci t)) (fun _ _ => rfl) (fun t ht => (hE2 t ht).symm)]
    rw [F2_congr cc cc (fun t => lam D p (leafOf cc t)) (fun t => lam 5 s (placeL cc D pv t)) (fun _ _ => rfl) hE1]
  refine ⟨ws ++ w1, pv, hchoice, ?_⟩
  rw [tv_bop, permW_append, ← hrow, permW_gate]
  exact dom_gate op hd1 hd2

def St (a b : F) (i c : Nat) (w1 u : List Nat) (D : Nat) : Prop :=
  ∃ p : Nat → Nat, D < 10 ∧ (∀ v, v < 5 → p v < 6) ∧ (∀ x, x < 15 → sig u x = lam D p x) ∧
    dom (tv a) (permW w1 (tv (TF i))) ∧ dom (tv b) (permW w1 (permW u (tv (TF c))))

theorem adjL (a b : F) (i c : Nat) (hi : i < 41) (hs : symOK i = true) (w1 u : List Nat) (D : Nat)
    (h : St a b i c w1 u D) : ∃ w1' u', St a b i c w1' u' (dc (dT i) D) := by
  obtain ⟨p, hD, hp, hsig, hd1, hd2⟩ := h
  obtain ⟨hdt, hpt, t, ht, hst⟩ := sym_valid i hi hs
  have hti : permW (invW t) (tv (TF i)) = tv (TF i) := by
    conv => lhs; rw [← hst]
    exact permW_inv t _ (tv_lt _)
  refine ⟨invW t ++ w1, u ++ t, fun v => pcomp (pT i (dmapC D v)) (p v), (dc_spec (dT i) D 0 hdt hD (by norm_num)).1,
    fun v hv => (pcomp_spec _ _ 0 (hpt _ (dmapC_lt _ _)) (hp v hv) (by norm_num)).1, ?_, ?_, ?_⟩
  · intro x hx
    have hlx : lam D p x < 15 := lam_lt D p x hx (hp _ (Nat.mod_lt _ (by norm_num)))
    rw [sig_append, hsig x hx, ht _ hlx, lam_comp (dT i) D (pT i) p hdt hD hpt hp x hx]
  · rw [permW_append, hti]; exact hd1
  · rw [permW_append, permW_append u t, permW_inv t _ (permW_lt _ _ (tv_lt _))]; exact hd2

theorem adjR (a b : F) (i c : Nat) (hc : c < 41) (hs : symOK c = true) (w1 u : List Nat) (D : Nat)
    (h : St a b i c w1 u D) : ∃ w1' u', St a b i c w1' u' (dc D (dT c)) := by
  obtain ⟨p, hD, hp, hsig, hd1, hd2⟩ := h
  obtain ⟨hdt, hpt, t, ht, hst⟩ := sym_valid c hc hs
  refine ⟨w1, t ++ u, fun v => pcomp (p (dmapC (dT c) v)) (pT c v), (dc_spec D (dT c) 0 hD hdt (by norm_num)).1,
    fun v hv => (pcomp_spec _ _ 0 (hp _ (dmapC_lt _ _)) (hpt v hv) (by norm_num)).1, ?_, hd1, ?_⟩
  · intro x hx
    have hlx : lam (dT c) (pT c) x < 15 := lam_lt _ _ x hx (hpt _ (Nat.mod_lt _ (by norm_num)))
    rw [sig_append, ht x hx, hsig _ hlx, lam_comp D (dT c) p (pT c) hD hdt hp hpt x hx]
  · rw [permW_append, hst]; exact hd2

theorem d3_fin (a b : F) (op : Bool) (i c : Nat) (hi : i < 41) (hc : c < 41) (w1 u : List Nat) (D : Nat)
    (h : St a b i c w1 u D) (hr : repOK2 i c D = true) :
    ∃ w D pv, D < 10 ∧ repOK2 i c D = true ∧ choiceOK i D c pv ∧
      dom (tv (fun z => bop op (a z) (b z))) (permW w (tv (RowF i D c pv op))) := by
  obtain ⟨p, hD, hp, hsig, hd1, hd2⟩ := h
  obtain ⟨w, pv, hch, hdom⟩ := d3_core0 a b op w1 u i hi hd1 c hc hd2 D p hD hp hsig
  exact ⟨w, D, pv, hD, hr, hch, hdom⟩

theorem d3_core (a b : F) (op : Bool) (w1 : List Nat) (i : Nat) (hi : i < 41) (hd1 : dom (tv a) (permW w1 (tv (TF i))))
    (w2 : List Nat) (c : Nat) (hc : c < 41) (hd2 : dom (tv b) (permW w2 (tv (TF c)))) (ho : ocheck i c = true) :
    ∃ w D pv, D < 10 ∧ repOK2 i c D = true ∧ choiceOK i D c pv ∧
      dom (tv (fun z => bop op (a z) (b z))) (permW w (tv (RowF i D c pv op))) := by
  let u := w2 ++ invW w1
  have hu : permW w2 (tv (TF c)) = permW w1 (permW u (tv (TF c))) := by
    show _ = permW w1 (permW (w2 ++ invW w1) (tv (TF c)))
    rw [permW_append, permW_inv' w1 _ (permW_lt _ _ (tv_lt _))]
  rw [hu] at hd2
  obtain ⟨D, p, hD, hp, hsig⟩ := sig_nf u
  have hst : St a b i c w1 u D := ⟨p, hD, hp, hsig, hd1, hd2⟩
  have h1 := allBelow_spec _ _ (allBelow_spec _ _ symCheck_ok i hi) c hc
  simp only [ho, Bool.not_true, Bool.false_or] at h1
  have hk := allBelow_spec _ _ h1 D hD
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hk
  rcases hk with ((hr | ⟨hs, hr⟩) | ⟨hs, hr⟩) | ⟨⟨hs1, hs2⟩, hr⟩
  · exact d3_fin a b op i c hi hc w1 u D hst hr
  · obtain ⟨hdt, -⟩ := sym_valid i hi hs
    rw [dcT_eq _ _ hdt hD] at hr
    obtain ⟨w1', u', h'⟩ := adjL a b i c hi hs w1 u D hst
    exact d3_fin a b op i c hi hc w1' u' _ h' hr
  · obtain ⟨hdt, -⟩ := sym_valid c hc hs
    rw [dcT_eq _ _ hD hdt] at hr
    obtain ⟨w1', u', h'⟩ := adjR a b i c hc hs w1 u D hst
    exact d3_fin a b op i c hi hc w1' u' _ h' hr
  · obtain ⟨hdt1, -⟩ := sym_valid i hi hs1
    obtain ⟨hdt2, -⟩ := sym_valid c hc hs2
    have hD1 : dc (dT i) D < 10 := (dc_spec (dT i) D 0 hdt1 hD (by norm_num)).1
    rw [dcT_eq _ _ hdt1 hD, dcT_eq _ _ hD1 hdt2] at hr
    obtain ⟨w1', u', h'⟩ := adjL a b i c hi hs1 w1 u D hst
    obtain ⟨w1'', u'', h''⟩ := adjR a b i c hc hs2 w1' u' _ h'
    exact d3_fin a b op i c hi hc w1'' u'' _ h'' hr
theorem d3_pair (a b : F) (ha : a ∈ DF 2) (hb : b ∈ DF 2) (op : Bool) (hpa : proper (tv a)) (hpb : proper (tv b)) :
    ∃ w i D c pv, i < 41 ∧ D < 10 ∧ c < 41 ∧ ocheck i c = true ∧ repOK2 i c D = true ∧ choiceOK i D c pv ∧
      dom (tv (fun z => bop op (a z) (b z))) (permW w (tv (RowF i D c pv op))) := by
  obtain ⟨codeA, lfA, hlA, rfl⟩ := DF2_form a ha
  obtain ⟨codeB, lfB, hlB, rfl⟩ := DF2_form b hb
  obtain ⟨w1, i, hi, hd1⟩ := d2_cover codeA lfA hlA hpa.1 hpa.2
  obtain ⟨w2, c, hc, hd2⟩ := d2_cover codeB lfB hlB hpb.1 hpb.2
  rcases orient i c hi hc with ho | ho
  · obtain ⟨w, D, pv, hD, hrp, hch, hdom⟩ := d3_core _ _ op w1 i hi hd1 w2 c hc hd2 ho
    exact ⟨w, i, D, c, pv, hi, hD, hc, ho, hrp, hch, hdom⟩
  · obtain ⟨w, D, pv, hD, hrp, hch, hdom⟩ := d3_core _ _ op w2 c hc hd2 w1 i hi hd1 ho
    refine ⟨w, c, D, i, pv, hc, hD, hi, ho, hrp, hch, ?_⟩
    rw [tv_bop] at hdom ⊢
    rw [gate_comm]
    exact hdom
theorem d3_cover (g : F) (hg : g ∈ DF 3) (hp : proper (tv g)) :
    ∃ w i D c pv op, i < 41 ∧ D < 10 ∧ c < 41 ∧ ocheck i c = true ∧ repOK2 i c D = true ∧ choiceOK i D c pv ∧
      dom (tv g) (permW w (tv (RowF i D c pv op))) := by
  obtain ⟨op, a, b, ha, hb, rfl⟩ := DF3_form g hg
  rw [tv_bop] at hp
  by_cases hpb : proper (tv b)
  · by_cases hpa : proper (tv a)
    · obtain ⟨w, i, D, c, pv, h1, h2, h3, h0, hr0, h4, h5⟩ := d3_pair a b ha hb op hpa hpb
      exact ⟨w, i, D, c, pv, op, h1, h2, h3, h0, hr0, h4, h5⟩
    · have hp' : proper (gate op (tv b) (tv a)) := by rw [gate_comm]; exact hp
      obtain ⟨hdom, hpb'⟩ := improper_child op (tv b) (tv a) hp' hpa
      obtain ⟨w, i, D, c, pv, h1, h2, h3, h0, hr0, h4, h5⟩ := d3_pair b b hb hb false hpb' hpb'
      refine ⟨w, i, D, c, pv, false, h1, h2, h3, h0, hr0, h4, ?_⟩
      have e : gate false (tv b) (tv b) = tv b := Nat.and_self _
      rw [tv_bop, e] at h5
      rw [tv_bop, gate_comm]
      exact dom_trans hdom h5
  · obtain ⟨hdom, hpa'⟩ := improper_child op (tv a) (tv b) hp hpb
    obtain ⟨w, i, D, c, pv, h1, h2, h3, h0, hr0, h4, h5⟩ := d3_pair a a ha ha false hpa' hpa'
    refine ⟨w, i, D, c, pv, false, h1, h2, h3, h0, hr0, h4, ?_⟩
    rw [tv_bop] at h5
    have e : gate false (tv a) (tv a) = tv a := Nat.and_self _
    rw [e] at h5
    rw [tv_bop]
    exact dom_trans hdom h5

-- ===== repunits and products of packed numbers =====
def rep (W m : Nat) : Nat := Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul W m)) 1) (Nat.sub (Nat.shiftLeft 1 W) 1)

theorem geom (W m : Nat) : (2 ^ W - 1) * pk (fun _ => 1) W m + 1 = 2 ^ (W * m) := by
  induction m with
  | zero => simp [pk]
  | succ m ih =>
    have ha : 1 ≤ 2 ^ W := Nat.one_le_two_pow
    rw [pk]
    calc (2 ^ W - 1) * (2 ^ (W * m) * 1 + pk (fun _ => 1) W m) + 1
        = (2 ^ W - 1) * 2 ^ (W * m) + ((2 ^ W - 1) * pk (fun _ => 1) W m + 1) := by ring
      _ = (2 ^ W - 1) * 2 ^ (W * m) + 2 ^ (W * m) := by rw [ih]
      _ = (2 ^ W - 1 + 1) * 2 ^ (W * m) := by ring
      _ = 2 ^ (W * (m + 1)) := by rw [Nat.sub_add_cancel ha, Nat.mul_add, Nat.mul_one, Nat.pow_add]; ring

theorem rep_eq (W m : Nat) (hW : 0 < W) : rep W m = pk (fun _ => 1) W m := by
  have h := geom W m
  have hpos : 0 < 2 ^ W - 1 := by
    have := Nat.one_lt_two_pow (show W ≠ 0 by omega); omega
  show (1 <<< (W * m) - 1) / (1 <<< W - 1) = _
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft, ← h, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hpos]

theorem pk_append (f : Nat → Nat) (w a b : Nat) :
    pk f w (a + b) = pk f w a + 2 ^ (w * a) * pk (fun j => f (a + j)) w b := by
  induction b with
  | zero => simp [pk]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, pk, ih, pk]
    rw [show w * (a + b) = w * a + w * b by ring, Nat.pow_add]
    ring

theorem pk_mul_pk (f g : Nat → Nat) (W m n : Nat) (hm : 0 < m) :
    pk f (W * m) n * pk g W m = pk (fun k => f (k / m) * g (k % m)) W (m * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    rw [pk, Nat.add_mul, ih, show m * (n + 1) = m * n + m by ring, pk_append]
    have e : pk (fun j => (fun k => f (k / m) * g (k % m)) (m * n + j)) W m = pk (fun j => f n * g j) W m := by
      apply pk_congr; intro j hj
      simp only
      rw [show m * n + j = j + m * n by ring, Nat.add_mul_div_left _ _ hm, Nat.add_mul_mod_self_left,
        Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, Nat.zero_add]
    rw [e, ← pk_mul, show W * m * n = W * (m * n) by ring]
    ring

theorem pk_rep (f : Nat → Nat) (W m n : Nat) (hm : 0 < m) :
    pk f W m * pk (fun _ => 1) (W * m) n = pk (fun k => f (k % m)) W (m * n) := by
  rw [Nat.mul_comm, pk_mul_pk _ _ W m n hm]
  apply pk_congr; intro k _; simp

theorem pk_const (c W n : Nat) : c * pk (fun _ => 1) W n = pk (fun _ => c) W n := by
  rw [pk_mul]; apply pk_congr; intro _ _; simp

theorem pk_zero (w k : Nat) : pk (fun _ => 0) w k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pk, ih]

theorem pk_pad (g : Nat → Nat) (w m N : Nat) (hmN : m ≤ N) (hz : ∀ j, m ≤ j → j < N → g j = 0) :
    pk g w m = pk g w N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmN
  rw [pk_append]
  have : pk (fun j => g (m + j)) w k = 0 := by
    have : pk (fun j => g (m + j)) w k = pk (fun _ => 0) w k := pk_congr _ _ _ _ (fun j hj => hz _ (by omega) (by omega))
    rw [this]; exact pk_zero w k
  rw [this]; simp

theorem Fits_mono (f : Nat → Nat) (w w' n : Nat) (h : Fits f w n) (hw : w ≤ w') : Fits f w' n :=
  fun i hi => lt_of_lt_of_le (h i hi) (Nat.pow_le_pow_right (by norm_num) hw)

theorem gate_pk (b : Bool) (f g : Nat → Nat) (W n : Nat) (hW : 0 < W) (hf : Fits f W n) (hg : Fits g W n) :
    gate b (pk f W n) (pk g W n) = pk (fun i => gate b (f i) (g i)) W n := by
  cases b
  · exact pk_land f g W n hW hf hg
  · exact pk_lor f g W n hW hf hg

theorem gate_lt_pow (b : Bool) (x y k : Nat) (hx : x < 2 ^ k) (hy : y < 2 ^ k) : gate b x y < 2 ^ k := by
  cases b
  · exact lt_of_le_of_lt Nat.and_le_left hx
  · exact Nat.or_lt_two_pow hx hy

-- ===== multi-lane popcount: six pair-sum steps =====
def pstepsR (X R : Nat) : Nat :=
  pstep (pstep (pstep (pstep (pstep (pstep X (Nat.mul Q1 R) 1) (Nat.mul Q2 R) 2) (Nat.mul Q4 R) 4)
    (Nat.mul Q8 R) 8) (Nat.mul Q16 R) 16) (Nat.mul Q32 R) 32

theorem mask_rep (w N n : Nat) (Q : Nat) (hQ : Q = pk (fun _ => 2 ^ w - 1) (2 * w) N) (h256 : 2 * w * N = 256) (hN : 0 < N) :
    Nat.mul Q (rep 256 n) = pk (fun _ => 2 ^ w - 1) (2 * w) (N * n) := by
  show Q * rep 256 n = _
  rw [rep_eq 256 n (by norm_num), hQ, ← h256, pk_rep _ _ _ _ hN]

theorem lanePop (X n : Nat) (hX : X < 2 ^ (256 * n)) :
    pstepsR X (rep 256 n) = pk (fun j => cntR X (64 * j) 64) 64 (4 * n) := by
  have h0 : pk (fun j => cntR X (1 * j) 1) 1 (2 * (128 * n)) = X := by
    conv_rhs => rw [← pk_bits X (256 * n) hX]
    rw [show 2 * (128 * n) = 256 * n by ring]
    exact pk_congr _ _ _ _ (fun i _ => by simp)
  unfold pstepsR
  conv_lhs => rw [← h0]
  rw [pstep_eq X 1 (128 * n) (by norm_num) _ (mask_rep 1 128 n Q1 Q1_eq (by norm_num) (by norm_num))]
  rw [show pk (fun j => cntR X (2 * 1 * j) (2 * 1)) (2 * 1) (128 * n) = pk (fun j => cntR X (2 * j) 2) 2 (2 * (64 * n)) by
    rw [show 2 * (64 * n) = 128 * n by ring]]
  rw [pstep_eq X 2 (64 * n) (by norm_num) _ (mask_rep 2 64 n Q2 Q2_eq (by norm_num) (by norm_num))]
  rw [show pk (fun j => cntR X (2 * 2 * j) (2 * 2)) (2 * 2) (64 * n) = pk (fun j => cntR X (4 * j) 4) 4 (2 * (32 * n)) by
    rw [show 2 * (32 * n) = 64 * n by ring]]
  rw [pstep_eq X 4 (32 * n) (by norm_num) _ (mask_rep 4 32 n Q4 Q4_eq (by norm_num) (by norm_num))]
  rw [show pk (fun j => cntR X (2 * 4 * j) (2 * 4)) (2 * 4) (32 * n) = pk (fun j => cntR X (8 * j) 8) 8 (2 * (16 * n)) by
    rw [show 2 * (16 * n) = 32 * n by ring]]
  rw [pstep_eq X 8 (16 * n) (by norm_num) _ (mask_rep 8 16 n Q8 Q8_eq (by norm_num) (by norm_num))]
  rw [show pk (fun j => cntR X (2 * 8 * j) (2 * 8)) (2 * 8) (16 * n) = pk (fun j => cntR X (16 * j) 16) 16 (2 * (8 * n)) by
    rw [show 2 * (8 * n) = 16 * n by ring]]
  rw [pstep_eq X 16 (8 * n) (by norm_num) _ (mask_rep 16 8 n Q16 Q16_eq (by norm_num) (by norm_num))]
  rw [show pk (fun j => cntR X (2 * 16 * j) (2 * 16)) (2 * 16) (8 * n) = pk (fun j => cntR X (32 * j) 32) 32 (2 * (4 * n)) by
    rw [show 2 * (4 * n) = 8 * n by ring]]
  rw [pstep_eq X 32 (4 * n) (by norm_num) _ (mask_rep 32 4 n Q32 Q32_eq (by norm_num) (by norm_num))]

-- ===== counting helpers =====
theorem cntR_zero_bits (x lo n : Nat) (h : ∀ i, lo ≤ i → i < lo + n → x.testBit i = false) : cntR x lo n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [cntR]; rw [ih (fun i h1 h2 => h i h1 (by omega)), h (lo + n) (by omega) (by omega)]; rfl

theorem cntR_off (x y base c k : Nat) (h : ∀ b, b < k → x.testBit (base + c + b) = y.testBit (c + b)) :
    cntR x (base + c) k = cntR y c k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [cntR]; rw [ih (fun b hb => h b (by omega)), h k (by omega)]

theorem cntR_comp (x M lo n : Nat) (hM : ∀ i, lo ≤ i → i < lo + n → M.testBit i = true) :
    cntR (x ^^^ M) lo n + cntR x lo n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cntR]
    have h1 := ih (fun i h1 h2 => hM i h1 (by omega))
    rw [Nat.testBit_xor, hM (lo + n) (by omega) (by omega)]
    cases x.testBit (lo + n) <;> simp <;> omega

theorem cB_acc (t : Nat) : cB t + cntR t 45 135 = 135 := by
  unfold cB rect
  exact cntR_comp t MV 45 135 (fun i h1 h2 => by rw [testBit_MV]; simp; omega)

-- ===== combined layout: accepted U at bits 0..44, accepted V at bits 64..198 =====
def prepR (O R : Nat) : Nat := Nat.lor (Nat.land O (Nat.mul MA R)) (Nat.shiftLeft (Nat.land O (Nat.mul MV R)) 19)

theorem MA_lt : MA < 2 ^ 45 := by unfold MA; omega
theorem MV_lt : MV < 2 ^ 180 := by unfold MV; omega

theorem prep_bits (t p : Nat) : (prepR t 1).testBit p =
    ((decide (p < 45) && t.testBit p) || (decide (64 ≤ p) && decide (p < 199) && t.testBit (p - 19))) := by
  show ((t &&& (MA * 1)) ||| ((t &&& (MV * 1)) <<< 19)).testBit p = _
  rw [Nat.mul_one, Nat.mul_one, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_and,
    testBit_MA, testBit_MV]
  by_cases h1 : p < 45
  · simp [h1, show ¬ (64 ≤ p) by omega]
    intro _ h2; omega
  · by_cases h2 : 64 ≤ p
    · by_cases h3 : p < 199
      · simp [h1, h2, h3, show 19 ≤ p by omega, show 45 ≤ p - 19 by omega, show p - 19 < 180 by omega]
      · simp [h1, h2, h3, show 19 ≤ p by omega, show ¬ (p - 19 < 180) by omega]
    · by_cases h4 : 19 ≤ p
      · simp [h1, h2, h4, show ¬ (45 ≤ p - 19) by omega]
      · simp [h1, h2, h4]

theorem prep_lt (t : Nat) : prepR t 1 < 2 ^ 256 := by
  have h1 : t &&& (MA * 1) < 2 ^ 256 := lt_of_lt_of_le (Nat.and_lt_two_pow t (by rw [Nat.mul_one]; exact MA_lt)) (by norm_num)
  have h2 : (t &&& (MV * 1)) <<< 19 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    have : t &&& (MV * 1) < 2 ^ 180 := Nat.and_lt_two_pow t (by rw [Nat.mul_one]; exact MV_lt)
    calc (t &&& (MV * 1)) * 2 ^ 19 < 2 ^ 180 * 2 ^ 19 := Nat.mul_lt_mul_of_pos_right this (by norm_num)
      _ ≤ 2 ^ 256 := by norm_num
  exact Nat.or_lt_two_pow h1 h2

theorem prep_cA (t : Nat) : cntR (prepR t 1) 0 64 = cA t := by
  unfold cA
  rw [show (64 : Nat) = 45 + 19 by rfl, cntR_add]
  have hz : cntR (prepR t 1) (0 + 45) 19 = 0 := cntR_zero_bits _ _ _ (fun i h1 h2 => by
    rw [prep_bits]; simp [show ¬ (i < 45) by omega, show ¬ (64 ≤ i) by omega])
  rw [hz, Nat.add_zero]
  apply cntR_congr; intro i _ hi
  rw [prep_bits]; simp [show i < 45 by omega, show ¬ (64 ≤ i) by omega]

theorem prep_cV (t : Nat) : cntR (prepR t 1) 64 192 = cntR t 45 135 := by
  rw [show (192 : Nat) = 135 + 57 by rfl, cntR_add]
  have hz : cntR (prepR t 1) (64 + 135) 57 = 0 := cntR_zero_bits _ _ _ (fun i h1 h2 => by
    rw [prep_bits]; simp [show ¬ (i < 45) by omega, show ¬ (i < 199) by omega])
  rw [hz, Nat.add_zero]
  have := cntR_off (prepR t 1) t 19 45 135 (fun b hb => by
    rw [prep_bits]
    simp [show ¬ (19 + 45 + b < 45) by omega, show 64 ≤ 19 + 45 + b by omega, show 19 + 45 + b < 199 by omega]
    congr 1; omega)
  simpa using this

-- per-row counts with one lane
def cntAB (t : Nat) : Nat := pstepsR (prepR t 1) 1
def popA2 (t : Nat) : Nat := fld (cntAB t) 64 0
def popB2 (t : Nat) : Nat := Nat.sub 135 (Nat.add (fld (cntAB t) 64 1) (Nat.add (fld (cntAB t) 64 2) (fld (cntAB t) 64 3)))

theorem rep_one : rep 256 1 = 1 := by decide

theorem cntAB_eq (t : Nat) : cntAB t = pk (fun j => cntR (prepR t 1) (64 * j) 64) 64 4 := by
  have h := lanePop (prepR t 1) 1 (by simpa using prep_lt t)
  rw [rep_one] at h
  exact h

theorem cnt_fits (X : Nat) (n : Nat) : Fits (fun j => cntR X (64 * j) 64) 64 n :=
  fun j _ => lt_of_le_of_lt (cntR_le _ _ _) (by norm_num)

theorem popA2_eq (t : Nat) : popA2 t = cA t := by
  unfold popA2
  rw [cntAB_eq, fld_pk _ _ _ _ (by norm_num) (cnt_fits _ _) (by norm_num)]
  simpa using prep_cA t

theorem popB2_eq (t : Nat) : popB2 t = cB t := by
  unfold popB2
  rw [cntAB_eq, fld_pk _ _ _ _ (by norm_num) (cnt_fits _ _) (by norm_num),
    fld_pk _ _ _ _ (by norm_num) (cnt_fits _ _) (by norm_num), fld_pk _ _ _ _ (by norm_num) (cnt_fits _ _) (by norm_num)]
  have h1 : cntR (prepR t 1) (64 * 1) 64 + (cntR (prepR t 1) (64 * 2) 64 + cntR (prepR t 1) (64 * 3) 64) =
      cntR (prepR t 1) 64 192 := by
    rw [show (192 : Nat) = 64 + 64 + 64 by rfl, cntR_add, cntR_add]; ring_nf
  have h2 := cB_acc t
  show 135 - (cntR (prepR t 1) (64 * 1) 64 + (cntR (prepR t 1) (64 * 2) 64 + cntR (prepR t 1) (64 * 3) 64)) = cB t
  rw [h1, prep_cV]; omega

def F0 : Nat := 0xffffffffffffffff

-- hits of a lane: bit 256*i is set when image i makes a hit
def hitsOf (ta tb n X6 : Nat) : Nat :=
  Nat.land (Nat.land
    (Nat.shiftRight (Nat.add (Nat.land X6 (Nat.mul F0 (rep 256 n))) (Nat.mul (Nat.sub 64 ta) (rep 256 n))) 6)
    (Nat.shiftRight (Nat.sub (Nat.mul (Nat.sub 391 tb) (rep 256 n))
      (Nat.land (Nat.add (Nat.add (Nat.shiftRight X6 64) (Nat.shiftRight X6 128)) (Nat.shiftRight X6 192))
        (Nat.mul F0 (rep 256 n)))) 8)) (rep 256 n)

def laneHits (op : Bool) (ta tb n P r : Nat) : Nat :=
  hitsOf ta tb n (pstepsR (prepR (gate op (Nat.mul r (rep 256 n)) P) (rep 256 n)) (rep 256 n))

theorem pk_shl19 (g : Nat → Nat) (n : Nat) : Nat.shiftLeft (pk g 256 n) 19 = pk (fun i => Nat.shiftLeft (g i) 19) 256 n := by
  show pk g 256 n <<< 19 = pk (fun i => g i <<< 19) 256 n
  rw [Nat.shiftLeft_eq, Nat.mul_comm, pk_mul]
  apply pk_congr; intro i _; rw [Nat.shiftLeft_eq, Nat.mul_comm]

theorem prepR_pk (o : Nat → Nat) (n : Nat) (ho : ∀ i, i < n → o i < 2 ^ 180) :
    prepR (pk o 256 n) (rep 256 n) = pk (fun i => prepR (o i) 1) 256 n := by
  have hR := rep_eq 256 n (by norm_num)
  have fo : Fits o 256 n := fun i hi => lt_of_lt_of_le (ho i hi) (by norm_num)
  have fA : Fits (fun _ => MA) 256 n := fun _ _ => lt_of_lt_of_le MA_lt (by norm_num)
  have fV : Fits (fun _ => MV) 256 n := fun _ _ => lt_of_lt_of_le MV_lt (by norm_num)
  unfold prepR
  rw [hR]
  show (pk o 256 n &&& MA * pk (fun _ => 1) 256 n) ||| Nat.shiftLeft (pk o 256 n &&& MV * pk (fun _ => 1) 256 n) 19 = _
  rw [pk_const, pk_const, pk_land _ _ _ _ (by norm_num) fo fA, pk_land _ _ _ _ (by norm_num) fo fV, pk_shl19]
  have f1 : Fits (fun i => o i &&& MA) 256 n := fun i _ =>
    lt_of_lt_of_le (Nat.and_lt_two_pow _ MA_lt) (by norm_num)
  have f2 : Fits (fun i => Nat.shiftLeft (o i &&& MV) 19) 256 n := fun i _ => by
    show (o i &&& MV) <<< 19 < 2 ^ 256
    rw [Nat.shiftLeft_eq]
    calc (o i &&& MV) * 2 ^ 19 < 2 ^ 180 * 2 ^ 19 := Nat.mul_lt_mul_of_pos_right (Nat.and_lt_two_pow _ MV_lt) (by norm_num)
      _ ≤ 2 ^ 256 := by norm_num
  rw [pk_lor _ _ _ _ (by norm_num) f1 f2]
  apply pk_congr; intro i _
  show (o i &&& MA) ||| Nat.shiftLeft (o i &&& MV) 19 = (o i &&& MA * 1) ||| Nat.shiftLeft (o i &&& MV * 1) 19
  rw [Nat.mul_one, Nat.mul_one]

theorem testBit6 (v : Nat) (h1 : 64 ≤ v) (h2 : v < 128) : v.testBit 6 = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]; simp; omega

theorem testBit8 (v : Nat) (h1 : 256 ≤ v) (h2 : v < 512) : v.testBit 8 = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]; simp; omega

theorem merge4 (f : Nat → Nat) (n : Nat) :
    pk f 64 (4 * n) = pk (fun i => f (4 * i) + 2 ^ 64 * f (4 * i + 1) + 2 ^ 128 * (f (4 * i + 2) + 2 ^ 64 * f (4 * i + 3))) 256 n := by
  rw [show 4 * n = 2 * (2 * n) by ring, pk_merge2, show 2 * 64 = 128 by rfl, pk_merge2, show 2 * 128 = 256 by rfl]
  apply pk_congr; intro i _
  simp only [show 2 * (2 * i) = 4 * i by ring, show 2 * (2 * i) + 1 = 4 * i + 1 by ring,
    show 2 * (2 * i + 1) = 4 * i + 2 by ring, show 2 * (2 * i + 1) + 1 = 4 * i + 3 by ring]

theorem laneHits_spec (op : Bool) (ta tb n P r : Nat) (img : Nat → Nat) (hP : P = pk img 256 n)
    (himg : ∀ i, i < n → img i < 2 ^ 180) (hr : r < 2 ^ 180) (hta : ta ≤ 45) (htb : tb ≤ 135)
    (i : Nat) (hi : i < n) (hA : ta ≤ cA (gate op r (img i))) (hB : tb ≤ cB (gate op r (img i))) :
    (laneHits op ta tb n P r).testBit (256 * i) = true := by
  have hR := rep_eq 256 n (by norm_num)
  let o := fun i => gate op r (img i)
  have ho : ∀ i, i < n → o i < 2 ^ 180 := fun i hi => gate_lt_pow op _ _ _ hr (himg i hi)
  have hO : gate op (Nat.mul r (rep 256 n)) P = pk o 256 n := by
    rw [hP, show Nat.mul r (rep 256 n) = r * rep 256 n from rfl, hR, pk_const]
    exact gate_pk op _ _ 256 n (by norm_num) (fun _ _ => lt_of_lt_of_le hr (by norm_num))
      (fun j hj => lt_of_lt_of_le (himg j hj) (by norm_num))
  let X0 := pk (fun i => prepR (o i) 1) 256 n
  have hX0 : prepR (gate op (Nat.mul r (rep 256 n)) P) (rep 256 n) = X0 := by rw [hO, prepR_pk o n ho]
  have fX0 : Fits (fun i => prepR (o i) 1) 256 n := fun i _ => prep_lt _
  have hX0lt : X0 < 2 ^ (256 * n) := pk_lt _ _ _ fX0
  let f := fun j => cntR X0 (64 * j) 64
  have hX6 : pstepsR X0 (rep 256 n) = pk f 64 (4 * n) := lanePop X0 n hX0lt
  have ff : Fits f 64 (4 * n) := cnt_fits _ _
  have hf_le : ∀ j, f j ≤ 64 := fun j => cntR_le _ _ _
  have hlane : ∀ i, i < n → ∀ q, q < 4 → f (4 * i + q) = cntR (prepR (o i) 1) (64 * q) 64 := by
    intro i hi q hq
    show cntR X0 (64 * (4 * i + q)) 64 = _
    rw [show 64 * (4 * i + q) = 256 * i + 0 + 64 * q by ring]
    have := cntR_off X0 (prepR (o i) 1) (256 * i + 0) (64 * q) 64 (fun b hb => by
      rw [show 256 * i + 0 + 64 * q + b = 256 * i + (64 * q + b) by ring]
      rw [testBit_pk _ 256 n fX0 i _ (by omega)]
      simp [hi])
    rw [show 256 * i + 0 + 64 * q = 256 * i + 0 + 64 * q from rfl] at this
    simpa using this
  have hzero : ∀ j, 4 * n ≤ j → f j = 0 := fun j hj =>
    cntR_zero_above _ _ _ (lt_of_lt_of_le hX0lt (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hfA : f (4 * i) = cA (o i) := by rw [show 4 * i = 4 * i + 0 by rfl, hlane i hi 0 (by norm_num)]; simpa using prep_cA (o i)
  have hfV : f (4 * i + 1) + f (4 * i + 2) + f (4 * i + 3) = 135 - cB (o i) := by
    rw [hlane i hi 1 (by norm_num), hlane i hi 2 (by norm_num), hlane i hi 3 (by norm_num)]
    have h1 : cntR (prepR (o i) 1) 64 192 =
        cntR (prepR (o i) 1) 64 64 + cntR (prepR (o i) 1) 128 64 + cntR (prepR (o i) 1) 192 64 := by
      rw [show (192 : Nat) = 64 + 64 + 64 from rfl, cntR_add, cntR_add]
    have h3 := prep_cV (o i)
    have h2 := cB_acc (o i)
    show cntR (prepR (o i) 1) 64 64 + cntR (prepR (o i) 1) 128 64 + cntR (prepR (o i) 1) 192 64 = 135 - cB (o i)
    omega
  -- the masked low field: cA in each lane
  have hF : Nat.mul F0 (rep 256 n) = pk (fun _ => F0) 256 n := by rw [hR]; exact pk_const _ _ _
  have fF : Fits (fun _ => F0) 256 n := fun _ _ => by unfold F0; norm_num
  have fL : Fits (fun i => f (4 * i) + 2 ^ 64 * f (4 * i + 1) + 2 ^ 128 * (f (4 * i + 2) + 2 ^ 64 * f (4 * i + 3))) 256 n := by
    intro j _
    have a := hf_le (4 * j); have b := hf_le (4 * j + 1); have c := hf_le (4 * j + 2); have d := hf_le (4 * j + 3)
    calc f (4 * j) + 2 ^ 64 * f (4 * j + 1) + 2 ^ 128 * (f (4 * j + 2) + 2 ^ 64 * f (4 * j + 3))
        ≤ 64 + 2 ^ 64 * 64 + 2 ^ 128 * (64 + 2 ^ 64 * 64) := by gcongr
      _ < 2 ^ 256 := by norm_num
  have hlow : Nat.land (pk f 64 (4 * n)) (Nat.mul F0 (rep 256 n)) = pk (fun i => f (4 * i)) 256 n := by
    rw [hF, merge4]
    show pk _ 256 n &&& pk _ 256 n = _
    rw [pk_land _ _ _ _ (by norm_num) fL fF]
    apply pk_congr; intro j _
    show _ &&& 0xffffffffffffffff = _
    rw [show (0xffffffffffffffff : Nat) = 2 ^ 64 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    rw [show f (4 * j) + 2 ^ 64 * f (4 * j + 1) + 2 ^ 128 * (f (4 * j + 2) + 2 ^ 64 * f (4 * j + 3)) =
      f (4 * j) + 2 ^ 64 * (f (4 * j + 1) + 2 ^ 64 * (f (4 * j + 2) + 2 ^ 64 * f (4 * j + 3))) by ring]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (lt_of_le_of_lt (hf_le _) (by norm_num))]
  have hHA : Nat.add (Nat.land (pk f 64 (4 * n)) (Nat.mul F0 (rep 256 n))) (Nat.mul (Nat.sub 64 ta) (rep 256 n)) =
      pk (fun i => f (4 * i) + (64 - ta)) 256 n := by
    rw [hlow, show Nat.mul (Nat.sub 64 ta) (rep 256 n) = (64 - ta) * rep 256 n from rfl, hR, pk_const]
    exact pk_add _ _ _ _
  -- the sum of the three high fields in each lane
  have hshr : ∀ k, k < 4 → pk f 64 (4 * n) >>> (64 * k) = pk (fun j => f (j + k)) 64 (4 * n) := by
    intro k hk
    rw [pk_shr_fields f 64 (4 * n) k (by norm_num) ff]
    exact pk_pad _ _ _ _ (by omega) (fun j h1 _ => hzero _ (by omega))
  have hS : Nat.add (Nat.add (Nat.shiftRight (pk f 64 (4 * n)) 64) (Nat.shiftRight (pk f 64 (4 * n)) 128))
      (Nat.shiftRight (pk f 64 (4 * n)) 192) = pk (fun j => f (j + 1) + f (j + 2) + f (j + 3)) 64 (4 * n) := by
    show pk f 64 (4 * n) >>> (64 * 1) + pk f 64 (4 * n) >>> (64 * 2) + pk f 64 (4 * n) >>> (64 * 3) = _
    rw [hshr 1 (by norm_num), hshr 2 (by norm_num), hshr 3 (by norm_num), pk_add, pk_add]
  let h := fun j => cond (Nat.beq (j % 4) 0) F0 0
  have hh0 : ∀ j, h (4 * j) = F0 := fun j => by
    show cond (Nat.beq ((4 * j) % 4) 0) F0 0 = F0; rw [show (4 * j) % 4 = 0 by omega]; rfl
  have hh1 : ∀ j, h (4 * j + 1) = 0 := fun j => by
    show cond (Nat.beq ((4 * j + 1) % 4) 0) F0 0 = 0; rw [show (4 * j + 1) % 4 = 1 by omega]; rfl
  have hh2 : ∀ j, h (4 * j + 2) = 0 := fun j => by
    show cond (Nat.beq ((4 * j + 2) % 4) 0) F0 0 = 0; rw [show (4 * j + 2) % 4 = 2 by omega]; rfl
  have hh3 : ∀ j, h (4 * j + 3) = 0 := fun j => by
    show cond (Nat.beq ((4 * j + 3) % 4) 0) F0 0 = 0; rw [show (4 * j + 3) % 4 = 3 by omega]; rfl
  have hF64 : pk (fun _ => F0) 256 n = pk h 64 (4 * n) := by
    rw [merge4]; apply pk_congr; intro j _
    show F0 = h (4 * j) + 2 ^ 64 * h (4 * j + 1) + 2 ^ 128 * (h (4 * j + 2) + 2 ^ 64 * h (4 * j + 3))
    rw [hh0, hh1, hh2, hh3]; simp
  have fS : Fits (fun j => f (j + 1) + f (j + 2) + f (j + 3)) 64 (4 * n) := fun j _ => by
    have := hf_le (j + 1); have := hf_le (j + 2); have := hf_le (j + 3)
    show f (j + 1) + f (j + 2) + f (j + 3) < 2 ^ 64
    omega
  have fh : Fits h 64 (4 * n) := fun j _ => by
    show cond (Nat.beq (j % 4) 0) F0 0 < 2 ^ 64
    cases Nat.beq (j % 4) 0 <;> simp [F0]
  have hSF : Nat.land (pk (fun j => f (j + 1) + f (j + 2) + f (j + 3)) 64 (4 * n)) (Nat.mul F0 (rep 256 n)) =
      pk (fun i => f (4 * i + 1) + f (4 * i + 2) + f (4 * i + 3)) 256 n := by
    rw [hF, hF64]
    show pk _ 64 (4 * n) &&& pk h 64 (4 * n) = _
    rw [pk_land _ _ _ _ (by norm_num) fS fh, merge4]
    apply pk_congr; intro j _
    rw [hh0, hh1, hh2, hh3, Nat.and_zero, Nat.and_zero, Nat.and_zero, Nat.mul_zero, Nat.add_zero, Nat.add_zero,
      Nat.mul_zero, Nat.add_zero]
    show (f (4 * j + 1) + f (4 * j + 2) + f (4 * j + 3)) &&& 0xffffffffffffffff = _
    rw [show (0xffffffffffffffff : Nat) = 2 ^ 64 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (fS (4 * j) (by omega))
  have hHB : Nat.sub (Nat.mul (Nat.sub 391 tb) (rep 256 n))
      (Nat.land (Nat.add (Nat.add (Nat.shiftRight (pk f 64 (4 * n)) 64) (Nat.shiftRight (pk f 64 (4 * n)) 128))
        (Nat.shiftRight (pk f 64 (4 * n)) 192)) (Nat.mul F0 (rep 256 n))) =
      pk (fun i => (391 - tb) - (f (4 * i + 1) + f (4 * i + 2) + f (4 * i + 3))) 256 n := by
    rw [hS, hSF, show Nat.mul (Nat.sub 391 tb) (rep 256 n) = (391 - tb) * rep 256 n from rfl, hR, pk_const]
    show pk _ 256 n - pk _ 256 n = _
    rw [pk_sub _ _ _ _ (fun j _ => by
      have := hf_le (4 * j + 1); have := hf_le (4 * j + 2); have := hf_le (4 * j + 3); omega)]
  -- assemble
  unfold laneHits hitsOf
  rw [hX0, hX6, hHA, hHB]
  show ((pk _ 256 n >>> 6) &&& (pk _ 256 n >>> 8) &&& rep 256 n).testBit (256 * i) = true
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight, hR,
    show 6 + 256 * i = 256 * i + 6 by ring, show 8 + 256 * i = 256 * i + 8 by ring]
  have fHA : Fits (fun i => f (4 * i) + (64 - ta)) 256 n := fun j _ => by
    have := hf_le (4 * j)
    show f (4 * j) + (64 - ta) < 2 ^ 256
    exact lt_of_lt_of_le (show f (4 * j) + (64 - ta) < 2 ^ 8 by omega) (by norm_num)
  have fHB : Fits (fun i => (391 - tb) - (f (4 * i + 1) + f (4 * i + 2) + f (4 * i + 3))) 256 n := fun j _ => by
    show (391 - tb) - (f (4 * j + 1) + f (4 * j + 2) + f (4 * j + 3)) < 2 ^ 256
    exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_lt_of_le (show 391 - tb < 2 ^ 9 by omega) (by norm_num))
  have f1 : Fits (fun _ => 1) 256 n := fun _ _ => by norm_num
  rw [show 256 * i + 6 = 256 * i + 6 from rfl, testBit_pk _ 256 n fHA i 6 (by norm_num),
    testBit_pk _ 256 n fHB i 8 (by norm_num), show 256 * i = 256 * i + 0 by rfl, testBit_pk _ 256 n f1 i 0 (by norm_num)]
  have hA' : ta ≤ cA (o i) := hA
  have hB' : tb ≤ cB (o i) := hB
  have hcA : cA (o i) ≤ 45 := cntR_le _ _ _
  have hcB : cB (o i) ≤ 135 := cntR_le _ _ _
  simp only [hi, decide_true, Bool.true_and, Nat.testBit_zero, Nat.one_mod, Bool.and_true]
  rw [hfA, testBit6 _ (by omega) (by omega), Bool.true_and]
  have : 391 - tb - (f (4 * i + 1) + f (4 * i + 2) + f (4 * i + 3)) = 256 + (cB (o i) - tb) := by
    rw [hfV]; omega
  rw [this]
  exact testBit8 _ (by omega) (by omega)

-- ===== Kronecker construction of packed columns =====
def kbase (W inner : Nat) (val : Nat → Nat) (L : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun c acc => Nat.add acc (Nat.shiftLeft (val c) (Nat.mul (Nat.mul W inner) c))) L

def kron (W inner L outer : Nat) (val : Nat → Nat) : Nat :=
  Nat.mul (Nat.mul (kbase W inner val L) (rep W inner)) (rep (Nat.mul (Nat.mul W inner) L) outer)

theorem kbase_eq (W inner : Nat) (val : Nat → Nat) (L : Nat) : kbase W inner val L = pk val (W * inner) L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    show kbase W inner val L + val L <<< (W * inner * L) = _
    rw [ih, pk, Nat.shiftLeft_eq]; ring

theorem kron_eq (W inner L outer : Nat) (val : Nat → Nat) (hW : 0 < W) (hin : 0 < inner) (hL : 0 < L) :
    kron W inner L outer val = pk (fun k => val ((k / inner) % L)) W (inner * L * outer) := by
  show kbase W inner val L * rep W inner * rep (W * inner * L) outer = _
  rw [kbase_eq, rep_eq W inner hW, rep_eq (W * inner * L) outer (by positivity), pk_mul_pk _ _ W inner L hin,
    show W * inner * L = W * (inner * L) by ring, pk_rep _ W (inner * L) outer (by positivity)]
  apply pk_congr; intro k _
  simp only [Nat.mul_one]
  rw [Nat.mod_mul_right_div_self]

-- ===== lanes =====
def laneP (s d : Nat) : Nat :=
  evalHv (hCode s) (fun j => kron 256 (divOf s (Nat.mod (hLeaf (hCode s) j) 5)) (locLen (rankOf s (Nat.mod (hLeaf (hCode s) j) 5)))
    (outOf s (Nat.mod (hLeaf (hCode s) j) 5)) (fun c => varAt (hImg s d (hLeaf (hCode s) j) c)))

def radixShape : Bool :=
  allBelow 41 (fun s => allBelow 5 (fun v => Nat.ble 1 (divOf s v) && Nat.ble 1 (locLen (rankOf s v)) &&
    Nat.beq (Nat.mul (Nat.mul (divOf s v) (locLen (rankOf s v))) (outOf s v)) (nImg s)))

set_option maxRecDepth 10000 in
theorem radixShape_ok : radixShape = true := by decide +kernel

theorem radix_shape (s v : Nat) (hs : s < 41) (hv : v < 5) :
    0 < divOf s v ∧ 0 < locLen (rankOf s v) ∧ divOf s v * locLen (rankOf s v) * outOf s v = nImg s := by
  have h := allBelow_spec _ _ (allBelow_spec _ _ radixShape_ok s hs) v hv
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  exact ⟨h.1.1, h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem varAt_lt (x : Nat) : varAt x < 2 ^ 180 := by rw [← tv_var]; exact tv_lt _

def B180 (f : Nat → Nat) (n : Nat) : Prop := ∀ i, i < n → f i < 2 ^ 180

theorem gate_pk180 (b : Bool) (f g : Nat → Nat) (n : Nat) (hf : B180 f n) (hg : B180 g n) :
    gate b (pk f 256 n) (pk g 256 n) = pk (fun i => gate b (f i) (g i)) 256 n ∧ B180 (fun i => gate b (f i) (g i)) n :=
  ⟨gate_pk b f g 256 n (by norm_num) (fun i hi => lt_of_lt_of_le (hf i hi) (by norm_num))
      (fun i hi => lt_of_lt_of_le (hg i hi) (by norm_num)),
    fun i hi => gate_lt_pow b _ _ _ (hf i hi) (hg i hi)⟩

theorem evalHv_pk (code : Nat) (col : Nat → Nat) (cv : Nat → Nat → Nat) (n : Nat)
    (hcol : ∀ j, j < 8 → col j = pk (fun i => cv i j) 256 n) (hb : ∀ j, j < 8 → B180 (fun i => cv i j) n) :
    evalHv code col = pk (fun i => evalHv code (cv i)) 256 n := by
  unfold evalHv
  rw [hcol 0 (by norm_num), hcol 1 (by norm_num), hcol 2 (by norm_num), hcol 3 (by norm_num),
    hcol 4 (by norm_num), hcol 5 (by norm_num), hcol 6 (by norm_num), hcol 7 (by norm_num)]
  obtain ⟨e1, b1⟩ := gate_pk180 (tb code 3) _ _ n (hb 0 (by norm_num)) (hb 1 (by norm_num))
  obtain ⟨e2, b2⟩ := gate_pk180 (tb code 4) _ _ n (hb 2 (by norm_num)) (hb 3 (by norm_num))
  obtain ⟨e3, b3⟩ := gate_pk180 (tb code 5) _ _ n (hb 4 (by norm_num)) (hb 5 (by norm_num))
  obtain ⟨e4, b4⟩ := gate_pk180 (tb code 6) _ _ n (hb 6 (by norm_num)) (hb 7 (by norm_num))
  rw [e1, e2, e3, e4]
  obtain ⟨e5, b5⟩ := gate_pk180 (tb code 1) _ _ n b1 b2
  obtain ⟨e6, b6⟩ := gate_pk180 (tb code 2) _ _ n b3 b4
  rw [e5, e6]
  exact (gate_pk180 (tb code 0) _ _ n b5 b6).1

theorem laneP_eq (s d : Nat) (hs : s < 41) : laneP s d = pk (fun i => tv (imgF s d i)) 256 (nImg s) := by
  unfold laneP
  rw [evalHv_pk _ _ (fun i j => varAt (imgLf s d i j)) (nImg s)]
  · apply pk_congr; intro i _
    rw [imgF, tv_FH]
  · intro j _
    obtain ⟨h1, h2, h3⟩ := radix_shape s (Nat.mod (hLeaf (hCode s) j) 5) hs (Nat.mod_lt _ (by norm_num))
    rw [kron_eq _ _ _ _ _ (by norm_num) h1 h2, h3]
    rfl
  · intro j _ i _; exact varAt_lt _

-- ===== enumeration of set bits by bisection =====
def winZero (m a b : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight m a) (Nat.sub (Nat.shiftLeft 1 b) 1)) 0

def scanB (W : Nat) (f : Nat → Bool) (m : Nat) : Nat → Nat → Nat → Bool
  | 0, lo, size => winZero m (Nat.mul W lo) (Nat.mul W size) || (Nat.beq size 1 && (!tb m (Nat.mul W lo) || f lo))
  | k + 1, lo, size => winZero m (Nat.mul W lo) (Nat.mul W size) || (Nat.beq size 1 && (!tb m (Nat.mul W lo) || f lo)) ||
      (Nat.ble 2 size && scanB W f m k lo (Nat.div size 2) && scanB W f m k (Nat.add lo (Nat.div size 2)) (Nat.sub size (Nat.div size 2)))

theorem winZero_spec (m a b : Nat) (h : winZero m a b = true) (j : Nat) (hj : j < b) : m.testBit (a + j) = false := by
  have e := Nat.eq_of_beq_eq_true h
  have e2 : (m >>> a) % 2 ^ b = 0 := by
    rw [← Nat.and_two_pow_sub_one_eq_mod]
    have : Nat.shiftLeft 1 b = 2 ^ b := by show 1 <<< b = 2 ^ b; rw [Nat.one_shiftLeft]
    rw [this] at e; exact e
  have := congrArg (fun x => x.testBit j) e2
  simp only [Nat.testBit_mod_two_pow, Nat.zero_testBit, Nat.testBit_shiftRight] at this
  simpa [hj] using this

theorem scanB_spec (W : Nat) (hW : 0 < W) (f : Nat → Bool) (m : Nat) (k : Nat) :
    ∀ lo size, scanB W f m k lo size = true → ∀ i, lo ≤ i → i < lo + size → m.testBit (W * i) = true → f i = true := by
  have base : ∀ lo size, (winZero m (Nat.mul W lo) (Nat.mul W size) = true ∨ (Nat.beq size 1 && (!tb m (Nat.mul W lo) || f lo)) = true) →
      ∀ i, lo ≤ i → i < lo + size → m.testBit (W * i) = true → f i = true := by
    intro lo size h i h1 h2 hm
    rcases h with h | h
    · have := winZero_spec m _ _ h (W * i - W * lo) (by
        show W * i - W * lo < W * size
        have : W * i < W * (lo + size) := Nat.mul_lt_mul_of_pos_left h2 hW
        have : W * lo ≤ W * i := Nat.mul_le_mul_left _ h1
        rw [Nat.mul_add] at *; omega)
      rw [show Nat.mul W lo + (W * i - W * lo) = W * i by
        show W * lo + (W * i - W * lo) = W * i
        have : W * lo ≤ W * i := Nat.mul_le_mul_left _ h1; omega] at this
      rw [this] at hm; exact absurd hm (by simp)
    · simp only [Bool.and_eq_true, Nat.beq_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
      have hi : i = lo := by
        have := Nat.eq_of_beq_eq_true h.1; omega
      subst hi
      rcases h.2 with h3 | h3
      · rw [← tb_eq] at hm; rw [show Nat.mul W i = W * i from rfl] at h3; rw [h3] at hm; exact absurd hm (by simp)
      · exact h3
  induction k with
  | zero => intro lo size h; exact base lo size (by simpa [scanB] using h)
  | succ k ih =>
    intro lo size h i h1 h2 hm
    simp only [scanB, Bool.or_eq_true] at h
    rcases h with h | h
    · exact base lo size h i h1 h2 hm
    · simp only [Bool.and_eq_true, Nat.ble_eq] at h
      obtain ⟨⟨_, ha⟩, hb⟩ := h
      rcases Nat.lt_or_ge i (lo + size / 2) with h3 | h3
      · exact ih lo (size / 2) ha i h1 h3 hm
      · exact ih (lo + size / 2) (size - size / 2) hb i h3 (by omega) hm

-- ===== nested packing =====
theorem pk_nest (G : Nat → Nat → Nat) (w m n : Nat) (hm : 0 < m) :
    pk (fun l => pk (G l) w m) (w * m) n = pk (fun k => G (k / m) (k % m)) w (m * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    rw [pk, ih, show m * (n + 1) = m * n + m by ring, pk_append, show w * m * n = w * (m * n) by ring]
    have e : pk (fun j => (fun k => G (k / m) (k % m)) (m * n + j)) w m = pk (G n) w m := by
      apply pk_congr; intro j hj
      simp only
      rw [show m * n + j = j + m * n by ring, Nat.add_mul_div_left _ _ hm, Nat.add_mul_mod_self_left,
        Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, Nat.zero_add]
    rw [e]; ring

-- ===== bytewise minimum =====
def swarMin (G8 F7 X Y : Nat) : Nat :=
  Nat.lor (Nat.land X (Nat.mul (Nat.shiftRight (Nat.land (Nat.sub (Nat.lor Y G8) X) G8) 7) 127))
    (Nat.land Y (Nat.xor F7 (Nat.mul (Nat.shiftRight (Nat.land (Nat.sub (Nat.lor Y G8) X) G8) 7) 127)))

def cbit (x y : Nat) : Nat := (((y ||| 128) - x) &&& 128) >>> 7

def sminCheck : Bool :=
  allBelow 128 (fun x => allBelow 128 (fun y =>
    Nat.beq (y ||| 128) (y + 128) && Nat.ble x (y ||| 128) && Nat.blt ((y ||| 128) - x) 256 &&
    Nat.beq ((((y ||| 128) - x) &&& 128)) (128 * cbit x y) && Nat.ble (cbit x y) 1 &&
    Nat.beq ((x &&& (cbit x y * 127)) ||| (y &&& (127 ^^^ (cbit x y * 127)))) (min x y)))

set_option maxRecDepth 100000 in
theorem sminCheck_ok : sminCheck = true := by decide +kernel

theorem smin_facts (x y : Nat) (hx : x < 128) (hy : y < 128) :
    x ≤ (y ||| 128) ∧ (y ||| 128) - x < 256 ∧ (((y ||| 128) - x) &&& 128) = 128 * cbit x y ∧ cbit x y ≤ 1 ∧
    ((x &&& (cbit x y * 127)) ||| (y &&& (127 ^^^ (cbit x y * 127)))) = min x y := by
  have h := allBelow_spec _ _ (allBelow_spec _ _ sminCheck_ok x hx) y hy
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  exact ⟨h.1.1.1.1.2, h.1.1.1.2, Nat.eq_of_beq_eq_true h.1.1.2, h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem swarMin_pk (x y : Nat → Nat) (N : Nat) (hx : ∀ k, k < N → x k < 128) (hy : ∀ k, k < N → y k < 128) :
    swarMin (pk (fun _ => 128) 8 N) (pk (fun _ => 127) 8 N) (pk x 8 N) (pk y 8 N) = pk (fun k => min (x k) (y k)) 8 N := by
  have F : ∀ (f : Nat → Nat), (∀ k, k < N → f k < 256) → Fits f 8 N := fun f h k hk => h k hk
  have fx : Fits x 8 N := F _ (fun k hk => by have := hx k hk; omega)
  have fy : Fits y 8 N := F _ (fun k hk => by have := hy k hk; omega)
  have f128 : Fits (fun _ => 128) 8 N := F _ (fun _ _ => by norm_num)
  have f127 : Fits (fun _ => 127) 8 N := F _ (fun _ _ => by norm_num)
  have e1 : Nat.lor (pk y 8 N) (pk (fun _ => 128) 8 N) = pk (fun k => y k ||| 128) 8 N := pk_lor _ _ _ _ (by norm_num) fy f128
  have e2 : Nat.sub (pk (fun k => y k ||| 128) 8 N) (pk x 8 N) = pk (fun k => (y k ||| 128) - x k) 8 N :=
    pk_sub _ _ _ _ (fun k hk => (smin_facts _ _ (hx k hk) (hy k hk)).1)
  have fd : Fits (fun k => (y k ||| 128) - x k) 8 N := F _ (fun k hk => (smin_facts _ _ (hx k hk) (hy k hk)).2.1)
  have e3 : Nat.land (pk (fun k => (y k ||| 128) - x k) 8 N) (pk (fun _ => 128) 8 N) = pk (fun k => 128 * cbit (x k) (y k)) 8 N := by
    rw [show Nat.land _ _ = pk _ 8 N &&& pk _ 8 N from rfl, pk_land _ _ _ _ (by norm_num) fd f128]
    exact pk_congr _ _ _ _ (fun k hk => (smin_facts _ _ (hx k hk) (hy k hk)).2.2.1)
  have e4 : Nat.shiftRight (pk (fun k => 128 * cbit (x k) (y k)) 8 N) 7 = pk (fun k => cbit (x k) (y k)) 8 N := by
    rw [show (fun k => 128 * cbit (x k) (y k)) = (fun k => 128 * (fun k => cbit (x k) (y k)) k) from rfl, ← pk_mul]
    show (128 * pk (fun k => cbit (x k) (y k)) 8 N) >>> 7 = _
    rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 7 = 128 by norm_num, Nat.mul_div_cancel_left _ (by norm_num)]
  have e5 : Nat.mul (pk (fun k => cbit (x k) (y k)) 8 N) 127 = pk (fun k => cbit (x k) (y k) * 127) 8 N := by
    show pk _ 8 N * 127 = _
    rw [Nat.mul_comm, pk_mul]; apply pk_congr; intro k _; ring
  have fm : Fits (fun k => cbit (x k) (y k) * 127) 8 N := F _ (fun k hk => by
    have := (smin_facts _ _ (hx k hk) (hy k hk)).2.2.2.1; show cbit (x k) (y k) * 127 < 256; omega)
  unfold swarMin
  rw [e1, e2, e3, e4, e5]
  show (pk x 8 N &&& pk _ 8 N) ||| (pk y 8 N &&& (pk (fun _ => 127) 8 N ^^^ pk _ 8 N)) = _
  rw [pk_land _ _ _ _ (by norm_num) fx fm, pk_xor _ _ _ _ (by norm_num) f127 fm]
  have fxm : Fits (fun k => 127 ^^^ cbit (x k) (y k) * 127) 8 N := F _ (fun k hk => by
    have := fm k hk; exact Nat.xor_lt_two_pow (by norm_num : (127 : Nat) < 2 ^ 8) this)
  rw [pk_land _ _ _ _ (by norm_num) fy fxm]
  have fa : Fits (fun k => x k &&& cbit (x k) (y k) * 127) 8 N := F _ (fun k hk =>
    lt_of_le_of_lt Nat.and_le_left (by have := hx k hk; omega))
  have fb : Fits (fun k => y k &&& (127 ^^^ cbit (x k) (y k) * 127)) 8 N := F _ (fun k hk =>
    lt_of_le_of_lt Nat.and_le_left (by have := hy k hk; omega))
  rw [pk_lor _ _ _ _ (by norm_num) fa fb]
  exact pk_congr _ _ _ _ (fun k hk => (smin_facts _ _ (hx k hk) (hy k hk)).2.2.2.2)

-- ===== byte sums within 64-bit lanes =====
def bsum (C : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.add C (Nat.shiftRight C 8)) (Nat.shiftRight C 16)) (Nat.shiftRight C 24)) (Nat.shiftRight C 32)

theorem bsum_pk (c : Nat → Nat) (n : Nat) (hc : ∀ k, c k ≤ 40) :
    Nat.land (bsum (pk c 8 (8 * n))) (Nat.mul 255 (rep 64 n)) =
      pk (fun l => c (8 * l) + c (8 * l + 1) + c (8 * l + 2) + c (8 * l + 3) + c (8 * l + 4)) 64 n := by
  let cz := fun i => if i < 8 * n then c i else 0
  have fc : Fits c 8 (8 * n) := fun k _ => by have := hc k; show c k < 2 ^ 8; omega
  have hsh : ∀ t, t < 5 → pk c 8 (8 * n) >>> (8 * t) = pk (fun j => cz (j + t)) 8 (8 * n) := by
    intro t ht
    rw [pk_shr_fields c 8 (8 * n) t (by norm_num) fc]
    rw [pk_congr (fun j => c (j + t)) (fun j => cz (j + t)) 8 (8 * n - t) (fun j hj => by simp only [cz]; rw [if_pos (by omega)])]
    exact pk_pad _ _ _ _ (by omega) (fun j h1 _ => by simp only [cz]; rw [if_neg (by omega)])
  have h0 : pk c 8 (8 * n) = pk (fun j => cz (j + 0)) 8 (8 * n) :=
    pk_congr _ _ _ _ (fun j hj => by simp only [cz, Nat.add_zero]; rw [if_pos hj])
  have hb : bsum (pk c 8 (8 * n)) = pk (fun j => cz (j + 0) + cz (j + 1) + cz (j + 2) + cz (j + 3) + cz (j + 4)) 8 (8 * n) := by
    unfold bsum
    show pk c 8 (8 * n) + pk c 8 (8 * n) >>> (8 * 1) + pk c 8 (8 * n) >>> (8 * 2) + pk c 8 (8 * n) >>> (8 * 3) +
      pk c 8 (8 * n) >>> (8 * 4) = _
    rw [hsh 1 (by norm_num), hsh 2 (by norm_num), hsh 3 (by norm_num), hsh 4 (by norm_num), h0, pk_add, pk_add, pk_add, pk_add]
  have hm : Nat.mul 255 (rep 64 n) = pk (fun k => if k % 8 = 0 then 255 else 0) 8 (8 * n) := by
    show 255 * rep 64 n = _
    rw [rep_eq 64 n (by norm_num), pk_const, show (64 : Nat) = 8 * 8 by rfl]
    rw [show pk (fun _ => 255) (8 * 8) n = pk (fun l => pk (fun e => if e = 0 then 255 else 0) 8 8) (8 * 8) n by
      apply pk_congr; intro _ _; decide]
    rw [pk_nest _ 8 8 n (by norm_num)]
    try (apply pk_congr; intro k _; simp)
  have fs : Fits (fun j => cz (j + 0) + cz (j + 1) + cz (j + 2) + cz (j + 3) + cz (j + 4)) 8 (8 * n) := fun j _ => by
    have h : ∀ i, cz i ≤ 40 := fun i => by simp only [cz]; split <;> [exact hc i; omega]
    have := h (j + 0); have := h (j + 1); have := h (j + 2); have := h (j + 3); have := h (j + 4)
    show cz (j + 0) + cz (j + 1) + cz (j + 2) + cz (j + 3) + cz (j + 4) < 2 ^ 8; omega
  have fmk : Fits (fun k => if k % 8 = 0 then 255 else 0) 8 (8 * n) := fun k _ => by
    show (if k % 8 = 0 then 255 else 0) < 2 ^ 8; split <;> norm_num
  rw [hb, hm]
  show pk _ 8 (8 * n) &&& pk _ 8 (8 * n) = _
  rw [pk_land _ _ _ _ (by norm_num) fs fmk, show 8 * n = 8 * n from rfl]
  rw [← show pk (fun l => pk (fun e => if e = 0 then c (8 * l) + c (8 * l + 1) + c (8 * l + 2) + c (8 * l + 3) + c (8 * l + 4) else 0) 8 8) (8 * 8) n =
      pk (fun l => c (8 * l) + c (8 * l + 1) + c (8 * l + 2) + c (8 * l + 3) + c (8 * l + 4)) 64 n by
    apply pk_congr; intro l _; simp [pk]]
  rw [pk_nest _ 8 8 n (by norm_num)]
  apply pk_congr; intro k hk
  have hk8 : k / 8 < n := by omega
  by_cases h0 : k % 8 = 0
  · simp only [h0, if_true]
    have hk' : k = 8 * (k / 8) := by omega
    have hv : ∀ t, t < 5 → cz (k + t) = c (8 * (k / 8) + t) := fun t ht => by
      simp only [cz]; rw [if_pos (by omega)]; congr 1; omega
    rw [hv 0 (by norm_num), hv 1 (by norm_num), hv 2 (by norm_num), hv 3 (by norm_num), hv 4 (by norm_num)]
    have := fs k hk
    rw [show (255 : Nat) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt]
    · simp
    · rw [← hv 0 (by norm_num), ← hv 1 (by norm_num), ← hv 2 (by norm_num), ← hv 3 (by norm_num), ← hv 4 (by norm_num)]
      exact this
  · simp [h0]

-- ===== block profiles =====
def aE (e t : Nat) : Nat := cntR t (9 * e) 9
def bE (j t : Nat) : Nat := cntR (rect t) (45 + 27 * j) 27

theorem cA_split (t : Nat) : cA t = aE 0 t + aE 1 t + aE 2 t + aE 3 t + aE 4 t := by
  unfold cA aE
  rw [show (45 : Nat) = 9 + 9 + 9 + 9 + 9 by rfl, cntR_add, cntR_add, cntR_add, cntR_add]

theorem cB_split (t : Nat) : cB t = bE 0 t + bE 1 t + bE 2 t + bE 3 t + bE 4 t := by
  unfold cB bE
  rw [show (135 : Nat) = 27 + 27 + 27 + 27 + 27 by rfl, cntR_add, cntR_add, cntR_add, cntR_add]

theorem cntR_and_le (x y lo n : Nat) : cntR (x &&& y) lo n ≤ cntR x lo n ∧ cntR (x &&& y) lo n ≤ cntR y lo n := by
  rw [cntR_card, cntR_card, cntR_card]
  constructor <;> apply Finset.card_le_card <;> intro i <;> simp only [Finset.mem_filter, Nat.testBit_and, Bool.and_eq_true] <;>
    exact fun h => ⟨h.1, by first | exact h.2.1 | exact h.2.2⟩

theorem cntR_or_le (x y lo n : Nat) : cntR (x ||| y) lo n ≤ cntR x lo n + cntR y lo n := by
  rw [cntR_card, cntR_card, cntR_card]
  calc _ ≤ ((Finset.range n).filter (fun i => x.testBit (lo + i) = true) ∪
          (Finset.range n).filter (fun i => y.testBit (lo + i) = true)).card := by
        apply Finset.card_le_card; intro i
        simp only [Finset.mem_filter, Finset.mem_union, Nat.testBit_or, Bool.or_eq_true]; tauto
    _ ≤ _ := Finset.card_union_le _ _

theorem rect_bit (t p : Nat) (h1 : 45 ≤ p) (h2 : p < 180) : (rect t).testBit p = !t.testBit p := by
  unfold rect; rw [Nat.testBit_xor, testBit_MV]; simp [h1, h2]

def combA (op : Bool) (x y : Nat) : Nat := cond op (min 9 (x + y)) (min x y)
def combB (op : Bool) (x y : Nat) : Nat := cond op (min x y) (min 27 (x + y))

theorem aE_gate (op : Bool) (r I e : Nat) : aE e (gate op r I) ≤ combA op (aE e r) (aE e I) := by
  unfold aE combA
  cases op
  · have := cntR_and_le r I (9 * e) 9; exact le_min this.1 this.2
  · exact le_min (cntR_le _ _ _) (cntR_or_le r I _ _)

theorem bE_gate (op : Bool) (r I j : Nat) (hj : j < 5) : bE j (gate op r I) ≤ combB op (bE j r) (bE j I) := by
  unfold bE combB
  cases op
  · have e : cntR (rect (gate false r I)) (45 + 27 * j) 27 = cntR (rect r ||| rect I) (45 + 27 * j) 27 := by
      apply cntR_congr; intro i h1 h2
      rw [rect_bit _ _ (by omega) (by omega), Nat.testBit_or, rect_bit _ _ (by omega) (by omega),
        rect_bit _ _ (by omega) (by omega)]
      show (!(r &&& I).testBit i) = _
      rw [Nat.testBit_and]; cases r.testBit i <;> cases I.testBit i <;> rfl
    rw [e]; exact le_min (cntR_le _ _ _) (cntR_or_le _ _ _ _)
  · have e : cntR (rect (gate true r I)) (45 + 27 * j) 27 = cntR (rect r &&& rect I) (45 + 27 * j) 27 := by
      apply cntR_congr; intro i h1 h2
      rw [rect_bit _ _ (by omega) (by omega), Nat.testBit_and, rect_bit _ _ (by omega) (by omega),
        rect_bit _ _ (by omega) (by omega)]
      show (!(r ||| I).testBit i) = _
      rw [Nat.testBit_or]; cases r.testBit i <;> cases I.testBit i <;> rfl
    rw [e]; have := cntR_and_le (rect r) (rect I) (45 + 27 * j) 27; exact le_min this.1 this.2

theorem aE_le (e t : Nat) : aE e t ≤ 9 := cntR_le _ _ _
theorem bE_le (j t : Nat) : bE j t ≤ 27 := cntR_le _ _ _

-- ===== computing profiles =====
def pop9Tab : Nat := pk (fun x => cntR x 0 9) 4 512
def pop9 (x : Nat) : Nat := fld pop9Tab 4 x

theorem pop9_eq (x : Nat) (hx : x < 512) : pop9 x = cntR x 0 9 :=
  fld_pk _ 4 512 x (by norm_num) (fun i _ => lt_of_le_of_lt (cntR_le _ _ _) (by norm_num)) hx

theorem cntR_fld9 (r k : Nat) : cntR (fld r 9 k) 0 9 = cntR r (9 * k) 9 := by
  rw [fld_eq]
  rw [show cntR ((r >>> (9 * k)) % 2 ^ 9) 0 9 = cntR (r >>> (9 * k)) 0 9 from by
    apply cntR_congr; intro i _ hi; rw [Nat.testBit_mod_two_pow]; simp; omega]
  rw [cntR_shift, Nat.add_zero]

def profA (r : Nat) : Nat := pk (fun e => pop9 (fld r 9 e)) 8 5
def profB (r : Nat) : Nat :=
  pk (fun j => Nat.sub 27 (Nat.add (Nat.add (pop9 (fld r 9 (5 + 3 * j))) (pop9 (fld r 9 (6 + 3 * j)))) (pop9 (fld r 9 (7 + 3 * j))))) 8 5

theorem profA_eq (r : Nat) : profA r = pk (fun e => aE e r) 8 5 := by
  unfold profA; apply pk_congr; intro e _
  rw [pop9_eq _ (fld_lt _ _ _), cntR_fld9]; rfl

theorem profB_eq (r : Nat) : profB r = pk (fun j => bE j r) 8 5 := by
  unfold profB; apply pk_congr; intro j hj
  rw [pop9_eq _ (fld_lt _ _ _), pop9_eq _ (fld_lt _ _ _), pop9_eq _ (fld_lt _ _ _), cntR_fld9, cntR_fld9, cntR_fld9]
  have h3 : cntR r (9 * (5 + 3 * j)) 9 + cntR r (9 * (6 + 3 * j)) 9 + cntR r (9 * (7 + 3 * j)) 9 = cntR r (45 + 27 * j) 27 := by
    rw [show (27 : Nat) = 9 + 9 + 9 by rfl, cntR_add, cntR_add]
    rw [show 9 * (5 + 3 * j) = 45 + 27 * j by ring, show 9 * (6 + 3 * j) = 45 + 27 * j + 9 by ring,
      show 9 * (7 + 3 * j) = 45 + 27 * j + 9 + 9 by ring]
  have hc : bE j r + cntR r (45 + 27 * j) 27 = 27 := by
    unfold bE rect
    exact cntR_comp r MV _ 27 (fun i h1 h2 => by rw [testBit_MV]; simp; omega)
  show 27 - (cntR r (9 * (5 + 3 * j)) 9 + cntR r (9 * (6 + 3 * j)) 9 + cntR r (9 * (7 + 3 * j)) 9) = bE j r
  omega

theorem testBit_land' (x y i : Nat) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) := Nat.testBit_and x y i

-- ===== the scope guard =====
def G8m : Nat := 0x8080808080808080
def F7m : Nat := 0x7f7f7f7f7f7f7f7f
def N9m : Nat := 0x0909090909090909
def N27m : Nat := 0x1b1b1b1b1b1b1b1b

def thr (S ta n : Nat) : Nat := Nat.shiftRight (Nat.add (Nat.land (bsum S) (Nat.mul 255 (rep 64 n))) (Nat.mul (Nat.sub 256 ta) (rep 64 n))) 8

def guardMask (op : Bool) (ta tb n pa pb HA HB : Nat) : Nat :=
  Nat.land (Nat.land
    (thr (cond op (swarMin (Nat.mul G8m (rep 64 n)) (Nat.mul F7m (rep 64 n)) (Nat.mul N9m (rep 64 n)) (Nat.add (Nat.mul pa (rep 64 n)) HA))
      (swarMin (Nat.mul G8m (rep 64 n)) (Nat.mul F7m (rep 64 n)) (Nat.mul pa (rep 64 n)) HA)) ta n)
    (thr (cond op (swarMin (Nat.mul G8m (rep 64 n)) (Nat.mul F7m (rep 64 n)) (Nat.mul pb (rep 64 n)) HB)
      (swarMin (Nat.mul G8m (rep 64 n)) (Nat.mul F7m (rep 64 n)) (Nat.mul N27m (rep 64 n)) (Nat.add (Nat.mul pb (rep 64 n)) HB))) tb n))
    (rep 64 n)

def ext8 (a : Nat → Nat) (e : Nat) : Nat := if e < 5 then a e else 0

theorem pk5_8 (a : Nat → Nat) : pk a 8 5 = pk (ext8 a) 8 8 := by
  rw [pk_congr a (ext8 a) 8 5 (fun e he => by simp [ext8, he])]
  exact pk_pad _ _ _ _ (by norm_num) (fun j h1 _ => by simp [ext8]; omega)

theorem repl8 (a : Nat → Nat) (n : Nat) : Nat.mul (pk a 8 5) (rep 64 n) = pk (fun k => ext8 a (k % 8)) 8 (8 * n) := by
  show pk a 8 5 * rep 64 n = _
  rw [rep_eq 64 n (by norm_num), pk_const, pk5_8, show (64 : Nat) = 8 * 8 by rfl, pk_nest (fun _ e => ext8 a e) 8 8 n (by norm_num)]

theorem lanes8 (h : Nat → Nat → Nat) (n : Nat) :
    pk (fun l => pk (h l) 8 5) 64 n = pk (fun k => ext8 (h (k / 8)) (k % 8)) 8 (8 * n) := by
  rw [show (64 : Nat) = 8 * 8 by rfl]
  rw [pk_congr (fun l => pk (h l) 8 5) (fun l => pk (ext8 (h l)) 8 8) (8 * 8) n (fun l _ => pk5_8 _)]
  exact pk_nest (fun l e => ext8 (h l) e) 8 8 n (by norm_num)

theorem const8 (c : Nat) (hc : c < 256) (M : Nat) (hM : M = pk (fun _ => c) 8 8) (n : Nat) :
    Nat.mul M (rep 64 n) = pk (fun _ => c) 8 (8 * n) := by
  show M * rep 64 n = _
  rw [rep_eq 64 n (by norm_num), pk_const, hM, show (64 : Nat) = 8 * 8 by rfl, pk_nest (fun _ _ => c) 8 8 n (by norm_num)]

theorem thr_spec (c : Nat → Nat) (ta n l : Nat) (hc : ∀ k, c k ≤ 40) (hl : l < n) (hta : ta ≤ 256)
    (h : ta ≤ c (8 * l) + c (8 * l + 1) + c (8 * l + 2) + c (8 * l + 3) + c (8 * l + 4)) :
    (thr (pk c 8 (8 * n)) ta n).testBit (64 * l) = true := by
  unfold thr
  rw [bsum_pk c n hc, show Nat.mul (Nat.sub 256 ta) (rep 64 n) = (256 - ta) * rep 64 n from rfl,
    rep_eq 64 n (by norm_num), pk_const]
  show ((pk _ 64 n + pk _ 64 n) >>> 8).testBit (64 * l) = true
  rw [pk_add, Nat.testBit_shiftRight, show 8 + 64 * l = 64 * l + 8 by ring]
  have f : Fits (fun i => c (8 * i) + c (8 * i + 1) + c (8 * i + 2) + c (8 * i + 3) + c (8 * i + 4) + (256 - ta)) 64 n :=
    fun i _ => by
      have := hc (8 * i); have := hc (8 * i + 1); have := hc (8 * i + 2); have := hc (8 * i + 3); have := hc (8 * i + 4)
      show c (8 * i) + c (8 * i + 1) + c (8 * i + 2) + c (8 * i + 3) + c (8 * i + 4) + (256 - ta) < 2 ^ 64; omega
  rw [testBit_pk _ 64 n f l 8 (by norm_num)]
  simp only [hl, decide_true, Bool.true_and]
  have := hc (8 * l); have := hc (8 * l + 1); have := hc (8 * l + 2); have := hc (8 * l + 3); have := hc (8 * l + 4)
  exact testBit8 _ (by omega) (by omega)

theorem G8m_eq : G8m = pk (fun _ => 128) 8 8 := by decide
theorem F7m_eq : F7m = pk (fun _ => 127) 8 8 := by decide
theorem N9m_eq : N9m = pk (fun _ => 9) 8 8 := by decide
theorem N27m_eq : N27m = pk (fun _ => 27) 8 8 := by decide

theorem guard_spec (op : Bool) (ta tb n : Nat) (a b : Nat → Nat) (hA hB : Nat → Nat → Nat)
    (ha : ∀ e, a e ≤ 9) (hb : ∀ j, b j ≤ 27) (hha : ∀ l e, hA l e ≤ 9) (hhb : ∀ l j, hB l j ≤ 27)
    (hta : ta ≤ 256) (htb : tb ≤ 256) (l : Nat) (hl : l < n)
    (hSA : ta ≤ combA op (a 0) (hA l 0) + combA op (a 1) (hA l 1) + combA op (a 2) (hA l 2) + combA op (a 3) (hA l 3) +
      combA op (a 4) (hA l 4))
    (hSB : tb ≤ combB op (b 0) (hB l 0) + combB op (b 1) (hB l 1) + combB op (b 2) (hB l 2) + combB op (b 3) (hB l 3) +
      combB op (b 4) (hB l 4)) :
    (guardMask op ta tb n (pk a 8 5) (pk b 8 5) (pk (fun l => pk (hA l) 8 5) 64 n) (pk (fun l => pk (hB l) 8 5) 64 n)).testBit (64 * l) = true := by
  have eG := const8 128 (by norm_num) G8m G8m_eq n
  have eF := const8 127 (by norm_num) F7m F7m_eq n
  have e9 := const8 9 (by norm_num) N9m N9m_eq n
  have e27 := const8 27 (by norm_num) N27m N27m_eq n

  have xa : ∀ k, ext8 a (k % 8) ≤ 9 := fun k => by unfold ext8; split <;> [exact ha _; omega]
  have xb : ∀ k, ext8 b (k % 8) ≤ 27 := fun k => by unfold ext8; split <;> [exact hb _; omega]
  have xha : ∀ k, ext8 (hA (k / 8)) (k % 8) ≤ 9 := fun k => by unfold ext8; split <;> [exact hha _ _; omega]
  have xhb : ∀ k, ext8 (hB (k / 8)) (k % 8) ≤ 27 := fun k => by unfold ext8; split <;> [exact hhb _ _; omega]
  have lane : ∀ (u v : Nat → Nat) (t : Nat), t < 5 → u ((8 * l + t) % 8) = u t ∧ (8 * l + t) / 8 = l := fun u v t ht =>
    ⟨by rw [show (8 * l + t) % 8 = t by omega], by omega⟩
  have k5 : ∀ t, t < 5 → (8 * l + t) % 8 = t ∧ (8 * l + t) / 8 = l := fun t ht => ⟨by omega, by omega⟩
  unfold guardMask
  rw [repl8 a n, repl8 b n, lanes8 hA n, lanes8 hB n, eG, eF]
  rw [testBit_land', testBit_land']
  have hR : (rep 64 n).testBit (64 * l) = true := by
    rw [rep_eq 64 n (by norm_num), show 64 * l = 64 * l + 0 by rfl, testBit_pk _ 64 n (fun _ _ => by norm_num) l 0 (by norm_num)]
    simp [hl]
  rw [hR, Bool.and_true]
  cases op
  · -- AND: min on A, capped sum on B
    have sA := swarMin_pk (fun k => ext8 a (k % 8)) (fun k => ext8 (hA (k / 8)) (k % 8)) (8 * n)
      (fun k _ => by have := xa k; omega) (fun k _ => by have := xha k; omega)
    rw [show Nat.add (pk (fun k => ext8 b (k % 8)) 8 (8 * n)) (pk (fun k => ext8 (hB (k / 8)) (k % 8)) 8 (8 * n)) =
      pk (fun k => ext8 b (k % 8) + ext8 (hB (k / 8)) (k % 8)) 8 (8 * n) from pk_add _ _ _ _]
    have sB := swarMin_pk (fun _ => 27) (fun k => ext8 b (k % 8) + ext8 (hB (k / 8)) (k % 8)) (8 * n)
      (fun _ _ => by norm_num) (fun k _ => by have := xb k; have := xhb k; omega)
    simp only [cond_false]
    rw [sA, e27, sB, Bool.and_eq_true]
    constructor
    · apply thr_spec _ ta n l (fun k => le_trans (min_le_left _ _) (by have := xa k; omega)) hl hta
      simp only [(k5 0 (by norm_num)).1, (k5 0 (by norm_num)).2, (k5 1 (by norm_num)).1, (k5 1 (by norm_num)).2,
        (k5 2 (by norm_num)).1, (k5 2 (by norm_num)).2, (k5 3 (by norm_num)).1, (k5 3 (by norm_num)).2,
        (k5 4 (by norm_num)).1, (k5 4 (by norm_num)).2, Nat.add_zero, ext8]
      simpa [combA, show 8 * l % 8 = 0 by omega, show 8 * l / 8 = l by omega] using hSA
    · apply thr_spec _ tb n l (fun k => le_trans (min_le_left _ _) (by norm_num)) hl htb
      simp only [(k5 0 (by norm_num)).1, (k5 0 (by norm_num)).2, (k5 1 (by norm_num)).1, (k5 1 (by norm_num)).2,
        (k5 2 (by norm_num)).1, (k5 2 (by norm_num)).2, (k5 3 (by norm_num)).1, (k5 3 (by norm_num)).2,
        (k5 4 (by norm_num)).1, (k5 4 (by norm_num)).2, Nat.add_zero, ext8]
      simpa [combB, show 8 * l % 8 = 0 by omega, show 8 * l / 8 = l by omega] using hSB
  · -- OR: capped sum on A, min on B
    rw [show Nat.add (pk (fun k => ext8 a (k % 8)) 8 (8 * n)) (pk (fun k => ext8 (hA (k / 8)) (k % 8)) 8 (8 * n)) =
      pk (fun k => ext8 a (k % 8) + ext8 (hA (k / 8)) (k % 8)) 8 (8 * n) from pk_add _ _ _ _]
    have sA := swarMin_pk (fun _ => 9) (fun k => ext8 a (k % 8) + ext8 (hA (k / 8)) (k % 8)) (8 * n)
      (fun _ _ => by norm_num) (fun k _ => by have := xa k; have := xha k; omega)
    have sB := swarMin_pk (fun k => ext8 b (k % 8)) (fun k => ext8 (hB (k / 8)) (k % 8)) (8 * n)
      (fun k _ => by have := xb k; omega) (fun k _ => by have := xhb k; omega)
    simp only [cond_true]
    rw [e9, sA, sB, Bool.and_eq_true]
    constructor
    · apply thr_spec _ ta n l (fun k => le_trans (min_le_left _ _) (by norm_num)) hl hta
      simp only [(k5 0 (by norm_num)).1, (k5 0 (by norm_num)).2, (k5 1 (by norm_num)).1, (k5 1 (by norm_num)).2,
        (k5 2 (by norm_num)).1, (k5 2 (by norm_num)).2, (k5 3 (by norm_num)).1, (k5 3 (by norm_num)).2,
        (k5 4 (by norm_num)).1, (k5 4 (by norm_num)).2, Nat.add_zero, ext8]
      simpa [combA, show 8 * l % 8 = 0 by omega, show 8 * l / 8 = l by omega] using hSA
    · apply thr_spec _ tb n l (fun k => le_trans (min_le_left _ _) (by have := xb k; omega)) hl htb
      simp only [(k5 0 (by norm_num)).1, (k5 0 (by norm_num)).2, (k5 1 (by norm_num)).1, (k5 1 (by norm_num)).2,
        (k5 2 (by norm_num)).1, (k5 2 (by norm_num)).2, (k5 3 (by norm_num)).1, (k5 3 (by norm_num)).2,
        (k5 4 (by norm_num)).1, (k5 4 (by norm_num)).2, Nat.add_zero, ext8]
      simpa [combB, show 8 * l % 8 = 0 by omega, show 8 * l / 8 = l by omega] using hSB

-- ===== generators permute blocks =====
def blkA (k e : Nat) : Nat := gP k (9 * e) / 9
def blkB (k j : Nat) : Nat := (gP k (45 + 27 * j) - 45) / 27

def blkCheck : Bool :=
  allBelow 19 (fun k =>
    allBelow 5 (fun e => Nat.blt (blkA k e) 5 && (Nat.ble k 3 || Nat.beq (blkA k e) e) &&
      allBelow 9 (fun i => Nat.beq (gP k (9 * e + i) / 9) (blkA k e) && Nat.blt (gP k (9 * e + i)) 45 &&
        Nat.beq (idxW (invG k) (9 * blkA k e + i) / 9) e && Nat.blt (idxW (invG k) (9 * blkA k e + i)) 45)) &&
    allBelow 5 (fun j => Nat.blt (blkB k j) 5 && (Nat.ble k 3 || Nat.beq (blkB k j) j) &&
      allBelow 27 (fun i => Nat.ble 45 (gP k (45 + 27 * j + i)) && Nat.blt (gP k (45 + 27 * j + i)) 180 &&
        Nat.beq ((gP k (45 + 27 * j + i) - 45) / 27) (blkB k j) &&
        Nat.ble 45 (idxW (invG k) (45 + 27 * blkB k j + i)) && Nat.blt (idxW (invG k) (45 + 27 * blkB k j + i)) 180 &&
        Nat.beq ((idxW (invG k) (45 + 27 * blkB k j + i) - 45) / 27) j)))

set_option maxRecDepth 100000 in
theorem blkCheck_ok : blkCheck = true := by decide +kernel

theorem idx_one (k p : Nat) (hk : k < 19) : idxW [k] p = gP k p := by
  show genP k p = gP k p; simp [genP, hk]

theorem idx_inv1 (k p : Nat) (hp : p < 180) : idxW (invG k) (idxW [k] p) = p := by
  have := idxW_invG' k p hp; rw [idxW_append] at this; exact this

theorem idx_inv2 (k p : Nat) (hp : p < 180) : idxW [k] (idxW (invG k) p) = p := by
  have := idxW_invG k p hp; rw [idxW_append] at this; exact this

theorem aE_gen (k e t : Nat) (hk : k < 19) (he : e < 5) : aE e (permW [k] t) = aE (blkA k e) t := by
  have h := allBelow_spec _ _ blkCheck_ok k hk
  simp only [Bool.and_eq_true] at h
  have hA := allBelow_spec _ _ h.1 e he
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.or_eq_true, Nat.ble_eq] at hA
  have hi := fun i (hi : i < 9) => allBelow_spec _ _ hA.2 i hi
  simp only [Bool.and_eq_true, Nat.blt_eq] at hi
  unfold aE
  apply cntR_bij _ _ (9 * e) (9 * blkA k e) 9 (idxW [k]) (idxW (invG k))
  · intro i hi'
    have := hi i hi'; rw [idx_one k _ hk]
    have e1 := Nat.eq_of_beq_eq_true this.1.1.1; constructor <;> omega
  · intro i hi'
    have := hi i hi'
    have e1 := Nat.eq_of_beq_eq_true this.1.2; constructor <;> omega
  · intro i hi'; exact idx_inv1 k _ (by omega)
  · intro i hi'
    have := hi i hi'
    exact idx_inv2 k _ (by have := hA.1.1; omega)
  · intro i hi'; exact testBit_permW [k] t _ (by omega)

theorem bE_gen (k j t : Nat) (hk : k < 19) (hj : j < 5) : bE j (permW [k] t) = bE (blkB k j) t := by
  have h := allBelow_spec _ _ blkCheck_ok k hk
  simp only [Bool.and_eq_true] at h
  have hB := allBelow_spec _ _ h.2 j hj
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.or_eq_true, Nat.ble_eq] at hB
  have hi := fun i (hi : i < 27) => allBelow_spec _ _ hB.2 i hi
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hi
  unfold bE
  apply cntR_bij _ _ (45 + 27 * j) (45 + 27 * blkB k j) 27 (idxW [k]) (idxW (invG k))
  · intro i hi'
    have := hi i hi'; rw [idx_one k _ hk]
    have e1 := Nat.eq_of_beq_eq_true this.1.1.1.2
    have := this.1.1.1.1; constructor <;> omega
  · intro i hi'
    have := hi i hi'
    have e1 := Nat.eq_of_beq_eq_true this.2
    have := this.1; constructor <;> omega
  · intro i hi'; exact idx_inv1 k _ (by omega)
  · intro i hi'; exact idx_inv2 k _ (by have := hB.1.1; omega)
  · intro i hi'
    have hq := hi i hi'
    rw [rect_bit _ _ (by omega) (by omega), testBit_permW [k] t _ (by omega), idx_one k _ hk,
      rect_bit _ _ (by have := hq.1.1.1.1.1; omega) (by have := hq.1.1.1.1.2; omega)]

def SameProf (t1 t2 : Nat) : Prop := ∀ e, e < 5 → aE e t1 = aE e t2 ∧ bE e t1 = bE e t2

theorem blk_lt (k e : Nat) (hk : k < 19) (he : e < 5) : blkA k e < 5 ∧ blkB k e < 5 := by
  have h := allBelow_spec _ _ blkCheck_ok k hk
  simp only [Bool.and_eq_true] at h
  have hA := allBelow_spec _ _ h.1 e he
  have hB := allBelow_spec _ _ h.2 e he
  simp only [Bool.and_eq_true, Nat.blt_eq] at hA hB
  exact ⟨hA.1.1, hB.1.1⟩

theorem sameProf_of_bits (x y : Nat) (h : ∀ p, p < 180 → x.testBit p = y.testBit p) : SameProf x y := by
  intro e he
  constructor
  · unfold aE; apply cntR_congr; intro i h1 h2; exact h i (by omega)
  · unfold bE; apply cntR_congr; intro i h1 h2
    rw [rect_bit _ _ (by omega) (by omega), rect_bit _ _ (by omega) (by omega), h i (by omega)]

theorem sameProf_permW (w : List Nat) (t1 t2 : Nat) (h : SameProf t1 t2) : SameProf (permW w t1) (permW w t2) := by
  induction w generalizing t1 t2 with
  | nil => exact h
  | cons k w ih =>
    apply ih
    by_cases hk : k < 19
    · intro e he
      have e1 := aE_gen k e t1 hk he; have e2 := aE_gen k e t2 hk he
      have e3 := bE_gen k e t1 hk he; have e4 := bE_gen k e t2 hk he
      have hb := blk_lt k e hk he
      change aE e (permW [k] t1) = aE e (permW [k] t2) ∧ bE e (permW [k] t1) = bE e (permW [k] t2)
      rw [e1, e2, e3, e4]; exact ⟨(h _ hb.1).1, (h _ hb.2).2⟩
    · have hg : ∀ t p, p < 180 → (permP (genP k) t).testBit p = t.testBit p := fun t p hp => by
        rw [testBit_permP]; simp [genP, hk, hp]
      intro e he
      have s1 := sameProf_of_bits _ _ (hg t1) e he
      have s2 := sameProf_of_bits _ _ (hg t2) e he
      have := h e he
      show aE e (permP (genP k) t1) = aE e (permP (genP k) t2) ∧ bE e (permP (genP k) t1) = bE e (permP (genP k) t2)
      exact ⟨by rw [s1.1, s2.1, this.1], by rw [s1.2, s2.2, this.2]⟩

theorem sameProf_trans {x y z : Nat} (h1 : SameProf x y) (h2 : SameProf y z) : SameProf x z :=
  fun e he => ⟨(h1 e he).1.trans (h2 e he).1, (h1 e he).2.trans (h2 e he).2⟩

theorem sameProf_symm {x y : Nat} (h : SameProf x y) : SameProf y x :=
  fun e he => ⟨(h e he).1.symm, (h e he).2.symm⟩

theorem sameProf_local (w : List Nat) (hw : ∀ k ∈ w, 4 ≤ k) (X : Nat) : SameProf (permW w X) X := by
  induction w generalizing X with
  | nil => exact fun e he => ⟨rfl, rfl⟩
  | cons k w ih =>
    have h1 : SameProf (permW [k] X) X := by
      intro e he
      by_cases hk : k < 19
      · have h := allBelow_spec _ _ blkCheck_ok k hk
        simp only [Bool.and_eq_true] at h
        have hA := allBelow_spec _ _ h.1 e he
        have hB := allBelow_spec _ _ h.2 e he
        simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at hA hB
        have k4 := hw k (by simp)
        have ea : blkA k e = e := by
          rcases hA.1.2 with h' | h'
          · omega
          · exact Nat.eq_of_beq_eq_true h'
        have eb : blkB k e = e := by
          rcases hB.1.2 with h' | h'
          · omega
          · exact Nat.eq_of_beq_eq_true h'
        rw [aE_gen k e X hk he, bE_gen k e X hk he, ea, eb]; exact ⟨rfl, rfl⟩
      · have : ∀ p, p < 180 → (permW [k] X).testBit p = X.testBit p := fun p hp => by
          show (permP (genP k) X).testBit p = _
          rw [testBit_permP]; simp [genP, hk, hp]
        exact sameProf_of_bits _ _ this e he
    have h2 := ih (fun k' hk' => hw k' (by simp [hk'])) (permW [k] X)
    show SameProf (permW w (permP (genP k) X)) X
    exact sameProf_trans h2 h1

theorem wLoc_ge4 (p : Nat → Nat) (hp : ∀ v, v < 5 → p v < 6) : ∀ k ∈ wLoc p, 4 ≤ k := by
  have h : ∀ v c, c < 6 → ∀ k ∈ wLv v c, 4 ≤ k := by
    intro v c hc k hk
    interval_cases c <;> simp [wLv] at hk <;> omega
  intro k hk
  simp only [wLoc, List.mem_append] at hk
  rcases hk with hk | hk | hk | hk | hk
  · exact h 0 _ (hp 0 (by norm_num)) k hk
  · exact h 1 _ (hp 1 (by norm_num)) k hk
  · exact h 2 _ (hp 2 (by norm_num)) k hk
  · exact h 3 _ (hp 3 (by norm_num)) k hk
  · exact h 4 _ (hp 4 (by norm_num)) k hk

theorem cvec_lt (s i v : Nat) (hs : s < 41) (hv : v < 5) : cvec s i v < 6 := by
  have hr := rankOf_lt s v hs hv
  apply locOpt_lt _ _ hr
  unfold digit
  exact lt_of_lt_of_le (Nat.mod_lt _ (by unfold locLen; cases Nat.beq (rankOf s v) 0 <;> cases Nat.beq (rankOf s v) 1 <;> simp))
    (locLen_le _)

theorem tv_imgF_words (s d i : Nat) (hs : s < 41) (hd : d < 10) :
    tv (imgF s d i) = permW (wLoc (cvec s i) ++ wDih d) (tv (HF s)) := by
  have hc : ∀ v, v < 5 → cvec s i v < 6 := fun v hv => cvec_lt s i v hs hv
  have hsig : ∀ x, x < 15 → sig (wLoc (cvec s i) ++ wDih d) x = lam d (cvec s i) x := by
    intro x hx
    have hv : x % 5 < 5 := Nat.mod_lt _ (by norm_num)
    rw [sig_append, sig_wLoc _ hc x hx, sig_wDih d _ hd (lam_lt 5 _ x hx (hc _ hv)), lam_split d _ x hx (hc _ hv)]
  have hl := fun j (hj : j < 8) => hLeaf_lt s j hs hj
  rw [← tv_actW, actW_sig, HF, act_FH _ _ _ hl, imgF]
  congr 1
  apply FH_congr; intro j hj
  rw [hsig _ (hl j hj)]; rfl

theorem lane_sameProf (s d i : Nat) (hs : s < 41) (hd : d < 10) :
    SameProf (tv (imgF s d i)) (tv (imgF s d 0)) := by
  rw [tv_imgF_words s d i hs hd, tv_imgF_words s d 0 hs hd, permW_append, permW_append]
  apply sameProf_permW
  exact sameProf_trans (sameProf_local _ (wLoc_ge4 _ (fun v hv => cvec_lt s i v hs hv)) _)
    (sameProf_symm (sameProf_local _ (wLoc_ge4 _ (fun v hv => cvec_lt s 0 v hs hv)) _))

-- the first image of a lane, computed directly
def imgVec0 (s d : Nat) : Nat := evalHv (hCode s) (fun j => varAt (hImg s d (hLeaf (hCode s) j) 0))

theorem imgVec0_eq (s d : Nat) : imgVec0 s d = tv (imgF s d 0) := by
  have z : ∀ a b : Nat, Nat.mod (Nat.div 0 a) b = 0 := fun a b => by show 0 / a % b = 0; simp
  rw [imgF, tv_FH]; unfold imgVec0 imgLf digit
  simp only [z]

-- guard soundness for a group of lanes
theorem guard_sound (op : Bool) (ta tb nL : Nat) (Ls Ld : Nat → Nat) (hs : ∀ l, l < nL → Ls l < 41)
    (hd : ∀ l, l < nL → Ld l < 10) (hta : ta ≤ 256) (htb : tb ≤ 256) (r l i : Nat) (hl : l < nL)
    (hA : ta ≤ cA (gate op r (tv (imgF (Ls l) (Ld l) i)))) (hB : tb ≤ cB (gate op r (tv (imgF (Ls l) (Ld l) i)))) :
    (guardMask op ta tb nL (profA r) (profB r) (pk (fun l => profA (imgVec0 (Ls l) (Ld l))) 64 nL)
      (pk (fun l => profB (imgVec0 (Ls l) (Ld l))) 64 nL)).testBit (64 * l) = true := by
  rw [profA_eq, profB_eq]
  rw [pk_congr (fun l => profA (imgVec0 (Ls l) (Ld l))) (fun l => pk (fun e => aE e (tv (imgF (Ls l) (Ld l) 0))) 8 5) 64 nL
    (fun l _ => by rw [profA_eq, imgVec0_eq])]
  rw [pk_congr (fun l => profB (imgVec0 (Ls l) (Ld l))) (fun l => pk (fun e => bE e (tv (imgF (Ls l) (Ld l) 0))) 8 5) 64 nL
    (fun l _ => by rw [profB_eq, imgVec0_eq])]
  have sp := lane_sameProf (Ls l) (Ld l) i (hs l hl) (hd l hl)
  apply guard_spec op ta tb nL (fun e => aE e r) (fun j => bE j r) (fun l e => aE e (tv (imgF (Ls l) (Ld l) 0)))
    (fun l j => bE j (tv (imgF (Ls l) (Ld l) 0))) (fun e => aE_le _ _) (fun j => bE_le _ _) (fun _ _ => aE_le _ _)
    (fun _ _ => bE_le _ _) hta htb l hl
  · rw [cA_split] at hA
    have g := fun e => aE_gate op r (tv (imgF (Ls l) (Ld l) i)) e
    rw [← (sp 0 (by norm_num)).1, ← (sp 1 (by norm_num)).1, ← (sp 2 (by norm_num)).1, ← (sp 3 (by norm_num)).1,
      ← (sp 4 (by norm_num)).1]
    have := g 0; have := g 1; have := g 2; have := g 3; have := g 4
    omega
  · rw [cB_split] at hB
    have g := fun j (hj : j < 5) => bE_gate op r (tv (imgF (Ls l) (Ld l) i)) j hj
    rw [← (sp 0 (by norm_num)).2, ← (sp 1 (by norm_num)).2, ← (sp 2 (by norm_num)).2, ← (sp 3 (by norm_num)).2,
      ← (sp 4 (by norm_num)).2]
    have := g 0 (by norm_num); have := g 1 (by norm_num); have := g 2 (by norm_num); have := g 3 (by norm_num)
    have := g 4 (by norm_num)
    omega

-- ===== renaming by tree labels =====
def dvPack : Nat := 0x7014446938088d129c11a2014e344480a6888dc05111a4e022344a704688
def lpPack : Nat := 0x189921498864
def dvAt (h v : Nat) : Nat := Nat.land (Nat.shiftRight dvPack (Nat.mul 3 (Nat.add (Nat.mul 5 h) v))) 7
def lpAt (cl l : Nat) : Nat := Nat.land (Nat.shiftRight lpPack (Nat.mul 2 (Nat.add (Nat.mul 3 cl) l))) 3
def rlab (lab x : Nat) : Nat :=
  Nat.add (dvAt (Nat.land lab 15) (Nat.mod x 5))
    (Nat.mul 5 (lpAt (Nat.land (Nat.shiftRight lab (Nat.add 4 (Nat.mul 3 (dvAt (Nat.land lab 15) (Nat.mod x 5))))) 7) (Nat.div x 5)))

def dOfH (h : Nat) : Nat := srch (fun D => allBelow 5 (fun v => Nat.beq (dvAt h v) (dmapC D v))) 10
def pOfC (cl : Nat) : Nat := srch (fun c => allBelow 3 (fun l => Nat.beq (lpAt cl l) (permAt c l))) 6

def rlabCheck : Bool :=
  allBelow 16 (fun h => Nat.blt (dOfH h) 10 && allBelow 5 (fun v => Nat.beq (dvAt h v) (dmapC (dOfH h) v))) &&
  allBelow 8 (fun cl => Nat.blt (pOfC cl) 6 && allBelow 3 (fun l => Nat.beq (lpAt cl l) (permAt (pOfC cl) l)))

set_option maxRecDepth 10000 in
theorem rlabCheck_ok : rlabCheck = true := by decide +kernel

theorem rlab_real (lab : Nat) : ∃ w : List Nat, ∀ x, x < 15 → sig w x = rlab lab x := by
  have h := rlabCheck_ok
  simp only [rlabCheck, Bool.and_eq_true] at h
  let hh := Nat.land lab 15
  have hh16 : hh < 16 := Nat.and_lt_two_pow lab (by norm_num : (15 : Nat) < 2 ^ 4)
  have h1 := allBelow_spec _ _ h.1 hh hh16
  simp only [Bool.and_eq_true, Nat.blt_eq] at h1
  let P := fun v => pOfC (Nat.land (Nat.shiftRight lab (Nat.add 4 (Nat.mul 3 (dvAt hh v)))) 7)
  have hP : ∀ v, v < 5 → P v < 6 := fun v _ => by
    have h8 : Nat.land (Nat.shiftRight lab (Nat.add 4 (Nat.mul 3 (dvAt hh v)))) 7 < 8 :=
      Nat.and_lt_two_pow _ (by norm_num : (7 : Nat) < 2 ^ 3)
    have := allBelow_spec _ _ h.2 _ h8
    simp only [Bool.and_eq_true, Nat.blt_eq] at this
    exact this.1
  obtain ⟨w, hw⟩ := lam_real (dOfH hh) P h1.1 hP
  refine ⟨w, fun x hx => ?_⟩
  rw [hw x hx]
  have hv : x % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have e1 := Nat.eq_of_beq_eq_true (allBelow_spec _ _ h1.2 (x % 5) hv)
  have h8 : Nat.land (Nat.shiftRight lab (Nat.add 4 (Nat.mul 3 (dvAt hh (x % 5))))) 7 < 8 :=
    Nat.and_lt_two_pow _ (by norm_num : (7 : Nat) < 2 ^ 3)
  have h2 := allBelow_spec _ _ h.2 _ h8
  simp only [Bool.and_eq_true, Nat.blt_eq] at h2
  have e2 := Nat.eq_of_beq_eq_true (allBelow_spec _ _ h2.2 (x / 5) (by omega))
  show dmapC (dOfH hh) (x % 5) + 5 * permAt (P (x % 5)) (x / 5) =
    dvAt hh (x % 5) + 5 * lpAt (Nat.land (Nat.shiftRight lab (Nat.add 4 (Nat.mul 3 (dvAt hh (x % 5))))) 7) (x / 5)
  rw [← e1, e2]

-- ===== the decision tree =====
def nd (j : Nat) (a b : Nat → Nat) (o : Nat) : Nat := cond (tb o j) (b o) (a o)
def lf (x : Nat) (_ : Nat) : Nat := x

set_option maxRecDepth 20000 in
def treeE : Nat → Nat :=
  nd 17 (nd 40 (nd 9 (nd 6 (nd 129 (nd 165 (nd 75 (nd 97 (nd 123 (lf 16731030) (nd 116 (lf 16259558) (lf 16256486))) (nd 82 (nd 113 (lf 16467862) (nd 12 (lf 16253366) (lf 14680064))) (nd 110 (lf 16259558) (lf 16253414)))) (nd 122 (nd 124 (lf 16259462) (nd 65 (lf 16259510) (lf 14680169))) (nd 89 (nd 5 (lf 10485865) (nd 141 (lf 16467862) (lf 14680121))) (lf 16256438)))) (nd 2 (nd 128 (nd 42 (nd 44 (nd 41 (nd 38 (nd 8 (nd 16 (nd 14 (nd 37 (nd 12 (nd 13 (nd 43 (nd 10 (nd 7 (nd 11 (nd 15 (nd 97 (nd 132 (lf 17825926) (lf 13303814)) (nd 96 (lf 17915897) (lf 10489225))) (lf 18350473)) (lf 10489225)) (lf 19070985)) (lf 10492297)) (lf 17845638)) (lf 10492297)) (lf 10485769)) (lf 17842566)) (nd 153 (lf 10489225) (nd 50 (lf 10489225) (nd 4 (lf 10489225) (nd 147 (lf 12632073) (lf 10489225)))))) (lf 18350473)) (lf 13303814)) (lf 16777606)) (lf 16783366)) (lf 16780294)) (nd 160 (lf 27812616) (lf 17829254))) (nd 46 (nd 16 (nd 13 (nd 43 (nd 41 (nd 8 (nd 37 (nd 11 (nd 15 (nd 7 (nd 10 (nd 12 (nd 14 (nd 42 (nd 38 (nd 44 (lf 17825926) (lf 16780294)) (lf 18350854)) (lf 10489606)) (lf 17846025)) (lf 17842953)) (lf 17826569)) (lf 17826569)) (lf 16777993)) (lf 17829641)) (lf 10486534)) (lf 13303814)) (lf 16783366)) (lf 10489606)) (lf 17842953)) (lf 16784137)) (nd 0 (lf 2624905) (lf 17825926)))) (nd 157 (nd 95 (nd 81 (nd 93 (lf 19009334) (nd 88 (lf 14680169) (lf 16259894))) (nd 92 (nd 121 (lf 16259942) (lf 16259846)) (lf 16256870))) (nd 94 (nd 110 (nd 15 (lf 16256822) (lf 14680121)) (lf 16256774)) (nd 91 (nd 68 (lf 16253750) (lf 14680064)) (lf 16253702)))) (nd 143 (nd 88 (nd 80 (nd 85 (lf 16256006) (nd 122 (lf 16259078) (lf 16252934))) (nd 108 (lf 16256054) (lf 16256102))) (nd 82 (nd 95 (lf 16259126) (lf 16252982)) (nd 108 (lf 16253030) (lf 16259174)))) (nd 54 (nd 44 (nd 7 (nd 43 (nd 37 (nd 42 (nd 16 (nd 8 (nd 38 (nd 11 (nd 41 (nd 14 (nd 15 (nd 10 (nd 12 (nd 13 (lf 17825926) (lf 18359049)) (lf 18359049)) (lf 10496393)) (lf 10493961)) (lf 18378505)) (lf 16849670)) (lf 10497801)) (lf 16843526)) (lf 17834761)) (lf 10496393)) (lf 17829254)) (lf 17842566)) (lf 17845638)) (lf 13312009)) (lf 16846598)) (nd 15 (nd 7 (nd 8 (nd 12 (lf 17825926) (lf 10534921)) (lf 3694601)) (lf 19120137)) (lf 10493961))))))) (nd 52 (nd 61 (nd 134 (nd 72 (nd 85 (nd 87 (lf 16468134) (lf 16256054)) (lf 16730278)) (nd 91 (nd 85 (nd 96 (lf 16729238) (lf 16256102)) (lf 16259078)) (lf 16473238))) (nd 37 (nd 111 (nd 42 (lf 13303814) (lf 2125190)) (nd 38 (nd 78 (lf 12591110) (lf 5767174)) (nd 162 (lf 28009224) (lf 22747241)))) (nd 42 (nd 91 (lf 2624902) (lf 28205832)) (lf 2100614)))) (nd 13 (nd 43 (nd 16 (nd 8 (nd 11 (nd 15 (nd 41 (nd 39 (nd 14 (nd 12 (nd 36 (nd 5 (nd 2 (nd 37 (nd 42 (nd 38 (nd 44 (lf 18219401) (lf 18353926)) (lf 18350854)) (lf 10489606)) (lf 10486534)) (lf 19071750)) (lf 19071750)) (lf 10486534)) (lf 17842953)) (lf 17846025)) (lf 10492678)) (nd 1 (nd 65 (lf 2128262) (lf 2122118)) (lf 18350854))) (lf 16777993)) (lf 17829641)) (lf 13303814)) (lf 16784137)) (lf 10489606)) (nd 0 (nd 120 (lf 2146313) (lf 29934337)) (lf 17842953)))) (nd 2 (nd 8 (nd 39 (nd 143 (nd 0 (nd 152 (lf 13631589) (lf 3686409)) (nd 140 (lf 13238281) (lf 2103689))) (nd 145 (nd 15 (nd 13 (nd 0 (lf 13156358) (lf 18875401)) (lf 2097161)) (nd 0 (nd 84 (lf 2146313) (lf 28197633)) (lf 2621833))) (nd 54 (lf 19011974) (nd 67 (nd 149 (lf 13156358) (lf 18874374)) (lf 13303814))))) (nd 56 (nd 82 (nd 57 (lf 2097158) (lf 2128262)) (lf 30130952)) (nd 85 (nd 46 (lf 12583942) (lf 2122118)) (lf 28001032)))) (nd 4 (nd 179 (lf 13156358) (nd 63 (lf 10887174) (lf 10904329))) (lf 13156358))) (nd 142 (nd 172 (nd 117 (nd 86 (nd 87 (lf 16468262) (lf 16259894)) (lf 16730406)) (nd 91 (nd 96 (nd 85 (lf 16729366) (lf 16259846)) (lf 16256870)) (lf 16473366))) (nd 5 (lf 17833990) (nd 135 (lf 19054601) (lf 13312009)))) (nd 54 (nd 8 (nd 36 (lf 19011974) (lf 10559494)) (lf 13246473)) (nd 7 (nd 63 (lf 18874758) (nd 146 (lf 2146313) (nd 0 (lf 13107206) (nd 1 (lf 13312009) (lf 3670022))))) (nd 71 (lf 18882566) (lf 13131782)))))))) (nd 5 (nd 53 (nd 167 (nd 102 (nd 91 (nd 105 (lf 16252985) (lf 16254057)) (nd 78 (nd 86 (lf 16401657) (lf 16407801)) (lf 16253961))) (nd 86 (nd 144 (nd 88 (lf 16407705) (nd 148 (lf 16252937) (lf 9964596))) (nd 42 (lf 16467193) (nd 146 (lf 9964548) (lf 9964644)))) (nd 105 (lf 16407721) (lf 16253033)))) (nd 97 (lf 18219401) (nd 87 (lf 17915897) (lf 17829641)))) (nd 169 (nd 117 (nd 150 (nd 94 (lf 16729369) (nd 95 (lf 16729465) (nd 110 (nd 170 (lf 9964980) (lf 16253753)) (lf 16407929)))) (nd 107 (nd 100 (lf 16253705) (lf 16407929)) (nd 79 (lf 16253801) (nd 39 (lf 16467241) (nd 157 (lf 9965028) (lf 9964932)))))) (nd 123 (nd 122 (lf 16407833) (lf 16407849)) (nd 165 (nd 172 (lf 9965412) (nd 173 (lf 9965316) (lf 9965364))) (nd 109 (lf 16467241) (lf 16253801))))) (nd 177 (nd 81 (nd 107 (nd 101 (lf 16253321) (lf 16408569)) (nd 152 (lf 16731049) (lf 16468905))) (nd 96 (nd 82 (lf 16408489) (lf 16408473)) (nd 115 (lf 16467881) (lf 16254345)))) (nd 143 (nd 3 (lf 18243974) (lf 19005449)) (nd 60 (nd 7 (lf 18243977) (lf 19060742)) (nd 128 (lf 19077129) (nd 148 (lf 18874377) (nd 3 (nd 66 (lf 18882566) (nd 2 (lf 13238281) (lf 13246473))) (lf 13107209))))))))) (nd 2 (nd 144 (nd 174 (nd 75 (nd 70 (lf 16771990) (nd 64 (lf 16509846) (lf 10904329))) (nd 113 (nd 96 (lf 16777110) (lf 16508838)) (nd 72 (lf 16508918) (lf 16508822)))) (lf 18899337)) (nd 49 (nd 103 (nd 71 (lf 16770326) (nd 122 (nd 163 (lf 16508182) (lf 19120134)) (lf 16508182))) (nd 75 (nd 88 (lf 16509206) (lf 16509302)) (nd 81 (lf 16514422) (lf 16514326)))) (nd 7 (nd 61 (lf 18243977) (lf 13115401)) (nd 103 (nd 64 (nd 62 (lf 16770198) (lf 18923526)) (nd 102 (nd 51 (lf 16508054) (lf 19054598)) (lf 16508054))) (nd 122 (nd 114 (lf 16514198) (lf 16514294)) (nd 88 (lf 16509078) (lf 16509174))))))) (nd 23 (nd 162 (nd 96 (nd 32 (lf 12083331) (nd 174 (lf 12058755) (lf 12107907))) (nd 34 (nd 37 (nd 58 (lf 12059043) (lf 5243267)) (nd 149 (nd 145 (lf 7343875) (lf 7368451)) (lf 7393027))) (nd 145 (nd 58 (lf 12083619) (lf 5267843)) (nd 58 (lf 12108195) (lf 5292419))))) (nd 64 (nd 35 (lf 8585219) (nd 73 (lf 8588291) (lf 8591363))) (nd 119 (nd 115 (lf 8784992) (lf 8906224)) (nd 29 (nd 115 (lf 8391776) (lf 8578544)) (nd 137 (lf 8512992) (lf 8513008)))))) (nd 19 (nd 68 (nd 76 (lf 8784899) (nd 77 (lf 8787971) (lf 8781827))) (nd 118 (nd 138 (lf 8519136) (lf 8519152)) (nd 74 (nd 139 (lf 8788064) (lf 8912368)) (nd 142 (lf 8394848) (lf 8584688))))) (nd 71 (nd 28 (lf 8391683) (nd 78 (lf 8388611) (lf 8394755))) (nd 142 (nd 125 (lf 8781920) (nd 34 (lf 8514016) (lf 8388704))) (nd 79 (nd 62 (lf 8514032) (lf 17834761)) (nd 30 (lf 8907248) (lf 8579568)))))))))) (nd 26 (nd 34 (nd 36 (nd 23 (nd 2 (nd 146 (nd 97 (nd 89 (nd 96 (nd 84 (nd 90 (nd 83 (nd 86 (lf 17301561) (lf 17301609)) (lf 17301609)) (lf 17301513)) (lf 17301513)) (lf 17385769)) (lf 17385849)) (lf 17385753)) (nd 84 (nd 94 (nd 122 (nd 97 (nd 118 (nd 119 (nd 98 (lf 17307657) (lf 17307753)) (lf 17307753)) (lf 17307705)) (lf 17307705)) (lf 17456505)) (lf 17456409)) (lf 17456425))) (nd 8 (nd 92 (nd 116 (nd 113 (lf 11534336) (lf 11682720)) (lf 11682720)) (lf 11682720)) (nd 137 (lf 12058656) (nd 128 (lf 12058672) (nd 122 (lf 12058624) (lf 4718592)))))) (nd 104 (nd 2 (nd 65 (lf 14680121) (lf 11731001)) (nd 6 (lf 14876672) (lf 15329440))) (nd 165 (nd 173 (nd 171 (lf 7364608) (lf 7340032)) (nd 136 (lf 15220793) (lf 7389184))) (nd 114 (lf 14745657) (nd 7 (lf 15329440) (lf 11534393)))))) (nd 18 (nd 33 (nd 15 (nd 118 (lf 11731972) (lf 11537412)) (nd 37 (lf 11011077) (nd 158 (nd 84 (lf 6844165) (lf 6843397)) (nd 125 (lf 6840325) (lf 6846469))))) (nd 121 (nd 140 (nd 166 (nd 162 (nd 156 (nd 171 (nd 131 (nd 179 (lf 17308084) (lf 17308132)) (lf 17308132)) (lf 17308036)) (lf 17308036)) (lf 17456292)) (lf 17456276)) (lf 17456372)) (nd 11 (nd 161 (nd 167 (nd 152 (lf 11558917) (lf 11674533)) (lf 11674533)) (lf 11674533)) (nd 145 (nd 173 (nd 177 (nd 167 (nd 158 (nd 156 (nd 135 (lf 17301940) (lf 17301892)) (lf 17301892)) (lf 17301988)) (lf 17301988)) (lf 17385636)) (lf 17385716)) (lf 17385620))))) (nd 7 (nd 79 (nd 106 (nd 19 (nd 60 (lf 11207687) (lf 14876680)) (lf 15400968)) (nd 153 (lf 11732018) (lf 11683730))) (nd 134 (nd 143 (nd 146 (nd 166 (nd 138 (nd 129 (nd 157 (lf 17301985) (lf 17301889)) (lf 17301889)) (lf 17301937)) (lf 17301937)) (lf 17385713)) (lf 17385617)) (nd 43 (lf 11534385) (lf 17385633)))) (nd 4 (nd 60 (nd 61 (nd 86 (nd 91 (nd 76 (nd 93 (nd 51 (lf 17308130) (lf 17308034)) (lf 17308034)) (lf 17308082)) (lf 17308082)) (lf 17456370)) (lf 17456274)) (lf 17456290)) (nd 16 (nd 134 (nd 5 (lf 15204402) (nd 151 (lf 11212807) (lf 15729026))) (nd 142 (lf 15729410) (nd 173 (lf 15728642) (lf 14882823)))) (nd 95 (nd 171 (lf 12017554) (lf 11688850)) (nd 23 (lf 11730994) (lf 11534386)))))))) (nd 41 (nd 29 (nd 2 (nd 177 (lf 14680064) (nd 106 (lf 11730953) (lf 11534345))) (nd 129 (nd 6 (lf 14680064) (lf 15204352)) (nd 138 (lf 14745609) (nd 89 (lf 15220745) (lf 15204352))))) (nd 33 (nd 2 (nd 65 (lf 14680169) (nd 105 (lf 11731049) (lf 11534441))) (nd 103 (nd 6 (lf 15073280) (lf 15597568)) (nd 111 (lf 14745705) (nd 87 (lf 15220841) (lf 15597568))))) (nd 131 (nd 135 (nd 145 (nd 15 (lf 15728649) (nd 95 (lf 7864329) (nd 79 (lf 7864425) (lf 7864377)))) (lf 16253321)) (nd 62 (lf 16252937) (lf 16253705))) (nd 63 (nd 16 (lf 15729033) (nd 84 (lf 7864761) (nd 113 (lf 7864713) (lf 7864809)))) (nd 1 (nd 121 (lf 7865193) (nd 102 (lf 7865145) (lf 7865097))) (lf 15729417)))))) (nd 15 (nd 51 (nd 152 (nd 18 (lf 16730004) (nd 133 (nd 179 (lf 11212808) (lf 14877704)) (lf 10485857))) (nd 147 (nd 75 (nd 109 (lf 16253316) (lf 16253313)) (nd 71 (lf 16252929) (lf 16253697))) (nd 118 (nd 67 (lf 16253745) (lf 16253364)) (nd 89 (lf 16252977) (lf 16253361))))) (nd 3 (nd 104 (nd 134 (lf 16729236) (lf 16253956)) (nd 152 (lf 16729364) (lf 16254724))) (nd 161 (nd 118 (lf 11732068) (lf 11537508)) (nd 117 (lf 11732020) (lf 11537460))))) (nd 101 (nd 2 (nd 125 (nd 99 (nd 158 (lf 16259169) (nd 175 (lf 16254049) (lf 16253025))) (lf 16729233)) (nd 87 (nd 161 (lf 16259553) (nd 153 (lf 16253409) (lf 16254433))) (nd 157 (lf 16254817) (nd 152 (lf 16259937) (lf 16253793))))) (nd 31 (lf 11207685) (lf 11404293))) (nd 56 (nd 151 (lf 11537457) (lf 11541553)) (nd 82 (lf 16729361) (lf 16730001))))))) (nd 1 (nd 146 (nd 151 (nd 14 (nd 8 (nd 7 (nd 106 (nd 105 (lf 12591113) (lf 9438009)) (nd 35 (lf 9437961) (lf 9438057))) (lf 18744073)) (nd 6 (lf 18793225) (lf 18752265))) (nd 30 (nd 98 (nd 139 (lf 6341640) (lf 6864904)) (nd 99 (lf 6342024) (lf 6342408))) (nd 34 (nd 97 (nd 138 (lf 6317064) (lf 6840328)) (nd 86 (lf 6317832) (lf 6317448))) (nd 147 (nd 78 (lf 6292488) (nd 117 (lf 6292872) (lf 6293256))) (nd 75 (nd 35 (lf 6815752) (lf 9967673)) (nd 91 (lf 9967721) (lf 9967625))))))) (nd 0 (nd 16 (nd 3 (nd 2 (nd 42 (nd 36 (nd 44 (nd 5 (nd 43 (nd 37 (nd 38 (nd 8 (nd 41 (nd 39 (nd 4 (nd 117 (nd 144 (nd 7 (nd 6 (lf 14024709) (lf 2294537)) (lf 2294537)) (lf 2100617)) (lf 27804417)) (lf 2491145)) (lf 3201032)) (lf 3397640)) (lf 2843401)) (lf 3348488)) (lf 3545096)) (lf 3569672)) (lf 3040009)) (lf 3373064)) (lf 3151880)) (lf 3176456)) (lf 2646793)) (lf 2491145)) (nd 84 (nd 113 (lf 14024709) (nd 70 (lf 9437193) (lf 9437577))) (nd 80 (nd 140 (lf 9437289) (nd 109 (lf 9437673) (lf 28001025))) (nd 131 (lf 9437241) (lf 9437625))))) (nd 3 (nd 15 (lf 2097161) (nd 28 (lf 525065) (lf 2105353))) (nd 10 (lf 18875401) (nd 131 (lf 12582921) (lf 12583945)))))) (nd 0 (nd 151 (nd 101 (nd 73 (lf 13631589) (nd 156 (nd 27 (lf 6867976) (lf 9968009)) (nd 27 (lf 6871048) (lf 9968393)))) (nd 55 (nd 81 (nd 32 (lf 6818824) (lf 9968057)) (nd 20 (lf 9968105) (lf 6843400))) (nd 18 (nd 75 (lf 9968441) (lf 9968489)) (nd 76 (lf 6846472) (lf 6821896))))) (nd 11 (nd 10 (nd 61 (nd 36 (nd 46 (lf 3152353) (lf 17834761)) (nd 38 (lf 3152257) (lf 3152305))) (nd 71 (nd 56 (lf 3152689) (lf 17220361)) (nd 15 (nd 46 (lf 17826569) (lf 3151921)) (lf 20447237)))) (nd 15 (lf 20971525) (lf 20971653))) (nd 46 (nd 149 (lf 27812609) (lf 20971541)) (lf 14025525)))) (nd 128 (nd 2 (nd 10 (nd 52 (lf 10485769) (nd 12 (lf 10493961) (lf 10485769))) (lf 12582921)) (lf 18359049)) (nd 139 (nd 8 (lf 2100617) (lf 18555657)) (nd 130 (lf 12582921) (nd 134 (lf 12725241) (lf 17834761))))))) (nd 2 (nd 10 (nd 51 (nd 170 (nd 109 (lf 16252985) (nd 77 (lf 16254057) (lf 10485817))) (lf 17826569)) (nd 141 (nd 90 (nd 45 (lf 16253321) (lf 10683145)) (nd 118 (lf 16253369) (lf 16253417))) (nd 12 (lf 10485769) (nd 117 (nd 142 (lf 16253705) (nd 128 (lf 10485769) (lf 4194313))) (nd 82 (lf 16253753) (lf 16253801)))))) (nd 22 (nd 21 (nd 29 (nd 131 (lf 11731977) (lf 11537417)) (nd 28 (nd 134 (lf 11732025) (lf 11537465)) (nd 106 (lf 11732073) (lf 11537513)))) (nd 149 (nd 97 (nd 78 (nd 107 (nd 93 (nd 72 (nd 86 (nd 83 (lf 17301945) (lf 17301993)) (lf 17301993)) (lf 17301897)) (lf 17301897)) (lf 17385721)) (lf 17385641)) (lf 17385625)) (nd 86 (nd 112 (nd 111 (nd 78 (nd 117 (nd 89 (nd 83 (lf 17308089) (lf 17308137)) (lf 17308137)) (lf 17308041)) (lf 17308041)) (lf 17456297)) (lf 17456281)) (lf 17456377)))) (nd 20 (nd 29 (nd 134 (lf 11737097) (lf 11541513)) (nd 83 (nd 133 (lf 11737193) (lf 11541609)) (nd 102 (lf 11737145) (lf 11541561)))) (nd 18 (nd 137 (nd 89 (nd 88 (nd 96 (nd 81 (nd 93 (nd 73 (nd 103 (lf 17302377) (lf 17302329)) (lf 17302329)) (lf 17302281)) (lf 17302281)) (lf 17386409)) (lf 17386393)) (lf 17386489)) (nd 121 (nd 84 (nd 113 (nd 87 (nd 72 (nd 92 (nd 98 (lf 17308473) (lf 17308521)) (lf 17308521)) (lf 17308425)) (lf 17308425)) (lf 17457145)) (lf 17457065)) (lf 17457049))) (nd 140 (nd 161 (lf 15728649) (lf 18547465)) (nd 132 (nd 136 (lf 15729033) (lf 18350473)) (nd 157 (lf 15729417) (lf 2097161)))))))) (nd 18 (nd 20 (nd 75 (nd 11 (lf 11016192) (lf 14686208)) (nd 76 (nd 150 (lf 14882816) (lf 11212800)) (nd 151 (lf 15079424) (lf 11409408)))) (nd 61 (nd 142 (lf 12107808) (nd 107 (lf 12107824) (nd 54 (lf 4767744) (lf 12107776)))) (nd 77 (nd 83 (nd 98 (lf 11583488) (lf 11723680)) (lf 11723680)) (lf 11723680)))) (nd 32 (nd 29 (nd 121 (nd 153 (lf 12083200) (lf 11011072)) (nd 111 (lf 12083232) (nd 129 (lf 12083248) (lf 4743168)))) (nd 95 (nd 92 (nd 98 (lf 11558912) (lf 11674528)) (lf 11674528)) (lf 11674528))) (nd 0 (nd 5 (nd 143 (lf 18596617) (lf 17023753)) (nd 63 (lf 16827145) (lf 18400009))) (nd 116 (nd 30 (lf 11404288) (lf 65545)) (lf 11207680))))))))) (nd 2 (nd 3 (nd 10 (nd 139 (nd 12 (nd 18 (nd 62 (nd 20 (nd 51 (lf 3149670) (lf 17834372)) (nd 26 (lf 3149574) (lf 3149622))) (nd 24 (nd 122 (nd 7 (lf 10707332) (lf 13631584)) (nd 111 (lf 13631504) (nd 99 (nd 9 (lf 13631488) (lf 2097156)) (nd 4 (lf 20971536) (nd 5 (lf 20971520) (lf 20972384)))))) (nd 45 (lf 3148902) (lf 3149286)))) (nd 66 (nd 21 (nd 9 (lf 3149238) (lf 12649473)) (lf 3149190)) (nd 21 (nd 9 (lf 3148854) (lf 12649473)) (nd 47 (lf 3148806) (lf 20971527))))) (nd 66 (nd 0 (nd 14 (nd 19 (nd 20 (lf 18874753) (lf 12582913)) (lf 13052913)) (lf 10887169)) (lf 16826756)) (nd 53 (nd 19 (nd 18 (lf 17826180) (lf 10485761)) (lf 12582913)) (nd 99 (nd 16 (nd 119 (lf 10485764) (lf 2097156)) (lf 18399620)) (nd 113 (nd 0 (lf 17966993) (lf 10682756)) (nd 45 (nd 15 (nd 63 (lf 12583937) (lf 13312001)) (lf 3670017)) (nd 56 (lf 19015665) (nd 1 (nd 123 (lf 18874372) (lf 3670017)) (lf 4194308))))))))) (nd 50 (nd 100 (nd 41 (nd 68 (nd 85 (nd 9 (lf 2103686) (lf 3152641)) (lf 29934344)) (lf 10492678)) (nd 152 (nd 24 (nd 121 (lf 27290627) (nd 144 (lf 27812611) (lf 27811843))) (nd 70 (nd 18 (lf 27683843) (lf 27487235)) (lf 30327560))) (nd 9 (lf 2627974) (lf 3152737)))) (nd 89 (nd 23 (nd 55 (nd 24 (lf 27285507) (nd 21 (lf 27482115) (lf 27678723))) (nd 26 (nd 118 (lf 27712262) (lf 27278086)) (nd 48 (lf 27490307) (lf 29612035)))) (nd 24 (nd 25 (nd 21 (lf 29415427) (lf 27293699)) (lf 29808643)) (nd 124 (nd 159 (lf 28205059) (lf 28205827)) (lf 27686915)))) (nd 56 (nd 150 (nd 20 (nd 24 (lf 22943844) (lf 22747236)) (lf 22550628)) (nd 19 (nd 26 (lf 22937700) (lf 22741092)) (lf 22544484))) (nd 76 (nd 47 (nd 175 (lf 27812614) (lf 27796230)) (nd 156 (lf 28008451) (lf 28009219))) (nd 18 (lf 27680771) (nd 24 (lf 27287555) (lf 27484163))))))) (nd 110 (nd 149 (nd 174 (nd 115 (nd 26 (lf 22943841) (lf 28197640)) (nd 65 (lf 27804419) (lf 29934339))) (nd 55 (nd 79 (lf 27275014) (lf 27803651)) (nd 61 (lf 29933571) (nd 69 (lf 27271942) (lf 22943745))))) (nd 39 (nd 9 (lf 2621830) (lf 3151969)) (nd 112 (nd 9 (lf 2097158) (lf 3151873)) (lf 27804424)))) (nd 79 (nd 103 (nd 25 (nd 71 (lf 29412355) (nd 63 (lf 27282435) (lf 27709190))) (nd 69 (nd 23 (lf 29608963) (lf 29805571)) (nd 18 (lf 27675651) (lf 27479043)))) (nd 172 (nd 71 (nd 46 (lf 15204449) (lf 30327555)) (lf 28197635)) (nd 61 (lf 30326787) (nd 174 (lf 15204353) (lf 28196867))))) (nd 87 (nd 22 (nd 125 (lf 27706118) (nd 70 (lf 29605891) (lf 27475971))) (nd 53 (nd 25 (lf 29409283) (lf 29802499)) (nd 25 (lf 27279363) (lf 27672579)))) (nd 150 (nd 25 (lf 30327558) (nd 47 (lf 28001027) (lf 30130947))) (nd 111 (nd 64 (lf 28000259) (lf 30130179)) (lf 28230406)))))))) (nd 15 (nd 18 (nd 50 (nd 71 (nd 156 (nd 146 (nd 128 (lf 16252932) (lf 16729252)) (lf 16730276)) (nd 166 (nd 134 (lf 16729236) (lf 16252980)) (nd 105 (lf 16729332) (lf 10485764)))) (nd 47 (lf 17826180) (lf 13303809))) (nd 119 (nd 69 (nd 156 (lf 16253316) (nd 161 (lf 16253412) (lf 16253364))) (nd 85 (nd 153 (lf 16253700) (nd 157 (lf 16253748) (lf 16253796))) (lf 10485764))) (nd 139 (nd 54 (nd 16 (lf 16730004) (lf 13132164)) (nd 85 (lf 16729364) (nd 106 (nd 16 (lf 18875396) (lf 10903940)) (lf 13303809)))) (nd 127 (nd 164 (lf 18877540) (lf 18877444)) (nd 135 (lf 18874372) (lf 18874468)))))) (nd 156 (nd 106 (nd 70 (lf 16253697) (nd 97 (nd 145 (nd 166 (lf 14681096) (lf 15073288)) (nd 144 (lf 14680072) (lf 11016200))) (nd 51 (nd 42 (lf 14680161) (lf 14680065)) (nd 88 (lf 1) (lf 65537))))) (nd 81 (lf 16253313) (nd 86 (lf 16252929) (nd 45 (lf 10485761) (lf 4194305))))) (nd 133 (nd 106 (nd 137 (nd 76 (lf 16253745) (lf 11409416)) (nd 76 (lf 16253793) (lf 15074312))) (nd 74 (lf 16253953) (lf 16254337))) (nd 151 (lf 10485761) (nd 50 (lf 10485857) (lf 3594248)))))) (nd 139 (nd 56 (nd 22 (nd 50 (nd 179 (nd 177 (lf 16729233) (lf 16259169)) (nd 164 (nd 159 (lf 16253025) (lf 16254049)) (lf 16254001))) (nd 62 (lf 17834372) (lf 13238273))) (nd 42 (nd 135 (nd 176 (nd 131 (nd 137 (nd 129 (nd 157 (lf 17301601) (lf 17301505)) (lf 17301505)) (lf 17385745)) (lf 17385761)) (nd 67 (nd 172 (lf 17385841) (lf 17456408)) (lf 17456504))) (nd 44 (lf 17301553) (lf 11537505))) (nd 152 (nd 128 (nd 140 (nd 135 (nd 130 (nd 132 (lf 17302369) (lf 17302273)) (lf 17302273)) (lf 17302321)) (lf 17386385)) (lf 17386401)) (nd 37 (lf 17386481) (lf 11537409))))) (nd 45 (nd 179 (nd 52 (lf 17450264) (nd 177 (lf 16730001) (lf 16259553))) (nd 140 (nd 35 (lf 16253409) (lf 16254433)) (lf 16254385))) (nd 76 (nd 179 (nd 177 (lf 16729361) (lf 16259937)) (nd 165 (nd 178 (lf 16254817) (lf 16253793)) (lf 16254769))) (nd 108 (nd 13 (lf 10493956) (lf 17825793)) (nd 66 (lf 18874369) (lf 13238273)))))) (nd 148 (nd 140 (nd 54 (nd 93 (lf 16259457) (nd 130 (nd 36 (lf 17302321) (lf 17301553)) (lf 11541601))) (nd 68 (lf 18874465) (lf 16259841))) (nd 56 (nd 110 (lf 16252929) (nd 78 (lf 15597576) (lf 11534433))) (nd 94 (lf 16253697) (lf 16253313)))) (nd 152 (nd 165 (nd 115 (lf 15204360) (lf 11541505)) (nd 63 (lf 18874753) (nd 122 (lf 16259121) (lf 16259889)))) (nd 68 (nd 22 (lf 18877441) (lf 11534337)) (nd 55 (nd 21 (lf 16253745) (lf 17981431)) (lf 16253361)))))))) (nd 119 (nd 9 (nd 111 (nd 81 (nd 106 (nd 130 (lf 17980534) (lf 10492678)) (nd 133 (nd 126 (nd 5 (lf 27312902) (lf 27509510)) (nd 30 (lf 6843395) (lf 9968100))) (nd 168 (nd 39 (lf 9968052) (lf 6818819)) (nd 29 (lf 6867971) (lf 9968004))))) (nd 28 (nd 179 (nd 121 (lf 6341635) (lf 6865667)) (nd 140 (lf 6342403) (lf 6342019))) (nd 35 (nd 150 (nd 103 (lf 6292483) (lf 6816515)) (nd 141 (lf 6293251) (lf 6292867))) (nd 151 (nd 99 (nd 80 (lf 6317059) (lf 22550625)) (lf 6841091)) (nd 133 (nd 1 (lf 22550529) (lf 6317443)) (lf 6317827)))))) (nd 53 (nd 103 (nd 7 (nd 24 (nd 128 (lf 15728644) (lf 17450902)) (nd 25 (lf 17450134) (nd 34 (lf 17450262) (lf 12632070)))) (nd 44 (nd 171 (lf 9961524) (nd 170 (lf 9961476) (lf 9961572))) (nd 32 (lf 6840707) (nd 29 (lf 6865283) (lf 6816131))))) (nd 1 (nd 72 (nd 150 (lf 29934342) (lf 27837190)) (nd 113 (nd 7 (lf 27515654) (lf 27319046)) (lf 20971616))) (nd 39 (nd 127 (lf 9967716) (nd 162 (lf 9967668) (lf 9967620))) (nd 160 (lf 6840323) (nd 126 (lf 6815747) (lf 6864899)))))) (nd 88 (nd 156 (nd 164 (nd 4 (nd 97 (lf 27512582) (lf 28033798)) (lf 27315974)) (nd 39 (lf 9968436) (lf 6821891))) (nd 133 (nd 167 (lf 30130950) (nd 31 (lf 6846467) (lf 9968484))) (nd 29 (lf 6871043) (lf 9968388)))) (nd 108 (lf 20971520) (lf 13631584))))) (nd 166 (nd 164 (nd 123 (nd 33 (nd 165 (nd 159 (nd 171 (nd 178 (nd 154 (lf 17308516) (lf 17308468)) (lf 17308468)) (lf 17308420)) (lf 17308420)) (lf 17457060)) (nd 165 (nd 130 (nd 172 (nd 134 (nd 176 (lf 17307652) (lf 17307748)) (lf 17307748)) (lf 17307700)) (lf 17307700)) (lf 17456420))) (lf 12725236)) (nd 177 (nd 39 (lf 11738164) (nd 121 (nd 38 (lf 17457140) (lf 17456500)) (lf 14680116))) (nd 83 (lf 15728644) (lf 11730996)))) (nd 178 (nd 28 (nd 153 (nd 77 (lf 15728642) (lf 14680164)) (lf 11738212)) (nd 154 (nd 148 (nd 43 (lf 17456404) (lf 17457044)) (lf 14680068)) (lf 11738116))) (nd 29 (nd 95 (lf 15728644) (lf 11731044)) (nd 98 (lf 15728644) (lf 11730948)))))) (nd 10 (nd 107 (nd 78 (nd 93 (nd 7 (lf 15729028) (nd 44 (nd 170 (lf 9961860) (nd 151 (lf 9961956) (lf 9961908))) (nd 31 (lf 6843779) (nd 29 (lf 6868355) (lf 6819203))))) (nd 168 (nd 175 (lf 1597828) (lf 14155780)) (nd 162 (lf 8962051) (nd 175 (lf 27804422) (lf 29885190))))) (nd 61 (nd 7 (lf 15729412) (nd 44 (nd 139 (lf 9962340) (nd 173 (lf 9962244) (lf 9962292))) (nd 31 (lf 6846851) (nd 165 (lf 6822275) (lf 6871427))))) (nd 9 (nd 12 (nd 24 (nd 15 (nd 8 (nd 13 (nd 21 (nd 18 (nd 16 (nd 20 (nd 23 (nd 19 (nd 26 (nd 25 (nd 22 (nd 14 (nd 11 (lf 13631488) (lf 2294148)) (lf 2294148)) (lf 3591171)) (lf 3394563)) (lf 3369987)) (lf 3197955)) (lf 3566595)) (lf 3173379)) (lf 3039620)) (lf 3148803)) (lf 3542019)) (lf 2228228)) (lf 1597828)) (lf 2646404)) (lf 3345411)) (lf 2097156)) (nd 15 (lf 2097156) (lf 2105348))))) (nd 6 (lf 20971520) (nd 111 (nd 127 (nd 147 (lf 13631504) (nd 64 (lf 6847235) (lf 6844163))) (nd 69 (nd 126 (lf 6819587) (lf 6868739)) (nd 156 (lf 6822659) (lf 6871811)))) (nd 5 (lf 20971616) (lf 20971744))))) (nd 14 (nd 16 (nd 1 (lf 12583940) (nd 75 (nd 130 (lf 15729026) (lf 15729410)) (lf 2228228))) (nd 88 (nd 83 (nd 60 (nd 98 (nd 77 (nd 48 (nd 90 (lf 17308466) (lf 17308418)) (lf 17308418)) (lf 17308514)) (lf 17308514)) (lf 17457058)) (lf 17457138)) (nd 81 (nd 153 (nd 83 (lf 17457042) (lf 11730946)) (lf 11534338)) (nd 162 (lf 11731042) (lf 11534434))))) (nd 38 (nd 179 (nd 174 (nd 148 (nd 169 (nd 154 (nd 161 (nd 140 (lf 17302276) (lf 17302372)) (lf 17302372)) (lf 17302324)) (lf 17302324)) (lf 17386388)) (nd 44 (lf 11534436) (lf 17386404))) (nd 92 (lf 15204450) (nd 175 (nd 147 (lf 17386484) (lf 11534388)) (lf 11534340)))) (nd 161 (nd 169 (nd 146 (nd 144 (nd 140 (nd 145 (nd 154 (lf 17301508) (lf 17301556)) (lf 17385748)) (lf 17301604)) (lf 17385764)) (lf 17385844)) (nd 159 (lf 17301556) (lf 11541604))) (nd 84 (nd 82 (lf 525058) (lf 15204354)) (nd 36 (nd 34 (lf 11541508) (lf 11541556)) (lf 17301604))))))))) (nd 46 (nd 165 (nd 9 (nd 50 (nd 51 (nd 162 (nd 95 (nd 78 (lf 17975283) (lf 16783362)) (lf 17981427)) (nd 160 (lf 12582914) (nd 176 (lf 14025144) (lf 13303810)))) (nd 24 (nd 93 (lf 16783362) (lf 16780290)) (lf 17909651))) (nd 65 (nd 92 (nd 84 (nd 19 (lf 25690981) (lf 16783410)) (lf 16783458)) (nd 78 (lf 16780338) (lf 16780386))) (nd 112 (nd 33 (nd 45 (lf 26222600) (lf 9437956)) (lf 7865140)) (nd 10 (nd 30 (lf 24117353) (lf 26214408)) (lf 22413315))))) (nd 179 (nd 7 (nd 41 (nd 62 (nd 87 (nd 82 (nd 72 (nd 90 (nd 80 (nd 95 (lf 17307698) (lf 17307746)) (lf 17307746)) (lf 17307650)) (lf 17307650)) (lf 17456402)) (lf 17456418)) (nd 28 (nd 53 (lf 17456498) (lf 17450359)) (lf 14155780))) (nd 80 (lf 11732066) (lf 11731970))) (nd 89 (nd 87 (nd 141 (nd 60 (lf 14686215) (lf 15079431)) (lf 12582914)) (lf 12017650)) (nd 10 (nd 56 (lf 8962052) (nd 68 (lf 25690885) (lf 22020099))) (nd 156 (lf 12017570) (lf 9968482))))) (nd 18 (nd 99 (nd 130 (nd 12 (lf 29385092) (lf 9965026)) (nd 92 (lf 25166213) (lf 26738744))) (nd 166 (lf 14025144) (nd 36 (lf 18400130) (nd 171 (lf 12582914) (lf 20971544))))) (nd 21 (nd 161 (lf 18359170) (lf 12582914)) (nd 161 (nd 155 (lf 17456503) (lf 18350978)) (nd 7 (lf 11730951) (lf 15729410))))))) (nd 99 (nd 102 (nd 100 (nd 34 (nd 51 (nd 97 (nd 32 (lf 23068674) (lf 23461890)) (lf 15729026)) (nd 21 (nd 10 (lf 29409668) (lf 9968098)) (nd 62 (lf 16780386) (lf 16783458)))) (nd 44 (nd 32 (lf 11534342) (nd 152 (lf 7865092) (lf 7865188))) (nd 170 (nd 1 (lf 29560582) (nd 0 (lf 29757190) (lf 9438052))) (nd 48 (lf 23265282) (lf 9438004))))) (nd 38 (nd 103 (lf 11534390) (lf 11534438)) (nd 65 (lf 14025097) (nd 139 (lf 26217480) (lf 26220552))))) (nd 89 (nd 7 (nd 113 (lf 11541510) (lf 11668486)) (nd 93 (lf 18023170) (nd 18 (lf 18016243) (lf 17967091)))) (nd 47 (nd 178 (lf 17973235) (lf 18022387)) (nd 159 (lf 26738792) (nd 98 (lf 25166085) (lf 26738696)))))) (nd 164 (nd 171 (nd 18 (nd 80 (lf 14025096) (nd 147 (lf 26739080) (nd 92 (lf 11731047) (lf 26739464)))) (nd 11 (nd 176 (lf 15728642) (lf 2097154)) (nd 58 (nd 75 (nd 115 (lf 11011079) (lf 11730999)) (lf 11404295)) (nd 83 (lf 11409415) (lf 11016199))))) (nd 12 (nd 47 (lf 18016147) (nd 60 (nd 170 (nd 33 (lf 24118121) (lf 26228744)) (lf 25166181)) (nd 7 (lf 27471622) (lf 27668230)))) (nd 158 (nd 26 (lf 18744194) (nd 20 (lf 18793346) (lf 18752386))) (nd 59 (nd 20 (lf 20971528) (lf 12790770)) (lf 25166133))))) (nd 124 (nd 24 (nd 33 (nd 114 (lf 13156354) (nd 177 (lf 9967714) (lf 20971577))) (nd 27 (lf 20972345) (nd 74 (lf 20971673) (lf 26225672)))) (nd 26 (nd 22 (nd 9 (lf 3670019) (nd 132 (lf 65538) (lf 2))) (lf 13107203)) (nd 8 (nd 21 (lf 11668534) (nd 104 (lf 11541606) (lf 11668582))) (lf 13131779)))) (nd 178 (nd 172 (nd 161 (nd 21 (lf 18555778) (nd 26 (lf 18547586) (lf 18596738))) (nd 53 (lf 17966995) (lf 24117737))) (nd 18 (lf 13631592) (lf 12790770))) (nd 111 (nd 101 (lf 11541558) (lf 17834882)) (nd 101 (nd 31 (lf 20972009) (nd 29 (lf 20972393) (lf 20971625))) (nd 13 (nd 21 (nd 11 (nd 16 (lf 21495816) (lf 20971544)) (lf 20971656)) (nd 104 (lf 13303810) (lf 4194306))) (lf 20971528))))))))) (nd 34 (nd 154 (nd 177 (nd 173 (nd 119 (nd 15 (nd 82 (nd 10 (lf 27466500) (nd 11 (lf 27269892) (lf 27663108))) (nd 14 (lf 27286276) (nd 12 (lf 27679492) (lf 27482884)))) (lf 6292482)) (nd 55 (nd 90 (nd 92 (nd 81 (lf 11688866) (lf 11688946)) (lf 11683746)) (nd 4 (lf 11683826) (nd 12 (lf 22943763) (lf 22550547)))) (nd 74 (nd 10 (lf 22550627) (nd 166 (lf 22943843) (lf 17450263))) (nd 139 (lf 6293250) (lf 6292866))))) (nd 8 (nd 118 (lf 14680069) (nd 84 (nd 78 (lf 9437572) (lf 14240676)) (nd 10 (nd 122 (lf 9437188) (lf 14155780)) (lf 15204356)))) (nd 41 (nd 96 (lf 12058627) (nd 57 (lf 12058659) (lf 5243139))) (nd 9 (nd 84 (nd 75 (lf 29409284) (lf 27321092)) (lf 29410052)) (nd 80 (nd 3 (lf 9968002) (lf 6867973)) (nd 3 (lf 9968050) (lf 6818821))))))) (nd 70 (nd 172 (nd 139 (nd 170 (nd 11 (lf 27283204) (nd 10 (lf 27479812) (lf 27676420))) (nd 124 (lf 28009221) (nd 155 (lf 28001028) (lf 25190836)))) (nd 158 (nd 14 (lf 27280132) (nd 10 (lf 27476740) (lf 27673348))) (nd 144 (lf 27804420) (lf 28197636)))) (nd 109 (nd 33 (nd 27 (nd 56 (lf 16783362) (lf 16783410)) (lf 27288325)) (nd 27 (lf 27681541) (lf 27484933))) (nd 30 (nd 9 (lf 29410053) (lf 27288324)) (nd 81 (lf 28836613) (lf 27280133))))) (nd 109 (nd 104 (nd 35 (nd 112 (lf 27287685) (nd 65 (lf 16780290) (lf 16780338))) (nd 32 (lf 27484293) (lf 27680901))) (nd 13 (nd 151 (lf 28008581) (lf 27463428)) (nd 113 (nd 9 (lf 27660036) (lf 27266820)) (lf 27788036)))) (nd 10 (nd 117 (nd 71 (lf 27279493) (lf 28836229)) (nd 11 (lf 29409413) (nd 149 (lf 27984644) (lf 27460356)))) (nd 12 (nd 14 (nd 80 (lf 29385476) (lf 29384708)) (nd 99 (lf 27656964) (lf 28181252))) (nd 63 (nd 43 (lf 6819589) (lf 9964978)) (nd 165 (nd 1 (lf 9964930) (lf 6868741)) (lf 27263748)))))))) (nd 178 (nd 15 (nd 96 (nd 31 (nd 27 (lf 27687685) (nd 32 (lf 27491077) (lf 27294469))) (nd 36 (lf 12059395) (nd 29 (lf 27286277) (lf 29416197)))) (nd 28 (nd 27 (lf 27687045) (nd 33 (lf 27293829) (lf 27490437))) (nd 168 (nd 82 (lf 12059427) (lf 4719363)) (nd 101 (lf 29415557) (lf 27285637))))) (nd 141 (nd 36 (nd 42 (lf 11016197) (lf 6871045)) (nd 57 (nd 93 (nd 6 (lf 9968434) (lf 6821893)) (lf 27324164)) (nd 0 (lf 9968386) (lf 29413124)))) (nd 9 (nd 151 (nd 64 (lf 29416196) (lf 27327236)) (nd 93 (lf 29934340) (lf 27845380))) (nd 13 (nd 82 (lf 29391620) (lf 27294468)) (nd 0 (nd 78 (lf 9967666) (lf 9967618)) (nd 89 (lf 6864901) (lf 6815749))))))) (nd 166 (nd 97 (nd 118 (nd 27 (nd 116 (lf 27684613) (lf 27812612)) (nd 32 (lf 27488005) (lf 27291397))) (nd 105 (lf 27283205) (nd 104 (lf 29413125) (lf 27291396)))) (nd 124 (nd 35 (lf 27290757) (nd 30 (lf 27487365) (lf 27683973))) (nd 156 (nd 140 (lf 29388548) (lf 29909764)) (nd 99 (lf 27282565) (lf 29412485))))) (nd 28 (nd 176 (nd 64 (nd 81 (lf 25190884) (lf 28205829)) (lf 28205189)) (nd 107 (nd 58 (nd 123 (lf 22938722) (lf 25715556)) (lf 22943842)) (nd 84 (nd 94 (lf 25190788) (lf 27811973)) (lf 27812613)))) (nd 123 (nd 84 (nd 106 (lf 22545506) (lf 27803781)) (nd 168 (lf 27804421) (lf 22550626))) (nd 102 (nd 107 (lf 25715460) (lf 25190660)) (nd 58 (lf 29933701) (lf 29934341)))))))) (nd 32 (nd 29 (nd 137 (nd 129 (nd 112 (nd 176 (nd 172 (lf 7340803) (lf 7365379)) (lf 7389955)) (nd 152 (nd 158 (nd 167 (lf 11534341) (lf 11682725)) (lf 11682725)) (lf 11682725))) (nd 87 (nd 116 (nd 30 (lf 27479173) (lf 27675781)) (nd 67 (lf 25190756) (lf 28196997))) (nd 136 (nd 31 (lf 27479813) (lf 27676421)) (lf 28197637)))) (nd 69 (nd 125 (nd 173 (nd 31 (lf 27482885) (lf 27679493)) (nd 61 (lf 25715508) (lf 22747234))) (nd 159 (nd 31 (lf 27476741) (lf 27673349)) (nd 82 (lf 25190708) (lf 28001029)))) (nd 100 (nd 28 (nd 134 (lf 27672709) (lf 22742114)) (lf 27476101)) (nd 147 (nd 28 (lf 27678853) (lf 27482245)) (lf 28000389))))) (nd 155 (nd 8 (nd 118 (lf 14876677) (nd 68 (nd 97 (lf 15204404) (lf 9437236)) (nd 61 (lf 15220788) (lf 9437620)))) (nd 63 (nd 47 (lf 29606661) (lf 12083203)) (nd 44 (nd 84 (lf 12083235) (lf 5267715)) (lf 29606021)))) (nd 77 (nd 88 (nd 176 (lf 29612165) (nd 108 (lf 29609093) (lf 30130309))) (nd 164 (lf 29609733) (nd 121 (lf 29612805) (lf 30130949)))) (nd 9 (nd 70 (lf 12083971) (nd 86 (lf 12084003) (lf 4743939))) (lf 11212805))))) (nd 29 (nd 154 (nd 8 (nd 118 (lf 15073285) (nd 83 (nd 84 (lf 15220836) (lf 9437284)) (nd 65 (lf 15204452) (lf 9437668)))) (nd 91 (nd 173 (lf 12107779) (lf 29803269)) (nd 33 (lf 29802629) (nd 61 (lf 12107811) (lf 5292291))))) (nd 53 (nd 57 (nd 108 (lf 29805701) (nd 134 (lf 30326917) (lf 29808773))) (nd 170 (nd 163 (lf 29806341) (lf 30327557)) (lf 29809413))) (nd 15 (nd 96 (lf 12108547) (nd 57 (lf 12108579) (lf 4768515))) (lf 11409413)))) (nd 116 (nd 138 (nd 5 (lf 13631504) (nd 6 (nd 137 (lf 13632272) (lf 7864372)) (nd 148 (nd 152 (lf 7346947) (lf 7396099)) (lf 7371523)))) (nd 68 (nd 100 (nd 44 (nd 179 (lf 7864324) (lf 7864420)) (nd 0 (lf 29760262) (lf 29563654))) (nd 101 (nd 6 (lf 27671302) (lf 27474694)) (nd 175 (lf 28205830) (lf 28189446)))) (nd 86 (nd 171 (lf 28009222) (nd 75 (lf 17842566) (lf 27992838))) (nd 103 (nd 171 (lf 22747233) (lf 22747137)) (nd 0 (lf 27665158) (lf 27468550)))))) (nd 117 (nd 10 (nd 1 (nd 48 (lf 29557510) (lf 10534916)) (nd 137 (nd 44 (lf 7864708) (lf 29754118)) (nd 145 (lf 7864804) (lf 7864756)))) (nd 167 (nd 176 (nd 161 (lf 11583493) (lf 11723685)) (lf 11723685)) (lf 11723685))) (nd 105 (nd 162 (nd 1 (nd 3 (nd 15 (nd 8 (lf 2146308) (lf 13632256)) (lf 2105348)) (lf 2105348)) (lf 13631488)) (nd 87 (nd 159 (lf 30081798) (lf 28001030)) (nd 174 (lf 28197638) (lf 30278406)))) (nd 1 (nd 5 (lf 20971664) (lf 20971648)) (nd 0 (nd 5 (lf 20972304) (lf 20972288)) (lf 20447232)))))))))))) (nd 112 (nd 93 (nd 76 (nd 108 (nd 97 (nd 0 (nd 16 (nd 10 (lf 14025525) (nd 129 (lf 1055112) (lf 1598217))) (nd 15 (lf 13631589) (nd 31 (nd 23 (nd 33 (lf 12084069) (lf 5267848)) (nd 78 (lf 7393032) (lf 7343880))) (nd 107 (nd 148 (nd 18 (lf 7346952) (lf 7340808)) (lf 12058760)) (nd 21 (lf 7396104) (lf 7389960)))))) (nd 140 (nd 23 (nd 168 (lf 6317063) (lf 6323207)) (nd 169 (lf 6317111) (nd 154 (lf 6323255) (nd 14 (lf 2125193) (lf 2624905))))) (nd 128 (nd 133 (nd 2 (lf 18353545) (lf 10497801)) (lf 16781065)) (nd 49 (lf 16781065) (nd 14 (lf 2128265) (lf 2627977)))))) (nd 27 (nd 26 (nd 11 (nd 36 (nd 23 (nd 39 (nd 40 (nd 38 (nd 30 (nd 44 (nd 33 (nd 41 (nd 42 (nd 34 (nd 35 (nd 37 (nd 43 (nd 31 (nd 28 (nd 29 (nd 32 (lf 14024758) (lf 2295552)) (lf 2295552)) (lf 2492160)) (lf 2492160)) (lf 3397767)) (lf 3201159)) (lf 2844416)) (lf 3041024)) (lf 3348615)) (lf 3569799)) (lf 2647808)) (lf 3373191)) (lf 2100608)) (lf 3176839)) (lf 3594375)) (lf 3545223)) (lf 1601280)) (lf 3149191)) (nd 94 (lf 3149191) (nd 141 (lf 18399616) (lf 12058725)))) (nd 36 (nd 152 (nd 38 (lf 14024758) (nd 25 (lf 3176887) (lf 3176935))) (nd 114 (lf 7371528) (lf 5292424))) (nd 25 (lf 3149239) (lf 3149287)))) (nd 26 (nd 86 (nd 5 (lf 7365384) (lf 2100608)) (nd 34 (lf 18350464) (lf 18359040))) (nd 19 (nd 81 (lf 7368456) (lf 2125184)) (nd 72 (nd 119 (lf 5243272) (lf 6292536)) (lf 2624896)))))) (nd 62 (nd 65 (nd 4 (nd 32 (nd 145 (nd 27 (lf 27684608) (nd 28 (lf 27488000) (lf 27291392))) (nd 2 (nd 143 (lf 29413120) (nd 144 (lf 27283200) (nd 81 (lf 27684617) (lf 27479817)))) (nd 82 (nd 5 (lf 27488009) (lf 27291401)) (lf 29609737)))) (nd 146 (nd 31 (lf 29609728) (lf 29806336)) (nd 27 (lf 27676416) (lf 27479808)))) (nd 96 (nd 8 (nd 3 (lf 29413129) (nd 9 (lf 9968391) (lf 6871040))) (nd 3 (lf 29806345) (nd 10 (lf 10017543) (lf 6871136)))) (nd 68 (nd 0 (lf 27676425) (lf 27283209)) (nd 26 (nd 0 (lf 6822752) (lf 6822656)) (nd 1 (lf 10014519) (lf 9965367)))))) (nd 156 (nd 3 (nd 33 (nd 32 (nd 7 (nd 2 (nd 29 (lf 27282560) (lf 27683968)) (nd 81 (lf 29585161) (lf 27324169))) (nd 1 (lf 27717385) (nd 98 (lf 27520777) (lf 27463433)))) (nd 152 (lf 29805696) (nd 30 (lf 27675776) (lf 27479168)))) (nd 134 (nd 32 (lf 29412480) (lf 29609088)) (nd 34 (lf 27487360) (lf 27290752)))) (nd 0 (nd 71 (nd 87 (nd 24 (lf 6871904) (nd 12 (lf 10014471) (lf 29781769))) (lf 27660041)) (nd 19 (lf 6847328) (lf 10014567))) (nd 71 (nd 73 (lf 27266825) (nd 21 (lf 6871808) (nd 13 (lf 9965319) (lf 29388553)))) (nd 25 (lf 6847232) (lf 9965415))))) (nd 142 (nd 32 (nd 29 (nd 47 (lf 27290624) (lf 6293304)) (nd 27 (lf 27683840) (lf 27487232))) (nd 71 (nd 30 (lf 6342456) (lf 6317880)) (nd 88 (lf 6317112) (lf 6341688)))) (nd 2 (nd 32 (nd 79 (nd 0 (lf 29757193) (nd 3 (lf 29560585) (lf 29363977))) (nd 5 (nd 135 (lf 27282432) (lf 29412352)) (nd 7 (lf 27668233) (lf 27709193)))) (nd 144 (nd 28 (lf 27479040) (lf 27675648)) (nd 30 (lf 29805568) (lf 29608960)))) (nd 96 (nd 8 (lf 27315977) (lf 27512585)) (nd 5 (lf 27471625) (lf 27275017))))))) (nd 90 (nd 0 (nd 79 (nd 168 (nd 19 (lf 6342455) (lf 6342407)) (nd 22 (nd 45 (lf 6348599) (nd 68 (lf 6341687) (lf 6347831))) (lf 6348551))) (nd 2 (nd 56 (nd 3 (lf 29805577) (nd 26 (lf 6821984) (lf 10017591))) (nd 22 (lf 6846560) (nd 11 (lf 10017639) (lf 29805705)))) (nd 4 (nd 154 (lf 29609097) (lf 29608969)) (nd 55 (lf 29412361) (lf 29412489))))) (nd 22 (nd 178 (nd 49 (nd 10 (lf 26739176) (lf 6846464)) (nd 101 (lf 6292535) (nd 4 (lf 6317879) (lf 6293303)))) (nd 40 (nd 3 (lf 6324023) (lf 6299447)) (nd 68 (lf 25166261) (lf 26739128)))) (nd 72 (nd 7 (nd 171 (lf 6299399) (lf 6293255)) (nd 53 (lf 6323975) (lf 6317831))) (nd 20 (lf 6821888) (nd 50 (lf 9968487) (lf 9968439)))))) (nd 47 (nd 0 (nd 30 (nd 28 (nd 73 (lf 27675657) (nd 88 (lf 27683849) (nd 146 (lf 27709184) (lf 27471616)))) (nd 31 (nd 35 (lf 27275008) (lf 27668224)) (lf 29757184))) (nd 141 (nd 28 (lf 29560576) (lf 29363968)) (nd 35 (lf 27315968) (lf 27512576)))) (nd 82 (nd 5 (lf 27487241) (lf 27290633)) (nd 3 (lf 27479049) (lf 27282441)))) (nd 32 (nd 0 (nd 142 (nd 27 (lf 29781760) (nd 29 (lf 29388544) (lf 29585152))) (nd 3 (nd 135 (lf 27266816) (lf 27324160)) (nd 88 (lf 27683977) (lf 27675785)))) (nd 87 (nd 6 (lf 27290761) (lf 27487369)) (nd 4 (lf 27479177) (lf 27282569)))) (nd 31 (nd 107 (lf 12083336) (nd 146 (lf 27520768) (lf 27463424))) (nd 49 (nd 28 (lf 27717376) (lf 27660032)) (lf 12107912)))))))) (nd 117 (nd 33 (nd 28 (nd 98 (nd 79 (lf 13828198) (nd 68 (nd 75 (lf 12059493) (lf 12108645)) (lf 13328389))) (nd 69 (nd 116 (lf 20971521) (nd 59 (lf 12059109) (lf 6317058))) (nd 74 (lf 13828102) (nd 32 (lf 13828097) (lf 10493957))))) (nd 44 (nd 22 (nd 37 (nd 43 (nd 42 (nd 26 (nd 41 (nd 35 (nd 32 (nd 25 (nd 24 (nd 19 (nd 29 (nd 18 (nd 39 (nd 40 (nd 21 (nd 20 (nd 23 (lf 17829253) (lf 18350464)) (lf 18350464)) (lf 10492288)) (lf 17842565)) (lf 17842565)) (lf 18350464)) (lf 19071360)) (lf 10486144)) (lf 10489216)) (lf 10489216)) (lf 19087360)) (nd 172 (lf 17834752) (lf 13303808))) (lf 17845637)) (lf 18353536)) (lf 16777605)) (lf 16783749)) (lf 17825797)) (lf 10492288)) (lf 16780677))) (nd 18 (nd 24 (nd 35 (lf 17829253) (lf 13246469)) (nd 143 (nd 31 (lf 10497024) (lf 18403072)) (lf 4719368))) (nd 28 (lf 18399616) (nd 2 (lf 5243144) (lf 18359040))))) (nd 19 (nd 59 (nd 175 (nd 44 (nd 60 (lf 12083360) (nd 168 (lf 12084000) (lf 25169335))) (nd 162 (nd 15 (lf 27684612) (lf 27488004)) (lf 28009220))) (nd 104 (lf 30130948) (nd 13 (lf 29609732) (lf 29806340)))) (nd 149 (nd 11 (lf 13115393) (lf 6317058)) (nd 9 (lf 6342402) (nd 104 (nd 23 (lf 25693959) (lf 25694007)) (lf 6317826))))) (nd 162 (nd 179 (nd 54 (nd 20 (lf 12059424) (lf 30130185)) (lf 28033801)) (nd 154 (nd 51 (lf 28033033) (lf 26739171)) (nd 99 (lf 25169287) (lf 12058784)))) (nd 166 (nd 169 (nd 48 (lf 30130313) (nd 155 (lf 12107936) (lf 26274820))) (lf 28041993)) (nd 6 (lf 30130953) (nd 65 (lf 12108576) (nd 81 (lf 25694055) (lf 25169383))))))))) (nd 168 (nd 169 (nd 3 (nd 35 (nd 171 (nd 79 (nd 0 (nd 163 (lf 26217475) (lf 30081792)) (nd 161 (lf 28000265) (lf 26739075))) (nd 166 (nd 161 (nd 74 (lf 25166128) (lf 25166256)) (nd 119 (lf 8391781) (lf 26739123))) (lf 28008457))) (nd 144 (nd 166 (nd 167 (lf 26763652) (lf 27984640)) (lf 28001024)) (nd 73 (nd 52 (lf 28001033) (nd 61 (lf 24117635) (lf 28000393))) (nd 173 (lf 28009225) (nd 156 (lf 26242052) (lf 28008585)))))) (nd 166 (nd 59 (nd 69 (nd 62 (nd 30 (lf 26763700) (lf 26763748)) (nd 137 (lf 28041984) (lf 30106368))) (nd 47 (nd 131 (lf 24117732) (lf 26225667)) (lf 10707332))) (nd 0 (nd 100 (nd 32 (lf 8588389) (lf 8784997)) (lf 17966993)) (nd 12 (lf 10707332) (lf 18596228)))) (nd 149 (nd 171 (lf 28033792) (lf 30130944)) (nd 162 (lf 27992832) (nd 139 (lf 28009216) (nd 90 (lf 12083208) (lf 12083976))))))) (nd 124 (nd 27 (nd 18 (nd 11 (nd 44 (nd 21 (nd 37 (nd 35 (nd 26 (nd 24 (nd 23 (nd 19 (nd 29 (nd 20 (nd 25 (nd 28 (nd 32 (nd 22 (nd 30 (nd 31 (nd 34 (nd 33 (lf 13828913) (lf 2295557)) (lf 2295557)) (lf 2492165)) (lf 2492165)) (lf 3594370)) (lf 3041029)) (lf 2100613)) (lf 3569794)) (lf 3348610)) (lf 2647813)) (lf 3545218)) (lf 3397762)) (lf 3176834)) (lf 3373186)) (lf 2844421)) (lf 14024753)) (lf 3201154)) (nd 24 (lf 13828913) (nd 41 (lf 3176882) (lf 3176930)))) (lf 13828913)) (nd 39 (lf 3149234) (nd 36 (lf 3149282) (lf 3149186)))) (nd 44 (nd 178 (lf 13303808) (nd 171 (lf 10486149) (lf 2100613))) (nd 38 (lf 2624901) (lf 2125189)))) (nd 175 (nd 156 (nd 10 (lf 29585156) (lf 29781764)) (lf 12084000)) (nd 37 (nd 20 (lf 12059424) (lf 12108576)) (nd 131 (lf 28041988) (nd 16 (lf 27520772) (lf 27717380))))))) (nd 29 (nd 27 (nd 171 (nd 176 (nd 64 (lf 12058784) (lf 13828193)) (nd 100 (nd 173 (lf 28033024) (lf 25169159)) (nd 2 (lf 30081033) (lf 27992073)))) (nd 64 (lf 20971526) (nd 82 (lf 13828102) (lf 13828097)))) (nd 20 (nd 40 (nd 23 (nd 25 (nd 26 (nd 44 (nd 21 (nd 35 (nd 37 (nd 41 (nd 38 (nd 19 (nd 22 (nd 36 (nd 42 (nd 43 (nd 33 (nd 34 (nd 39 (lf 17829248) (lf 10486149)) (lf 19071365)) (lf 19071365)) (lf 18350469)) (lf 18350469)) (lf 10486149)) (lf 17842560)) (lf 17842560)) (lf 10489221)) (lf 10489221)) (lf 10492293)) (lf 13303808)) (lf 17825792)) (lf 18353541)) (lf 16780672)) (lf 17845632)) (lf 16783744)) (lf 10492293)) (lf 16777600))) (nd 36 (nd 107 (nd 38 (lf 17829248) (nd 28 (lf 10497797) (lf 18403077))) (nd 28 (nd 141 (lf 30081024) (lf 27992064)) (lf 8394853))) (nd 31 (lf 10493957) (nd 42 (lf 18399621) (lf 8388709)))))) (nd 154 (nd 155 (nd 43 (nd 40 (nd 167 (nd 103 (nd 146 (lf 30130176) (nd 142 (lf 28008448) (lf 28000256))) (nd 77 (lf 30081801) (lf 27992841))) (nd 158 (nd 170 (lf 2236805) (lf 2097541)) (lf 3670016))) (nd 32 (nd 22 (nd 23 (nd 25 (nd 35 (nd 24 (nd 19 (nd 29 (nd 20 (nd 21 (nd 44 (nd 18 (nd 26 (nd 33 (nd 34 (nd 31 (nd 30 (nd 27 (nd 28 (lf 13828097) (lf 2097541)) (lf 2097541)) (lf 2490757)) (lf 2490757)) (lf 2294149)) (lf 2294149)) (lf 3369986)) (lf 3148802)) (lf 1597829)) (lf 3197954)) (lf 3345410)) (lf 2646405)) (lf 3542018)) (lf 3173378)) (lf 2843013)) (lf 3566594)) (lf 3394562)) (lf 3591170)) (lf 3039621))) (nd 27 (nd 18 (nd 24 (nd 115 (lf 13828097) (lf 8781925)) (nd 37 (lf 3176546) (lf 3176498))) (nd 37 (lf 3148898) (lf 3148850))) (nd 36 (lf 2621829) (nd 178 (lf 8585317) (lf 2105349))))) (nd 36 (nd 38 (nd 147 (nd 30 (lf 17837824) (lf 17834373)) (nd 150 (lf 25169207) (lf 12083360))) (nd 141 (nd 27 (lf 18599685) (nd 29 (lf 10686213) (lf 10710789))) (lf 8591461))) (nd 27 (lf 18596229) (nd 28 (lf 10707333) (lf 10682757))))) (nd 82 (nd 88 (nd 18 (nd 73 (nd 24 (nd 44 (lf 17837829) (nd 5 (lf 12083301) (lf 12083685))) (nd 1 (lf 4743944) (nd 33 (lf 10686208) (nd 30 (lf 10710784) (lf 18599680))))) (nd 162 (lf 17825920) (nd 106 (nd 29 (nd 32 (lf 13238277) (lf 10903941)) (lf 17834368)) (nd 136 (nd 179 (lf 12107936) (lf 12108261)) (lf 30106372))))) (nd 1 (nd 149 (nd 151 (lf 6317112) (nd 144 (lf 5267720) (lf 30130304))) (nd 32 (nd 87 (lf 30106377) (lf 28008576)) (lf 28000384))) (nd 35 (nd 72 (nd 32 (lf 2097152) (lf 10682752)) (lf 18547456)) (nd 27 (lf 18596224) (lf 18555648))))) (nd 20 (nd 73 (nd 27 (nd 28 (nd 33 (nd 34 (nd 41 (nd 26 (nd 43 (nd 42 (nd 35 (nd 38 (nd 44 (nd 31 (nd 30 (nd 37 (nd 39 (nd 40 (nd 36 (nd 47 (nd 145 (nd 150 (lf 20971526) (lf 24641538)) (lf 23592966)) (nd 29 (nd 32 (lf 13828102) (lf 2294144)) (lf 2294144))) (lf 3148807)) (lf 3591175)) (lf 3542023)) (lf 3197959)) (lf 2097152)) (lf 2490752)) (lf 3369991)) (lf 3173383)) (lf 2843008)) (lf 3345415)) (lf 3394567)) (lf 1597824)) (lf 3566599)) (lf 3039616)) (lf 2646400)) (lf 2490752)) (lf 2097152)) (nd 34 (nd 80 (lf 10879360) (lf 20971526)) (nd 29 (lf 18792832) (lf 10903936)))) (nd 27 (nd 36 (nd 38 (nd 179 (lf 25169255) (nd 124 (lf 13828102) (lf 5292296))) (nd 18 (lf 3176551) (lf 3176471))) (nd 21 (lf 3148903) (lf 3148855))) (nd 18 (lf 2621824) (nd 0 (lf 525056) (lf 2105728)))))) (nd 31 (nd 98 (nd 95 (nd 27 (nd 71 (nd 72 (lf 12107877) (lf 20972385)) (nd 36 (nd 24 (nd 38 (lf 18752256) (lf 17026821)) (lf 10907392)) (lf 17023365))) (lf 18899328)) (nd 36 (nd 27 (nd 38 (nd 69 (lf 20972390) (lf 13828198)) (nd 25 (lf 3177271) (nd 21 (lf 3177319) (lf 3177223)))) (nd 21 (lf 2627968) (nd 22 (lf 2128256) (lf 2103680)))) (nd 21 (lf 3149671) (nd 26 (lf 3149575) (lf 3149623))))) (nd 172 (nd 18 (nd 27 (nd 24 (lf 13828193) (nd 38 (lf 3177314) (nd 44 (lf 3177218) (lf 3177266)))) (nd 43 (lf 2103685) (nd 38 (lf 2627973) (lf 2128261)))) (nd 37 (lf 3149666) (nd 44 (lf 3149570) (lf 3149618)))) (nd 30 (nd 19 (nd 28 (nd 40 (lf 13246469) (lf 20971521)) (lf 17834368)) (nd 26 (lf 20971526) (nd 134 (lf 12107936) (lf 27984649)))) (nd 27 (nd 18 (nd 52 (lf 10903941) (nd 38 (nd 24 (lf 10903941) (lf 17026816)) (lf 10907397))) (lf 17023360)) (lf 18899333))))) (nd 35 (nd 29 (nd 78 (lf 17825925) (nd 18 (nd 77 (lf 13156352) (nd 24 (nd 38 (lf 18874757) (lf 10882821)) (lf 16830208))) (lf 16826752))) (nd 3 (lf 18744064) (nd 36 (nd 38 (nd 24 (lf 18875136) (lf 10882816)) (lf 16830213)) (lf 16826757)))) (nd 18 (nd 36 (nd 38 (nd 24 (lf 13156352) (nd 79 (lf 4768520) (nd 161 (lf 17223424) (lf 18796288)))) (nd 74 (lf 17223429) (nd 106 (lf 18796293) (lf 8788069)))) (nd 173 (lf 18792837) (lf 17219973))) (nd 92 (lf 18792832) (lf 17219968))))))))) (nd 163 (nd 133 (nd 152 (nd 176 (nd 12 (nd 13 (nd 56 (nd 173 (nd 46 (lf 3694593) (lf 17834372)) (nd 1 (lf 10013799) (lf 9964647))) (nd 10 (nd 14 (lf 2843012) (lf 3694593)) (lf 10903940))) (nd 125 (nd 7 (lf 18792836) (lf 6341634)) (lf 17219972))) (nd 128 (nd 157 (nd 43 (nd 82 (nd 39 (lf 27471623) (nd 38 (lf 27668231) (lf 27275015))) (nd 38 (lf 22943744) (lf 22550528))) (nd 139 (lf 17023364) (lf 22747136))) (nd 24 (nd 43 (nd 149 (lf 8519576) (lf 27312903)) (nd 37 (lf 27706119) (lf 27509511))) (nd 88 (nd 30 (lf 29808640) (nd 35 (lf 29415424) (lf 29612032))) (nd 27 (nd 35 (lf 22937703) (lf 22741095)) (lf 22544487))))) (nd 4 (nd 28 (nd 0 (nd 29 (nd 5 (lf 27515657) (lf 27671305)) (nd 33 (lf 27482112) (lf 27490304))) (nd 85 (nd 3 (lf 27474697) (lf 27278089)) (lf 29563657))) (nd 148 (nd 44 (nd 27 (lf 27686912) (lf 27293696)) (lf 8906648)) (nd 32 (lf 27285504) (lf 27678720)))) (nd 71 (nd 75 (nd 1 (lf 29760265) (lf 29367049)) (nd 2 (lf 27712265) (lf 27319049))) (nd 84 (nd 8 (lf 6841088) (lf 6841184)) (nd 38 (lf 29803271) (nd 41 (lf 29606663) (lf 29410055)))))))) (nd 161 (nd 126 (nd 23 (nd 100 (nd 67 (nd 36 (lf 27671303) (nd 41 (lf 27474695) (lf 27278087))) (nd 37 (lf 29754119) (nd 39 (lf 29557511) (lf 29360903)))) (nd 172 (nd 162 (lf 17456376) (lf 8578968)) (nd 89 (lf 15400984) (nd 19 (lf 8514456) (lf 15329528))))) (nd 30 (nd 175 (nd 124 (lf 27663104) (nd 32 (lf 22943767) (lf 22747159))) (nd 39 (lf 22740999) (lf 12635192))) (nd 149 (nd 174 (nd 18 (lf 17457144) (lf 12594232)) (lf 22550551)) (nd 29 (lf 27269888) (lf 27466496))))) (nd 3 (nd 33 (nd 7 (nd 35 (nd 94 (lf 29415561) (lf 27490441)) (nd 130 (lf 29784832) (lf 27720448))) (nd 76 (lf 27482249) (nd 5 (lf 29612169) (lf 29808777)))) (nd 27 (nd 34 (lf 27523840) (lf 27327232)) (nd 87 (nd 34 (lf 29588224) (lf 29391616)) (lf 8513432)))) (nd 93 (nd 11 (nd 8 (lf 9967719) (lf 10016871)) (nd 8 (lf 6840320) (lf 6840416))) (nd 82 (nd 0 (lf 27687049) (lf 27293833)) (nd 1 (lf 27678857) (lf 27285641)))))) (nd 26 (nd 21 (nd 168 (nd 171 (nd 44 (lf 27271943) (nd 41 (lf 27468551) (lf 27665159))) (nd 57 (lf 27796231) (nd 79 (lf 27992839) (lf 28189447)))) (nd 148 (nd 81 (lf 27673346) (lf 27288322)) (nd 93 (lf 27287554) (lf 27672578)))) (nd 97 (nd 83 (nd 5 (lf 6323207) (nd 6 (lf 6294535) (lf 6347783))) (nd 126 (lf 29409282) (lf 29410050))) (nd 100 (nd 171 (nd 19 (lf 27475970) (lf 27279362)) (lf 28000258)) (nd 80 (nd 20 (lf 27280130) (lf 27476738)) (lf 28001026))))) (nd 88 (nd 83 (nd 7 (lf 6298679) (nd 5 (lf 6323255) (lf 6347831))) (nd 144 (nd 53 (nd 25 (lf 29606658) (lf 29803266)) (lf 30130946)) (nd 45 (nd 24 (lf 29802498) (lf 29605890)) (lf 30130178)))) (nd 155 (nd 119 (nd 18 (lf 27681538) (lf 27484930)) (nd 24 (lf 27680770) (lf 27484162))) (nd 4 (nd 27 (nd 29 (lf 23461895) (lf 23265287)) (lf 23068679)) (nd 119 (lf 28009218) (lf 28008450)))))))) (nd 134 (nd 3 (nd 93 (nd 170 (nd 91 (nd 168 (nd 60 (lf 24705417) (lf 29933705)) (lf 27837193)) (nd 176 (nd 62 (nd 168 (nd 64 (lf 10486151) (lf 17981335)) (lf 17981335)) (lf 17975287)) (lf 17975287))) (nd 81 (lf 17981431) (nd 158 (lf 27836425) (lf 26738787)))) (nd 166 (lf 17826183) (lf 17915799))) (nd 167 (nd 59 (nd 171 (lf 20971523) (nd 164 (nd 73 (lf 24010755) (lf 24672649)) (lf 12083376))) (nd 165 (nd 9 (lf 6342018) (lf 6317442)) (nd 80 (lf 29885193) (lf 27796233)))) (nd 174 (nd 83 (nd 53 (lf 27795465) (nd 70 (lf 25166208) (lf 26738739))) (nd 158 (lf 29884425) (nd 170 (lf 25166080) (lf 26738691)))) (nd 76 (nd 25 (lf 6298679) (nd 47 (lf 6294535) (lf 27803785))) (nd 11 (lf 12084016) (lf 27811977)))))) (nd 29 (nd 117 (nd 158 (nd 137 (lf 27287552) (nd 165 (lf 27795456) (lf 27811840))) (nd 101 (lf 29385472) (nd 156 (lf 26222595) (lf 29909760)))) (nd 47 (lf 3149193) (lf 24672640))) (nd 27 (nd 83 (nd 155 (nd 179 (nd 99 (lf 27680768) (lf 28205056)) (lf 28188672)) (nd 144 (lf 29778688) (nd 70 (lf 30302976) (lf 26228739)))) (lf 3149289)) (nd 54 (lf 3149241) (nd 51 (lf 27484160) (lf 29582080))))))) (nd 74 (nd 92 (nd 55 (nd 40 (nd 179 (nd 41 (nd 0 (nd 4 (lf 25690928) (lf 25690976)) (nd 158 (lf 12594231) (lf 25690880))) (lf 10903943)) (nd 146 (nd 5 (nd 166 (lf 24118116) (lf 28229632)) (nd 22 (nd 7 (lf 6844160) (lf 6844256)) (nd 7 (lf 9965031) (lf 10014183)))) (nd 164 (nd 87 (nd 36 (lf 22741000) (lf 12594231)) (lf 30277632)) (nd 2 (nd 132 (lf 26220547) (nd 4 (lf 22216712) (lf 22413320))) (lf 22020104))))) (nd 44 (nd 85 (nd 12 (nd 20 (lf 17457143) (lf 12011415)) (nd 170 (lf 12017559) (nd 21 (lf 17456375) (lf 12635191)))) (lf 10879367)) (nd 6 (lf 18792839) (lf 22747155)))) (nd 80 (nd 7 (nd 96 (nd 167 (nd 3 (lf 22550536) (lf 22943752)) (nd 51 (nd 22 (lf 6299063) (lf 6299015)) (nd 1 (lf 22938728) (lf 22545512)))) (nd 60 (nd 141 (lf 28196864) (nd 108 (lf 29360905) (lf 30326784))) (nd 131 (lf 28238592) (nd 79 (lf 27279497) (lf 28181248))))) (nd 161 (nd 61 (nd 1 (nd 8 (lf 29754121) (lf 22747144)) (lf 29557513)) (nd 0 (nd 108 (lf 27672713) (lf 22742120)) (nd 21 (lf 22747235) (lf 27476105)))) (nd 20 (nd 1 (lf 6348167) (lf 6323591)) (nd 151 (lf 6347831) (nd 5 (lf 6323639) (lf 6348215)))))) (nd 159 (nd 5 (nd 31 (nd 8 (nd 152 (lf 27517696) (lf 27460352)) (nd 6 (lf 29606025) (lf 27484297))) (nd 129 (nd 30 (lf 27656960) (lf 27263744)) (nd 32 (lf 27321088) (lf 27714304)))) (nd 2 (nd 7 (lf 27680905) (nd 3 (lf 29802633) (nd 22 (lf 6843488) (lf 10017255)))) (nd 1 (lf 27287689) (nd 22 (lf 6843392) (nd 10 (lf 9968103) (lf 29409417)))))) (nd 32 (nd 2 (nd 5 (nd 132 (lf 27279360) (lf 29409280)) (nd 84 (lf 27665161) (lf 27706121))) (nd 89 (nd 3 (lf 27468553) (lf 27271945)) (nd 8 (lf 27312905) (lf 27509513)))) (nd 138 (nd 30 (lf 27672576) (lf 27475968)) (nd 34 (lf 29605888) (lf 29802496))))))) (nd 6 (nd 80 (nd 36 (nd 41 (nd 33 (nd 27 (nd 2 (nd 37 (nd 38 (nd 28 (nd 35 (nd 31 (nd 30 (nd 44 (nd 34 (nd 32 (nd 29 (nd 39 (nd 40 (nd 43 (nd 42 (lf 13632259) (lf 2294535)) (lf 2294535)) (lf 2491143)) (lf 2491143)) (lf 3348480)) (lf 3397632)) (lf 3569664)) (lf 2843399)) (lf 3201024)) (lf 3594240)) (lf 3373056)) (lf 3545088)) (lf 2646791)) (lf 2097927)) (lf 14024707)) (lf 3151872)) (lf 3176448)) (lf 3040007)) (lf 2097927)) (nd 83 (nd 89 (lf 13631507) (lf 21495811)) (nd 36 (lf 20971523) (nd 84 (lf 12591111) (lf 19399683))))) (nd 147 (nd 158 (nd 177 (lf 30277641) (lf 30278409)) (nd 179 (nd 171 (lf 25166176) (lf 28197001)) (lf 26739459))) (lf 13632259)))) (nd 97 (nd 88 (nd 43 (nd 42 (nd 164 (nd 45 (nd 1 (lf 2106375) (lf 2111495)) (nd 16 (lf 7343104) (lf 7346176))) (nd 13 (nd 47 (lf 7392256) (lf 5267584)) (nd 171 (lf 7395328) (lf 5268224)))) (lf 10707335)) (nd 42 (lf 18596231) (nd 10 (nd 98 (lf 25690933) (lf 22216707)) (lf 10682759)))) (nd 118 (nd 167 (nd 159 (nd 13 (lf 6317058) (lf 6341634)) (nd 13 (lf 12083328) (lf 28230409))) (nd 71 (nd 9 (lf 12083968) (lf 30326921)) (nd 68 (lf 26739555) (lf 28229641)))) (nd 6 (lf 13631587) (nd 5 (lf 13631715) (lf 13632355))))) (nd 149 (nd 140 (nd 35 (nd 114 (nd 61 (nd 67 (lf 24705408) (lf 29933568)) (nd 155 (lf 27836416) (nd 162 (lf 24117348) (lf 27845376)))) (lf 3149577)) (nd 31 (lf 3149625) (lf 3149673))) (nd 0 (nd 61 (nd 65 (lf 18016151) (nd 3 (lf 16826759) (lf 28189449))) (nd 173 (nd 119 (lf 28188681) (lf 18016247)) (nd 179 (nd 55 (lf 25166304) (lf 28205193)) (lf 26739507)))) (nd 43 (nd 4 (lf 16826759) (nd 13 (lf 6317058) (lf 6341634))) (nd 41 (lf 17023367) (lf 17219975))))) (nd 141 (nd 129 (nd 32 (nd 105 (nd 55 (nd 93 (nd 58 (lf 26214403) (lf 29884416)) (lf 24010756)) (nd 177 (lf 27788032) (lf 27803648))) (lf 3148809)) (nd 31 (lf 3148857) (lf 3148905))) (nd 59 (lf 17834375) (nd 67 (nd 53 (lf 10493959) (lf 17967095)) (lf 17973143)))) (nd 89 (nd 7 (lf 13631507) (lf 13632275)) (nd 72 (nd 41 (nd 3 (lf 10486151) (lf 20971523)) (nd 36 (lf 18399623) (lf 10493959))) (nd 6 (nd 2 (nd 7 (lf 20971523) (lf 20972387)) (nd 5 (nd 0 (lf 20971747) (lf 21495811)) (nd 3 (lf 20971619) (lf 20971539)))) (nd 3 (nd 2 (lf 20971651) (lf 20971667)) (nd 7 (lf 20972307) (lf 20972291))))))))))) (nd 5 (nd 145 (nd 28 (nd 147 (nd 30 (nd 127 (nd 171 (lf 22747143) (nd 175 (nd 53 (lf 22742119) (lf 22219783)) (lf 22747239))) (nd 171 (lf 28196873) (nd 175 (nd 178 (lf 24118019) (lf 28181257)) (lf 28197641)))) (nd 165 (nd 162 (nd 131 (nd 37 (lf 22550535) (lf 12594184)) (lf 29557504)) (nd 99 (lf 27476096) (nd 168 (lf 22023175) (lf 22545511)))) (nd 32 (nd 37 (lf 22550631) (lf 12591112)) (nd 130 (nd 118 (lf 6317496) (lf 6317112)) (nd 127 (lf 27476736) (lf 8912792)))))) (nd 80 (nd 176 (nd 1 (nd 177 (nd 107 (lf 27491072) (lf 27673353)) (nd 6 (lf 27490432) (lf 27656969))) (nd 160 (nd 3 (lf 27476745) (lf 27280137)) (nd 7 (lf 27263753) (lf 27460361)))) (nd 88 (nd 45 (nd 108 (lf 6317447) (lf 27474688)) (nd 20 (lf 6317447) (lf 6317495))) (nd 4 (lf 27475977) (nd 1 (lf 27672585) (lf 27279369))))) (nd 143 (nd 56 (nd 61 (nd 32 (lf 29409408) (nd 31 (lf 29606016) (lf 29802624))) (nd 35 (lf 27312896) (nd 34 (lf 27509504) (lf 27706112)))) (nd 31 (lf 29606656) (nd 33 (lf 29803264) (lf 29410048)))) (nd 97 (nd 162 (lf 29605897) (nd 174 (lf 27517705) (lf 29606665))) (nd 35 (nd 53 (nd 54 (lf 29582089) (lf 27484937)) (lf 27484169)) (nd 54 (nd 157 (lf 27484288) (lf 27468544)) (lf 27484928))))))) (nd 27 (nd 89 (nd 174 (nd 166 (nd 114 (lf 27687040) (nd 173 (lf 28205184) (lf 26764084))) (nd 114 (lf 27671296) (lf 28189440))) (nd 141 (nd 147 (lf 6341688) (lf 27687680)) (lf 28205824))) (nd 117 (nd 151 (nd 67 (nd 153 (lf 27665152) (lf 27681536)) (nd 138 (lf 6342072) (lf 27680896))) (nd 167 (nd 68 (lf 27673344) (lf 27672704)) (lf 29754112))) (nd 171 (nd 39 (lf 22943751) (lf 12635144)) (nd 174 (nd 168 (lf 22416391) (lf 22938727)) (nd 40 (lf 22943847) (lf 12632072)))))) (nd 128 (nd 149 (nd 105 (nd 29 (lf 6292536) (lf 22747238)) (nd 10 (nd 171 (lf 17456280) (lf 17450136)) (nd 13 (lf 6292920) (nd 167 (lf 17450904) (lf 17457048))))) (nd 33 (nd 176 (nd 63 (lf 27280128) (lf 27279488)) (lf 29360896)) (nd 52 (nd 166 (lf 27287680) (lf 27288320)) (lf 27271936)))) (nd 162 (nd 115 (nd 172 (nd 13 (lf 15597592) (nd 54 (lf 15722744) (lf 8907672))) (lf 27278080)) (lf 27796224)) (nd 165 (nd 115 (lf 27293824) (nd 173 (lf 27811968) (lf 26763316))) (nd 102 (lf 27812608) (lf 27294464))))))) (nd 31 (nd 0 (nd 115 (nd 30 (nd 90 (nd 52 (nd 63 (lf 29612809) (lf 27523849)) (lf 29612041)) (nd 167 (nd 166 (lf 27663113) (lf 27679497)) (lf 27678729))) (nd 35 (nd 56 (nd 60 (lf 27482240) (lf 29563648)) (lf 27482880)) (nd 54 (nd 160 (lf 27515648) (lf 29612160)) (lf 29612800)))) (nd 126 (nd 171 (lf 17975287) (lf 17826183)) (nd 162 (lf 22741096) (nd 174 (nd 51 (lf 22747160) (lf 23265336)) (lf 22747240))))) (nd 4 (nd 106 (nd 164 (nd 77 (nd 177 (lf 27482889) (lf 27466505)) (nd 66 (lf 27491081) (lf 29588233))) (nd 94 (nd 22 (lf 6317111) (lf 6317063)) (nd 82 (lf 27490313) (lf 27482121)))) (nd 171 (nd 36 (lf 22544488) (nd 155 (lf 12591159) (lf 6160391))) (nd 165 (nd 173 (lf 22550552) (lf 23068728)) (nd 36 (lf 22550632) (lf 12591111))))) (nd 174 (nd 47 (nd 125 (lf 27285513) (lf 27803657)) (nd 99 (nd 173 (lf 27788041) (lf 24117251)) (lf 27269897))) (nd 97 (nd 60 (nd 54 (lf 12058629) (lf 27286281)) (nd 82 (lf 12083205) (lf 12107781))) (lf 27804425))))) (nd 138 (nd 171 (nd 78 (nd 93 (lf 29885184) (nd 29 (lf 29367040) (lf 29760256))) (nd 106 (nd 18 (lf 8579992) (nd 97 (lf 15395064) (lf 15204376))) (lf 30278400))) (nd 30 (nd 166 (nd 168 (lf 26764036) (nd 106 (lf 27678848) (lf 28196992))) (nd 86 (lf 28197632) (lf 27679488))) (nd 84 (nd 166 (nd 53 (lf 27803776) (lf 26763268)) (lf 27804416)) (nd 32 (nd 57 (lf 27285632) (lf 27286272)) (nd 68 (lf 28205825) (lf 28009217)))))) (nd 32 (nd 174 (nd 166 (nd 169 (lf 26763364) (nd 99 (lf 29933696) (lf 29415552))) (nd 117 (lf 27837184) (lf 27319040))) (nd 106 (nd 62 (lf 29416192) (nd 80 (lf 12059400) (lf 12058632))) (lf 29934336))) (nd 165 (nd 166 (nd 96 (nd 69 (lf 29808768) (lf 30130945)) (nd 53 (lf 30326912) (lf 26764132))) (nd 88 (lf 27712256) (lf 28230400))) (nd 114 (nd 101 (nd 10 (lf 30327553) (nd 82 (lf 12107784) (lf 12108552))) (nd 156 (lf 8585112) (lf 29809408))) (lf 30327552))))))) (nd 74 (nd 25 (nd 60 (nd 52 (nd 177 (lf 14025192) (nd 142 (nd 99 (lf 28196866) (lf 28197634)) (lf 14025144))) (nd 9 (nd 14 (nd 173 (lf 29784836) (nd 126 (lf 29778692) (lf 30302980))) (nd 13 (nd 144 (lf 27523844) (lf 27517700)) (nd 128 (lf 27714308) (nd 121 (lf 27720452) (lf 28238596))))) (nd 122 (nd 47 (lf 29588228) (nd 19 (lf 27479810) (nd 20 (lf 27283202) (lf 27676418)))) (nd 80 (nd 169 (lf 12107909) (lf 29582084)) (nd 20 (lf 27282434) (nd 19 (lf 27479042) (lf 27675650))))))) (nd 50 (nd 158 (nd 176 (nd 9 (nd 178 (lf 27687684) (nd 142 (lf 28205828) (lf 27681540))) (nd 144 (lf 27491076) (lf 27484932))) (nd 12 (lf 29803268) (nd 177 (lf 29606660) (lf 30278407)))) (nd 146 (nd 12 (lf 29809412) (nd 134 (lf 30327559) (lf 29612804))) (nd 171 (nd 94 (lf 14162018) (lf 28230407)) (nd 38 (lf 12108549) (lf 30327556))))) (nd 24 (nd 128 (nd 21 (nd 63 (lf 27678722) (lf 22741093)) (nd 98 (nd 22 (lf 27482114) (lf 27285506)) (lf 27803650))) (nd 21 (nd 66 (lf 27679490) (lf 22747237)) (nd 71 (nd 23 (lf 27286274) (lf 27482882)) (lf 27804418)))) (nd 7 (nd 106 (lf 6292535) (lf 6292919)) (nd 169 (nd 125 (lf 6341687) (lf 6342071)) (nd 101 (lf 22544485) (lf 22550629))))))) (nd 1 (nd 75 (nd 26 (nd 153 (nd 137 (lf 6348167) (lf 6347783)) (nd 123 (lf 6341639) (lf 6342023))) (nd 162 (nd 37 (lf 22937704) (lf 12632119)) (nd 174 (nd 51 (lf 22943768) (lf 23461944)) (nd 40 (lf 22943848) (lf 12632071))))) (nd 53 (nd 6 (nd 85 (nd 177 (lf 27288329) (lf 29385481)) (nd 156 (lf 27714313) (lf 29803273))) (nd 59 (nd 21 (lf 6868832) (nd 12 (lf 10014087) (lf 29778697))) (nd 7 (lf 27681545) (nd 18 (lf 6868064) (lf 10017159))))) (nd 95 (nd 6 (lf 29802505) (nd 26 (lf 6818912) (lf 10017207))) (nd 4 (nd 8 (lf 27287561) (lf 27680777)) (nd 14 (lf 10014135) (lf 6819680)))))) (nd 60 (nd 153 (nd 26 (nd 160 (lf 12017575) (nd 101 (lf 6819584) (lf 12011431))) (nd 9 (nd 56 (lf 17450999) (lf 17450903)) (nd 14 (lf 9964983) (nd 164 (lf 17450135) (lf 17450231))))) (nd 159 (nd 9 (nd 84 (lf 12017655) (lf 9968007)) (nd 21 (lf 6867968) (lf 29410057))) (nd 146 (nd 85 (nd 21 (lf 6868736) (lf 9964935)) (lf 27321097)) (lf 12011511)))) (nd 78 (nd 177 (nd 128 (lf 6292871) (nd 131 (lf 6293255) (lf 6292487))) (nd 8 (nd 45 (lf 6294535) (lf 6297607)) (nd 148 (lf 22943845) (lf 22937701)))) (nd 3 (lf 29409289) (nd 20 (lf 6818816) (lf 9968055))))))) (nd 143 (nd 90 (nd 89 (nd 51 (nd 8 (nd 0 (nd 160 (lf 29416201) (lf 27327241)) (nd 9 (lf 9967623) (lf 6864896))) (nd 6 (nd 64 (lf 29809417) (lf 27720457)) (nd 38 (nd 9 (lf 10016775) (lf 6864992)) (lf 12058757)))) (nd 6 (nd 1 (lf 29808649) (nd 3 (lf 29415433) (nd 9 (lf 9967671) (lf 6815744)))) (nd 23 (nd 47 (lf 6815840) (nd 148 (lf 29416194) (lf 29415426))) (nd 128 (nd 21 (lf 29808642) (lf 29612034)) (nd 46 (lf 10016823) (nd 22 (lf 29612802) (lf 29809410))))))) (nd 38 (nd 86 (nd 126 (nd 24 (lf 27686914) (nd 19 (lf 27490306) (lf 27293698))) (nd 24 (lf 27687682) (nd 25 (lf 27491074) (lf 27294466)))) (nd 39 (nd 44 (lf 29563655) (nd 102 (lf 27712263) (lf 29809415))) (nd 94 (nd 37 (lf 29760263) (lf 29367047)) (lf 29885191)))) (nd 46 (nd 15 (nd 159 (lf 26739560) (nd 68 (lf 25166309) (lf 26739512))) (nd 81 (lf 14161922) (nd 18 (lf 12083973) (lf 14161970)))) (nd 75 (nd 159 (lf 12059397) (nd 103 (lf 27837191) (lf 29934343))) (nd 147 (nd 43 (lf 29416199) (lf 29612807)) (nd 43 (lf 27319047) (lf 27515655))))))) (nd 19 (nd 101 (nd 79 (nd 64 (nd 174 (nd 54 (lf 29933570) (lf 28033799)) (lf 30081799)) (nd 21 (nd 58 (lf 29805570) (lf 30326786)) (nd 25 (lf 29608962) (lf 29412354)))) (nd 154 (nd 36 (lf 29757191) (nd 42 (lf 29363975) (lf 29560583))) (nd 38 (nd 178 (lf 27709191) (lf 27487234)) (nd 44 (lf 27315975) (lf 27512583))))) (nd 171 (nd 64 (nd 25 (lf 30130951) (lf 29934338)) (nd 44 (lf 29413127) (nd 40 (lf 29609735) (lf 29806343)))) (nd 22 (nd 146 (nd 97 (lf 29609730) (lf 27488002)) (lf 12083333)) (nd 70 (lf 30327554) (nd 23 (lf 29413122) (lf 29806338)))))) (nd 168 (nd 69 (nd 8 (nd 51 (lf 27294473) (lf 27293705)) (nd 52 (lf 27687689) (lf 27686921))) (nd 82 (nd 20 (nd 1 (lf 6816608) (lf 6816512)) (nd 8 (lf 9964599) (lf 10013751))) (nd 119 (lf 27812610) (lf 27811842)))) (nd 94 (nd 131 (nd 161 (lf 28205058) (nd 18 (lf 27683842) (lf 27290626))) (nd 18 (nd 179 (lf 28205826) (lf 27684610)) (lf 27291394))) (nd 8 (nd 12 (lf 9964551) (nd 24 (lf 6865664) (lf 29391625))) (nd 7 (lf 29784841) (nd 18 (lf 6865760) (lf 10013703)))))))) (nd 126 (nd 162 (nd 3 (lf 29933577) (nd 7 (lf 27811849) (nd 12 (lf 12058800) (lf 12059440)))) (nd 175 (nd 4 (nd 51 (lf 29909769) (lf 26238980)) (nd 24 (lf 12107952) (nd 51 (lf 27845385) (lf 26271748)))) (nd 3 (lf 29934345) (nd 24 (lf 12108592) (lf 27812617))))) (nd 81 (nd 171 (nd 152 (lf 28205065) (nd 164 (nd 12 (lf 7370752) (lf 7367680)) (nd 170 (lf 5243648) (lf 5243008)))) (nd 175 (nd 146 (nd 177 (lf 26245124) (lf 30302985)) (lf 5292160)) (nd 2 (lf 28205833) (lf 5292800)))) (nd 171 (nd 0 (lf 30326793) (nd 10 (lf 12059392) (lf 12058752))) (nd 166 (nd 178 (nd 159 (lf 26277892) (lf 12107904)) (lf 28238601)) (nd 0 (lf 30327561) (lf 12108544)))))))))))

-- ===== targets (stored with rejected maxterm bits) =====
def targets : List Nat := [0x6db6db600000000000007ffffffbfdfefe0024807ffff, 0xffffffe00000000000007e3f1f8ffffffe00008fdfedb, 0x1fffffffffffffffffe00000000000000fffedf, 0xffffffe00000000000007e3f1f8ffffffe00001dbffff, 0xffffffe00000000000007e3f1f8ffffffe000486fffff, 0xffffffe00000000000007e3f1f8ffffffe00008dbffff, 0x1fffffffffffffffffe0000000000000ffffe1b, 0xffffffe00000000000007ffffffffffffe0003803ffff, 0xffffffe00000000000007ffffffffffffe000480fffff, 0xd86c361fffffffffffff80001ff0000000000036c7fff, 0xd86c361fffffffffffff803fe00007e000000036c7fff, 0xffffffe3f1f8001209000000000ffffffe0003927fe3f, 0xdfeff7fffff8ffffff1f8000000fc7fffe000036ffe3f, 0x1b0d86c3f1f8fc7e3f1f8007e3f007e3f0000036ffe3f, 0x80403fffffffffffff80001ff000000e00000fdb7ff, 0x1f8fc7e00fc7e001f8fc003f1f8007fffe00000fdb7ff, 0xffffffe00ffffc01b0d86c361b0ffffffe006d8fc01ff, 0xd86c001b6db003ffff007fffe00fc7e0000324b6c7e1b, 0x1f8fc7ff8fc003f1f800003f1f8007fffe00000fffe3f, 0x1f8fc7e00fc7e001f8fc003f1f8007fffe000036db7ff, 0xffffffe001f8fc00361b6db6db6ffffffe000d80fffff, 0xffffffffffff1f61b0c06c361b0ffffffe006d8feda3f, 0xffffffff8fc001b0d80036db6dbffffffe001fb6db63f, 0xd86c36000ffffc01ffffffffffffc7e000000036c7fff, 0xffffffe00168b400361b7dfeff7ffffffe0001927ffff, 0xffffffe00000000000007ffffffffffffe003b003ffff, 0x3ffff007fffffffffffffffff80000ff, 0xffffdb7f8fc003f1f8007e3f1f8ffffffe03259fdb63f, 0xfffffffffff80361b0006c361b0ffffffe006d8fdbe3f, 0xffffdfff8fc7e3f1f8d87e3f1f81fffffe006f8fdb67f, 0x1f8fc7ff8fc7e3f1f8fc003f1f8007fffe000486fffff, 0x1f8fc7ffffffe36dfefc003ffff007fffe001f80fffff, 0xff7fbfc00fc7e001f8fc7ffffffffffffe000d813ffff, 0xffffffe001b0fc00361f7e3f1f8ffffffe001fb6c7edb, 0xfbfdfee001b0d800361b7ffffffffffffe001f827ffff, 0xffffffe00000000000006db6db6ffffffe000d8b7ffff, 0xffffffe3f1f8007e3f0077fffffffffffe001f807ffff, 0x3f1f8ffffffffffffffffffff8000209, 0x3ffc7fc7fffffffffffffffff8000209, 0x3ffffffffffffffffffffffff8000007, 0x3ffffffffffffffffffffffff800001b, 0x3ffffffffffffffffffffffff8000049, 0x1c0e070381c0e07ffffffffffffe0700003ffff, 0x1f8fc003f1f8007ffffffffffffe0700003ffff, 0x1ff00003fe00007ffffffffffffe0700003ffff, 0x2480000493ffff007ffffb6fffff6dffff800001b, 0x3fe00007ffffff007fffe00ffffc01ffff800001b, 0x8040201b6db6dbfdfeff7fbfdfee000000000dffffe00, 0x8241209ffff803ffff007ffffc0e00038000007fffe1b, 0x9048241ffffffffffffff038000e07000000007fffe07, 0x92492492492493f1f8fc7e3f1f8fc7e3f1ffff86c0000, 0x92492492492493ffff007fffe00ffffc01ffff800001b, 0xb45a2d1b0d86c3f1f8fc7e3f1f8e3f1c00000dffffe00, 0xb45a2d1b6db6db6db6db6db6db6e3f1c00000dffffe00, 0xd86c361b0d86c3f1f8fc7e3f1f8fc7e000000dbfffe00, 0xd86c361b0d86c3f1f8fc7e3f1f8fc7e000000dffdfe00, 0xd86c361b0d86c3f1f8fc7e3f1f8fc7e000000dffffe00, 0xd86c361b6db6db6db6db6db6db6fc7e000000dffffe00]
def targetPack : Nat := packList targets 180
def targetT (m : Nat) : Nat := Nat.xor (fld targetPack 180 m) MV

-- ===== hits =====
def hitF (sop rop : Bool) (i D c pv s d k : Nat) : F := fun z => bop sop (RowF i D c pv rop z) (imgF s d k z)

theorem tv_hitF (sop rop : Bool) (i D c pv s d k : Nat) :
    tv (hitF sop rop i D c pv s d k) = gate sop (tv (RowF i D c pv rop)) (tv (imgF s d k)) := by
  show tv (fun z => bop sop (RowF i D c pv rop z) (imgF s d k z)) = _
  rw [tv_bop]

theorem tv_RowF (i D c pv : Nat) (rop : Bool) :
    tv (RowF i D c pv rop) = gate rop (evalT2 (tplAt i) (leafOf (tplAt i))) (evalT2 (tplAt c) (placeL (tplAt c) D pv)) := by
  unfold RowF; rw [tv_bop, TF, tv_F2, tv_F2]

theorem evalT2_congr (code : Nat) (lf lf' : Nat → Nat) (h : ∀ t, t < 4 → lf t = lf' t) : evalT2 code lf = evalT2 code lf' := by
  unfold evalT2; rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)]

theorem evalHv_congr (code : Nat) (c c' : Nat → Nat) (h : ∀ j, j < 8 → c j = c' j) : evalHv code c = evalHv code c' := by
  unfold evalHv
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num)]

def leaf8 (lv j : Nat) : Nat := Nat.land (Nat.shiftRight lv (Nat.mul 4 j)) 15

def clsOK (sop rop : Bool) (i D c pv s lv o : Nat) : Bool :=
  Nat.blt (Nat.shiftRight (treeE (Nat.xor o MV)) 19) 58 &&
  domB (gate sop (gate rop (evalT2 (tplAt i) (fun t => rlab (treeE (Nat.xor o MV)) (leafOf (tplAt i) t)))
      (evalT2 (tplAt c) (fun t => rlab (treeE (Nat.xor o MV)) (placeL (tplAt c) D pv t))))
    (evalHv (hCode s) (fun j => varAt (rlab (treeE (Nat.xor o MV)) (leaf8 lv j)))))
    (targetT (Nat.shiftRight (treeE (Nat.xor o MV)) 19))

theorem placeL_lt (cc D pv t : Nat) (hc : leafOf cc t < 15) (hp : pvF pv (dmapC D (leafOf cc t % 5)) < 6) :
    placeL cc D pv t < 15 := by
  have hw := dmapC_lt D (leafOf cc t % 5)
  have := permAt_lt _ (leafOf cc t / 5) hp (by omega)
  show dmapC D (leafOf cc t % 5) + 5 * permAt (pvF pv (dmapC D (leafOf cc t % 5))) (leafOf cc t / 5) < 15
  omega

theorem imgLf_lt (s d k j : Nat) (hs : s < 41) (hj : j < 8) : imgLf s d k j < 15 := by
  rw [imgLf_eq s d k j hs hj]
  exact lam_lt _ _ _ (hLeaf_lt s j hs hj) (cvec_lt s k _ hs (Nat.mod_lt _ (by norm_num)))

theorem clsOK_spec (sop rop : Bool) (i D c pv s d k lv : Nat) (hi : i < 41) (hc : c < 41) (hs : s < 41)
    (hpv : ∀ w, w < 5 → pvF pv w < 6) (hlv : ∀ j, j < 8 → leaf8 lv j = imgLf s d k j)
    (h : clsOK sop rop i D c pv s lv (tv (hitF sop rop i D c pv s d k)) = true) :
    ∃ w m, m < 58 ∧ dom (permW w (tv (hitF sop rop i D c pv s d k))) (targetT m) := by
  generalize ho : tv (hitF sop rop i D c pv s d k) = o at h
  simp only [clsOK, Bool.and_eq_true, Nat.blt_eq] at h
  generalize hlab : treeE (Nat.xor o MV) = lab at h
  obtain ⟨w, hw⟩ := rlab_real lab
  refine ⟨w, lab >>> 19, h.1, ?_⟩
  have hd := domB_spec _ _ h.2
  have hlI : ∀ t, t < 4 → leafOf (tplAt i) t < 15 := fun t ht => tplLeaf_lt i t hi ht
  have hlC : ∀ t, t < 4 → placeL (tplAt c) D pv t < 15 := fun t ht =>
    placeL_lt _ _ _ _ (tplLeaf_lt c t hc ht) (hpv _ (dmapC_lt _ _))
  have hlH : ∀ j, j < 8 → imgLf s d k j < 15 := fun j hj => imgLf_lt s d k j hs hj
  have c1 : evalT2 (tplAt i) (fun t => rlab lab (leafOf (tplAt i) t)) = evalT2 (tplAt i) (fun t => sig w (leafOf (tplAt i) t)) :=
    evalT2_congr _ _ _ (fun t ht => (hw _ (hlI t ht)).symm)
  have c2 : evalT2 (tplAt c) (fun t => rlab lab (placeL (tplAt c) D pv t)) =
      evalT2 (tplAt c) (fun t => sig w (placeL (tplAt c) D pv t)) :=
    evalT2_congr _ _ _ (fun t ht => (hw _ (hlC t ht)).symm)
  have c3 : evalHv (hCode s) (fun j => varAt (rlab lab (leaf8 lv j))) = evalHv (hCode s) (fun j => varAt (sig w (imgLf s d k j))) :=
    evalHv_congr _ _ _ (fun j hj => by rw [hlv j hj, hw _ (hlH j hj)])
  have e : permW w o = gate sop (gate rop (evalT2 (tplAt i) (fun t => sig w (leafOf (tplAt i) t)))
      (evalT2 (tplAt c) (fun t => sig w (placeL (tplAt c) D pv t))))
      (evalHv (hCode s) (fun j => varAt (sig w (imgLf s d k j)))) := by
    rw [← ho, ← tv_actW, actW_sig]
    have ea : act (fun x => fv (sig w x.val)) (hitF sop rop i D c pv s d k) =
        fun z => bop sop (bop rop (F2 (tplAt i) (fun t => sig w (leafOf (tplAt i) t)) z)
          (F2 (tplAt c) (fun t => sig w (placeL (tplAt c) D pv t)) z)) (FH (hCode s) (fun j => sig w (imgLf s d k j)) z) := by
      rw [← act_F2 _ _ _ hlI, ← act_F2 _ _ _ hlC, ← act_FH _ _ _ hlH]; rfl
    rw [ea, tv_bop, tv_bop, tv_F2, tv_F2, tv_FH]
  rw [c1, c2, c3, ← e] at hd
  exact hd

-- ===== exact bits of accumulated single bits =====
theorem accRec_bits (P : Nat → Bool) (n q : Nat) :
    (accRec P (fun p => Nat.shiftLeft 1 p) n).testBit q = (decide (q < n) && P q) := by
  induction n with
  | zero => simp [accRec]
  | succ n ih =>
    have e : accRec P (fun p => Nat.shiftLeft 1 p) (n + 1) =
        cond (P n) (accRec P (fun p => Nat.shiftLeft 1 p) n ||| Nat.shiftLeft 1 n) (accRec P (fun p => Nat.shiftLeft 1 p) n) := rfl
    rw [e]
    have hb : (Nat.shiftLeft 1 n).testBit q = decide (q = n) := by
      show (1 <<< n).testBit q = _
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow]; simp [eq_comm]
    cases hP : P n
    · simp only [cond_false, ih]
      by_cases h : q = n
      · subst h; simp [hP]
      · by_cases h2 : q < n
        · simp [h2, show q < n + 1 by omega]
        · simp [h2, show ¬ q < n + 1 by omega]
    · simp only [cond_true, Nat.testBit_or, ih, hb]
      by_cases h : q = n
      · subst h; simp [hP]
      · by_cases h2 : q < n
        · simp [h, h2, show q < n + 1 by omega]
        · simp [h, h2, show ¬ q < n + 1 by omega]

-- ===== stars =====
def csTab : Nat := packList [15, 23, 27, 29, 30, 39, 43, 45, 46, 51, 53, 54, 57, 58, 60] 6
def starMask (v cs : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun ch acc =>
    cond (tb cs ch)
      (cond (Nat.blt ch 3) (Nat.lor acc (Nat.shiftLeft 7 (Nat.add (Nat.mul 9 (Nat.mod (Nat.add v 4) 5)) (Nat.mul 3 ch))))
        (Nat.lor acc (Nat.shiftLeft 73 (Nat.sub (Nat.add (Nat.mul 9 v) ch) 3))))
      acc) 6
def starAt (k : Nat) : Nat := starMask (Nat.div k 15) (fld csTab 6 (Nat.mod k 15))
def starPack : Nat := pk starAt 45 75

def anyK (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun k acc => acc || f k) n

theorem anyK_spec (n : Nat) (f : Nat → Bool) (h : anyK n f = true) : ∃ k, k < n ∧ f k = true := by
  induction n with
  | zero => simp [anyK] at h
  | succ n ih =>
    have e : anyK (n + 1) f = (anyK n f || f n) := rfl
    rw [e, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨k, hk, hf⟩ := ih h; exact ⟨k, by omega, hf⟩
    · exact ⟨n, by omega, h⟩

def starLtCheck : Bool := allBelow 75 (fun k => Nat.blt (starAt k) (2 ^ 45))

set_option maxRecDepth 10000 in
theorem starLtCheck_ok : starLtCheck = true := by decide +kernel

theorem starAt_lt (k : Nat) (hk : k < 75) : starAt k < 2 ^ 45 :=
  (Nat.blt_eq).mp (allBelow_spec _ _ starLtCheck_ok k hk)

theorem starFld (k : Nat) (hk : k < 75) : fld starPack 45 k = starAt k :=
  fld_pk _ 45 75 k (by norm_num) (fun i hi => starAt_lt i hi) hk

def subA (t s : Nat) : Prop := ∀ p, p < 45 → t.testBit p = true → s.testBit p = true

def starOK (o : Nat) : Bool := anyK 75 (fun k => Nat.beq (Nat.land (Nat.land o MA) (Nat.xor (fld starPack 45 k) MA)) 0)

theorem starOK_spec (o : Nat) (h : starOK o = true) : ∃ k, k < 75 ∧ subA o (starAt k) := by
  obtain ⟨k, hk, hf⟩ := anyK_spec _ _ h
  refine ⟨k, hk, fun p hp ho => ?_⟩
  have e := congrArg (fun x => x.testBit p) (Nat.eq_of_beq_eq_true hf)
  change ((o &&& MA) &&& (fld starPack 45 k ^^^ MA)).testBit p = (0 : Nat).testBit p at e
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, testBit_MA, starFld k hk] at e
  simp only [hp, decide_true, ho, Bool.true_and, Nat.zero_testBit, Bool.xor_true] at e
  cases h2 : (starAt k).testBit p <;> simp_all

-- invariance of the star family under the generators (A part)
def imgA (k s : Nat) : Nat := accRec (fun p => tb s (gP k p)) (fun p => Nat.shiftLeft 1 p) 45
def starImg (k m : Nat) : Nat := srch (fun m' => Nat.beq (fld starPack 45 m') (imgA k (fld starPack 45 m))) 75

def starInvCheck : Bool :=
  allBelow 19 (fun k => allBelow 75 (fun m => Nat.blt (starImg k m) 75 &&
    Nat.beq (fld starPack 45 (starImg k m)) (imgA k (fld starPack 45 m))))

set_option maxRecDepth 100000 in
theorem starInvCheck_ok : starInvCheck = true := by decide +kernel

theorem star_gen (k m : Nat) (hk : k < 19) (hm : m < 75) :
    ∃ m', m' < 75 ∧ ∀ p, p < 45 → (starAt m).testBit (gP k p) = (starAt m').testBit p := by
  have h := allBelow_spec _ _ (allBelow_spec _ _ starInvCheck_ok k hk) m hm
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  refine ⟨starImg k m, h.1, fun p hp => ?_⟩
  have e := congrArg (fun x => x.testBit p) (Nat.eq_of_beq_eq_true h.2)
  simp only [imgA, accRec_bits, hp, decide_true, Bool.true_and, starFld _ h.1, starFld _ hm, tb_eq] at e
  exact e.symm

theorem subA_permW_star (w : List Nat) (t : Nat) (m : Nat) (hm : m < 75) (h : subA t (starAt m)) :
    ∃ m', m' < 75 ∧ subA (permW w t) (starAt m') := by
  induction w generalizing t m with
  | nil => exact ⟨m, hm, h⟩
  | cons k w ih =>
    have step : ∃ m', m' < 75 ∧ subA (permP (genP k) t) (starAt m') := by
      by_cases hk : k < 19
      · obtain ⟨m', hm', he⟩ := star_gen k m hk hm
        refine ⟨m', hm', fun p hp ht => ?_⟩
        rw [testBit_permP] at ht
        simp only [show p < 180 by omega, decide_true, Bool.true_and, genP, hk, if_true] at ht
        have hs := (genP_side k p (by omega)).1 hp
        simp only [genP, hk, if_true] at hs
        rw [← he p hp]; exact h _ hs ht
      · refine ⟨m, hm, fun p hp ht => ?_⟩
        rw [testBit_permP] at ht
        simp only [show p < 180 by omega, decide_true, Bool.true_and, genP, hk, if_false] at ht
        exact h p hp ht
    obtain ⟨m', hm', hs⟩ := step
    exact ih (permP (genP k) t) m' hm' hs

-- ===== domination search inside a lane =====
def domZ (r P n : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.land (Nat.mul r (rep 256 n)) (Nat.xor P (Nat.mul mask180 (rep 256 n)))) (Nat.mul MA (rep 256 n)))
    (Nat.land (Nat.land P (Nat.xor (Nat.mul r (rep 256 n)) (Nat.mul mask180 (rep 256 n)))) (Nat.mul MV (rep 256 n)))

def domLane (r P n : Nat) : Bool :=
  !Nat.beq (Nat.land (Nat.shiftLeft (rep 256 n) 255)
    (Nat.xor (Nat.add (domZ r P n) (Nat.mul (Nat.sub (2 ^ 255) 1) (rep 256 n))) (Nat.shiftLeft (rep 256 n) 255))) 0

theorem pk_ne_zero (f : Nat → Nat) (w n : Nat) (h : pk f w n ≠ 0) : ∃ i, i < n ∧ f i ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [pk_congr f (fun _ => 0) w n (fun i hi => hc i hi)]
  exact pk_zero w n

theorem mask180_lt : mask180 < 2 ^ 180 := by show 2 ^ 180 - 1 < 2 ^ 180; omega

theorem domLane_spec (r n : Nat) (img : Nat → Nat) (hr : r < 2 ^ 180) (himg : ∀ i, i < n → img i < 2 ^ 180)
    (h : domLane r (pk img 256 n) n = true) : ∃ i, i < n ∧ dom r (img i) := by
  have hR := rep_eq 256 n (by norm_num)
  have F : ∀ f : Nat → Nat, (∀ i, i < n → f i < 2 ^ 180) → Fits f 256 n :=
    fun f hf i hi => lt_of_lt_of_le (hf i hi) (by norm_num)
  let z := fun i => ((r &&& (img i ^^^ mask180)) &&& MA) ||| ((img i &&& (r ^^^ mask180)) &&& MV)
  have hz : ∀ i, i < n → z i < 2 ^ 180 := fun i hi =>
    Nat.or_lt_two_pow (lt_of_le_of_lt Nat.and_le_right (lt_of_lt_of_le MA_lt (by norm_num)))
      (lt_of_le_of_lt Nat.and_le_right MV_lt)
  have hZ : domZ r (pk img 256 n) n = pk z 256 n := by
    unfold domZ
    rw [hR]
    show ((r * pk _ 256 n &&& (pk img 256 n ^^^ mask180 * pk _ 256 n)) &&& MA * pk _ 256 n) |||
      ((pk img 256 n &&& (r * pk _ 256 n ^^^ mask180 * pk _ 256 n)) &&& MV * pk _ 256 n) = _
    rw [pk_const, pk_const, pk_const, pk_const]
    have fr := F (fun _ => r) (fun _ _ => hr)
    have fm := F (fun _ => mask180) (fun _ _ => mask180_lt)
    have fa := F (fun _ => MA) (fun _ _ => lt_of_lt_of_le MA_lt (by norm_num))
    have fv := F (fun _ => MV) (fun _ _ => MV_lt)
    have fi := F img himg
    rw [pk_xor _ _ _ _ (by norm_num) fi fm, pk_xor _ _ _ _ (by norm_num) fr fm]
    have fx1 := F (fun i => img i ^^^ mask180) (fun i hi => Nat.xor_lt_two_pow (himg i hi) mask180_lt)
    have fx2 := F (fun _ => r ^^^ mask180) (fun _ _ => Nat.xor_lt_two_pow hr mask180_lt)
    rw [pk_land _ _ _ _ (by norm_num) fr fx1, pk_land _ _ _ _ (by norm_num) fi fx2]
    have fy1 := F (fun i => r &&& (img i ^^^ mask180)) (fun _ _ => lt_of_le_of_lt Nat.and_le_left hr)
    have fy2 := F (fun i => img i &&& (r ^^^ mask180)) (fun i hi => lt_of_le_of_lt Nat.and_le_left (himg i hi))
    rw [pk_land _ _ _ _ (by norm_num) fy1 fa, pk_land _ _ _ _ (by norm_num) fy2 fv]
    have fz1 := F (fun i => (r &&& (img i ^^^ mask180)) &&& MA) (fun _ _ => lt_of_le_of_lt (Nat.and_le_left.trans Nat.and_le_left) hr)
    have fz2 := F (fun i => (img i &&& (r ^^^ mask180)) &&& MV) (fun i hi => lt_of_le_of_lt Nat.and_le_left (lt_of_le_of_lt Nat.and_le_left (himg i hi)))
    rw [pk_lor _ _ _ _ (by norm_num) fz1 fz2]
  unfold domLane at h
  rw [hZ, hR] at h
  simp only [Bool.not_eq_true'] at h
  replace h := Nat.ne_of_beq_eq_false h
  have hT : Nat.shiftLeft (pk (fun _ => 1) 256 n) 255 = pk (fun _ => 2 ^ 255) 256 n := by
    show pk _ 256 n <<< 255 = _
    rw [Nat.shiftLeft_eq, Nat.mul_comm, pk_mul]
    apply pk_congr; intro _ _; ring
  have hW : Nat.add (pk z 256 n) (Nat.mul (Nat.sub (2 ^ 255) 1) (pk (fun _ => 1) 256 n)) =
      pk (fun i => z i + (2 ^ 255 - 1)) 256 n := by
    show pk z 256 n + (2 ^ 255 - 1) * pk _ 256 n = _
    rw [pk_const, pk_add]
  rw [hT, hW] at h
  have fW : Fits (fun i => z i + (2 ^ 255 - 1)) 256 n := fun i hi => by
    have := hz i hi; show z i + (2 ^ 255 - 1) < 2 ^ 256
    have : (2 : Nat) ^ 180 ≤ 2 ^ 255 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have : (2 : Nat) ^ 256 = 2 ^ 255 + 2 ^ 255 := by norm_num
    omega
  have fT : Fits (fun _ => 2 ^ 255) 256 n := fun _ _ => by norm_num
  change pk _ 256 n &&& (pk _ 256 n ^^^ pk _ 256 n) ≠ 0 at h
  rw [pk_xor _ _ _ _ (by norm_num) fW fT] at h
  have fX : Fits (fun i => (z i + (2 ^ 255 - 1)) ^^^ 2 ^ 255) 256 n := fun i hi => Nat.xor_lt_two_pow (fW i hi) (fT i hi)
  rw [pk_land _ _ _ _ (by norm_num) fT fX] at h
  obtain ⟨i, hi, hne⟩ := pk_ne_zero _ _ _ h
  refine ⟨i, hi, ?_⟩
  -- the field is nonzero only when z i = 0
  have hz0 : z i = 0 := by
    by_contra hz1
    apply hne
    have hb : (z i + (2 ^ 255 - 1)).testBit 255 = true := by
      have h1 : 2 ^ 255 ≤ z i + (2 ^ 255 - 1) := by omega
      have h2 := fW i hi
      have e : z i + (2 ^ 255 - 1) = 2 ^ 255 + (z i + (2 ^ 255 - 1) - 2 ^ 255) := by omega
      rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by
        have : (2 : Nat) ^ 256 = 2 ^ 255 + 2 ^ 255 := by norm_num
        change z i + (2 ^ 255 - 1) < 2 ^ 256 at h2
        omega)]
      rfl
    apply Nat.eq_of_testBit_eq; intro q
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, Nat.testBit_two_pow]
    by_cases hq : 255 = q
    · subst hq; rw [hb]; rfl
    · simp [hq]
  intro p hp
  have e := congrArg (fun x => x.testBit p) hz0
  simp only [z, Nat.zero_testBit, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, testBit_mask180, testBit_MA,
    testBit_MV, hp, decide_true, Bool.xor_true, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at e
  constructor
  · intro hpa hrp
    by_contra hi2
    simp only [Bool.not_eq_true] at hi2
    have := e.1; simp [hrp, hi2, hpa] at this
  · intro hpa hip
    by_contra hr2
    simp only [Bool.not_eq_true] at hr2
    have := e.2; simp [hip, hr2, hpa, show p < 180 from hp] at this

-- ===== existence search by bisection =====
def anyB (W : Nat) (f : Nat → Bool) (m : Nat) : Nat → Nat → Nat → Bool
  | 0, lo, size => Nat.beq size 1 && f lo
  | k + 1, lo, size => !winZero m (Nat.mul W lo) (Nat.mul W size) &&
      ((Nat.beq size 1 && f lo) || (Nat.ble 2 size && (anyB W f m k lo (size / 2) ||
        anyB W f m k (lo + size / 2) (size - size / 2))))

theorem anyB_spec (W : Nat) (f : Nat → Bool) (m k : Nat) :
    ∀ lo size, anyB W f m k lo size = true → ∃ l, lo ≤ l ∧ l < lo + size ∧ f l = true := by
  induction k with
  | zero =>
    intro lo size h
    simp only [anyB, Bool.and_eq_true] at h
    have := Nat.eq_of_beq_eq_true h.1
    exact ⟨lo, le_rfl, by omega, h.2⟩
  | succ k ih =>
    intro lo size h
    simp only [anyB, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at h
    rcases h.2 with h2 | h2
    · have := Nat.eq_of_beq_eq_true h2.1
      exact ⟨lo, le_rfl, by omega, h2.2⟩
    · rcases h2.2 with h3 | h3
      · obtain ⟨l, h4, h5, h6⟩ := ih _ _ h3; exact ⟨l, h4, by omega, h6⟩
      · obtain ⟨l, h4, h5, h6⟩ := ih _ _ h3; exact ⟨l, by omega, by omega, h6⟩

-- ===== packed leaves of the images of a lane =====
def laneLacc (s d : Nat) (J : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.add acc (Nat.shiftLeft
    (kron 32 (divOf s (Nat.mod (hLeaf (hCode s) j) 5)) (locLen (rankOf s (Nat.mod (hLeaf (hCode s) j) 5)))
      (outOf s (Nat.mod (hLeaf (hCode s) j) 5)) (fun c => hImg s d (hLeaf (hCode s) j) c)) (Nat.mul 4 j))) J
def laneL (s d : Nat) : Nat := laneLacc s d 8

theorem laneLacc_eq (s d : Nat) (hs : s < 41) (J : Nat) (hJ : J ≤ 8) :
    laneLacc s d J = pk (fun k => pk (fun j => imgLf s d k j) 4 J) 32 (nImg s) := by
  induction J with
  | zero => show 0 = _; rw [show (fun k => pk (fun j => imgLf s d k j) 4 0) = fun _ => 0 from rfl, pk_zero]
  | succ J ih =>
    show laneLacc s d J + (kron 32 _ _ _ _ <<< (4 * J)) = _
    obtain ⟨h1, h2, h3⟩ := radix_shape s (Nat.mod (hLeaf (hCode s) J) 5) hs (Nat.mod_lt _ (by norm_num))
    rw [ih (by omega), kron_eq _ _ _ _ _ (by norm_num) h1 h2, h3, Nat.shiftLeft_eq, Nat.mul_comm, pk_mul, pk_add]
    apply pk_congr; intro k _
    show pk (fun j => imgLf s d k j) 4 J + 2 ^ (4 * J) * imgLf s d k J = 2 ^ (4 * J) * imgLf s d k J + pk (fun j => imgLf s d k j) 4 J
    ring

theorem laneL_leaf (s d k j : Nat) (hs : s < 41) (hk : k < nImg s) (hj : j < 8) :
    leaf8 (fld (laneL s d) 32 k) j = imgLf s d k j := by
  have fl : Fits (fun j => imgLf s d k j) 4 8 := fun j hj => lt_trans (imgLf_lt s d k j hs hj) (by norm_num)
  have f2 : Fits (fun k => pk (fun j => imgLf s d k j) 4 8) 32 (nImg s) := fun k _ =>
    pk_lt _ 4 8 (fun j hj => lt_trans (imgLf_lt s d k j hs hj) (by norm_num))
  unfold laneL
  rw [laneLacc_eq s d hs 8 le_rfl, fld_pk _ _ _ _ (by norm_num) f2 hk]
  exact fld_pk _ 4 8 j (by norm_num) fl hj

-- ===== the six bounds and the broad prefilter =====
def capsOK2 (a b : Nat) : Bool :=
  (Nat.blt b 135 || Nat.ble a 4) && (Nat.blt a 45 || Nat.ble b 4) && (Nat.blt a 10 || Nat.ble b 105) &&
  (Nat.blt a 21 || Nat.ble b 60) && (Nat.blt b 68 || Nat.ble a 18) && (Nat.blt b 34 || Nat.ble a 30)

def Caps (a b : Nat) : Prop :=
  (135 ≤ b → a ≤ 4) ∧ (45 ≤ a → b ≤ 4) ∧ (10 ≤ a → b ≤ 105) ∧ (21 ≤ a → b ≤ 60) ∧ (68 ≤ b → a ≤ 18) ∧ (34 ≤ b → a ≤ 30)

theorem capsOK2_spec (a b : Nat) (h : capsOK2 a b = true) : Caps a b := by
  simp only [capsOK2, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hh <;> omega

def broad (a b : Nat) : Bool :=
  (Nat.ble 21 a && Nat.ble 8 b) || (Nat.ble 3 a && Nat.ble 68 b) || (Nat.ble 10 a && Nat.ble 30 b)

-- ===== scope groups =====
def gNum (g : Nat) : Nat := Nat.mul (fld 0x04120c17 8 g) 10
def gSc0 (g : Nat) : Nat := fld 0x35231700 8 g
def gOr (g : Nat) : Bool := Nat.beq g 1 || Nat.beq g 3
def gTa (g : Nat) : Nat := fld 0x2d0a1515 8 g
def gTb (g : Nat) : Nat := fld 0x22874444 8 g
def cG2 : Nat := packList [23, 24, 25, 26, 27, 28, 29, 33, 34, 35, 38, 40] 8
def scopeH (sc : Nat) : Nat :=
  cond (Nat.blt sc 23) sc (cond (Nat.blt sc 35) (fld cG2 8 (Nat.sub sc 23))
    (cond (Nat.blt sc 53) (Nat.sub sc 12) (fld 0x05040100 8 (Nat.sub sc 53))))
def Ls (g l : Nat) : Nat := scopeH (Nat.add (gSc0 g) (Nat.div l 10))
def Ld (g l : Nat) : Nat := Nat.mod l 10
def gHA (g : Nat) : Nat := pk (fun l => profA (imgVec0 (Ls g l) (Ld g l))) 64 (gNum g)
def gHB (g : Nat) : Nat := pk (fun l => profB (imgVec0 (Ls g l) (Ld g l))) 64 (gNum g)
def hfVec (s : Nat) : Nat := evalHv (hCode s) (fun j => varAt (hLeaf (hCode s) j))

def scopeCheck : Bool :=
  allBelow 4 (fun g => allBelow (gNum g) (fun l => Nat.blt (Ls g l) 41 && Nat.blt (Ld g l) 10 &&
    cond (Nat.beq g 0) (Nat.ble (popB2 (hfVec (Ls g l))) 60) (cond (Nat.beq g 1) (Nat.ble (popA2 (hfVec (Ls g l))) 18)
      (cond (Nat.beq g 2) (Nat.ble (popB2 (hfVec (Ls g l))) 105) (Nat.ble (popA2 (hfVec (Ls g l))) 30)))))

set_option maxRecDepth 100000 in
theorem scopeCheck_ok : scopeCheck = true := by decide +kernel

theorem scope_spec (g l : Nat) (hg : g < 4) (hl : l < gNum g) :
    Ls g l < 41 ∧ Ld g l < 10 ∧
    (g = 0 → cB (tv (HF (Ls g l))) ≤ 60) ∧ (g = 1 → cA (tv (HF (Ls g l))) ≤ 18) ∧
    (g = 2 → cB (tv (HF (Ls g l))) ≤ 105) ∧ (g = 3 → cA (tv (HF (Ls g l))) ≤ 30) := by
  have h := allBelow_spec _ _ (allBelow_spec _ _ scopeCheck_ok g hg) l hl
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  have hv : hfVec (Ls g l) = tv (HF (Ls g l)) := by rw [HF, tv_FH]; rfl
  rw [hv] at h
  refine ⟨h.1.1, h.1.2, ?_, ?_, ?_, ?_⟩ <;> intro hgv <;> subst hgv <;> simp at h <;> first
    | (rw [← popB2_eq]; exact h.2) | (rw [← popA2_eq]; exact h.2)

theorem cA_img (s d k : Nat) (hs : s < 41) (hd : d < 10) : cA (tv (imgF s d k)) = cA (tv (HF s)) := by
  rw [tv_imgF_words s d k hs hd, cA_permW]

theorem cB_img (s d k : Nat) (hs : s < 41) (hd : d < 10) : cB (tv (imgF s d k)) = cB (tv (HF s)) := by
  rw [tv_imgF_words s d k hs hd, cB_permW]

theorem cA_gate_le (op : Bool) (r I : Nat) :
    cA (gate op r I) ≤ cond op (cA r + cA I) (cA r) := by
  rw [cA_split, cA_split r, cA_split I]
  have g := fun e => aE_gate op r I e
  cases op <;> simp only [combA, cond_true, cond_false] at g ⊢
  · have := g 0; have := g 1; have := g 2; have := g 3; have := g 4
    have := min_le_left (aE 0 r) (aE 0 I); have := min_le_left (aE 1 r) (aE 1 I); have := min_le_left (aE 2 r) (aE 2 I)
    have := min_le_left (aE 3 r) (aE 3 I); have := min_le_left (aE 4 r) (aE 4 I)
    omega
  · have := g 0; have := g 1; have := g 2; have := g 3; have := g 4
    have := min_le_right 9 (aE 0 r + aE 0 I); have := min_le_right 9 (aE 1 r + aE 1 I); have := min_le_right 9 (aE 2 r + aE 2 I)
    have := min_le_right 9 (aE 3 r + aE 3 I); have := min_le_right 9 (aE 4 r + aE 4 I)
    omega

theorem cB_gate_le (op : Bool) (r I : Nat) :
    cB (gate op r I) ≤ cond op (cB r) (cB r + cB I) := by
  rw [cB_split, cB_split r, cB_split I]
  have g := fun j (hj : j < 5) => bE_gate op r I j hj
  cases op <;> simp only [combB, cond_true, cond_false] at g ⊢
  · have := g 0 (by norm_num); have := g 1 (by norm_num); have := g 2 (by norm_num); have := g 3 (by norm_num)
    have := g 4 (by norm_num)
    have := min_le_right 27 (bE 0 r + bE 0 I); have := min_le_right 27 (bE 1 r + bE 1 I); have := min_le_right 27 (bE 2 r + bE 2 I)
    have := min_le_right 27 (bE 3 r + bE 3 I); have := min_le_right 27 (bE 4 r + bE 4 I)
    omega
  · have := g 0 (by norm_num); have := g 1 (by norm_num); have := g 2 (by norm_num); have := g 3 (by norm_num)
    have := g 4 (by norm_num)
    have := min_le_left (bE 0 r) (bE 0 I); have := min_le_left (bE 1 r) (bE 1 I); have := min_le_left (bE 2 r) (bE 2 I)
    have := min_le_left (bE 3 r) (bE 3 I); have := min_le_left (bE 4 r) (bE 4 I)
    omega

theorem broad_need (g l k r : Nat) (hg : g < 4) (hl : l < gNum g)
    (hA : gTa g ≤ cA (gate (gOr g) r (tv (imgF (Ls g l) (Ld g l) k))))
    (hB : gTb g ≤ cB (gate (gOr g) r (tv (imgF (Ls g l) (Ld g l) k)))) : broad (cA r) (cB r) = true := by
  obtain ⟨hs, hd, b0, b1, b2, b3⟩ := scope_spec g l hg hl
  have ea := cA_img _ _ k hs hd
  have eb := cB_img _ _ k hs hd
  have la := cA_gate_le (gOr g) r (tv (imgF (Ls g l) (Ld g l) k))
  have lb := cB_gate_le (gOr g) r (tv (imgF (Ls g l) (Ld g l) k))
  simp only [broad, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq]
  interval_cases g
  · have := b0 rfl
    simp only [show gOr 0 = false from rfl, show gTa 0 = 21 from rfl, show gTb 0 = 68 from rfl, cond_false] at hA hB la lb
    omega
  · have := b1 rfl
    simp only [show gOr 1 = true from rfl, show gTa 1 = 21 from rfl, show gTb 1 = 68 from rfl, cond_true] at hA hB la lb
    omega
  · have := b2 rfl
    simp only [show gOr 2 = false from rfl, show gTa 2 = 10 from rfl, show gTb 2 = 135 from rfl, cond_false] at hA hB la lb
    omega
  · have := b3 rfl
    simp only [show gOr 3 = true from rfl, show gTa 3 = 45 from rfl, show gTb 3 = 34 from rfl, cond_true] at hA hB la lb
    omega

-- ===== the row check =====
def hitOK (g : Nat) (rop : Bool) (i D c pv s lv o : Nat) : Bool :=
  cond (Nat.beq g 2) (starOK o) (cond (Nat.beq g 3) false
    (Nat.ble (popA2 o) 24 && Nat.ble (popB2 o) 86 && clsOK (gOr g) rop i D c pv s lv o))

def laneOK (g : Nat) (rop : Bool) (i D c pv r l : Nat) : Bool :=
  Nat.beq (laneHits (gOr g) (gTa g) (gTb g) (nImg (Ls g l)) (laneP (Ls g l) (Ld g l)) r) 0 ||
  scanB 256 (fun k => hitOK g rop i D c pv (Ls g l) (fld (laneL (Ls g l) (Ld g l)) 32 k)
      (gate (gOr g) r (fld (laneP (Ls g l) (Ld g l)) 256 k)))
    (laneHits (gOr g) (gTa g) (gTb g) (nImg (Ls g l)) (laneP (Ls g l) (Ld g l)) r) 9 0 (nImg (Ls g l))

def groupOK (g : Nat) (rop : Bool) (i D c pv r : Nat) : Bool :=
  scanB 64 (fun l => laneOK g rop i D c pv r l)
    (guardMask (gOr g) (gTa g) (gTb g) (gNum g) (profA r) (profB r) (gHA g) (gHB g)) 9 0 (gNum g)

def highOK (r a b : Nat) : Bool :=
  (!(Nat.ble 21 a && Nat.ble 34 b) || anyB 64 (fun l => domLane r (laneP (Ls 0 l) (Ld 0 l)) (nImg (Ls 0 l)))
    (guardMask false a b (gNum 0) (profA r) (profB r) (gHA 0) (gHB 0)) 9 0 (gNum 0)) &&
  (!(Nat.ble 10 a && Nat.ble 68 b) || anyB 64 (fun l => domLane r (laneP (Ls 2 l) (Ld 2 l)) (nImg (Ls 2 l)))
    (guardMask false a b (gNum 2) (profA r) (profB r) (gHA 2) (gHB 2)) 9 0 (gNum 2))

def rowOK (rop : Bool) (i D c pv r : Nat) : Bool :=
  capsOK2 (popA2 r) (popB2 r) && highOK r (popA2 r) (popB2 r) &&
  (!broad (popA2 r) (popB2 r) || (groupOK 0 rop i D c pv r && groupOK 1 rop i D c pv r &&
    groupOK 2 rop i D c pv r && groupOK 3 rop i D c pv r))

-- ===== semantics of a passing row =====
def HitConc (g o : Nat) : Prop :=
  (g = 2 → ∃ m, m < 75 ∧ subA o (starAt m)) ∧ (g = 3 → False) ∧
  (g < 2 → cA o ≤ 24 ∧ cB o ≤ 86 ∧ ∃ w m, m < 58 ∧ dom (permW w o) (targetT m))

def RowSem (r : Nat) : Prop :=
  Caps (cA r) (cB r) ∧
  (21 ≤ cA r → 34 ≤ cB r → ∃ l k, l < gNum 0 ∧ k < nImg (Ls 0 l) ∧ dom r (tv (imgF (Ls 0 l) (Ld 0 l) k))) ∧
  (10 ≤ cA r → 68 ≤ cB r → ∃ l k, l < gNum 2 ∧ k < nImg (Ls 2 l) ∧ dom r (tv (imgF (Ls 2 l) (Ld 2 l) k))) ∧
  ∀ g, g < 4 → ∀ l, l < gNum g → ∀ k, k < nImg (Ls g l) →
    gTa g ≤ cA (gate (gOr g) r (tv (imgF (Ls g l) (Ld g l) k))) →
    gTb g ≤ cB (gate (gOr g) r (tv (imgF (Ls g l) (Ld g l) k))) →
    HitConc g (gate (gOr g) r (tv (imgF (Ls g l) (Ld g l) k)))

theorem gTa_le (g : Nat) (hg : g < 4) : gTa g ≤ 45 := by interval_cases g <;> decide
theorem gTb_le (g : Nat) (hg : g < 4) : gTb g ≤ 135 := by interval_cases g <;> decide

theorem img_lt (s d k : Nat) : tv (imgF s d k) < 2 ^ 180 := tv_lt _

theorem lane_fld (s d k : Nat) (hs : s < 41) (hk : k < nImg s) : fld (laneP s d) 256 k = tv (imgF s d k) := by
  rw [laneP_eq s d hs]
  exact fld_pk _ 256 _ k (by norm_num) (fun i _ => lt_of_lt_of_le (tv_lt _) (by norm_num)) hk

theorem rowOK_spec (rop : Bool) (i D c pv : Nat) (hi : i < 41) (hc : c < 41) (hpv : ∀ w, w < 5 → pvF pv w < 6)
    (h : rowOK rop i D c pv (tv (RowF i D c pv rop)) = true) : RowSem (tv (RowF i D c pv rop)) := by
  generalize hr : tv (RowF i D c pv rop) = r at h
  have hrl : r < 2 ^ 180 := by rw [← hr]; exact tv_lt _
  simp only [rowOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hcaps, hhigh⟩, hgr⟩ := h
  rw [popA2_eq, popB2_eq] at hcaps hhigh hgr
  refine ⟨capsOK2_spec _ _ hcaps, ?_, ?_, ?_⟩
  · intro h1 h2
    simp only [highOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hhigh
    rcases hhigh.1 with h3 | h3
    · rw [show Nat.ble 21 (cA r) = true by rw [Nat.ble_eq]; exact h1, show Nat.ble 34 (cB r) = true by rw [Nat.ble_eq]; exact h2] at h3
      exact absurd h3 (by simp)
    · obtain ⟨l, _, hl, hd⟩ := anyB_spec _ _ _ _ _ _ h3
      have hs := (scope_spec 0 l (by norm_num) hl).1
      rw [laneP_eq _ _ hs] at hd
      obtain ⟨k, hk, hdom⟩ := domLane_spec r _ _ hrl (fun _ _ => tv_lt _) hd
      exact ⟨l, k, hl, hk, hdom⟩
  · intro h1 h2
    simp only [highOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hhigh
    rcases hhigh.2 with h3 | h3
    · rw [show Nat.ble 10 (cA r) = true by rw [Nat.ble_eq]; exact h1, show Nat.ble 68 (cB r) = true by rw [Nat.ble_eq]; exact h2] at h3
      exact absurd h3 (by simp)
    · obtain ⟨l, _, hl, hd⟩ := anyB_spec _ _ _ _ _ _ h3
      have hs := (scope_spec 2 l (by norm_num) hl).1
      rw [laneP_eq _ _ hs] at hd
      obtain ⟨k, hk, hdom⟩ := domLane_spec r _ _ hrl (fun _ _ => tv_lt _) hd
      exact ⟨l, k, hl, hk, hdom⟩
  · intro g hg l hl k hk hA hB
    obtain ⟨hs, hd, -⟩ := scope_spec g l hg hl
    have hbr := broad_need g l k r hg hl hA hB
    rcases hgr with h3 | h3
    · rw [hbr] at h3; exact absurd h3 (by simp)
    have hG : groupOK g rop i D c pv r = true := by
      interval_cases g
      · exact h3.1.1.1
      · exact h3.1.1.2
      · exact h3.1.2
      · exact h3.2
    -- the guard passes for lane l
    have hguard := guard_sound (gOr g) (gTa g) (gTb g) (gNum g) (Ls g) (Ld g)
      (fun l hl => (scope_spec g l hg hl).1) (fun l hl => (scope_spec g l hg hl).2.1)
      (by have := gTa_le g hg; omega) (by have := gTb_le g hg; omega) r l k hl hA hB
    have hlane := scanB_spec 64 (by norm_num) _ _ 9 0 (gNum g) hG l (by omega) (by omega) hguard
    simp only [laneOK, Bool.or_eq_true] at hlane
    -- the hit bit is set
    have hbit := laneHits_spec (gOr g) (gTa g) (gTb g) (nImg (Ls g l)) (laneP (Ls g l) (Ld g l)) r
      (fun k => tv (imgF (Ls g l) (Ld g l) k)) (laneP_eq _ _ hs) (fun _ _ => tv_lt _) hrl (gTa_le g hg) (gTb_le g hg) k hk hA hB
    rcases hlane with h4 | h4
    · have := Nat.eq_of_beq_eq_true h4
      rw [this] at hbit; simp at hbit
    have hhit := scanB_spec 256 (by norm_num) _ _ 9 0 (nImg (Ls g l)) h4 k (by omega) (by omega) hbit
    rw [lane_fld _ _ k hs hk] at hhit
    simp only [hitOK] at hhit
    refine ⟨?_, ?_, ?_⟩
    · intro hg2; subst hg2
      simp only [show Nat.beq 2 2 = true from rfl, cond_true] at hhit
      exact starOK_spec _ hhit
    · intro hg3; subst hg3
      simp only [show Nat.beq 3 2 = false from rfl, show Nat.beq 3 3 = true from rfl, cond_false, cond_true] at hhit
      exact absurd hhit (by simp)
    · intro hg2
      have e2 : Nat.beq g 2 = false := by interval_cases g <;> rfl
      have e3 : Nat.beq g 3 = false := by interval_cases g <;> rfl
      simp only [e2, e3, cond_false, Bool.and_eq_true, Nat.ble_eq] at hhit
      rw [popA2_eq, popB2_eq] at hhit
      refine ⟨hhit.1.1, hhit.1.2, ?_⟩
      have ho : gate (gOr g) r (tv (imgF (Ls g l) (Ld g l) k)) = tv (hitF (gOr g) rop i D c pv (Ls g l) (Ld g l) k) := by
        rw [tv_hitF, hr]
      rw [ho] at hhit ⊢
      exact clsOK_spec (gOr g) rop i D c pv (Ls g l) (Ld g l) k _ hi hc hs hpv
        (fun j hj => laneL_leaf _ _ k j hs hk hj) hhit.2

def firstPack : Nat := pk (fun i => evalT2 (tplAt i) (leafOf (tplAt i))) 180 41

def rowPairOK (i D c pv : Nat) : Bool :=
  rowOK false i D c pv (Nat.land (fld firstPack 180 i) (evalT2 (tplAt c) (placeL (tplAt c) D pv))) &&
  rowOK true i D c pv (Nat.lor (fld firstPack 180 i) (evalT2 (tplAt c) (placeL (tplAt c) D pv)))

def masksOf (i D c : Nat) : Nat := pk (fun w => choiceMask (usedAt (tplAt i) w) (usedPlaced (tplAt c) D w)) 6 5

def genGo (i D c ms : Nat) : Nat → Nat → Nat → Bool
  | 0, _, pv => rowPairOK i D c pv
  | k + 1, v, pv => allBelow 6 (fun p => !tb ms (Nat.add (Nat.mul 6 v) p) ||
      genGo i D c ms k (Nat.add v 1) (Nat.add pv (Nat.shiftLeft p (Nat.mul 3 v))))

def pairOK (i c : Nat) : Bool := allBelow 10 (fun D => !repOK2 i c D || genGo i D c (masksOf i D c) 5 0 0)
def HallP : Prop := ∀ i c, i < 41 → c < 41 → ocheck i c = true → pairOK i c = true

-- ===== correctness of the generation =====
def accOf (ch : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | k + 1, v, acc => accOf ch k (v + 1) (acc + ch v <<< (3 * v))

theorem genGo_spec (i D c ms : Nat) (ch : Nat → Nat) :
    ∀ k v acc, genGo i D c ms k v acc = true → (∀ w, v ≤ w → w < v + k → ch w < 6 ∧ tb ms (6 * w + ch w) = true) →
      rowPairOK i D c (accOf ch k v acc) = true := by
  intro k
  induction k with
  | zero => intro v acc h _; exact h
  | succ k ih =>
    intro v acc h hch
    have hv := hch v le_rfl (by omega)
    have h1 := allBelow_spec _ _ h (ch v) hv.1
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
    rcases h1 with h1 | h1
    · have : tb ms (6 * v + ch v) = false := h1
      rw [hv.2] at this; exact absurd this (by simp)
    · exact ih (v + 1) _ h1 (fun w h2 h3 => hch w (by omega) (by omega))

theorem accOf_eq (ch : Nat → Nat) : accOf ch 5 0 0 = pk ch 3 5 := by
  simp only [accOf, pk, Nat.shiftLeft_eq]; ring

theorem pvF_eq (P w : Nat) : pvF P w = fld P 3 w := rfl

theorem RowF_congr (i D c pv pv' : Nat) (rop : Bool) (h : ∀ w, w < 5 → pvF pv w = pvF pv' w) :
    RowF i D c pv rop = RowF i D c pv' rop := by
  have e : placeL (tplAt c) D pv = placeL (tplAt c) D pv' := by
    funext t; unfold placeL; rw [h _ (dmapC_lt _ _)]
  unfold RowF; rw [e]

theorem choiceMask_lt (s t : Nat) : choiceMask s t < 2 ^ 6 :=
  accRec_lt _ _ 6 6 (fun p hp => by
    show 1 <<< p < 2 ^ 6; rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by norm_num) hp)

theorem rowPairOK_spec (i D c pv : Nat) (hi : i < 41) (hc : c < 41) (hpv : ∀ w, w < 5 → pvF pv w < 6)
    (h : rowPairOK i D c pv = true) (rop : Bool) : RowSem (tv (RowF i D c pv rop)) := by
  have hf : fld firstPack 180 i = tv (TF i) := by
    rw [firstPack, fld_pk _ 180 41 i (by norm_num) (fun j _ => by rw [← tv_F2]; exact tv_lt _) hi, TF, tv_F2]
  have hs : evalT2 (tplAt c) (placeL (tplAt c) D pv) = tv (F2 (tplAt c) (placeL (tplAt c) D pv)) := by rw [tv_F2]
  simp only [rowPairOK, Bool.and_eq_true] at h
  rw [hf, hs] at h
  cases rop
  · apply rowOK_spec false i D c pv hi hc hpv
    have e : tv (RowF i D c pv false) = Nat.land (tv (TF i)) (tv (F2 (tplAt c) (placeL (tplAt c) D pv))) := by
      unfold RowF; rw [tv_bop]; rfl
    rw [e]; exact h.1
  · apply rowOK_spec true i D c pv hi hc hpv
    have e : tv (RowF i D c pv true) = Nat.lor (tv (TF i)) (tv (F2 (tplAt c) (placeL (tplAt c) D pv))) := by
      unfold RowF; rw [tv_bop]; rfl
    rw [e]; exact h.2

theorem stream_spec (hall : HallP) (i D c pv : Nat) (rop : Bool)
    (hi : i < 41) (hD : D < 10) (hc : c < 41) (ho : ocheck i c = true) (hrp : repOK2 i c D = true) (hch : choiceOK i D c pv) :
    RowSem (tv (RowF i D c pv rop)) := by
  have h0 : (!repOK2 i c D || genGo i D c (masksOf i D c) 5 0 0) = true := allBelow_spec _ _ (hall i c hi hc ho) D hD
  rw [hrp, Bool.not_true, Bool.false_or] at h0
  have h : genGo i D c (masksOf i D c) 5 0 0 = true := h0
  let ch := fun w => pvF pv w
  have hm : ∀ w, w < 5 → ch w < 6 ∧ tb (masksOf i D c) (6 * w + ch w) = true := by
    intro w hw
    refine ⟨(hch w hw).1, ?_⟩
    rw [tb_eq, masksOf, show 6 * w + ch w = 6 * w + ch w from rfl,
      testBit_pk _ 6 5 (fun j _ => choiceMask_lt _ _) w _ (hch w hw).1]
    simp only [hw, decide_true, Bool.true_and]
    rw [← tb_eq]; exact (hch w hw).2
  have hp := genGo_spec i D c (masksOf i D c) ch 5 0 0 h (fun w _ h3 => hm w (by omega))
  rw [accOf_eq] at hp
  have hpv : ∀ w, w < 5 → pvF (pk ch 3 5) w = pvF pv w := by
    intro w hw
    rw [pvF_eq, fld_pk _ 3 5 w (by norm_num) (fun j hj => lt_trans (hch j hj).1 (by norm_num)) hw]
  have hp2 := rowPairOK_spec i D c (pk ch 3 5) hi hc (fun w hw => by rw [hpv w hw]; exact (hch w hw).1) hp rop
  rwa [RowF_congr i D c (pk ch 3 5) pv rop hpv] at hp2

-- ===== lane bookkeeping =====
theorem lane_idx (g j d : Nat) (hd : d < 10) : Ls g (10 * j + d) = scopeH (gSc0 g + j) ∧ Ld g (10 * j + d) = d := by
  constructor
  · show scopeH (gSc0 g + (10 * j + d) / 10) = _; congr 2; omega
  · show (10 * j + d) % 10 = d; omega

-- G2 representatives with at least 11 accepted minterms are scopes of group 1
def laneF1 : Bool := allBelow 18 (fun j => Nat.blt (popA2 (hfVec (23 + j))) 11 ||
    anyK 12 (fun q => Nat.beq (scopeH (gSc0 1 + q)) (23 + j)))
-- G1 representatives with at least 23 accepted minterms are scopes of group 3
def laneF3 : Bool := allBelow 23 (fun s => Nat.blt (popA2 (hfVec s)) 23 || anyK 4 (fun q => Nat.beq (scopeH (gSc0 3 + q)) s))
def laneF0 : Bool := allBelow 23 (fun s => Nat.beq (scopeH (gSc0 0 + s)) s)
def laneF2 : Bool := allBelow 18 (fun j => Nat.beq (scopeH (gSc0 2 + j)) (23 + j))

set_option maxRecDepth 100000 in
theorem laneF1_ok : laneF1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem laneF3_ok : laneF3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem laneF0_ok : laneF0 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem laneF2_ok : laneF2 = true := by decide +kernel

theorem gNum0 : gNum 0 = 230 := rfl
theorem gNum1 : gNum 1 = 120 := rfl
theorem gNum2 : gNum 2 = 180 := rfl
theorem gNum3 : gNum 3 = 40 := rfl

theorem hf_eq (s : Nat) : hfVec s = tv (HF s) := by rw [HF, tv_FH]; rfl

-- every image of HF s is an image in some lane of a group containing scope s
theorem lane_of (g q s : Nat) (hq : 10 * q + 10 ≤ gNum g) (hsc : scopeH (gSc0 g + q) = s) (hs : s < 41) (w : List Nat) :
    ∃ l k, l < gNum g ∧ k < nImg (Ls g l) ∧ permW w (tv (HF s)) = tv (imgF (Ls g l) (Ld g l) k) := by
  obtain ⟨d, k, hd, hk, he⟩ := img_complete s hs w
  obtain ⟨e1, e2⟩ := lane_idx g q d hd
  refine ⟨10 * q + d, k, by omega, ?_, ?_⟩
  · rw [e1, hsc]; exact hk
  · rw [e1, e2, hsc]; exact he

theorem caps_mono {x y : Nat} (h : Caps (cA x) (cB x)) (ha : cA y ≤ cA x) (hb : cB y ≤ cB x) : Caps (cA y) (cB y) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hh
  · have := h1 (by omega); omega
  · have := h2 (by omega); omega
  · have := h3 (by omega); omega
  · have := h4 (by omega); omega
  · have := h5 (by omega); omega
  · have := h6 (by omega); omega

theorem caps_improper (x : Nat) (h : ¬ proper x) : Caps (cA x) (cB x) := by
  unfold proper at h; rw [not_and_or] at h
  have ha : cA x ≤ 45 := cntR_le _ _ _
  have hb : cB x ≤ 135 := cntR_le _ _ _
  rcases h with h | h <;> push_neg at h <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hh <;> omega

theorem dom_permW_trans {t r : Nat} (w : List Nat) (hd : dom t (permW w r)) (x : Nat) (hx : dom r x) :
    dom t (permW w x) := dom_trans hd (dom_permW w hx)

-- ===== facts about depth-three rectangles from the stream =====
section
variable (hall : HallP)
include hall

theorem d3_row (g : F) (hg : g ∈ DF 3) (hp : proper (tv g)) :
    ∃ w r, r < 2 ^ 180 ∧ RowSem r ∧ dom (tv g) (permW w r) := by
  obtain ⟨w, i, D, c, pv, op, hi, hD, hc, ho, hrp, hch, hd⟩ := d3_cover g hg hp
  exact ⟨w, _, tv_lt _, stream_spec hall i D c pv op hi hD hc ho hrp hch, hd⟩

theorem d3_caps (g : F) (hg : g ∈ DF 3) : Caps (cA (tv g)) (cB (tv g)) := by
  by_cases hp : proper (tv g)
  · obtain ⟨w, r, -, hs, hd⟩ := d3_row hall g hg hp
    apply caps_mono hs.1
    · have := cA_mono hd; rwa [cA_permW] at this
    · have := cB_mono hd; rwa [cB_permW] at this
  · exact caps_improper _ hp

-- G1 region: dominated by an image of a representative of group 0
theorem d3_highG1 (g : F) (hg : g ∈ DF 3) (h1 : 21 ≤ cA (tv g)) (h2 : 34 ≤ cB (tv g)) :
    ∃ s w, s < 23 ∧ dom (tv g) (permW w (tv (HF s))) := by
  obtain ⟨w, r, -, hs, hd⟩ := d3_row hall g hg ⟨by omega, by omega⟩
  have ha : 21 ≤ cA r := by have := cA_mono hd; rw [cA_permW] at this; omega
  have hb : 34 ≤ cB r := by have := cB_mono hd; rw [cB_permW] at this; omega
  obtain ⟨l, k, hl, hk, hd2⟩ := hs.2.1 ha hb
  obtain ⟨hsc, hdd, -⟩ := scope_spec 0 l (by norm_num) hl
  refine ⟨Ls 0 l, (wLoc (cvec (Ls 0 l) k) ++ wDih (Ld 0 l)) ++ w, ?_, ?_⟩
  · have hj := Nat.eq_of_beq_eq_true (allBelow_spec _ _ laneF0_ok (l / 10) (by rw [gNum0] at hl; omega))
    show scopeH (gSc0 0 + l / 10) < 23
    rw [hj]; rw [gNum0] at hl; omega
  · rw [permW_append, ← tv_imgF_words _ _ _ hsc hdd]
    exact dom_permW_trans w hd _ hd2

-- G2 region: dominated by an image of a representative of group 2
theorem d3_highG2 (g : F) (hg : g ∈ DF 3) (h1 : 10 ≤ cA (tv g)) (h2 : 68 ≤ cB (tv g)) :
    ∃ s w, 23 ≤ s ∧ s < 41 ∧ dom (tv g) (permW w (tv (HF s))) := by
  obtain ⟨w, r, -, hs, hd⟩ := d3_row hall g hg ⟨by omega, by omega⟩
  have ha : 10 ≤ cA r := by have := cA_mono hd; rw [cA_permW] at this; omega
  have hb : 68 ≤ cB r := by have := cB_mono hd; rw [cB_permW] at this; omega
  obtain ⟨l, k, hl, hk, hd2⟩ := hs.2.2.1 ha hb
  obtain ⟨hsc, hdd, -⟩ := scope_spec 2 l (by norm_num) hl
  refine ⟨Ls 2 l, (wLoc (cvec (Ls 2 l) k) ++ wDih (Ld 2 l)) ++ w, ?_, hsc, ?_⟩
  · have hj := Nat.eq_of_beq_eq_true (allBelow_spec _ _ laneF2_ok (l / 10) (by rw [gNum2] at hl; omega))
    show 23 ≤ scopeH (gSc0 2 + l / 10)
    rw [hj]; omega
  · rw [permW_append, ← tv_imgF_words _ _ _ hsc hdd]
    exact dom_permW_trans w hd _ hd2

end

def S4P (t : Nat) : Prop := cA t ≤ 9 ∨ ∃ m, m < 75 ∧ subA t (starAt m)

theorem cA_le_of_dom {x y : Nat} (w : List Nat) (h : dom x (permW w y)) : cA x ≤ cA y := by
  have := cA_mono h; rwa [cA_permW] at this

theorem cB_le_of_dom {x y : Nat} (w : List Nat) (h : dom x (permW w y)) : cB x ≤ cB y := by
  have := cB_mono h; rwa [cB_permW] at this

theorem crit_of_hit (g : Nat) (hg : g < 2) (t : Nat) (ht : t < 2 ^ 180) (w : List Nat) (o : Nat) (ho : o < 2 ^ 180)
    (hd : dom t (permW w o)) (hc : HitConc g o) :
    cA t ≤ 24 ∧ cB t ≤ 86 ∧ ∃ w m, m < 58 ∧ dom (permW w t) (targetT m) := by
  obtain ⟨h1, h2, ⟨w', m, hm, hd'⟩⟩ := hc.2.2 hg
  refine ⟨le_trans (cA_le_of_dom w hd) h1, le_trans (cB_le_of_dom w hd) h2, invW w ++ w', m, hm, ?_⟩
  have := dom_permW (invW w) hd
  rw [permW_inv w o ho] at this
  rw [permW_append]
  exact dom_trans (dom_permW w' this) hd'

section
variable (hall : HallP)
include hall

-- a high child dominated by a representative image, combined with any proper depth-three child
theorem transport (g : Nat) (hg : g < 4) (a b : F) (ha : a ∈ DF 3) (hb : b ∈ DF 3) (hpb : proper (tv b))
    (s : Nat) (hs : s < 41) (q : Nat) (hq : 10 * q + 10 ≤ gNum g) (hsc : scopeH (gSc0 g + q) = s)
    (w1 : List Nat) (hd1 : dom (tv a) (permW w1 (tv (HF s))))
    (hA : gTa g ≤ cA (gate (gOr g) (tv a) (tv b))) (hB : gTb g ≤ cB (gate (gOr g) (tv a) (tv b))) :
    ∃ w o, o < 2 ^ 180 ∧ dom (gate (gOr g) (tv a) (tv b)) (permW w o) ∧ HitConc g o := by
  obtain ⟨w2, r, hrl, hsem, hd2⟩ := d3_row hall b hb hpb
  let u := w1 ++ invW w2
  obtain ⟨l, k, hl, hk, he⟩ := lane_of g q s hq hsc hs u
  have hH : permW w1 (tv (HF s)) = permW w2 (permW u (tv (HF s))) := by
    show _ = permW w2 (permW (w1 ++ invW w2) (tv (HF s)))
    rw [permW_append, permW_inv' w2 _ (permW_lt _ _ (tv_lt _))]
  have hd : dom (gate (gOr g) (tv a) (tv b)) (permW w2 (gate (gOr g) r (tv (imgF (Ls g l) (Ld g l) k)))) := by
    have := dom_gate (gOr g) hd1 hd2
    rw [hH, he, ← permW_gate, gate_comm (gOr g) (tv (imgF (Ls g l) (Ld g l) k)) r] at this
    exact this
  refine ⟨w2, _, gate_lt_pow _ _ _ _ hrl (tv_lt _), hd, ?_⟩
  have h1 := cA_le_of_dom w2 hd
  have h2 := cB_le_of_dom w2 hd
  exact hsem.2.2.2 g hg l hl k hk (by omega) (by omega)
theorem lemmaC_and (a b : F) (ha : a ∈ DF 3) (hb : b ∈ DF 3) (h1 : 21 ≤ cA (gate false (tv a) (tv b)))
    (h2 : 68 ≤ cB (gate false (tv a) (tv b))) (h3 : 34 ≤ cB (tv a)) :
    cA (gate false (tv a) (tv b)) ≤ 24 ∧ cB (gate false (tv a) (tv b)) ≤ 86 ∧
      ∃ w m, m < 58 ∧ dom (permW w (gate false (tv a) (tv b))) (targetT m) := by
  have la := cA_gate_le false (tv a) (tv b)
  have lb := cB_gate_le false (tv a) (tv b)
  have la2 := cA_gate_le false (tv b) (tv a)
  rw [gate_comm] at la2
  simp only [cond_false] at la lb la2
  obtain ⟨s, w1, hs, hd1⟩ := d3_highG1 hall a ha (by omega) h3
  have caps_a := d3_caps hall a ha
  have hpb : proper (tv b) := by
    refine ⟨by omega, fun hz => ?_⟩
    have := caps_a.2.2.2.1 (by omega); omega
  have hsc := Nat.eq_of_beq_eq_true (allBelow_spec _ _ laneF0_ok s hs)
  obtain ⟨w, o, ho, hd, hc⟩ := transport hall 0 (by norm_num) a b ha hb hpb s (by omega) s
    (by rw [gNum0]; omega) hsc w1 hd1 h1 h2
  exact crit_of_hit 0 (by norm_num) _ (gate_lt_pow _ _ _ _ (tv_lt _) (tv_lt _)) w o ho hd hc

theorem lemmaC_or (a b : F) (ha : a ∈ DF 3) (hb : b ∈ DF 3) (h1 : 21 ≤ cA (gate true (tv a) (tv b)))
    (h2 : 68 ≤ cB (gate true (tv a) (tv b))) (h3 : 11 ≤ cA (tv a)) :
    cA (gate true (tv a) (tv b)) ≤ 24 ∧ cB (gate true (tv a) (tv b)) ≤ 86 ∧
      ∃ w m, m < 58 ∧ dom (permW w (gate true (tv a) (tv b))) (targetT m) := by
  have la := cA_gate_le true (tv a) (tv b)
  have lb := cB_gate_le true (tv a) (tv b)
  have lb2 := cB_gate_le true (tv b) (tv a)
  rw [gate_comm] at lb2
  simp only [cond_true] at la lb lb2
  obtain ⟨s, w1, hs1, hs2, hd1⟩ := d3_highG2 hall a ha (by omega) (by omega)
  have caps_a := d3_caps hall a ha
  have hpb : proper (tv b) := by
    refine ⟨fun hz => ?_, by omega⟩
    have := caps_a.2.2.2.1 (by omega); omega
  have hcs : 11 ≤ cA (tv (HF s)) := le_trans h3 (cA_le_of_dom w1 hd1)
  have hq := allBelow_spec _ _ laneF1_ok (s - 23) (by omega)
  rw [show 23 + (s - 23) = s by omega, hf_eq, popA2_eq] at hq
  simp only [Bool.or_eq_true, Nat.blt_eq] at hq
  rcases hq with hq | hq
  · omega
  obtain ⟨q, hq1, hq2⟩ := anyK_spec _ _ hq
  obtain ⟨w, o, ho, hd, hc⟩ := transport hall 1 (by norm_num) a b ha hb hpb s hs2 q
    (by rw [gNum1]; omega) (Nat.eq_of_beq_eq_true hq2) w1 hd1 h1 h2
  exact crit_of_hit 1 (by norm_num) _ (gate_lt_pow _ _ _ _ (tv_lt _) (tv_lt _)) w o ho hd hc

theorem lemmaC (op : Bool) (a b : F) (ha : a ∈ DF 3) (hb : b ∈ DF 3) (h1 : 21 ≤ cA (gate op (tv a) (tv b)))
    (h2 : 68 ≤ cB (gate op (tv a) (tv b))) :
    cA (gate op (tv a) (tv b)) ≤ 24 ∧ cB (gate op (tv a) (tv b)) ≤ 86 ∧
      ∃ w m, m < 58 ∧ dom (permW w (gate op (tv a) (tv b))) (targetT m) := by
  cases op
  · have lb := cB_gate_le false (tv a) (tv b)
    simp only [cond_false] at lb
    by_cases h3 : 34 ≤ cB (tv a)
    · exact lemmaC_and hall a b ha hb h1 h2 h3
    · have h4 : 34 ≤ cB (tv b) := by omega
      rw [gate_comm] at h1 h2 ⊢
      exact lemmaC_and hall b a hb ha h1 h2 h4
  · have la := cA_gate_le true (tv a) (tv b)
    simp only [cond_true] at la
    by_cases h3 : 11 ≤ cA (tv a)
    · exact lemmaC_or hall a b ha hb h1 h2 h3
    · have h4 : 11 ≤ cA (tv b) := by omega
      rw [gate_comm] at h1 h2 ⊢
      exact lemmaC_or hall b a hb ha h1 h2 h4

theorem lemmaA (op : Bool) (a b : F) (ha : a ∈ DF 3) (hb : b ∈ DF 3) (h : cB (gate op (tv a) (tv b)) = 135) :
    S4P (gate op (tv a) (tv b)) := by
  by_cases h0 : cA (gate op (tv a) (tv b)) ≤ 9
  · exact Or.inl h0
  right
  have caps_a := d3_caps hall a ha
  have caps_b := d3_caps hall b hb
  have hBa : cB (tv a) ≤ 135 := cntR_le _ _ _
  have hBb : cB (tv b) ≤ 135 := cntR_le _ _ _
  cases op
  · have la := cA_gate_le false (tv a) (tv b)
    have la2 := cA_gate_le false (tv b) (tv a)
    have lb := cB_gate_le false (tv a) (tv b)
    rw [gate_comm] at la2
    simp only [cond_false] at la lb la2
    -- one child rejects at least 68 maxterms
    have key : ∀ (x y : F), x ∈ DF 3 → y ∈ DF 3 → 10 ≤ cA (tv x) → 68 ≤ cB (tv x) → 10 ≤ cA (tv y) →
        10 ≤ cA (gate false (tv x) (tv y)) →
        cB (gate false (tv x) (tv y)) = 135 → ∃ m, m < 75 ∧ subA (gate false (tv x) (tv y)) (starAt m) := by
      intro x y hx hy hx1 hx2 hy1 hxy hc
      obtain ⟨s, w1, hs1, hs2, hd1⟩ := d3_highG2 hall x hx hx1 hx2
      have caps_x := d3_caps hall x hx
      have lbx := cB_gate_le false (tv x) (tv y)
      simp only [cond_false] at lbx
      have hpy : proper (tv y) := by
        refine ⟨by omega, fun hz => ?_⟩
        have := caps_x.1 (by omega); omega
      have hsc := Nat.eq_of_beq_eq_true (allBelow_spec _ _ laneF2_ok (s - 23) (by omega))
      rw [show 23 + (s - 23) = s by omega] at hsc
      have lax := cA_gate_le false (tv x) (tv y)
      simp only [cond_false] at lax
      obtain ⟨w, o, ho, hd, hc2⟩ := transport hall 2 (by norm_num) x y hx hy hpy s hs2 (s - 23)
        (by rw [gNum2]; omega) hsc w1 hd1 (by show 10 ≤ cA (gate false (tv x) (tv y)); omega)
        (by show 135 ≤ cB (gate false (tv x) (tv y)); omega)
      obtain ⟨m, hm, hsub⟩ := hc2.1 rfl
      obtain ⟨m', hm', hsub'⟩ := subA_permW_star w o m hm hsub
      exact ⟨m', hm', fun p hp ht => hsub' p hp ((hd p (by omega)).1 hp ht)⟩
    by_cases h3 : 68 ≤ cB (tv a)
    · exact key a b ha hb (by omega) h3 (by omega) (by omega) h
    · have h4 : 68 ≤ cB (tv b) := by omega
      have h5 : 10 ≤ cA (tv b) := by omega
      have h6 : 10 ≤ cA (tv a) := by omega
      have h7 : 10 ≤ cA (gate false (tv b) (tv a)) := by rw [gate_comm]; omega
      rw [gate_comm] at h ⊢
      exact key b a hb ha h5 h4 h6 h7 h
  · exfalso
    have la := cA_gate_le true (tv a) (tv b)
    have lb := cB_gate_le true (tv a) (tv b)
    have lb2 := cB_gate_le true (tv b) (tv a)
    rw [gate_comm] at lb2
    simp only [cond_true] at la lb lb2
    have := caps_a.1 (by omega); have := caps_b.1 (by omega); omega

theorem lemmaB (op : Bool) (a b : F) (ha : a ∈ DF 3) (hb : b ∈ DF 3) (h : cA (gate op (tv a) (tv b)) = 45) :
    cB (gate op (tv a) (tv b)) ≤ 33 := by
  by_contra hc
  push_neg at hc
  have caps_a := d3_caps hall a ha
  have caps_b := d3_caps hall b hb
  have hAa : cA (tv a) ≤ 45 := cntR_le _ _ _
  have hAb : cA (tv b) ≤ 45 := cntR_le _ _ _
  cases op
  · have la := cA_gate_le false (tv a) (tv b)
    have la2 := cA_gate_le false (tv b) (tv a)
    have lb := cB_gate_le false (tv a) (tv b)
    rw [gate_comm] at la2
    simp only [cond_false] at la lb la2
    have := caps_a.2.1 (by omega); have := caps_b.2.1 (by omega); omega
  · have key : ∀ (x y : F), x ∈ DF 3 → y ∈ DF 3 → 23 ≤ cA (tv x) → 34 ≤ cB (gate true (tv x) (tv y)) →
        cA (gate true (tv x) (tv y)) = 45 → False := by
      intro x y hx hy hx1 hc1 hc2
      have lbx := cB_gate_le true (tv x) (tv y)
      have lby := cB_gate_le true (tv y) (tv x)
      have lax := cA_gate_le true (tv x) (tv y)
      rw [gate_comm] at lby
      simp only [cond_true] at lbx lby lax
      obtain ⟨s, w1, hs, hd1⟩ := d3_highG1 hall x hx (by omega) (by omega)
      have caps_x := d3_caps hall x hx
      have hpy : proper (tv y) := by
        refine ⟨fun hz => ?_, by omega⟩
        have := caps_x.2.1 (by have : cA (tv x) ≤ 45 := cntR_le _ _ _; omega); omega
      have hcs : 23 ≤ cA (tv (HF s)) := le_trans hx1 (cA_le_of_dom w1 hd1)
      have hq := allBelow_spec _ _ laneF3_ok s hs
      rw [hf_eq, popA2_eq] at hq
      simp only [Bool.or_eq_true, Nat.blt_eq] at hq
      rcases hq with hq | hq
      · omega
      obtain ⟨q, hq1, hq2⟩ := anyK_spec _ _ hq
      obtain ⟨w, o, ho, hd, hc3⟩ := transport hall 3 (by norm_num) x y hx hy hpy s (by omega) q
        (by rw [gNum3]; omega) (Nat.eq_of_beq_eq_true hq2) w1 hd1 (by show 45 ≤ cA (gate true (tv x) (tv y)); omega)
        (by show 34 ≤ cB (gate true (tv x) (tv y)); omega)
      exact hc3.2.1 rfl
    have la := cA_gate_le true (tv a) (tv b)
    simp only [cond_true] at la
    by_cases h3 : 23 ≤ cA (tv a)
    · exact key a b ha hb h3 hc h
    · have h4 : 23 ≤ cA (tv b) := by omega
      rw [gate_comm] at hc h
      exact key b a hb ha h4 hc h
end

-- ===== counting under masks =====
def cntM (y : Nat) : Nat := cntR y 0 180

def orM (M : Nat → Nat) (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun c acc => Nat.lor acc (M c)) n
def sumF (g : Nat → Nat) (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun c acc => Nat.add acc (g c)) n

theorem sumF_succ (g : Nat → Nat) (n : Nat) : sumF g (n + 1) = sumF g n + g n := rfl
theorem orM_succ (M : Nat → Nat) (n : Nat) : orM M (n + 1) = orM M n ||| M n := rfl

theorem cntM_disj (x M1 M2 : Nat) (h : M1 &&& M2 = 0) :
    cntM (x &&& (M1 ||| M2)) = cntM (x &&& M1) + cntM (x &&& M2) := by
  unfold cntM
  rw [cntR_card, cntR_card, cntR_card, ← Finset.card_union_of_disjoint]
  · congr 1; ext i
    simp only [Finset.mem_filter, Finset.mem_union, Nat.testBit_and, Nat.testBit_or, Bool.and_eq_true, Bool.or_eq_true]
    tauto
  · rw [Finset.disjoint_filter]
    intro i _ h1 h2
    have := congrArg (fun z => z.testBit (0 + i)) h
    simp only [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_iff] at this
    simp only [Nat.testBit_and, Bool.and_eq_true] at h1 h2
    rcases this with h3 | h3
    · rw [h1.2] at h3; exact absurd h3 (by simp)
    · rw [h2.2] at h3; exact absurd h3 (by simp)

theorem orM_disj (M : Nat → Nat) (n c : Nat) (hc : n ≤ c) (h : ∀ a b, a < b → b ≤ c → M a &&& M b = 0) :
    orM M n &&& M c = 0 := by
  induction n with
  | zero => show 0 &&& M c = 0; simp
  | succ n ih =>
    rw [orM_succ, Nat.and_or_distrib_right, ih (by omega), h n c (by omega) le_rfl]
    rfl

theorem sum_cells (x : Nat) (M : Nat → Nat) (n : Nat) (h : ∀ a b, a < b → b < n → M a &&& M b = 0) :
    sumF (fun c => cntM (x &&& M c)) n = cntM (x &&& orM M n) := by
  induction n with
  | zero => show 0 = cntM (x &&& 0); rw [Nat.and_zero]; exact (cntR_zero_bits 0 0 180 (fun i _ _ => Nat.zero_testBit i)).symm
  | succ n ih =>
    rw [sumF_succ, ih (fun a b h1 h2 => h a b h1 (by omega)), orM_succ,
      cntM_disj x _ _ (orM_disj M n n le_rfl (fun a b h1 h2 => h a b h1 (by omega)))]

theorem cntM_and_le (x y M : Nat) : cntM ((x &&& y) &&& M) ≤ cntM (x &&& M) ∧ cntM ((x &&& y) &&& M) ≤ cntM (y &&& M) := by
  unfold cntM
  rw [cntR_card, cntR_card, cntR_card]
  constructor <;> apply Finset.card_le_card <;> intro i <;>
    simp only [Finset.mem_filter, Nat.testBit_and, Bool.and_eq_true] <;> tauto

theorem cntM_or_le (x y M : Nat) : cntM ((x ||| y) &&& M) ≤ cntM (x &&& M) + cntM (y &&& M) := by
  have e : (x ||| y) &&& M = (x &&& M) ||| (y &&& M) := Nat.and_or_distrib_right x y M
  rw [e]; unfold cntM
  have := cntR_or_le (x &&& M) (y &&& M) 0 180
  have e2 : ∀ z, (z &&& M) &&& M = z &&& M := fun z => by rw [Nat.and_assoc, Nat.and_self]
  exact this

theorem cntM_mono (x y M : Nat) (h : ∀ p, p < 180 → x.testBit p = true → y.testBit p = true) :
    cntM (x &&& M) ≤ cntM (y &&& M) := by
  unfold cntM; rw [cntR_card, cntR_card]
  apply Finset.card_le_card; intro i
  simp only [Finset.mem_filter, Finset.mem_range, Nat.testBit_and, Bool.and_eq_true, Nat.zero_add]
  intro hi; exact ⟨hi.1, h i hi.1 hi.2.1, hi.2.2⟩

theorem cntM_le_mask (x M : Nat) : cntM (x &&& M) ≤ cntM M := by
  unfold cntM; rw [cntR_card, cntR_card]
  apply Finset.card_le_card; intro i
  simp only [Finset.mem_filter, Nat.testBit_and, Bool.and_eq_true]; tauto

-- complement counts inside a mask that lies within V
theorem cntM_compl (x M : Nat) (hM : ∀ p, M.testBit p = true → 45 ≤ p ∧ p < 180) :
    cntM (rect x &&& M) + cntM (x &&& M) = cntM M := by
  unfold cntM
  rw [cntR_card, cntR_card, cntR_card, ← Finset.card_union_of_disjoint]
  · congr 1; ext i
    simp only [Finset.mem_filter, Finset.mem_union, Nat.testBit_and, Bool.and_eq_true, Finset.mem_range, Nat.zero_add]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      have := hM i h3
      rw [rect_bit x i this.1 this.2]
      cases hx : x.testBit i <;> simp [h1, h3]
  · rw [Finset.disjoint_filter]
    intro i _ h1 h2
    simp only [Nat.testBit_and, Bool.and_eq_true, Nat.zero_add] at h1 h2
    have := hM i h1.2
    rw [rect_bit x i this.1 this.2, h2.1] at h1; exact absurd h1.1 (by simp)

def compData : List (Nat × Nat × Nat) := [
  (0x5018a01a00000, 0x4627018a81243159144a6b0392c166045014d44000088046204108940a, 0x4ef63104004ef63180004ef63004044ef63100044ef63100804ef63004634ef63004c04ef63000084ef63000844ef6300100181201052948003185291a4001852933000105293300018509031801852900003180c6400020006738001000c840000000c84800318463001821800600182180c04a4001840303000185203240218480002431840048003104c642402184040024218004002421808003000184c6301821000630182104c033002104c0300021852903000104c90300010526025201052000180184c933000184091a52000409001801852633000104861a521001201a520100094b0021040606c00084600030018006003601800306000104c034802104801a52000089325210000900300184c000360184604c8031840044802104044a5831840003180104c64ec00084034e000104064b183000634ec0310400031800052933182004c604a40104c004a400052034a4000406361800040634a40100064ca401000334a421008034a400000944a420040434a42004c04ca43104004a763180004ca431800034a400008634a420008444a421000434a42001004ca42000064ed830840044a42000084e2400040306300004c606f600046306f60004c036f62004604ef63004004ef63100004ef60000064ef63000044ef6300080),
  (0x2810521800000, 0x150ac4a270488c0e2d3002c8a43439a9140575988044220380144a, 0x37b4840026f6900006ded213181bda4064037b480c62000909906030c1320c9498264198c004c8300090806300101018cc01020300004806732520080060012032060018264181800400203600800203001318cc000263180c004c82300009904030c11949b0002200b00004802012909900030c13201b0002518018004c606000098c06312000c69498264018c004c62252601904061211940c618033101b484630318001906948c1000929180001b6c3044004a40098c0948c1194129180329252480c806f6000c62c60003189bda4200037b4800026f69018c0),
  (0x402c8e16c0020, 0x944b1192616753580c4a2f1cb2c04422615840c0351d2142a, 0x4a529d8421001294a760108004a529d8802001294a762100004a529d8002319294a760100c64a529d8800319294a76000127000090084249c63181221092700c664884249c60199221092718c064884249c0031a4210927018069084249cc001a421092702520c084249d2048302109274a400c084249c8420000008c7210800004031c8420002000c700009008424100040122108040200048842011000012210804000060084249c000240108527001204884218c090012210863480004884218c004a52108400024094842100120025210840018c604800249c63181201012718c604880049d0840000000c73180960021180c03258100460018c9604201800049a421080002406908420012001a4210800000c06084249c060018210927300006084249c630192010927180664880249c031992210127018c060842318c030182108c631800608423180948242108004812090842001290024210800318006004249cc03018200927018c06084049d08402400080442100900400110840242000043180690042310c031a42008c4018c690840310e73a520000c7421009000019d2901a4010863481269080218c0949a42100634a400c00423192048302008c602520c084031929027601080048129d8802000094a76210000498c0c0002318c930300100c631920c0800318c632640001274a520d800218d2948360100634a520d880018d2949b60108004a526d88020012949b62100004a529d8002001294a760100004a529d8800001294a760000c6),
  (0x4050ac1910001, 0x2a118ac5a4355854160523945d60050500042819100ace005051544a, 0x4a53b48001085294ed20000634a53b4800300d294ed2000c604a53b490c0009294ed24300404a53b490c2001294ed2548000000004952318c031a465488431806919522188630246548c4218c690152318c601a4c54884318c093152210c031a4c54886218c0931522188031a4c548c42180693152310800330c548c630180c3152318cc0030c548c63300123152210c06048c548862000d231523108094e00548c63481380152318d290600548c6321080014c000c000012340842000004952108484200053006021080014c300000000c548c63001090100318c080240400c63400090100318c004a46000c63024091800318d200246000c6300129480010840902520004214800948001084004a40218c63024090086318d200240218c6318c690152000c631a4054806018c69015230010840005300003180c48060084c03312018401018cc48061080c60306030063300cc180c300c63024c5480421806931522008063306030c6000c693152210120048c0008430241230002188004c8c000c42000cc0152318c060300548c633000c0152318c063300430c63300cc010c318cc60300430c633180c0152018cc03300548c03018cc01523180094c80000c63481320000318d290480000c634a4123000018d204c8c000c0302532300031810844804000033181230cc0108c0348c330802421120100018006348c3308404211201003000e73a52530000421120146000129048c2180424813230862008094c8c2188404a418010c018d204e00430c03498d8010c000d2906d20000424813b48002008094e00430c60324d8010c0180094ed200084031938010c3000c634925480004a53b0000018d294ec0000c034a53b1800000d294ec0000c604a53b18000181294ec6000c004a53b0086000d294ec02180604a53b00863001294ecc0000424a53b30002009294ecc0008404a53b48000009294ed20000404a53b48002001294ed2430000),
  (0x284c641900000, 0x2a118944e09158b40e45219801687352280aeb00188044021380144a, 0x37b4880026f6900008ded222181bda4044837b4808620009111260012022520024424a400408894a40411129030c22252948c444a418008864e000110c906002224d80004449929308894318011129630c2224cc618044a652008864ca4011126948c022518c00044a4004880318008100c6000022252061040019802080030009009060012022460010424a4003088930006011294a4020012948c00024180080030186108c406c0200060600443258000886481801112660002224db0002200c09488890018611120d80022001b00024183000088030300110c0c00022180c6240018d2930889025260112463002218c0c24423001b4884303186008c694802000d2900000258c000894ca4610004948022181b61822002523000044a46108c0948c011892924044837b0000036f6000863c6000218dbda4400037b4800026f69010c0),
  (0x282c601900000, 0x251509c46091581cc02d2290c1687352280aeb0018804402b380144a, 0xded210009bda4000237b4848606f6901120ded2021880024224a4004048948009011294808122520618244a529184894a52609128630012252c618044a6523008946300011290012100c60020203180000489481840800660081000c0010224a400480483000901123000c1224c0018044a529004004a5230000906001000c0618223101b004001ec0008003030012192c000243240c004893300009126025212240061824483000044036c00088600600121818000243012930489031890006363001218c9498044901848446003690886094801000cc6180231a52000004b18001129948c10009290024302523000044a46088c0948c011892924044837b0000036f6000863c6000218dbda4200037b4800026f69010c0),
  (0x40285a1d00008, 0x4334928e654751150e91118b46e4b24b0d9a8535a29962530080044231300d42a, 0x6d3b08c0008369d84600801b4ec2308000da7612000006d3b0200000369d84021089b4ec0018c64da76020842201200a463188080052318c804800918c640198148c63224890a463191264850318c8c2302918c626198048c63248d20206319300c052318c80480230006002401180600012008c6000008004c018c0040026180600200130c600012000c63190040052318c404800610c620240030c43101200186310806004c318c803000918c6448d2048000000cc09042108066040318c804a42018c644992100c632312c00c0010189600601000c4b0031000061181300420308c0984010184604c2100093240418c6402701008421013b0802108986600c21085204829000006018148c632489209800002469048000012348080000061b0100842148d20804210a46900821085236020084229264000c6326c1b0980000364d84600001b06c2308422da76100000060180984211369d80800001b4ec0010844),
  (0x38043e1100000, 0x8b128ac12450390c164b451a80a6200100144a, 0x6f630037b100dbd8863dec4606f601a77b018dbd812363069480034a40c1812060d2003066301823252910120609264a44903003325801a4c0d840306c2300302018181181800c06d80601e0033036018c0c608c69486006d230018c02532908069484604a40026520241bd8800c600636f6001b7b00c7bd80c0),
  (0x38109e1930000, 0x10b11894561b08824ae4d0391486600592cd48a492200a6200100144a, 0x4a53b108004a53b080064a53b088634a53b088c04a53b008694a53b008c64a53b00923018c010929300c01092931800109292108c109290012010803001201086018c600840918c60089200000010929018c010809300c010809318001080900c69080091806908009018c010920300c01092031800109200012c1080001080088c920080088c918c0910009010800892620080089260252008406481200840621000108c9210001092621080088c600c6908920180690892002520088c048120088c0018c0108c6300c0108c631800108c64a4001080618c09109204a400108c03192008406324c008406498c00840631920088c0324c0088c0498c0088c00000c108c90000c109264a5201080000018100064a520084030001b100034a5200886000018108c00001b108600108c088c62008c088c62100c108c6018d208006300d20800631812100060013b10000018d2088c0300d2088c00253208003481320800331812108c02252c004064912c004064a412100034a52c084004a48c00806025320886048132088604a412108602108c00929318d200009318d2009204a41b100004a532100004a53b080004a53b0000642118008c64a53b008634a53b008c0),
  (0x7038c21d02010, 0xeb2a92c94547542c462d1b894c0cb1799d8a2b211a0e44c71420186a60008402a, 0x1e631b6108400798c6d8002101e631b6010040798c6d8800101e631b6010800798c6d8802001e631b6210000798c6d8021181e631b6100460798c6d8420181e631b60004c6798c6d8020319e631b61000c6798c6d80003240318c02108c9000c6008423240601802108c9018c0008423246018d22108c918c03488423246318122108c948006608423252030182108c94980060842324c001a42108c9300c090842324c600242108c978000c08423240318c00008c900c63000403240318c02000c900006008423240030002108c901800008423240631800108c0018c6008023000631802100c0000c6008423180601802108c6018c0008423180001982108c0000c0608423000600182108c0480064884200120301221080049800488420000630000108c901806008023240031802100c9018c6000023180631800100c6018c600800318c001981084c0300c060421300c600181084c03000660842180c030182108603180060842181200198108460480c0604211812600181084603000690842000c0302421080031800908420006318120108c918c03488023246018d22100c9318c660002100c63198010040318c660800101860024108800600c0904410018001a420840048000608423240000302108c63000090842319263198000440498c660020101263198100040498c060021199260198100466480c660420198c631a4010800318c690802000c631a421000060c60900211998300e41004666006390420199e000240000c9618c0900210118601a4100404600c690420011e0003621080070c6390000021863024008463618069040118d8031a4108063618c6900210018631a4100400618c690420001c318e400006760000c042131980003021086678000c0421199e0003610846378006d8421001e0303610840079800d8421000c630240108c63180690802318c031a42100c660c63900003258631a4000008318c6900003258631a4000067798c0d8042001e601b6200800780c6d88400018631b6000800618c6d80400018631b6200000798c6d8001001e631b6008000798c6d8400001e631b60000c6),
  (0x702cd42002010, 0x759549623168dc945475096164961b345e6762908d0721b0b0442035131c50865831802a, 0x1e631aa108400798c6a8002101e631aa010040798c6a8800101e631aa010800798c6a8802001e631aa210000798c6a8021181e631aa100460798c6a8420181e631aa0004c6798c6a8020319e631aa1000c6798c6a80003240318c02108c9000c6008423240601802108c9018c000842324c018d22108c930c0348842324c318122108c948006608423252030182108c94980060842325e0002a2108c900c66000423000330c02008c001863008403000331800008c001866000023000630c00008c000cc6000403000619800100c0018c3000403000331802000c001866008003000630c02000c0000063084230000300c2108c001800308423000318c00008c900c63000403240318c02000c901863000023180330c00100c600c66008003180001802108c9000c0008423240600002108c9018c6000422800631802008a0018c6008402800031802108c601806008423180630002108c63000648421300c030121084c03180048421301200192210800480c048842001260012210800018c0000423240601802008c9000c6008403240631800008a6018c6000402980631802000a6018c03004229806018c2008a6000c630840298c00198210860300c060842180c600182108604800660421181203018108460498006042118186001e108800600c07844100180019e208400318c060042200c60198200880300c660840200c318120108c930c0348802324c018d22100c930c6060042318c300d82008c63006360840318c630120084a63180648401298c031921080a6318c660002100c63198010040318c660800100c63198010800318c660802000c6319821000048c60480213252300d21004c948063484203252000182108c9498c660001101263198008040498c660400101e0002a210800318c060042198c60198200866300c6608401998000241084c678006a8421001e0302a10840079800a842100186319e008400618c67840100186319e10800060000a8842199e0002a108466618c07802119986019e100466600c678420199e6302a01080079806a8802001e031aa210000618c6a80020018631aa010000618c6a8800001e631aa000400798c6a8020001e631aa100000798c690000325e631aa0000c6),
  (0x300c861b00000, 0x1c4a650490cd48b15aac4e00118800a4715114960a010a0c44245100444a, 0x7df630000fbec40009f7d800033efb108c07df601186fbec034818000c693256018d26031831a4c9000630192000c661bc0018c03480031a4004a46001100608001a00018cc64a402000c80006348cc000c6933c0018cc033802000c05804348c0c00c463014010d26001801a4c00306049800608692000c1892400182124c0b8040018ca0084630012001264a520000c0048024912b008461aa40100030036100c400604031000d802613d291800032920018c006c003112b000693001800904031821188063063480c9480692252900d224a5221a4095b00230dec60840019d2000067dc00000c674840011f7000231b280008c64ae400186fb000230d5090800125350090054a4300006748023112bd800312a52104605424211800bec211819090046102f8108c07de400008c8600040190c002703e5200d2065f600008fbec00009f7d880003efb008c0),
  (0x4010521700000, 0x29c226503828d4ab858144a2f2388c564b141311420200a89422, 0x18c7b1800618c7b1980018c7b180c418c7b190c018c7b188c318c7b1812218c7b18cc218c7b1892018c60199261800c1992600c6c01926000180192608c0000c06184000180308c60008061840019802108000180608c600008618400198801080c00c0318c6018cc3180001992600c600192618c691800618c69198001800c18cc400c6c010c3180091892600c69019220000c0192618c721800418c721880218c7219000000120112418012188c400c72010c20001b008c21801218126180151810418c72180c318018180e200c720192018c721812000c750110000c78008e018c7218cc000018011041801b180c400c7b010c018c7b1806218c781810018c7b1886018c7b180c0),
  (0x2824821a00000, 0xe113008e1605000945e0a2522880101592cd420210985c88150089822, 0x7a52f788047a52f798007a52f78cc07a52f780c67a52f781230000f01926420000192602520019263000c31926018cc0192648009499267800079926498c049926318c931926210000188648c00018064100000c864200001806318c00100631800318044100900c04224c0010060000c011240000901926518c00080651000318047a40000c030000f0110448c0049804325200100348c0049880518c000086424c000c067a00000c06018c00192602520010c67900048c046252000803025200192362520000833000c310c4318c0310c4018cc010c448000499267a520000067180060c043000931126018c90192460000618c44800948cc46240060c807800078cc4498c048cc44800948926318cc310047a400798006000c608c40252f019203252c31800498c9480c6798c94800632529318c04a529498003252c310c0618cc60804718cc600064a52f488604a52c48cc0618cc600c47800f781264a52f481206252c608806252f61000798cf780627a52c790006252f601007a52f788007a52f780047a52f78080),
  (0x402c7a1300820, 0x42c064a3a9ac4625178e4564c2b1a8e90a21008402a, 0xc492930421003124a4c010800c492930802003124a4c210000c49293000221b124a4c010086c49293080021b124a4c0000c948063188423241200002108c94a403188423252918062108c94a46300842325ec000c2108c97b00600842325ec30002108c9c00093084232700480c2108c9c012900842325200240210843481200084210c0c00002108c934800304210012018c60008c948063180403252018c62000c9c0000000002201200002108c67800930842001e0480c21080060000308423258001802108c9600c000842325ec000c2108004c80900421001324800108400600063084221980300c210886600c60084221a404a402108007b00900842001ec4800210800600c6000423252918c00108c9600c0308023252918062008c960006308403252900c62100c9648c60002118192300c1004606480630420182a918c60000887b1203080210dec024c210043c012030802219ec300c200886c000930840219ec018c210086c00c63080021b004a4c000843c01293004010f004a4c200043c01290004221a4c3180010886c01263000221b00324c010086931290004210f12480c200800c4809308400030c4a4c010800c4929000420030c4a4c200800c312930840002d2318c000008b48c63000011f124a4c000800c492930040003124a4c200000948c630000327124a4c000086),
  (0x3818861a00000, 0xd6071688c4a0b0283cd400153ad142021018560a11218100e251a0042c, 0x4bdef488044bdef498004bdef488c04bdef490804bdef480094bdef480664bdef480c40000f018c948000498c930009318c902529018c932520318c903de0018c91940019804194001988022000010462200001809198c00008922006010060000f00ca64bc000080300009018c90000c018c62200900c0649800488801a4c0010091a520000491a52000809480004908630000318c94a0003100643c00010063000930c86238c001006330c0010064b0004884048000488c9018c900ca6018c6018c63000c308864b0004880430006310c923d2000c06339800080330009308c9318c0310863318000046331800080602520018c90252900c6603180018c63252030c6603de000c66318cc30880330c631040330c63180002529018c4330c6310041b9291980033de0000094bde0000060318c00c6432529310804800f480c9498c9480c6498cc480864a529480093318c308044a52f480434a52c4806603def018c04a52f480c04b18c480444bd8c4900033def310004b18c4800833def30c604bdef488004bdef480044bdef48080),
  (0x381c982000000, 0x350ac866b1189c4045168c4541303825004f43cac1ee50298816eb20108000a36009144a, 0x4cde20113378c604cde600133780084cde230133780664cde031000498c948006324c0218c9020c632409298c904006324ca018c94800228100010c00014002464018c03008401800480c6001231980049806480021240028cc9001003240029869001031a4004180900103319200108600106198c040c06000c63180078066020860180078c06000863240a00c69028060240a00cc6028061980a318041a0c6180c0018c9029030180830cc4020c6190694980032404024100180604c03018ce0080602526010ca3180002006324ca010660292319069488c042400225290006932004318c8200c6328c4010ca000c91a5203100e50c0402926300ca48c604a4a0024ca300c4428c0210ca310c04a922100ca400664c800024ce508044c0003193300066041833001061860339821812e5006404de318013798004b940020d3790004cd8400133788004cde001133780c0),
  (0x702ddc3400000, 0x4198c06434483546490281c4e29269144a0025a14224732880cea717b148060012ae16cb252281022802108c42060a0142a41120d44c443114ca2, 0x26f4a5e1000409bd29784020026f4a5e0180009bd29780000126f4a5e0008029bd297804000a6f4a5e2000029bd29780401026f4a5e2100009bd297800020a6f4a5e0000c09bd29780031826f4a5e0018009bd29780440000400082198c400008008663100021002198c400100008663100000182198c4000034886631000018c2198c4020c0008663120000002198c452400008663114000142198c4010002080021000480021800421000000042100002400010a220084008440000002400008c401809000021080001800018c40140300006308000012218c6200120308600080021002190810280000046200802100011080000c0008642100001002198c200080008663080800000198c00000078863001400000210c64020000046620809000011188200000408661880518c00018c100084408630000500002118c4000060086431006000021988480000008001900800001118c2020c02040020804019020006200084008663000518c00118c00146300806300000010218cc450000004433100800002118845180000800211060008210004000063086418800019021886201469000042800f0000011480020c04040300000000c2198c480000004003114000001198649800000400190083000111082000c6408600088518c00018c0000c630860200080190010060001290086210000318c2190005000030800310094800200844518003080001088300000108203463000052000631802010804000000866310093000201084418000084321104000c000c84418000044620900000c211862500c0480400080042002190800008940860181062100111000418840084300146000c000084020c600004209490180000c0202124004042000c31800108404000030843311c6000c100004524000044320940018c00106250000488431880a3180001081028c60040420100210c010c804008430044180003198218800020c000806311c6000c0000444a4c00084001146300c200002028c6000442000c3180001840031260040210146000c21180000009488603114a300010008250006480031894001942000625180050843001492100110c004a4c000800211490000219804498003006601146000c0118044a4c00080401146018c00008200009788601880831901000625180630004009060190210002028c6000063010518cc000cc051800300462010518cc001860000c96086010120018c0010c403d2000404209ca3000100042498004806600929000c019802438c0004040094c300010100203129000021054a000c010c805008448043181480012010c6049800488660012001920008c448006480403112001922000c47000650400189460194200002001296086000606000c010c044a5202080001108300c000c82420c0300041894f3000100c02730c0004400092900120198014a4003006620129001211980050000480663114a300c000082500067804018a06000c011802524064044000929001201984000129788600012402520000848300000843011c001980008628300000446009c60018010c027300030043009ce30001008027180650400009ca300c000042530c03000400a060018008c02830003002300946318c200080518c630804002000018011862520c048003189c0019c010062518c650800005251a520000c003d29000042026f0000110c027180660002009cc300c0008027180660040009cc300c010002518c6508001012921120190007300050443001463194200800518c650840002000018010cc4528c6300002054a318c100080728006004310260001e010c629a40048043009cc0018010c01528c6300003014a318c0100804b86348006001294990200002530c6300040054c318c101000528c6300042014c318c001800530c6300440026c00180000044a0c94800020a4c0018008c01528c6480031826f4800200004728c650400101cc2118010c00730c650402001064a5e210000730c650440001ca3198000840728c66004010260025e0000c499809780000126f480c000004730c660002005cc31980100017312650400005ca3258000041730c660042001294a5e018000730c670060001494a5e11000053d29480021024f001e0198009bc0078046002494a520000049bd264040000a6f211e008c009bd265080000268325e0000629a8c9780002026f319e0010009b129788000026f4a580000809bd29600040026f4a5e1000009bd297800000a6f4a5e0000409bd29780020026f4a5e010000),
  (0x301c9c1e00000, 0xd605039940023168941eab23a94d42a45080846415829d6e00121904a4251a0502c, 0x4bdef488024bdef480064bdef498004bdef480c34bdef490c04bdef489200000f0192648000499263000931926018cc019260252901926325203192603de001926194001980419400198802100001086220000108322000018062100900c042200601003420000100649000310042200900c031a4c001006318c0010060000c00d24228c000c061a520008064bc000080300009019260000c019040000f00d0449800488044a0003100343c00010031a52000086238c001003330c00100348000490c430000319263000930cc423d2000c034b0004880248000489263000c308c44b000488803000631126318c030cc4018cc00cc4318c0310c333980008033000930926318c63100402520019260318000cc603180018c30252900cc3018c9019244b18000083318cc308043252030cc303de000cc3330c631002330c6318000252901922330c6310801b929198004bde0000060318c00cc24800f48126498cc4800632529310c0498c9480c64a52948006498cc480c43318c308024a52f480624a52c480c33318c30cc04b18c4808203def019204a52f481204b18f480044bd8c4900033def3100033def30c604bdec480044bdef480024b18f481004bdef488004bdef48080),
  (0x301c7a1a00000, 0x462d038144a600583c006a153ad1420030ac14e011218100e251a0042c, 0x4bdef490044bdef480094bdef480664bdef48cc04bdef480c44bdef498800000f018c948000498c949800318c93000c318c902529018c932520318c903de0018c9218000188622000018461a400018092200001809198c0000890000c010c600009018c90000f010a64bc0000c03328003184022009010064980048c801a52000049328003180430000318c91a52001009018c6010c648000498864a0003180643c00018064b00048c404800048cc9018c9010a64b00048c043000c31086318c031086331800004623d200100602520018c933980010034bc004980030009310c903180010c602529010663318001006325203106603de00106602529018c4318cc3108033de0000094bde0000060318c010644800f480c93252931880498c9480c633d2931800498cc480864a529480093318c310603318c310044a52f480433398c318004a52c4806603def018c04a52f480c04b18c480444b18c4800833def308604bdef480044bdef480804bdef49000),
  (0x3844781a00000, 0x546012824266a118c40e45218ae56622782d140025814d80205088804a, 0x7cd240000f9a440011f34800043e69108c07cd201240f9a400319f34804620009209260012212520024804a400410494a00620926024641252f00082325e00104930146208c90400411920800824980a308494814620928528041192a500824992a010494a523109290012400c600240230d0030800301402000900122018c04988001000010494a4002080900100120c0518400180941004000041092904004000c001882499e001040302601000678004118004a482180003100948200208c00200411928000823240a00846481002092640004124c05004249929180004a94020006028c211889480800240a31049029c0100065280411809480824812a480031a523109207a8c20800949c024012918049229c6100044a804118c9510023192a3000630269108c0539020100f980800012a000494b1c600008538c21180a72442181f2000004b1c80010054d240000c720023818e3004623e69100007cd200008f98002319f23004903e69008c0),
  (0x3834b42b00000, 0x1a8ca6b03a0d52692182400ab128ac2645138800a23188a8c42d23abc1e0a2a80a564f202445087939b1d6e516381144a, 0x717880010e2f000061c5e6000038bc0318c7178c6300e2f018c21c5e231803000c619860018c618803318c300143318c228c8631829018c630900318c600186318835008631810018c63014a30cc60294631880524c6318600084030804200031800420061100c60004040c0018c00218601800230c624806000c60008c6008e02000610006300c2000c618c4d0080018800318c01000430cc0480c0018672800030800218c30300600060028003184831000109063000000126010824008318c4a0086318220180031180430c61418c300008280063014018c6604003000c33100618c65180c61052930000000a3318c00200631800298663000818cc600106018c05280001871000003000f180841146431803524420000900c6630008198c4001061988052860010090186618d80018630314300040010c631800318c62000f00cc402526000805006630c68300c31098a1000201cc330c838800318c6a500031890621860020c618c835200318c4a48c6300d40018c604000198c0318c331008018c63014918c641a9e000840528033100c5006610d8a00c6202520318804a4633107150000209ac10c601c184000008bc00010717800010149318c01c5e20000073066180117980000a2f200000318619800830c31801178c6600e2f018c0),
  (0x3834902100000, 0x2a15a0c1223138144a6a038008660329a5568b0103c8e87228894a8a203ac500a311a1c04a, 0x7cd20000cf9a480009f34980003e69010637cd202184f9a406301f34908600008310c6001063188800cc630d80018c633c0031866780063186080086318100188630146318c63246631889500c631929190c6329c0218c6001201144020c0031800498021000920084400c400060010063180a0180030008010c400084218c0018c031800210c620126300043206000cc080080018ca0100030006310c40280620c609808000c0a0108332400318064a460000c9000c618d20018c600128300804a404000c65180001900018c332000318c302804318604a4c2180c0018c630100218c602006218c651880011e0018c01bc00318603200420cc051884190c8010861a546000635380400060418843112a4800211948200804a80420c695100418c124980001923018c4028c63180948c06308ca30086229c620002328c4218095000631929190c603d4618c0004124218009a4841814e4980003e60000066400020ccc8000430d8e30083129c6210605392410c0c9a400011f33000023e60010637cd200004f9a480001f2300c603e69010c0),
  (0x4018ec2600404, 0x8625258d4560725044c08a028bcce71858898b072102d1c8465b02c000150d0144829220044c350402c0c, 0x7a5231a441081e948c6900c607a5231a4c0001e948c69180437a5231a46200de948c69000097a5231a460019e948c690084602520000c31a4c630c6030c69780001a4c31a5e000c0930c6978003198c31a5263000630c6902400000a108008000003084001c60000c2100c60000030840020c0000c1080c300c60308402a40000060024860000030846318c000082100c6000063004048c0300cc0100c6000063080048c0018cc2000c318c6018c6030c60018c0180c31800630c00600031800019d8000c6000c0748c0018cc00112300c033000448c03180c001106000003000942400000c0018893000020006298c000002124c830000200064800318cc018d2000c6330c0348c6002403180c630c6000c6048c6301860181231806618c0032460018c00000948000104292a0c000080024094800020846424c000060019483000010006320c0018c0000c000c6030c69018c0000c31a58000c6018c667a400000600192618c633000051800018c0018c830006200046240318060010c948c601042071803180600198600c0918040618001a462001200000630c6948000024631a5200006618c6948003018631a52000c063006948000198c3025c00006900067700030240019dc00006900c07700030240301d800000930066318c001880119800000930c06318c001882018c630c6018846618c30184010186300661080042520180000250948c0000009620c318040011294800900420600001a4031a58000c0900c6978000024031a5e000c09180667800319860199e00006918c067800319863019e000c69180067980019860019e600c0618006780031a46018de000c6918c0378c631a4001818630c09000604a52301840081e318c6900c00618c01a403001294806610400498c0024021198948c6000840498c301860119263006618806620c0198400118830c0610004780031a403199c90006918004724030246001189480092000062523180000218630c0900046618c01a402019e948c60000067a4031a4c0001e630c6900840798c31a40010de630c69008037a4c31a480001c948009000097a5231a400101e948c69008007a5231a440001e948069000067a52302400019c948069000087252302400021e948c6900004),
  (0x30307a1a00000, 0x552b188244a131191456072193d146a2a988164b36014000221100144a, 0x1398c40002731840024e63000089cc611181398c0348273180463000210d29000611a52000c424a4a0104694812110d29294211a525288234a00a104694814210d28528021a52a508034a67300069480031006300061018c0488400100018069180030892300060120c05082001940104003014010009000411a4c00084249800108094800010d29000401a520008224a4100080030142088c404c01000c528c23480100084600100108c9028621a4005002232529080004810010d26294401a489480400240a004693294300063500021992a0004349a600086034c0010cc0994601800098c22302680084003940100064a4021a40f28c03302691880003940108c073801000ce708200126a1844002940108c652840118d348003301ce1000043a63100007386111813980400014a000694c9c300c60738401189398c20001ce1806904a40000099cc600009290003482731804604e60008c6),
  (0x3818ae1c0c000, 0x95a55166b128ac26092791640800e81cb2430592d286a029b0c47600100144a, 0xda5292801b4a52201b694a4431ed29488c0da52900d3b4a52031b694a4091800631529018062a520318054a524000a94b0042152961084225200012500c00480a018120014030000928c000240518009000a3000631880900c6312400000054a409024a000129014004a40028000200833240420066480063140901806281203180502580000a04a4601880948c601012020083498042006930084208c6000c62a400300c548006300a9030000152048c031240918c024800021086480042112602409180c04a40301809024660012900cc04806320120025240192018c8900009490c0000c6298c0300c531806300a633000014c6018c9180c0324c30180931860300c648cc00192619800498c330180000864b00001126025291007b0000200c094a44306c000086061806180cc318030198601866030c600cc061004118cc2100231b000008036000010c060084218d2300c201a4630040348c0308c0918c011812018c401a403188604920488039252010072481221824948043048094940061084025320252400e404a483048c630009918c6024124a524003604a48006d2948800c2108018db4a52001b694a4031ed29480c0),
  (0x1142daa27cc0c0, 0x229292a0484c3b2b4aa2d06a95980e16753581c221b3040340ab31220d9023b4312528d100050a0351d2140a, 0x4a53b18c600000000021081294ec631800008001000204a53b18c600040008001001294ec631802000400080004a53b18c600000108400001294ec631802108000000004a53b18c600000008401081294ec631800108000004204a53b18c600000100420081294ec631802008000080204a53b18c600000108021001294ec631802100000084004a53b18c600042008400001294ec631802008401000004a53b18c600840108000001294ec6318c0000000004204a53b18c630000000020081294ec6318c0000000084004a53b18c630000008400001294ec6318c0000401000004a53b18c630000108000001294ec6318c0108000000004a53b18c630802000000001294ec6318c2100000000004a53b18c660000000000099294ec631980000000004064a53b18c660000000020019294ec631980000001000064a53b18c660000008000019294ec631980000400000064a53b18c660002000000019294ec631980100000000064a53b18c660800000000019294ec631a40000000000080000018c6908421084210a08420000018210842108428000e90006608421084210a00702400198210842108428380090006608421084210a0003a40301821084210842801c0900c0608421084210a0e002403018210842108428000e91800608421084210a00702460018210842108428380091800608421084210a003024031a40008421084281800900c6900021084210a003024601a4010042108428180091806900401084210a003024630242000421084281800918c0908001084210a0031a40302401080210842800c691800900420084210a060024601a42008021084281800918c0908020084210a0601a46002420080210842818c091800908020084210a060024031a42100021084281800918c0908400084210a0601a40302421000210842818c0900c0908400084210a060024601a40108401084281800918c0900421004210a0601a46002401084010842818c091800900421004210a0031a4001a420084010842800c691800908021004210a060024031a4210040108428180091806908401004210a0601a4001a421004010842818c090006908401004210a0001a4031a42108001084281800900c6908420004210a060024031a40108420084281800918c0900421080210a0601a40302401084200842818c0900c0900421080210a060024031a4200842008428180091806908021080210a0601a4001a420084200842818c090006908021080210a0031a4001a421004200842800c6900c0908401080210a0001a4601a4210802008428180091806908420080210a0001a4630242108400084281800918c0908421000210a0601a403024010842100428180691800900421084010a003024601a420084210042800c0918c0908021084010a0031a46002420084210042818c091800908021084010a003024031a421004210042800c0918c0908401084010a0031a40302421004210042818c0900c0908401084010a0630240302421080210042818c091800908420084010a0001a4601a42108401004280006918c0908421004010a0031a460024210840100428180691800908421004010a0001a4031a42108420004280006918c0908421080010a0031a4030242108420004281806900c0908421080010a003024601a401084210802800c0918c0900421084200a0031a46002401084210802818c091800900421084200a0601a4001a4200842108028180691800908021084200a003024031a421004210802800c091806908401084200a0031a4001a421004210802818c090006908401084200a0001a4601a42108021080280006918c0908420084200a0031a460024210802108028180691800908420084200a063024001a421084010802818c091800908421004200a0001a4031a4210842008028000691806908421080200a0031a4001a4210842008028180690006908421080200a0001a4031a421084210002800c0900c6908421084000a003024031a401084210840800c0918c090042108421020031a40302401084210840818c0900c09004210842102003024031a420084210840800c09180690802108421020031a4001a420084210840818c09000690802108421020601a4001a42100421084081806900c090840108421020001a4031a42108021084080006918c090842008421020031a4030242108021084081806900c090842008421020001a4031a421084010840800069180690842100421020031a4001a42108401084081806900069084210042102063024001a421084200840818c0900c090842108021020001a4601a421084210040800c09180690842108401020001a46302421084210800800c0918c090842108420020004a4001982108421084260240900066084210842109920024001982108421084260012900c06084210842109809024030182108421084264800900c060842108421098004a46001821084210842602409180060842108421099200246001821084210842618c0918c0908000084010a0601a46302401084000042818c091806900401004200a0601a4601a420080200802800c6900c6908401080000a0601a4031a421000010840818c0900c690002108021020031a4601a420084010040800c6918c090042008420020631a40002421084210842818c0900c6900001084210a063024601a400004210842818c0918c0900001084210a0601a4031a4210800008428180691806908420000210a0601a46302421080000842800c6918c0900420084010a0601a46302401080210042818c0918c0900420084010a0031a4601a4200840108028180691806908021004200a063024601a420084010802800c6900c690840108021020601a4031a421004200840818c0900c690840108021020031a4031a421084210000800c69180690842108400020031a463024210842100008000cc0006908421084210a006030001a42108421084283000c0006908421084210a000330030242108421084280180c00c0908421084210a0c003003024210842108428000cc1800908421084210a006030600242108421084283000c1800908421084210a000330031a42108421084250180c00c690842108421094c0030031a4210842108425000cc18069084210842109406030601a42108421084253000c18069084210842109400330630242108421084250180c18c090842108421094c003063024210842108425018cc000660842108421098c0330001982108421084263180c0006608421084210980633003018210842108426300cc00c060842108421098c603003018210842108426018cc180060842108421098c0330600182108421084263180c180060842108421098c0048600242008021084283001200c0908400084210a0c004860024010840108428300120006908401004210a0c004803024010842008428300120006908021080210a006048600242008421004280181200c0908401084010a00034860024210840100428000d200c0908421080010a00604860024010842108028018120006908401084200a00034860024210802108028000d20006908421080200a00604803024010842108408018120006908021084210200034803024210802108408000d200069084210042102000348630240108021004280181218c0900420084010a0c004863024010802100428000d21806908021004200a006048601a4200840108028300121806908021004200a000348031a42100420084080181200c690840108021020c0048031a4210042008408318120006900001084210a0c604803024000042108428318121800900001084210a0c0348001a4210800008428300d200c0908420000210a0c034860024210800008428018d20006908421084000200634803024210842100008018d2180090842108400020c6048631a400000210042818cd518c0900000084010a0c0348631a40108000004281987518c0900420000010a0c6048631a400004010802818cd51806900001004200a0c0348631a4200800008028198751806908020000200a0c6048631a400004200840818cd500c690000108021020c0348631a42100000084081987500c69084000002102006348631a401080210000830c7518c09004200840002006348631a420084010000830c7518069080210040002006348631a421004200000830c7500c690840108000020c634863024000002100428318d218c0900420000010a0c6348601a4000040108028318d21806908020000200a0c6348031a4000042008408318d200c690840000021020c634863024010802100008318d2180690802100400020c6348031a42100420000084a41518c0900000084010a1204d4630240108000004284a4151806900001004200a1204d4601a42008000080284a41500c690000108021021204d4031a42100000084080253518c090042008400020094d4601a42008401000080253500c690840108000020c64e000018210842108426324d80000608421084210992636000018210842108426025380000908421084210a1204e0000242108421084284a4180000908421084210a0c936000024000042108428498d80000900001084210a0c64e000024210800008428498d80000908420000210a0c64e000024210842100008324d800009084210840002000000631a00108021004200000018c68080210042008000000631a0210042008400000000006908421084210a00000003024210842108428000001800908421084210a084200000180000000084280000018c0900420084010a000000601a42008401080280000018c6900020004000a000000031a42100420084080000018c69004000800102000000631a42000400080082108000006000010840002084200000182108000000080000000c69084210842109400000601a42108421084250000018c090842108421094004240000021084210842402009000000842108421091000240000021084210842400129000600842108421080090240018021084210842048009000600842108421080004a4030002108421084200240900c000842108421081200240300021084210842000129180000842108421080090246000021084210842048009180000842108421080004a4631800008001000200240918c60000200040008120024631800008001000200012918c60004000800100009024631800100020004004800918c600040008001000004a4631802000400080000240918c60080010002000120024631802000400080000012900003084210842108c090240000c2108421084234800900003084210842108d20048600002008021084204801200c00084000842108120048600000108401084204801200060084010042108120048030000108420084204801200060080210802108009048600002008421004200241200c000840108401080004c8600002108401004200013200c000842108001080090486000001084210802002412000600840108420080004c86000021080210802000132000600842108020080090480300001084210840002412000600802108421000004c80300021080210840000132000600842100421000631a40002400000000842818c69000090000108400020631a40002421080000000842100000060000000000020c60306318c000000100020300cc18c630002000000080c60306318c000002000400300cc18c630040000001000c60306318c000040008000300cc18c630800000020000063306318c000800100000018cc18c630040008000000063306318c2000400000003180c000660000108421080c6030030180000421084203180c180060000108421080c033000198210800008420300cc00c060842000021080c0330600182108000084200013218c00004200840108009048630000108021004204801218c000042008401080004c8601802008401080200241218060080210042008120048601802008401080200013200c60084010802100009048031802100420084004801200c6008401080210000633000198210842100000018cc00c060842108400000063306001821084210000018c0918c0900000084010a0601a46302401080000042818c091806900001004200a0601a4601a420080000802818c0900c690000108021020601a4031a421000000840800c6918c090042008400020031a4601a420084010000800c6900c69084010800002000330000242108421084280180c0000908421084210a0c003000024210842108428018cc000060842108421098c0330000182108421084263180c000060842108421098094c8000002108421084204813200000084210842108129048000002108421084204a41200060000010842108129048030000000421084204a412180000000108421081204c8001802108000084204813200c000842000021081204c86000021080000842002532000600842108400000094c80300021084210000002532180000842108400000c603000024000042108428300cc0000908420000210a006330000242108421000084201218c00000000840109100448630000108000004244201218060000010042009100448601802008000080244201200c60000010802101100448031802100000084040211218c00004200840001008448601802008401000040211200c60084010800001108448000000000000084244211200000000010840001108448000002108000000044a41218c600000008401081204c8631800108000004204a41218c600000100420081204c8631802008000080204a41218c600000108021001204c8631802100000084000253218c600042008400000094c8631802008401000000253218c600840108000000c604863018000002100425300d218c060042000001094c604860198000040108025300d2180660802000020094c604803198000042008405300d200c6608400000210140634863018010802100005018d218066080210040001406348031982100420000054a41218c03000000840108d204c86300c0108000004234a41218063000010042008d204c86018c2008000080234a41200c63000010802100d204c80318c2100000084030253218c03004200840000c094c86018c2008401000030253200c63084010800000ce73a4631980000000000084a41b18c600000000400081204ec631800008000000204a41b18c600000008001001204ec631800100000004004a41b18c600000100020001204ec631802000000080000253b18c600002000400000094ec631800100020000000253b18c60080010000000108448631800000000000084a418000060000108421099204e000018210800008426498d8000060000000021098094e000018210842100006324d8000060000108400018c64e0000182108000000064a53b000000000108421081294ec000002108000084204a53b000600000000021081294ec030000000000084204a53b180000000000021081294ec000002108421000004a53b000600000108400001294ec030000000421000004a53b180000000108400001294ec001802108000000004a53b00c000842000000001294ec600002108000000004211218c63000000000001cc6348631a40000000000084a53b00003000000002108d294ec0000c0000421000034a53b00003084200000000d294ec630000000021004204a53b18c000042000001081294ec601800000401080204a53b180600802000020081294ec631800000000000204a53b00c600000108021001294ec031802100000084004a53b18c600000000001001294ec631800000000080004a53b18c000042008400001294ec601802008401000004a53b18c600000000400001294ec031802100420000004a53b18c600000008000001294ec631800000400000004a53b18c600002000000001294ec631800100000000004a53b18c600800000000001294ec63198000000000006),
  (0x68e1542700000, 0xa45609100a90625138b4d6050390cd26022a00ca6a01088840807a1c8eab52a28c4284102858eb701a1484a, 0xdef484001006f7a403000437bd20180401bde90000030def488000106f7a40000c637bd20010021bde90000600def480031086f7a404200037bd21190001bde9000a400def480071006000043298c100061210c60800310c8630c00004873182000c04398c10006119cc61008010ca630804008672184030023298c201802190c610006010e620080208843180002443218c20180121c86100c0010e6300c0208643184800043294c20200219c660100410ce630520008653184800023394c24800221c4600009110e6200a03048730c0002044398c23000221cc60180408ce630920008672184520044310c0200c221cc402004090e6181800048730c2800044398c34000221c8603000110e330100204673140c00043398c07800219c66000c6110e630009188873180060044398c003c0221cc300106110e628009308873100631840398c0318c021cc400186110e6100c630067318004a44339880318c219cc402520110e630129180673180949040398c05280219cc60252410ce6201ef008073186000040008c30000100085180060800210c00180002144000040018c3000c018042080030800630800304002100401043000830000021c420000910c0210804000652000420043280010006000cc60800300c0630c000046511420024000148300000194841000600c0420c00480031084001800018c2000c001084180090000420808304001800048044000c002082200031200000ca300980000431004000043290c000120010a4000081100420d002046000c450000439002500001944019480010c000800004653180a0000338c020000121c86018c610000208c00046520c06310200106240001194431a006000801800f0088000c000240039840028c22000203000008e300d40000870006c0000238003410011940010000010e630000300073182630c0000cc23180001064018c410003208c6304000102630c000186002402210630018610c00101000008730046318200100351000194000000411086308c6008002184631800000c02800121cc3118c0000a4181000048718c090002338c62318c0000c01010600c83000a000887198004004420cc2318c000c04118c600c00209290040018c46318030100078000198600110610c80000ca308600006900043280c2318c0000840200008ce6180cc308000086f00004300002000221cc60200010ce33000030887310003184420c804a481000630010611083100c000867318063004320cc24a402000461a000110e030d26008040186948c00000c00200221cc3125200008318de00046500c6a50023000632a0c021000000c0110e630d29208000100630023318634a40200c061a52010c00301290046418c494980000c6263001000431b8c0080a01894a30060100684182320003528c020000011e910c0000d4a30460000094980020c634a520000421a94600c001000930887300294a40001803520c019000018c6000e620de90040400c067184020c02630c1000401a94600c6000dcc0040300c4c6180000843630c1000020012910ce6000c9308073000a5180320c0003d22210601bd060086000d8c304030006c61800180404a4c101cc012529000a40012f304041800c6182020c0063d22000001a5e91000000129008073180c6004020cc04a4c001cc203186000831018e30403180687a42300003631200000403180080c618129300673006c62400010037bc020000603de00808318def2040000c6f4a400280037bcc200000131890008300dc9480070006f79800000837bd21000001bde90000010def480001006e62400300027bd20000801bde900c0000def480040004f7a40018c007bd2001cc0),
  (0x4058c82800000, 0x3501cd609002a4262532a0c5627100c454430788c5a0522a01560295a94c4872111c9ee5053ac806c14229c04a, 0x133788001266f000064cde6000099bc0320d3378c640266f018e04cde0318499bc4630100010c732400218c6180c631c6002866398005186732000318c61810331ca3020a638cc0318c61800c318e41a0c63186349886390c8218c618d25218e60400631cc6500c63980a50cc631925218c61a52631c40528c63900a498c7301ca318e230084000690004201920008a300c803180048004200660206000c8040c0500085000c602806000c00280039808280043008a000a42000631c06000c6018005006720009300a42000431c600300338900010c6019202000604003000c4000c630c100180018260180033380200060500632180a500003000918ce4028c600080500c320c683186000005198e60010031cc0014c33980040c6730008300e642400200c003c602900a50c0020d293000030004318c00206639000418672000f00cc4025260008651880008ca3180000004318e604000190c94940001800318c720140198e3039430004948003198ca010641a14601002021c301400418c32100a500642194918c00028c0318864280028d2a4884000100318e6020c33188052463210c8010c619904018c332940010645246320133000003190800cc3329001906672840008ca000c730129018e41a4c431c034a406388ca300c61194f000621a52231c009bc00011330006418149318e0328c4318067280320930000c61826f300004b94018c40830c3200ce608640266a0000404183318009bc63200d3790000266c200004cde0000499bc40000d2780c70266f018c0),
  (0x60e12c2900000, 0xa9558244442958148e65151149e6a038b440a034980566b404804e2552b941e0a43808c48a141b148e4161a094eb, 0x295a460000e14ad23380000a569180042052b48c04010295a464000814ad23200800a569190800052b48c00198295a466180014ad2300c640a569190630052b48c063000010027210e100800390870800019cc63840018c8631c2000c67198e118003398670000900cc630000480c3318090000630cc118003398c402400018c618480000e631c2010066318e100063314c709800194c33840200ce63182300067314c1000c338cc50000411cc638080200a631c0800005318e002400218c708006198663800040cc231c0900005318c130003398660000801cc628080200e63140002406318a000103310c500008198c428009000e63100038007318e000100318c700100018c638008000e63180800007318c130003298c608006198c62840600cc63180058006318c001cc0218c70190000cc6380083008631806380073188032000318c40010601cc618006300e631c0630007318e031c00318c7000e601cc6300c6300a63140631804318e0320c0198c6018c601cc6200c8300c630c2010000010e000801390000004011880004620000401c0010c2701001194000004708ca0000403840400ca0014201006021081200c000c040908001400205200006200c2010064210000146138040000a309c4000084000a00182010c600188002c002000408c40190c000006000e001c2328004000e0020003000601004114002840230c002102400005208813080301004000a309c0020480208a0010200246010860001231804300046118040040230c80200060104500c014800318840098401908000004208c00142640000008813200000804080031804638000480032942001860190a10008328085090001948028500000a4010264000300080480002946009800194830046000ce6100004184400800020c2208000800618006380060008319c2002460010c04000029006080091800528000208c22142001864010a00180038c640980019480200083088000c26000673000148003294000a400198800040018c8031c002800618ce13280000007000a001c633046000ce6010293800018080018c23000400009000c618120000663000001800318e020000298670900001cc038000200e33142950000008614a800008030180001cc600007488801800051847000000008030cc70000411c0638080000e61980002066010a031c0018c64000e60106318006488c01800010006318e000800398c60a56000000304c600c0319400380043188131c0300c64080c6194630040730c831800052463008000292318800018c001063304c618c00198003180618c81318c300804098c6190020046630cc30002631860000e030000298c600006018c6280c630003194063980018c81320c3000430990618040180c6300a3180063980418c01320c3180400990618c40004c630ce0000005a4660000100003398c7000c0018c6304c830c00018263186000ca032000018c4098e618003204c630c80010264186300060020c0218c0098c619460004c730c8300026418660000131d23000430a4e618c40000c70000631c095800018cc001cc0398c00016901863001290000630c004a40331800318c0018c4018c6010c6000c83000630c0641803318014ad23000040a529180060052b48c00200294a460300014ad23010000a569190000052948c04200295a46018c004ad20018c0),
  (0x5088be1b00000, 0x248a0b3481c4600439805a0f139084a0a35229c04a310a9d620340ac042c, 0x25297a442001294bd20100894a5e9100044a52f48444025297a400021294bd20218094a5e9009204a52f48809025297a400319294bd200248300c001092918c600088648009000444980900002224c00200011129020000088949080000444a506000022192000180111290100800889480c6000444a40003c02224c0001e010929420000088930006400444a4031a4022252630006110c9300c030889318c001844498094800022520001861092949000308864a480018444980002522225290000911129018c90008949800518424a4063240222500319800112830009408894a400424224a4c003cc0225290018901129318c630089480090004000c0040002000c318c000080918c6000800481200004430063180000112001000108c9210000088048120000244808400002210c4200c0010063008030800325200002200c04000022192420120008060008830800318c600040018c630000001200180011126018000088930000480424188930000100c031800108c642000008803000640042310c6000c22008600086110c0018083080600000400444980003000124c64a40000803000060088948000400424a40003000220c0000c6110c600008308463108041840018c6000c221806300c6110000000900089480007800241924000c2200c930009088040012c308400012900002318c6018c02008031940108c04a520000003000662440010004a402224094800911000018c000089481290000448d294800001060025e0108c04a40048444000c6480023180033cc20180600006111294800048886300c66000231006324022240601906108c03000848806300004a4404a4c0030c0118c631806008c60000f48806318005204031806324002248631946108004800048449480097a440200c0018c022526001260092948c6948000498c661802010c63290200086319481008030009408094a520624040012932121100004a5e001120325293008601929798040012633120001064a586008c03252f30043024007a4004a52633d2000c694a5e9008004a52f48800024c662400319294bd20000894a5e900120),
  (0x50d0b61900000, 0xa934cad56655039446a5053acc0e025390d48a13aa0d025360a0582b, 0x919d290080448ce948823024674a482001233a5260000919d292000448ce948046024674a480201233a5200012919d290012048ce94800630c60000614a400380041192001c002092600c000184948c03000c23240230004119201008030926008c00104930c03000824a462180040252001403308c9000a01984930045180c249082000061252010c602092900ca00104948005200c2324001a0041192001463300c900009018493000518cc04980019006125201140030929000090104948005200824a40228c0412500001003092940c000184648045300823240029006125081800030926000a801049300453008249802018c601920100c630126000093104930000224a14a400025221252910006308c93006431046498450188232522000c6124c6114062092600009498094980521882498c0011060a5290000930929300063184949800320824a4c00192602529000c9185294800949009480070008001803000031240018000308c018c0000c204800518cc2000631800010120014003000900c0000c4631040300020186218004001200146330004000a31980400c63000002248200006101261980000806000e90084301866000000240338000118c41000030886308c00100030040318803000200006119201000030926000a0018463004500082318c330000010c8180003080648ce00000030005200823100228c041240001cc630000000a00104648005000824980328c00124800148030920008c60104600000200c249800298c4000c6014062000600cc6000462006648002190033980012400195200090000cc9000470000740082300033a40011800194000092900ca6000463104031880018c2000c611800001200092948c0048c202246002461201230012610000000c0209290000631046300064a440010002a4c40180001929100804880031840318451a4c0000c2318c410006198c600804300a43104601865018023180002524018c91948918400308c641800018663180230000018c602526118c820004308c6410040186749802180c001924018c600006309293000630049480004a4404a52000126118c919d29008004800048c294a4674a400011233a5200100919d292000030006410094a4634a400025233252000109199290008448ca948009024664a40040120025200252919529000c6),
  (0x3814701a00000, 0x2162312c0114c50481c228734c28d4cb3122016eb7103c18e061000940a, 0x1bde4080037bc402006f7882300def100061bde0001237bc014806f7802630c0020529081020a521480414a448010294812920529194040808328081200604080030c08104c01a00209803500412006c0080400ca8204001b404080014804102448008243090020409001e4000c07808001860010294800f204c003c0409803528410006f0082030008204c9020040992002081498080102930529004091a9420008352840200294880048d290000902944000c2528400186948009001292000902944098014a4002246c6002020129205201bd4400002630010184f4802030dcc004031a520098c3630013000f7900000d8c0000802524098c3630002106c6000800def1000013180010c04a4014a46f7800400def004601bde0000c07bc014804f78000481ef004c6),
  (0x3020701900000, 0x2a9584c4e11268b4c06a1282c0e4372a29d64b029b2040a011a1c04a, 0x2324800034649300008c924000919240421232480c6046492108000124318c0020c631885310c6310a6318c480006310d0000c63100a318c632940318c60012200c6040cc00100a0180030000318c600104018c00240630c004808630004310c60480400080718400122000c6022400318c0000c4318c05008421940018c032520200064800331880500c421005488c6002063000050003310d10006520220018c0020003188640006318805008631140018c4210a6018c4214c4318005188421200018c02400031880028c631809480863014a480031a9a630000528042108a698800118d3080022940018c6049242101151863001ce300003464000006534c42100c69844201ce30042239c6010046b8c02108f72406102320008424640018c08c9200008d7240630232490000464901080),
  (0x48488a1b00000, 0x4ac4660128bc270b1a93514072193c226a059b0970202808440020130940a, 0x1ce62010039cc41180739904000e73300001ce6009c039cc000247398c0030e73001201ce60118c3000c24a4204944648409189291814411923028824984a00c4948d20308c912806124c3480c2498490184948940309090400611920800c249800990464801320926029c411920538824980a5184948c0a180061a40610083028623006a00c4600d20308800024600000028c00246e00c4400940188860014612400500c2480694980000d2a208001800612522500c2024009900030140188c90a520101214a4400246948000481401892600146118c0500c2318100184030d290012004006118009806230073018400014e300000200611920028823240949000481003092600144124c252860018009904600529000891cc03100c04a4824800a7100030dce10800029c411803528023186e7004020dce100041b9c2010039a8620000a51046309ce00806139c2000c0738423006e7000040a6a008061b9c001083738004006e700460014a00929139c0010c39380200c737100000273200001ce60100039cc40000739800400e730046014a40001239cc00018129004900273008c6),
  (0x30607c1d00000, 0x2a17894622b11826561103c00c0452182c9e6a25a280a6200008d82220130144a, 0xded240001bda4400137b4800046f69110c0ded202241bda4043100048849480092012900124224c0020844a409190894b006110c9030c42192c018844980c308894a52321124030c42250948c444a418010864e000210c906004224d8000844998c208864b18021129630c2224cc618044a652010864ca4021126948c022518c00044a4004900318009008c300122018c0498800100941004000002112900100220c061840019803080030129208600008222520018804a4003108932523000094a40400120d804000c180100030186110c4d800210060600843258001086481802112660004224c061884481290108906c0021000c0002200d800082019291888906c00110604a4e02200948c04490180108606000210c06312000c6c618003181b4884303180210c663080218d2900000241848886031800112994804000d2918400136c3084004a4600008948042181292040202524000804a49108609490011c1291844302523008904a46010c496d240001bd80800037b0000036f6000863c6000218dbda4400037b4800026f69010c0),
  (0x301c5a1600000, 0x1162313954c083450ac4a6a2299486625592c50a023900144a, 0x1ef0980003de1200047bc200012f78401481ef0902603de1004c618c240a528004c032500098293010130529780060992f000c14992901829480a13000402024000c8004800180c0880020c610052418c240a400400c0024000982930001205290202409880000c14a400098094a4003040903c04000c0404c1481200182900100304c603c240980a504c000008010264a52100009020040a4c9000c1319e00182033c00304c07a0230800a5048001100018264a0003052652804000c94808002529080263252020520528240980c60400021290102633de100004630200a40f784800018c0802622520005297bc200980f78000025ef0002903de0004c6)]

def cdH (m : Nat) : Nat := (compData.getD m (0, 0, 0)).1
def cdS (m : Nat) : Nat := (compData.getD m (0, 0, 0)).2.1
def cdP (m : Nat) : Nat := (compData.getD m (0, 0, 0)).2.2
def apc (m e : Nat) : Nat := Nat.land (Nat.shiftRight (cdH m) (Nat.mul 2 e)) 3
def bpc (m g : Nat) : Nat := Nat.land (Nat.shiftRight (cdH m) (Nat.add 10 (Nat.mul 2 g))) 3
def nSel (m : Nat) : Nat := Nat.land (Nat.shiftRight (cdH m) 20) 511
def nE2 (m : Nat) : Nat := Nat.land (Nat.shiftRight (cdH m) 29) 511
def nE3A (m : Nat) : Nat := Nat.land (Nat.shiftRight (cdH m) 38) 511
def nE3B (m : Nat) : Nat := Nat.land (Nat.shiftRight (cdH m) 47) 511

-- ===== cells of a completion context =====
def nsubA (code : Nat) : Nat := cond (Nat.beq code 0) 1 (cond (Nat.beq code 3) 9 3)
def baseA (e code x : Nat) : Nat :=
  cond (Nat.beq code 0) (Nat.shiftLeft 511 (Nat.mul 9 e)) (cond (Nat.beq code 1) (Nat.shiftLeft 7 (Nat.add (Nat.mul 9 e) (Nat.mul 3 x)))
    (cond (Nat.beq code 2) (Nat.shiftLeft 73 (Nat.add (Nat.mul 9 e) x)) (Nat.shiftLeft 1 (Nat.add (Nat.mul 9 e) x))))
def nsubB (code : Nat) : Nat := cond (Nat.beq code 0) 1 3
def pat27 (code x : Nat) : Nat :=
  cond (Nat.beq code 1) (Nat.shiftLeft 511 (Nat.mul 9 x)) (cond (Nat.beq code 2) (Nat.shiftLeft 0x1c0e07 (Nat.mul 3 x))
    (Nat.shiftLeft 0x1249249 x))
def baseB (g code x : Nat) : Nat :=
  cond (Nat.beq code 0) (Nat.shiftLeft 134217727 (Nat.add 45 (Nat.mul 27 g))) (Nat.shiftLeft (pat27 code x) (Nat.add 45 (Nat.mul 27 g)))

def posList (m : Nat) : List (Nat × Nat) :=
  (List.range 5).flatMap (fun e => (List.range (nsubA (apc m e))).filterMap (fun x =>
    cond (Nat.beq (Nat.land (baseA e (apc m e) x) (targetT m)) 0) none (some (Nat.land (baseA e (apc m e) x) (targetT m), e))))
def negList (m : Nat) : List Nat :=
  (List.range 5).flatMap (fun g => (List.range (nsubB (bpc m g))).filterMap (fun x =>
    cond (Nat.beq (Nat.land (baseB g (bpc m g) x) (targetT m)) 0) none (some (Nat.land (baseB g (bpc m g) x) (targetT m)))))

def npos (m : Nat) : Nat := (posList m).length
def nf (m : Nat) : Nat := Nat.add (npos m) (negList m).length
def cellM (m c : Nat) : Nat := cond (Nat.blt c (npos m)) ((posList m).getD c (0, 0)).1 ((negList m).getD (Nat.sub c (npos m)) 0)
def edgeOf (m c : Nat) : Nat := ((posList m).getD c (0, 0)).2
def blockA (e : Nat) : Nat := Nat.shiftLeft 511 (Nat.mul 9 e)

def profV (m x c : Nat) : Nat := cond (Nat.blt c (npos m)) (cntM (x &&& cellM m c)) (cntM (rect x &&& cellM m c))
def capV (m c : Nat) : Nat := cntM (cellM m c)
def capC (m c : Nat) : Nat := popc256 (cellM m c)

def cellCheck : Bool :=
  allBelow 37 (fun m => Nat.ble (nf m) 31 &&
    allBelow (nf m) (fun c => Nat.blt (cellM m c) (2 ^ 180) && Nat.ble (capC m c) 27 && Nat.beq (Nat.land (cellM m c) (targetT m)) (cellM m c) &&
      cond (Nat.blt c (npos m)) (Nat.blt (edgeOf m c) 5 && Nat.beq (Nat.land (cellM m c) (blockA (edgeOf m c))) (cellM m c))
        (Nat.beq (Nat.land (cellM m c) MV) (cellM m c)) &&
      allBelow c (fun a => Nat.beq (Nat.land (cellM m a) (cellM m c)) 0)) &&
    Nat.beq (orM (cellM m) (npos m)) (Nat.land (targetT m) MA) &&
    Nat.beq (orM (fun c => cellM m (Nat.add (npos m) c)) (Nat.sub (nf m) (npos m))) (Nat.land (targetT m) MV))

set_option maxRecDepth 100000 in
theorem cellCheck_ok : cellCheck = true := by decide +kernel

-- ===== consequences of the cell check =====
theorem cell_facts (m : Nat) (hm : m < 37) :
    nf m ≤ 31 ∧ (∀ c, c < nf m → cellM m c < 2 ^ 180 ∧ capC m c ≤ 27 ∧ cellM m c &&& targetT m = cellM m c ∧
      (c < npos m → edgeOf m c < 5 ∧ cellM m c &&& blockA (edgeOf m c) = cellM m c) ∧
      (npos m ≤ c → cellM m c &&& MV = cellM m c) ∧ (∀ a, a < c → cellM m a &&& cellM m c = 0)) ∧
    orM (cellM m) (npos m) = targetT m &&& MA ∧
    orM (fun c => cellM m (npos m + c)) (nf m - npos m) = targetT m &&& MV := by
  have h := allBelow_spec _ _ cellCheck_ok m hm
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun c hc => ?_, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩
  have hc2 := allBelow_spec _ _ h2 c hc
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc2
  obtain ⟨⟨⟨⟨hlt, hcap⟩, htg⟩, hside⟩, hdis⟩ := hc2
  refine ⟨hlt, hcap, Nat.eq_of_beq_eq_true htg, fun hp => ?_, fun hp => ?_, fun a ha => Nat.eq_of_beq_eq_true (allBelow_spec _ _ hdis a ha)⟩
  · rw [show Nat.blt c (npos m) = true by rw [Nat.blt_eq]; exact hp, cond_true] at hside
    simp only [Bool.and_eq_true, Nat.blt_eq] at hside
    exact ⟨hside.1, Nat.eq_of_beq_eq_true hside.2⟩
  · have e : Nat.blt c (npos m) = false := by
      cases h : Nat.blt c (npos m)
      · rfl
      · rw [Nat.blt_eq] at h; omega
    rw [e, cond_false] at hside
    exact Nat.eq_of_beq_eq_true hside

theorem npos_le (m : Nat) : npos m ≤ nf m := by unfold nf; show npos m ≤ npos m + _; omega

theorem cntM_eq_popc (y : Nat) (hy : y < 2 ^ 180) : cntM y = popc256 y := by
  rw [popc256_eq y (lt_of_lt_of_le hy (by norm_num)), cntM, show (256 : Nat) = 180 + 76 by rfl, cntR_add,
    cntR_zero_above y (0 + 180) 76 (by rw [Nat.zero_add]; exact hy), Nat.add_zero]

theorem capV_eq (m c : Nat) (hm : m < 37) (hc : c < nf m) : capV m c = capC m c :=
  cntM_eq_popc _ ((cell_facts m hm).2.1 c hc).1

theorem testBit_cellV (m c : Nat) (hm : m < 37) (hc : c < nf m) (hc2 : npos m ≤ c) (p : Nat)
    (hp : (cellM m c).testBit p = true) : 45 ≤ p ∧ p < 180 := by
  have h := ((cell_facts m hm).2.1 c hc).2.2.2.2.1 hc2
  have := congrArg (fun z => z.testBit p) h
  simp only [Nat.testBit_and, testBit_MV, hp, Bool.and_true] at this
  simpa using this

-- ===== transitions =====
def Tf (op isPos : Bool) (cap a b : Nat) : Nat :=
  cond isPos (cond op (min cap (a + b)) (min a b)) (cond op (min a b) (min cap (a + b)))

theorem Tf_mono (op isPos : Bool) (cap a b a' b' : Nat) (ha : a ≤ a') (hb : b ≤ b') : Tf op isPos cap a b ≤ Tf op isPos cap a' b' := by
  unfold Tf; cases op <;> cases isPos <;> simp only [cond_true, cond_false] <;> omega

theorem rect_and_cell (x y M : Nat) (hM : ∀ p, M.testBit p = true → 45 ≤ p ∧ p < 180) :
    rect (x &&& y) &&& M = (rect x ||| rect y) &&& M := by
  apply Nat.eq_of_testBit_eq; intro p
  rw [Nat.testBit_and, Nat.testBit_and]
  cases hm : M.testBit p
  · simp
  · have := hM p hm
    rw [rect_bit _ _ this.1 this.2, Nat.testBit_or, rect_bit _ _ this.1 this.2, rect_bit _ _ this.1 this.2, Nat.testBit_and]
    cases x.testBit p <;> cases y.testBit p <;> rfl

theorem rect_or_cell (x y M : Nat) (hM : ∀ p, M.testBit p = true → 45 ≤ p ∧ p < 180) :
    rect (x ||| y) &&& M = (rect x &&& rect y) &&& M := by
  apply Nat.eq_of_testBit_eq; intro p
  rw [Nat.testBit_and, Nat.testBit_and]
  cases hm : M.testBit p
  · simp
  · have := hM p hm
    rw [rect_bit _ _ this.1 this.2, Nat.testBit_and, rect_bit _ _ this.1 this.2, rect_bit _ _ this.1 this.2, Nat.testBit_or]
    cases x.testBit p <;> cases y.testBit p <;> rfl

theorem prof_gate (m : Nat) (hm : m < 37) (op : Bool) (x y c : Nat) (hc : c < nf m) :
    profV m (gate op x y) c ≤ Tf op (Nat.blt c (npos m)) (capV m c) (profV m x c) (profV m y c) := by
  unfold profV Tf
  by_cases hp : c < npos m
  · have e : Nat.blt c (npos m) = true := by rw [Nat.blt_eq]; exact hp
    rw [e]; simp only [cond_true]
    cases op
    · have := cntM_and_le x y (cellM m c); exact le_min this.1 this.2
    · exact le_min (by unfold capV; exact cntM_le_mask _ _) (cntM_or_le x y _)
  · have e : Nat.blt c (npos m) = false := by
      cases h : Nat.blt c (npos m)
      · rfl
      · rw [Nat.blt_eq] at h; exact absurd h hp
    rw [e]; simp only [cond_false]
    have hV := testBit_cellV m c hm hc (by omega)
    cases op
    · show cntM (rect (x &&& y) &&& cellM m c) ≤ min (capV m c) (cntM (rect x &&& cellM m c) + cntM (rect y &&& cellM m c))
      rw [rect_and_cell x y _ hV]
      exact le_min (by unfold capV; exact cntM_le_mask _ _) (cntM_or_le _ _ _)
    · show cntM (rect (x ||| y) &&& cellM m c) ≤ min (cntM (rect x &&& cellM m c)) (cntM (rect y &&& cellM m c))
      rw [rect_or_cell x y _ hV]
      have := cntM_and_le (rect x) (rect y) (cellM m c); exact le_min this.1 this.2

theorem profV_le_cap (m x c : Nat) (hm : m < 37) (hc : c < nf m) : profV m x c ≤ capV m c := by
  unfold profV capV; cases Nat.blt c (npos m) <;> exact cntM_le_mask _ _

theorem sumF_congr (g g' : Nat → Nat) (n : Nat) (h : ∀ c, c < n → g c = g' c) : sumF g n = sumF g' n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumF_succ, sumF_succ, ih (fun c hc => h c (by omega)), h n (by omega)]

theorem orM_and (M : Nat → Nat) (B n : Nat) : orM M n &&& B = orM (fun c => M c &&& B) n := by
  induction n with
  | zero => show 0 &&& B = 0; simp
  | succ n ih => rw [orM_succ, orM_succ, Nat.and_or_distrib_right, ih]

theorem cntM_low (y k : Nat) (hy : y < 2 ^ k) (hk : k ≤ 180) : cntM y = cntR y 0 k := by
  unfold cntM
  rw [show (180 : Nat) = k + (180 - k) by omega, cntR_add, cntR_zero_above y (0 + k) _ (by rw [Nat.zero_add]; exact hy),
    Nat.add_zero]

theorem cA_eq_cntM (y : Nat) : cA y = cntM (y &&& MA) := by
  rw [cntM_low _ 45 (Nat.and_lt_two_pow _ MA_lt) (by norm_num)]
  unfold cA; apply cntR_congr; intro i _ hi
  rw [Nat.testBit_and, testBit_MA]; simp [show i < 45 by omega]

theorem blockA_bit (e p : Nat) : (blockA e).testBit p = (decide (9 * e ≤ p) && decide (p < 9 * e + 9)) := by
  unfold blockA
  show (511 <<< (9 * e)).testBit p = _
  rw [Nat.testBit_shiftLeft, show (511 : Nat) = 2 ^ 9 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
  by_cases h : 9 * e ≤ p <;> simp [h] <;> omega

theorem aE_eq_cntM (e y : Nat) (he : e < 5) : aE e y = cntM (y &&& blockA e) := by
  unfold cntM aE
  rw [show (180 : Nat) = 9 * e + (9 + (180 - 9 * e - 9)) by omega, cntR_add, cntR_add]
  have h1 : cntR (y &&& blockA e) 0 (9 * e) = 0 := cntR_zero_bits _ _ _ (fun i _ hi => by
    rw [Nat.testBit_and, blockA_bit]; simp; omega)
  have h2 : cntR (y &&& blockA e) (0 + 9 * e + 9) (180 - 9 * e - 9) = 0 := cntR_zero_bits _ _ _ (fun i hi _ => by
    rw [Nat.testBit_and, blockA_bit]; simp; omega)
  rw [h1, h2, Nat.zero_add, Nat.add_zero, Nat.zero_add]
  apply cntR_congr; intro i hi1 hi2
  rw [Nat.testBit_and, blockA_bit]; simp [hi1, show i < 9 * e + 9 by omega]

-- the positive cells partition the accepted part of the target
theorem pos_sum (m x : Nat) (hm : m < 37) : sumF (profV m x) (npos m) = cA (x &&& targetT m) := by
  obtain ⟨_, hc, hor, _⟩ := cell_facts m hm
  have e1 : sumF (profV m x) (npos m) = sumF (fun c => cntM (x &&& cellM m c)) (npos m) := by
    apply sumF_congr; intro c hcn
    unfold profV; rw [show Nat.blt c (npos m) = true by rw [Nat.blt_eq]; exact hcn]; rfl
  rw [e1, sum_cells x (cellM m) (npos m) (fun a b hab hb => (hc b (by have := npos_le m; omega)).2.2.2.2.2 a hab), hor,
    cA_eq_cntM, Nat.and_assoc]

theorem blockA_disj (e e' : Nat) (he : e < 5) (he' : e' < 5) (hne : e ≠ e') : blockA e &&& blockA e' = 0 := by
  interval_cases e <;> interval_cases e' <;> first | (exact absurd rfl hne) | decide

theorem edge_sum (m x e : Nat) (hm : m < 37) (he : e < 5) :
    aE e (x &&& targetT m) = sumF (fun c => cond (Nat.beq (edgeOf m c) e) (profV m x c) 0) (npos m) := by
  obtain ⟨_, hc, hor, _⟩ := cell_facts m hm
  have hcell : ∀ c, c < npos m → cellM m c &&& blockA e = cond (Nat.beq (edgeOf m c) e) (cellM m c) 0 := by
    intro c hcn
    obtain ⟨he1, he2⟩ := (hc c (by have := npos_le m; omega)).2.2.2.1 hcn
    by_cases hq : edgeOf m c = e
    · rw [show Nat.beq (edgeOf m c) e = true by rw [hq]; exact Nat.beq_refl e, cond_true, ← hq, he2]
    · rw [show Nat.beq (edgeOf m c) e = false by
        cases h : Nat.beq (edgeOf m c) e
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hq, cond_false]
      rw [← he2, Nat.and_assoc, blockA_disj _ _ he1 he hq, Nat.and_zero]
  have hB : blockA e &&& MA = blockA e := by interval_cases e <;> decide
  have e1 : (x &&& targetT m) &&& blockA e = x &&& orM (fun c => cellM m c &&& blockA e) (npos m) := by
    rw [← orM_and, hor, Nat.and_assoc x, Nat.and_assoc (targetT m) MA, Nat.and_comm MA (blockA e), hB]
  have disj : ∀ a b, a < b → b < npos m → (cellM m a &&& blockA e) &&& (cellM m b &&& blockA e) = 0 := by
    intro a b hab hb
    have h0 := (hc b (by have := npos_le m; omega)).2.2.2.2.2 a hab
    apply Nat.eq_of_testBit_eq; intro p
    have := congrArg (fun z => z.testBit p) h0
    simp only [Nat.testBit_and, Nat.zero_testBit] at this ⊢
    cases ha : (cellM m a).testBit p <;> cases hb : (cellM m b).testBit p <;> simp_all
  rw [aE_eq_cntM e _ he, e1, ← sum_cells x _ (npos m) disj]
  apply sumF_congr; intro c hcn
  rw [hcell c hcn]
  cases Nat.beq (edgeOf m c) e
  · show cntM (x &&& 0) = 0; rw [Nat.and_zero]; exact cntR_zero_bits 0 0 180 (fun i _ _ => Nat.zero_testBit i)
  · show cntM (x &&& cellM m c) = profV m x c
    unfold profV; rw [show Nat.blt c (npos m) = true by rw [Nat.blt_eq]; exact hcn]; rfl

-- negative cells are full when every point of V minus the target's rejected side is rejected
theorem neg_full (m x : Nat) (hm : m < 37) (h : ∀ p, 45 ≤ p → p < 180 → (targetT m).testBit p = true → x.testBit p = false)
    (c : Nat) (hc1 : npos m ≤ c) (hc2 : c < nf m) : profV m x c = capV m c := by
  obtain ⟨_, hc, _, _⟩ := cell_facts m hm
  have hV := testBit_cellV m c hm hc2 hc1
  have htg := (hc c hc2).2.2.1
  unfold profV capV
  rw [show Nat.blt c (npos m) = false by
    cases hb : Nat.blt c (npos m)
    · rfl
    · rw [Nat.blt_eq] at hb; omega]
  show cntM (rect x &&& cellM m c) = cntM (cellM m c)
  congr 1
  apply Nat.eq_of_testBit_eq; intro p
  rw [Nat.testBit_and]
  cases hp : (cellM m c).testBit p
  · simp
  · have hpv := hV p hp
    have ht : (targetT m).testBit p = true := by
      have := congrArg (fun z => z.testBit p) htg
      simp only [Nat.testBit_and, hp, Bool.and_true] at this
      exact this
    rw [rect_bit _ _ hpv.1 hpv.2, h p hpv.1 hpv.2 ht]; rfl

-- ===== the family Gamma =====
def omegaAt (d e : Nat) : Nat :=
  fld 0x99014 4 (cond (Nat.blt d 5) (Nat.mod (Nat.sub (Nat.add d 5) e) 5) (Nat.mod (Nat.sub (Nat.add e d) 5) 5))

def Gamma (t : Nat) : Prop := cA t ≤ 20 ∨ (cA t ≤ 22 ∧ ∃ d, d < 10 ∧ ∀ e, e < 5 → aE e t ≤ omegaAt d e)

theorem cntR_subA (t s lo n : Nat) (h : ∀ p, lo ≤ p → p < lo + n → t.testBit p = true → s.testBit p = true) :
    cntR t lo n ≤ cntR s lo n := by
  rw [cntR_card, cntR_card]; apply Finset.card_le_card; intro i
  simp only [Finset.mem_filter, Finset.mem_range]; intro hi; exact ⟨hi.1, h _ (by omega) (by omega) hi.2⟩

theorem Gamma_mono {t s : Nat} (h : ∀ p, p < 45 → t.testBit p = true → s.testBit p = true) (hs : Gamma s) : Gamma t := by
  have hA : cA t ≤ cA s := cntR_subA _ _ _ _ (fun p _ h2 => h p (by omega))
  have hE : ∀ e, e < 5 → aE e t ≤ aE e s := fun e he => cntR_subA _ _ _ _ (fun p _ h2 => h p (by omega))
  rcases hs with hs | ⟨hs1, d, hd, hs2⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, d, hd, fun e he => le_trans (hE e he) (hs2 e he)⟩

def omegaGen (k d : Nat) : Nat := srch (fun d' => allBelow 5 (fun e => Nat.beq (omegaAt d (blkA k e)) (omegaAt d' e))) 10

def omegaCheck : Bool :=
  allBelow 19 (fun k => allBelow 10 (fun d => Nat.blt (omegaGen k d) 10 &&
    allBelow 5 (fun e => Nat.beq (omegaAt d (blkA k e)) (omegaAt (omegaGen k d) e))))

set_option maxRecDepth 10000 in
theorem omegaCheck_ok : omegaCheck = true := by decide +kernel

theorem Gamma_gen (k t : Nat) (h : Gamma t) : Gamma (permW [k] t) := by
  have hA : cA (permW [k] t) = cA t := cA_permW _ _
  by_cases hk : k < 19
  · rcases h with h | ⟨h1, d, hd, h2⟩
    · exact Or.inl (by omega)
    · have hc := allBelow_spec _ _ (allBelow_spec _ _ omegaCheck_ok k hk) d hd
      simp only [Bool.and_eq_true, Nat.blt_eq] at hc
      refine Or.inr ⟨by omega, omegaGen k d, hc.1, fun e he => ?_⟩
      rw [aE_gen k e t hk he, ← Nat.eq_of_beq_eq_true (allBelow_spec _ _ hc.2 e he)]
      exact h2 _ (blk_lt k e hk he).1
  · have hb : ∀ p, p < 180 → (permW [k] t).testBit p = t.testBit p := fun p hp => by
      show (permP (genP k) t).testBit p = _
      rw [testBit_permP]; simp [genP, hk, hp]
    exact Gamma_mono (fun p hp ht => by rw [hb p (by omega)] at ht; exact ht) h

theorem Gamma_permW (w : List Nat) (t : Nat) (h : Gamma t) : Gamma (permW w t) := by
  induction w generalizing t with
  | nil => exact h
  | cons k w ih => exact ih _ (Gamma_gen k t h)

-- ===== full-lane popcount =====
def pstepsR8 (X R : Nat) : Nat := pstep (pstep (pstepsR X R) (Nat.mul Q64 R) 64) (Nat.mul Q128 R) 128

theorem lanePop8 (X n : Nat) (hX : X < 2 ^ (256 * n)) :
    pstepsR8 X (rep 256 n) = pk (fun j => cntR X (256 * j) 256) 256 n := by
  unfold pstepsR8
  rw [lanePop X n hX]
  rw [show pk (fun j => cntR X (64 * j) 64) 64 (4 * n) = pk (fun j => cntR X (64 * j) 64) 64 (2 * (2 * n)) by
    rw [show 2 * (2 * n) = 4 * n by ring]]
  rw [pstep_eq X 64 (2 * n) (by norm_num) _ (mask_rep 64 2 n Q64 Q64_eq (by norm_num) (by norm_num))]
  rw [show pk (fun j => cntR X (2 * 64 * j) (2 * 64)) (2 * 64) (2 * n) = pk (fun j => cntR X (128 * j) 128) 128 (2 * (1 * n)) by
    rw [show 2 * (1 * n) = 2 * n by ring]]
  rw [pstep_eq X 128 (1 * n) (by norm_num) _ (mask_rep 128 1 n Q128 Q128_eq (by norm_num) (by norm_num))]
  rw [show 1 * n = n by ring]

-- ===== zero lanes =====
def zl (Z n : Nat) : Nat :=
  Nat.shiftRight (Nat.land (Nat.xor (Nat.add Z (Nat.mul (Nat.sub (2 ^ 255) 1) (rep 256 n))) (Nat.shiftLeft (rep 256 n) 255))
    (Nat.shiftLeft (rep 256 n) 255)) 255

theorem zl_spec (z : Nat → Nat) (n : Nat) (hz : ∀ j, j < n → z j < 2 ^ 255) (j : Nat) (hj : j < n) :
    (zl (pk z 256 n) n).testBit (256 * j) = decide (z j = 0) := by
  have hR := rep_eq 256 n (by norm_num)
  have hT : Nat.shiftLeft (rep 256 n) 255 = pk (fun _ => 2 ^ 255) 256 n := by
    rw [hR]; show pk _ 256 n <<< 255 = _
    rw [Nat.shiftLeft_eq, Nat.mul_comm, pk_mul]; apply pk_congr; intro _ _; ring
  have hW : Nat.add (pk z 256 n) (Nat.mul (Nat.sub (2 ^ 255) 1) (rep 256 n)) = pk (fun i => z i + (2 ^ 255 - 1)) 256 n := by
    rw [hR]; show pk z 256 n + (2 ^ 255 - 1) * pk _ 256 n = _; rw [pk_const, pk_add]
  have fW : Fits (fun i => z i + (2 ^ 255 - 1)) 256 n := fun i hi => by
    have := hz i hi; show z i + (2 ^ 255 - 1) < 2 ^ 256
    have : (2 : Nat) ^ 256 = 2 ^ 255 + 2 ^ 255 := by norm_num
    omega
  have fT : Fits (fun _ => 2 ^ 255) 256 n := fun _ _ => by norm_num
  unfold zl
  rw [hW, hT]
  show (((pk _ 256 n ^^^ pk _ 256 n) &&& pk _ 256 n) >>> 255).testBit (256 * j) = _
  rw [pk_xor _ _ _ _ (by norm_num) fW fT]
  have fX : Fits (fun i => (z i + (2 ^ 255 - 1)) ^^^ 2 ^ 255) 256 n := fun i hi => Nat.xor_lt_two_pow (fW i hi) (fT i hi)
  rw [pk_land _ _ _ _ (by norm_num) fX fT, Nat.testBit_shiftRight, show 255 + 256 * j = 256 * j + 255 by ring]
  have fY : Fits (fun i => ((z i + (2 ^ 255 - 1)) ^^^ 2 ^ 255) &&& 2 ^ 255) 256 n := fun i hi =>
    lt_of_le_of_lt Nat.and_le_left (fX i hi)
  rw [testBit_pk _ 256 n fY j 255 (by norm_num)]
  simp only [hj, decide_true, Bool.true_and, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_self, Bool.and_true]
  have h1 := hz j hj
  by_cases h0 : z j = 0
  · rw [h0, Nat.zero_add, Nat.testBit_two_pow_sub_one]; simp [h0]
  · have e : z j + (2 ^ 255 - 1) = 2 ^ 255 + (z j - 1) := by omega
    rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega)]; simp [h0]

-- ===== fieldwise comparison x <= y on 31 fields of each lane =====
def G8m31 : Nat := pk (fun q => cond (Nat.blt q 31) 128 0) 8 32

def cbitCheck : Bool := allBelow 128 (fun x => allBelow 128 (fun y => Nat.beq (cbit x y) (cond (Nat.ble x y) 1 0)))

set_option maxRecDepth 100000 in
theorem cbitCheck_ok : cbitCheck = true := by decide +kernel

theorem cbit_eq (x y : Nat) (hx : x < 128) (hy : y < 128) : cbit x y = cond (Nat.ble x y) 1 0 :=
  Nat.eq_of_beq_eq_true (allBelow_spec _ _ (allBelow_spec _ _ cbitCheck_ok x hx) y hy)

def leLanes (X Y n : Nat) : Nat :=
  zl (Nat.xor (Nat.land (Nat.sub (Nat.lor Y (Nat.mul G8m31 (rep 256 n))) X) (Nat.mul G8m31 (rep 256 n))) (Nat.mul G8m31 (rep 256 n))) n

def Lanes (v : Nat → Nat → Nat) (n : Nat) : Nat := pk (fun j => pk (v j) 8 32) 256 n

theorem lanes_view (v : Nat → Nat → Nat) (n : Nat) : Lanes v n = pk (fun q => v (q / 32) (q % 32)) 8 (32 * n) := by
  unfold Lanes; rw [show (256 : Nat) = 8 * 32 by rfl]; exact pk_nest v 8 32 n (by norm_num)

theorem const_lanes (c : Nat) (v : Nat → Nat) (hc : c = pk v 8 32) (n : Nat) :
    Nat.mul c (rep 256 n) = Lanes (fun _ => v) n := by
  show c * rep 256 n = _; rw [rep_eq 256 n (by norm_num), pk_const, hc]; rfl

def hfld (xv yv c : Nat) : Nat := cond (Nat.blt c 31) (cond (Nat.ble xv yv) 0 128) 0

theorem pk_eq_zero (f : Nat → Nat) (w n : Nat) (h : pk f w n = 0) (hw : 0 < w) (hf : Fits f w n) : ∀ i, i < n → f i = 0 := by
  intro i hi
  have := pk_field f w n i hw hf hi
  rw [h] at this; simpa using this.symm

theorem le_field (xv yv c : Nat) (hx : xv < 128) (hy : yv < 128) (hc32 : c < 32) (h31 : c = 31 → xv = 0 ∧ yv = 0) :
    (((yv ||| cond (Nat.blt c 31) 128 0) - xv) &&& cond (Nat.blt c 31) 128 0) ^^^ cond (Nat.blt c 31) 128 0 = hfld xv yv c ∧
    xv ≤ (yv ||| cond (Nat.blt c 31) 128 0) ∧ (yv ||| cond (Nat.blt c 31) 128 0) - xv < 256 := by
  unfold hfld
  by_cases hc : c < 31
  · have hb : Nat.blt c 31 = true := by rw [Nat.blt_eq]; exact hc
    simp only [hb, cond_true]
    obtain ⟨f1, f2, f3, f4, -⟩ := smin_facts xv yv hx hy
    refine ⟨?_, f1, f2⟩
    rw [f3, cbit_eq xv yv hx hy]
    cases Nat.ble xv yv <;> decide
  · have hb : Nat.blt c 31 = false := by
      cases h : Nat.blt c 31
      · rfl
      · rw [Nat.blt_eq] at h; exact absurd h hc
    have h0 : c = 31 := by omega
    simp only [hb, cond_false]
    obtain ⟨e1, e2⟩ := h31 h0; subst e1; subst e2; simp [hfld, hb]

theorem leLanes_spec (x y : Nat → Nat → Nat) (n : Nat) (hx : ∀ j q, x j q < 128) (hy : ∀ j q, y j q < 128)
    (hx31 : ∀ j, x j 31 = 0) (hy31 : ∀ j, y j 31 = 0) (j : Nat) (hj : j < n) :
    (leLanes (Lanes x n) (Lanes y n) n).testBit (256 * j) = true ↔ ∀ q, q < 31 → x j q ≤ y j q := by
  let g := fun q : Nat => cond (Nat.blt q 31) 128 0
  have hg : Nat.mul G8m31 (rep 256 n) = Lanes (fun _ => g) n := const_lanes _ _ rfl n
  have F : ∀ f : Nat → Nat, (∀ q, f q < 256) → Fits f 8 (32 * n) := fun f h q _ => h q
  have fy := F (fun q => y (q / 32) (q % 32)) (fun q => by have := hy (q / 32) (q % 32); omega)
  have fx := F (fun q => x (q / 32) (q % 32)) (fun q => by have := hx (q / 32) (q % 32); omega)

  have fg := F (fun q => g (q % 32)) (fun q => by show cond _ _ _ < 256; cases Nat.blt (q % 32) 31 <;> simp)
  have lf := fun q => le_field (x (q / 32) (q % 32)) (y (q / 32) (q % 32)) (q % 32) (hx _ _) (hy _ _)
    (Nat.mod_lt _ (by norm_num)) (fun h => by rw [h]; exact ⟨hx31 _, hy31 _⟩)
  unfold leLanes
  rw [hg, lanes_view, lanes_view, lanes_view]
  show (zl ((((pk _ 8 (32 * n) ||| pk _ 8 (32 * n)) - pk _ 8 (32 * n)) &&& pk _ 8 (32 * n)) ^^^ pk _ 8 (32 * n)) n).testBit (256 * j) = true ↔ _
  rw [pk_lor _ _ _ _ (by norm_num) fy fg, pk_sub _ _ _ _ (fun q _ => (lf q).2.1)]
  have fd := F (fun q => (y (q / 32) (q % 32) ||| g (q % 32)) - x (q / 32) (q % 32)) (fun q => (lf q).2.2)
  rw [pk_land _ _ _ _ (by norm_num) fd fg]
  have fa := F (fun q => ((y (q / 32) (q % 32) ||| g (q % 32)) - x (q / 32) (q % 32)) &&& g (q % 32))
    (fun q => lt_of_le_of_lt Nat.and_le_left ((lf q).2.2))
  rw [pk_xor _ _ _ _ (by norm_num) fa fg]
  rw [pk_congr _ (fun q => hfld (x (q / 32) (q % 32)) (y (q / 32) (q % 32)) (q % 32)) 8 (32 * n) (fun q _ => (lf q).1)]
  rw [← lanes_view (fun j c => hfld (x j c) (y j c) c) n]
  unfold Lanes
  have fh : ∀ j, Fits (fun c => hfld (x j c) (y j c) c) 8 32 := fun j c _ => by
    show hfld (x j c) (y j c) c < 2 ^ 8
    unfold hfld; cases Nat.blt c 31 <;> cases Nat.ble (x j c) (y j c) <;> decide
  have hz0 : ∀ j c, 31 ≤ c → c < 32 → hfld (x j c) (y j c) c = 0 := by
    intro j c h1 h2; have : c = 31 := by omega
    subst this; rfl
  have hz : ∀ j, j < n → pk (fun c => hfld (x j c) (y j c) c) 8 32 < 2 ^ 255 := fun j _ => by
    rw [← pk_pad _ 8 31 32 (by norm_num) (hz0 j)]
    exact lt_of_lt_of_le (pk_lt _ 8 31 (fun c hc => fh j c (by omega))) (by norm_num)
  rw [zl_spec _ n hz j hj, decide_eq_true_iff]
  constructor
  · intro h0 q hq
    have := pk_eq_zero _ 8 32 h0 (by norm_num) (fh j) q (by omega)
    unfold hfld at this
    rw [show Nat.blt q 31 = true by rw [Nat.blt_eq]; exact hq] at this
    cases hb : Nat.ble (x j q) (y j q)
    · rw [hb] at this; exact absurd this (by decide)
    · rw [Nat.ble_eq] at hb; exact hb
  · intro h0
    have hz1 : ∀ c, c < 32 → hfld (x j c) (y j c) c = 0 := by
      intro c hc
      by_cases h31 : c < 31
      · unfold hfld
        rw [show Nat.blt c 31 = true by rw [Nat.blt_eq]; exact h31,
          show Nat.ble (x j c) (y j c) = true by rw [Nat.ble_eq]; exact h0 c h31]
        rfl
      · exact hz0 j c (by omega) hc
    rw [pk_congr _ (fun _ => 0) 8 32 hz1]
    exact pk_zero 8 32

-- ===== fieldwise transitions on lanes =====
def G8u : Nat := pk (fun _ => 128) 8 32
def F7u : Nat := pk (fun _ => 127) 8 32

def trans (op : Bool) (X Y CAP POS NEG n : Nat) : Nat :=
  cond op
    (Nat.lor (Nat.land (swarMin (Nat.mul G8u (rep 256 n)) (Nat.mul F7u (rep 256 n)) CAP (Nat.add X Y)) POS)
      (Nat.land (swarMin (Nat.mul G8u (rep 256 n)) (Nat.mul F7u (rep 256 n)) X Y) NEG))
    (Nat.lor (Nat.land (swarMin (Nat.mul G8u (rep 256 n)) (Nat.mul F7u (rep 256 n)) X Y) POS)
      (Nat.land (swarMin (Nat.mul G8u (rep 256 n)) (Nat.mul F7u (rep 256 n)) CAP (Nat.add X Y)) NEG))

def selF (b : Bool) : Nat := cond b 255 0

theorem and_sel (v : Nat) (b : Bool) (hv : v < 256) : v &&& selF b = cond b v 0 := by
  cases b
  · show v &&& 0 = 0; simp
  · show v &&& 255 = v
    rw [show (255 : Nat) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hv]

theorem combine_sel (a b : Nat → Nat) (isPos isNeg : Nat → Bool) (N : Nat) (fa : ∀ q, a q < 256) (fb : ∀ q, b q < 256)
    (hdis : ∀ c, isPos c = true → isNeg c = false) :
    (pk (fun q => a q) 8 N &&& pk (fun q => selF (isPos (q % 32))) 8 N) |||
      (pk (fun q => b q) 8 N &&& pk (fun q => selF (isNeg (q % 32))) 8 N) =
    pk (fun q => cond (isPos (q % 32)) (a q) (cond (isNeg (q % 32)) (b q) 0)) 8 N := by
  have F : ∀ f : Nat → Nat, (∀ q, f q < 256) → Fits f 8 N := fun f h q _ => h q
  have fp := F (fun q => selF (isPos (q % 32))) (fun q => by show selF _ < 256; cases isPos (q % 32) <;> decide)
  have fn := F (fun q => selF (isNeg (q % 32))) (fun q => by show selF _ < 256; cases isNeg (q % 32) <;> decide)
  rw [pk_land _ _ _ _ (by norm_num) (F a fa) fp, pk_land _ _ _ _ (by norm_num) (F b fb) fn]
  rw [pk_lor _ _ _ _ (by norm_num) (F _ (fun q => lt_of_le_of_lt Nat.and_le_left (fa q)))
    (F _ (fun q => lt_of_le_of_lt Nat.and_le_left (fb q)))]
  apply pk_congr; intro q _
  rw [and_sel _ _ (fa q), and_sel _ _ (fb q)]
  cases hP : isPos (q % 32)
  · cases isNeg (q % 32) <;> simp
  · rw [hdis _ hP]; simp

theorem trans_spec (op : Bool) (x y : Nat → Nat → Nat) (cap : Nat → Nat) (isPos isNeg : Nat → Bool) (n : Nat)
    (hx : ∀ j c, x j c < 64) (hy : ∀ j c, y j c < 64) (hc : ∀ c, cap c < 64)
    (hdis : ∀ c, isPos c = true → isNeg c = false) :
    trans op (Lanes x n) (Lanes y n) (Lanes (fun _ => cap) n) (Lanes (fun _ c => selF (isPos c)) n)
      (Lanes (fun _ c => selF (isNeg c)) n) n =
    Lanes (fun j c => cond (isPos c) (cond op (min (cap c) (x j c + y j c)) (min (x j c) (y j c)))
      (cond (isNeg c) (cond op (min (x j c) (y j c)) (min (cap c) (x j c + y j c))) 0)) n := by
  have hG : Nat.mul G8u (rep 256 n) = pk (fun _ => 128) 8 (32 * n) := by
    rw [const_lanes G8u (fun _ => 128) rfl n, lanes_view]
  have hF : Nat.mul F7u (rep 256 n) = pk (fun _ => 127) 8 (32 * n) := by
    rw [const_lanes F7u (fun _ => 127) rfl n, lanes_view]
  unfold trans
  rw [hG, hF]
  simp only [lanes_view]
  rw [show Nat.add (pk (fun q => x (q / 32) (q % 32)) 8 (32 * n)) (pk (fun q => y (q / 32) (q % 32)) 8 (32 * n)) =
    pk (fun q => x (q / 32) (q % 32) + y (q / 32) (q % 32)) 8 (32 * n) from pk_add _ _ _ _]
  have m1 := swarMin_pk (fun q => x (q / 32) (q % 32)) (fun q => y (q / 32) (q % 32)) (32 * n)
    (fun q _ => by have := hx (q / 32) (q % 32); omega) (fun q _ => by have := hy (q / 32) (q % 32); omega)
  have m2 := swarMin_pk (fun q => cap (q % 32)) (fun q => x (q / 32) (q % 32) + y (q / 32) (q % 32)) (32 * n)
    (fun q _ => by have := hc (q % 32); omega) (fun q _ => by have := hx (q / 32) (q % 32); have := hy (q / 32) (q % 32); omega)
  rw [m1, m2]
  have b1 : ∀ q, min (x (q / 32) (q % 32)) (y (q / 32) (q % 32)) < 256 := fun q => by
    have := hx (q / 32) (q % 32); have := min_le_left (x (q / 32) (q % 32)) (y (q / 32) (q % 32)); omega
  have b2 : ∀ q, min (cap (q % 32)) (x (q / 32) (q % 32) + y (q / 32) (q % 32)) < 256 := fun q => by
    have := hc (q % 32); have := min_le_left (cap (q % 32)) (x (q / 32) (q % 32) + y (q / 32) (q % 32)); omega
  cases op
  · show (pk _ 8 (32 * n) &&& pk _ 8 (32 * n)) ||| (pk _ 8 (32 * n) &&& pk _ 8 (32 * n)) = _
    rw [combine_sel _ _ isPos isNeg (32 * n) b1 b2 hdis]; rfl
  · show (pk _ 8 (32 * n) &&& pk _ 8 (32 * n)) ||| (pk _ 8 (32 * n) &&& pk _ 8 (32 * n)) = _
    rw [combine_sel _ _ isPos isNeg (32 * n) b2 b1 hdis]; rfl

theorem sumF_add (g : Nat → Nat) (a b : Nat) : sumF g (a + b) = sumF g a + sumF (fun t => g (a + t)) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [show a + (b + 1) = (a + b) + 1 by omega, sumF_succ, ih, sumF_succ]; ring

theorem sumF_mono (g : Nat → Nat) (a b : Nat) (h : a ≤ b) : sumF g a ≤ sumF g b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [sumF_add]; omega

-- ===== sums of the 32 fields of each lane =====
def dbl (S k : Nat) : Nat := Nat.add S (Nat.shiftRight S (Nat.mul 8 k))
def bsum32 (S : Nat) : Nat := dbl (dbl (dbl (dbl (dbl S 1) 2) 4) 8) 16
def laneSum (S n : Nat) : Nat := Nat.land (bsum32 S) (Nat.mul 255 (rep 256 n))

def win (s : Nat → Nat) (k q : Nat) : Nat := sumF (fun t => s (q + t)) k

theorem win_dbl (s : Nat → Nat) (k q : Nat) : win s k q + win s k (q + k) = win s (k + k) q := by
  unfold win; rw [sumF_add]; congr 1; apply sumF_congr; intro t _; congr 1; ring

theorem dbl_spec (a : Nat → Nat) (N k : Nat) (hz : ∀ q, N ≤ q → a q = 0) (hs : ∀ q, a q + a (q + k) < 256) :
    dbl (pk a 8 N) k = pk (fun q => a q + a (q + k)) 8 N := by
  have fa : Fits a 8 N := fun q _ => by have := hs q; show a q < 2 ^ 8; omega
  unfold dbl
  show pk a 8 N + pk a 8 N >>> (8 * k) = _
  rw [pk_shr_fields a 8 N k (by norm_num) fa]
  rw [pk_pad (fun q => a (q + k)) 8 (N - k) N (by omega) (fun q h1 _ => hz _ (by omega)), pk_add]

theorem bsum32_spec (s : Nat → Nat) (N : Nat) (hz : ∀ q, N ≤ q → s q = 0) (hw : ∀ q, win s 32 q < 256) :
    bsum32 (pk s 8 N) = pk (fun q => win s 32 q) 8 N := by
  have hwz : ∀ k q, N ≤ q → win s k q = 0 := fun k q hq => by
    unfold win; induction k with
    | zero => rfl
    | succ k ih => rw [sumF_succ, ih, hz _ (by omega)]
  have hwle : ∀ k q, k ≤ 32 → win s k q ≤ win s 32 q := fun k q hk => sumF_mono _ _ _ hk
  have step : ∀ k, k + k ≤ 32 → dbl (pk (win s k) 8 N) k = pk (win s (k + k)) 8 N := by
    intro k hk
    rw [dbl_spec (win s k) N k (fun q hq => hwz k q hq) (fun q => by
      rw [win_dbl]; have := hwle (k + k) q hk; have := hw q; omega)]
    apply pk_congr; intro q _; exact win_dbl s k q
  have h1 : pk s 8 N = pk (win s 1) 8 N := pk_congr _ _ _ _ (fun q _ => by show s q = Nat.add 0 (s (q + 0)); simp)
  unfold bsum32
  rw [h1, step 1 (by norm_num), step 2 (by norm_num), step 4 (by norm_num), step 8 (by norm_num), step 16 (by norm_num)]

theorem low_byte (v : Nat → Nat) (n : Nat) (hv : ∀ q, v q < 256) :
    Nat.land (pk v 8 (32 * n)) (Nat.mul 255 (rep 256 n)) = pk (fun j => v (32 * j)) 256 n := by
  have hm : Nat.mul 255 (rep 256 n) = pk (fun q => cond (Nat.beq (q % 32) 0) 255 0) 8 (32 * n) := by
    rw [const_lanes 255 (fun c => cond (Nat.beq c 0) 255 0) (by decide) n, lanes_view]
  rw [hm]
  have F : ∀ f : Nat → Nat, (∀ q, f q < 256) → Fits f 8 (32 * n) := fun f h q _ => h q
  show pk v 8 (32 * n) &&& pk _ 8 (32 * n) = _
  rw [pk_land _ _ _ _ (by norm_num) (F v hv) (F _ (fun q => by show cond _ _ _ < 256; cases Nat.beq (q % 32) 0 <;> decide))]
  rw [← lanes_view (fun j c => v (32 * j + c) &&& cond (Nat.beq c 0) 255 0) n |>.trans (pk_congr _ _ _ _ (fun q _ => by
    show v (32 * (q / 32) + q % 32) &&& cond (Nat.beq (q % 32) 0) 255 0 = _; rw [show 32 * (q / 32) + q % 32 = q by omega]))]
  unfold Lanes; apply pk_congr; intro j _
  rw [show pk (fun c => v (32 * j + c) &&& cond (Nat.beq c 0) 255 0) 8 32 = pk (fun c => cond (Nat.beq c 0) (v (32 * j)) 0) 8 32 from
    pk_congr _ _ _ _ (fun c _ => by
      cases hc : Nat.beq c 0
      · show v (32 * j + c) &&& 0 = 0; simp
      · have := Nat.eq_of_beq_eq_true hc; subst this
        show v (32 * j + 0) &&& 255 = v (32 * j)
        rw [Nat.add_zero, show (255 : Nat) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hv _)])]
  rw [← pk_pad (fun c => cond (Nat.beq c 0) (v (32 * j)) 0) 8 1 32 (by norm_num) (fun c h1 _ => by
    rw [show Nat.beq c 0 = false by cases c; omega; rfl]; rfl)]
  simp [pk]

theorem laneSum_spec (s : Nat → Nat) (n : Nat) (hz : ∀ q, 32 * n ≤ q → s q = 0) (hw : ∀ q, win s 32 q < 256) :
    laneSum (pk s 8 (32 * n)) n = pk (fun j => win s 32 (32 * j)) 256 n := by
  unfold laneSum; rw [bsum32_spec s _ hz hw, low_byte _ n hw]

-- ===== thresholds on lane values =====
def thrL (P n th : Nat) : Nat := Nat.land (Nat.shiftRight (Nat.add P (Nat.mul (Nat.sub 256 th) (rep 256 n))) 8) (rep 256 n)

theorem thrL_spec (p : Nat → Nat) (n th : Nat) (hp : ∀ j, j < n → p j < 256) (hth : th ≤ 256) (j : Nat) (hj : j < n) :
    (thrL (pk p 256 n) n th).testBit (256 * j) = decide (th ≤ p j) := by
  have hR := rep_eq 256 n (by norm_num)
  unfold thrL
  rw [show Nat.mul (Nat.sub 256 th) (rep 256 n) = (256 - th) * rep 256 n from rfl, hR, pk_const]
  show (((pk p 256 n + pk _ 256 n) >>> 8) &&& pk _ 256 n).testBit (256 * j) = _
  rw [pk_add, Nat.testBit_and, Nat.testBit_shiftRight, show 8 + 256 * j = 256 * j + 8 by ring]
  have f1 : Fits (fun i => p i + (256 - th)) 256 n := fun i hi => by
    have := hp i hi; show _ < 2 ^ 256; exact lt_of_lt_of_le (show p i + (256 - th) < 2 ^ 9 by omega) (by norm_num)
  have f2 : Fits (fun _ => 1) 256 n := fun _ _ => by norm_num
  rw [testBit_pk _ 256 n f1 j 8 (by norm_num), show 256 * j = 256 * j + 0 by rfl, testBit_pk _ 256 n f2 j 0 (by norm_num)]
  simp only [hj, decide_true, Bool.true_and, Nat.testBit_zero, Nat.one_mod, decide_true, Bool.and_true]
  have := hp j hj
  by_cases h : th ≤ p j
  · rw [testBit8 _ (by omega) (by omega)]; simp [h]
  · rw [Nat.testBit_lt_two_pow (show p j + (256 - th) < 2 ^ 8 by omega)]; simp [h]

-- ===== bits of zero-lane masks sit at lane starts =====
theorem testBit_shr' (x s p : Nat) : (Nat.shiftRight x s).testBit p = x.testBit (s + p) := Nat.testBit_shiftRight x

theorem ex_bit (x : Nat) (h : x ≠ 0) : ∃ p, x.testBit p = true := by
  by_contra hc
  push_neg at hc
  apply h
  apply Nat.eq_of_testBit_eq; intro p
  simpa using hc p

theorem zl_pos (Z n p : Nat) (h : (zl Z n).testBit p = true) : ∃ j, j < n ∧ p = 256 * j := by
  unfold zl at h
  rw [testBit_shr', testBit_land'] at h
  have hT : (Nat.shiftLeft (rep 256 n) 255).testBit (255 + p) = true := by
    simp only [Bool.and_eq_true] at h; exact h.2
  have e : Nat.shiftLeft (rep 256 n) 255 = pk (fun _ => 2 ^ 255) 256 n := by
    rw [rep_eq 256 n (by norm_num)]; show pk _ 256 n <<< 255 = _
    rw [Nat.shiftLeft_eq, Nat.mul_comm, pk_mul]; apply pk_congr; intro _ _; ring
  rw [e, testBit_pk' _ 256 n (by norm_num) (fun _ _ => by norm_num)] at hT
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_two_pow] at hT
  refine ⟨(255 + p) / 256, hT.1, ?_⟩
  have := hT.2; omega

theorem zl_nonzero (Z n : Nat) (h : zl Z n ≠ 0) : ∃ j, j < n ∧ (zl Z n).testBit (256 * j) = true := by
  obtain ⟨p, hp⟩ := ex_bit _ h
  obtain ⟨j, hj, rfl⟩ := zl_pos Z n p hp
  exact ⟨j, hj, hp⟩

-- ===== context data as lanes =====
def gRect (g : Nat) : Nat := gate (Nat.beq (Nat.mod g 2) 1) (varAt (Nat.div g 30)) (varAt (Nat.mod (Nat.div g 2) 15))
def R450 : Nat := pk gRect 256 450
def repL (v n : Nat) : Nat := Nat.mul v (rep 256 n)

def eVal (m off k c : Nat) : Nat := cond (Nat.blt c (nf m)) (fld (cdP m) 5 (Nat.add off (Nat.add (Nat.mul k (nf m)) c))) 0
def LE2 (m : Nat) : Nat := Lanes (eVal m 0) (nE2 m)
def LE3A (m : Nat) : Nat := Lanes (eVal m (Nat.mul (nE2 m) (nf m))) (nE3A m)
def LE3B (m : Nat) : Nat := Lanes (eVal m (Nat.mul (Nat.add (nE2 m) (nE3A m)) (nf m))) (nE3B m)

def profC (m x c : Nat) : Nat :=
  cond (Nat.blt c (npos m)) (popc256 (Nat.land x (cellM m c))) (popc256 (Nat.land (Nat.xor x MV) (cellM m c)))
def selRect (m k : Nat) : Nat := gRect (fld (cdS m) 9 k)
def e1Val (m k c : Nat) : Nat := cond (Nat.blt c (nf m)) (profC m (selRect m k) c) 0
def LE1 (m : Nat) : Nat := Lanes (e1Val m) (nSel m)

def capVal (m c : Nat) : Nat := cond (Nat.blt c (nf m)) (capC m c) 0
def isPosC (m c : Nat) : Bool := Nat.blt c (npos m)
def isNegC (m c : Nat) : Bool := Nat.ble (npos m) c && Nat.blt c (nf m)
def CAPL (m n : Nat) : Nat := Lanes (fun _ => capVal m) n
def POSL (m n : Nat) : Nat := Lanes (fun _ c => selF (isPosC m c)) n
def NEGL (m n : Nat) : Nat := Lanes (fun _ c => selF (isNegC m c)) n
def CAPNL (m n : Nat) : Nat := Lanes (fun _ c => cond (isNegC m c) (capC m c) 0) n
def EML (m e n : Nat) : Nat := Lanes (fun _ c => selF (Nat.blt c (npos m) && Nat.beq (edgeOf m c) e)) n
def OML (d : Nat) : Nat := pk (fun c => cond (Nat.blt c 5) (omegaAt d c) 0) 8 32

-- profile lanes of packed rectangles
def profAcc (m R n : Nat) (C : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun c acc => Nat.add acc (Nat.shiftLeft
    (pstepsR8 (Nat.land (cond (Nat.blt c (npos m)) R (Nat.xor R (Nat.mul MV (rep 256 n)))) (Nat.mul (cellM m c) (rep 256 n))) (rep 256 n))
    (Nat.mul 8 c))) C
def profLanes (m R n : Nat) : Nat := profAcc m R n (nf m)

-- the checks
def anyLE (tau L n : Nat) : Bool := !Nat.beq (leLanes (repL tau n) L n) 0

def v1Check (m : Nat) : Bool :=
  Nat.beq (Nat.land (orM (fun k => leLanes (profLanes m R450 450) (repL (fld (LE1 m) 256 k) 450) 450) (nSel m)) (rep 256 450))
    (rep 256 450)

def transL (o : Bool) (m x L n : Nat) : Nat := trans o (repL x n) L (CAPL m n) (POSL m n) (NEGL m n) n

def v2Check (m : Nat) : Bool :=
  allBelow (nSel m) (fun i => allBelow 2 (fun o => allBelow (Nat.add i 1) (fun j =>
    anyLE (fld (transL (Nat.beq o 1) m (fld (LE1 m) 256 i) (LE1 m) (nSel m)) 256 j) (LE2 m) (nE2 m))))

def qA (m T n i : Nat) : Nat := Nat.land (thrL (laneSum (Nat.land T (POSL m n)) n) n 21) (rep 256 (Nat.add i 1))
def qB (m T n i : Nat) : Nat := Nat.land (zl (Nat.xor (Nat.land T (NEGL m n)) (CAPNL m n)) n) (rep 256 (Nat.add i 1))

def v3Check (m : Nat) : Bool :=
  allBelow (nE2 m) (fun i => allBelow 2 (fun o =>
    scanB 256 (fun j => anyLE (fld (transL (Nat.beq o 1) m (fld (LE2 m) 256 i) (LE2 m) (nE2 m)) 256 j) (LE3A m) (nE3A m))
      (qA m (transL (Nat.beq o 1) m (fld (LE2 m) 256 i) (LE2 m) (nE2 m)) (nE2 m) i) 9 0 (nE2 m) &&
    scanB 256 (fun j => anyLE (fld (transL (Nat.beq o 1) m (fld (LE2 m) 256 i) (LE2 m) (nE2 m)) 256 j) (LE3B m) (nE3B m))
      (qB m (transL (Nat.beq o 1) m (fld (LE2 m) 256 i) (LE2 m) (nE2 m)) (nE2 m) i) 9 0 (nE2 m)))

def edge5 (m T n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun e acc => Nat.add acc (Nat.shiftLeft (laneSum (Nat.land T (EML m e n)) n) (Nat.mul 8 e))) 5

def gammaLanes (m T n : Nat) : Nat :=
  Nat.lor (Nat.xor (rep 256 n) (thrL (laneSum (Nat.land T (POSL m n)) n) n 21))
    (Nat.land (Nat.xor (rep 256 n) (thrL (laneSum (Nat.land T (POSL m n)) n) n 23))
      (orM (fun d => leLanes (edge5 m T n) (repL (OML d) n) n) 10))

def v4Check (m : Nat) : Bool :=
  allBelow (nE3A m) (fun i =>
    Nat.beq (Nat.land (qB m (transL false m (fld (LE3A m) 256 i) (LE3A m) (nE3A m)) (nE3A m) i)
      (Nat.xor (rep 256 (nE3A m)) (gammaLanes m (transL false m (fld (LE3A m) 256 i) (LE3A m) (nE3A m)) (nE3A m)))) 0) &&
  allBelow (nE3B m) (fun i =>
    Nat.beq (Nat.land (rep 256 (Nat.add i 1))
      (Nat.xor (rep 256 (nE3B m)) (gammaLanes m (transL true m (fld (LE3B m) 256 i) (LE3B m) (nE3B m)) (nE3B m)))) 0)

def dataCheck (m : Nat) : Bool :=
  allBelow (Nat.add (Nat.add (nE2 m) (nE3A m)) (nE3B m)) (fun k => allBelow (nf m) (fun c => Nat.ble (eVal m 0 k c) (capC m c))) &&
  Nat.ble (sumF (capC m) (npos m)) 45 && Nat.ble 1 (nSel m) && Nat.ble (nSel m) 64 && Nat.ble (nE2 m) 256 &&
  Nat.ble (nE3A m) 300 && Nat.ble (nE3B m) 64

def compCheck (m : Nat) : Bool := dataCheck m && v1Check m && v2Check m && v3Check m && v4Check m

theorem orM_bit (M : Nat → Nat) (n p : Nat) (h : (orM M n).testBit p = true) : ∃ k, k < n ∧ (M k).testBit p = true := by
  induction n with
  | zero => simp [orM] at h
  | succ n ih =>
    rw [orM_succ, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨k, hk, hb⟩ := ih h; exact ⟨k, by omega, hb⟩
    · exact ⟨n, by omega, h⟩

theorem rep_bit (n j : Nat) (hj : j < n) : (rep 256 n).testBit (256 * j) = true := by
  rw [rep_eq 256 n (by norm_num), show 256 * j = 256 * j + 0 by rfl, testBit_pk _ 256 n (fun _ _ => by norm_num) j 0 (by norm_num)]
  simp [hj]

-- profile values agree with the computed ones
theorem profC_eq (m x c : Nat) (hm : m < 37) (hx : x < 2 ^ 180) (hc : c < nf m) : profC m x c = profV m x c := by
  obtain ⟨_, hcf, _, _⟩ := cell_facts m hm
  have hcl := (hcf c hc).1
  unfold profC profV
  cases Nat.blt c (npos m)
  · show popc256 (Nat.land (Nat.xor x MV) (cellM m c)) = cntM (rect x &&& cellM m c)
    rw [cntM_eq_popc _ (lt_of_le_of_lt Nat.and_le_right hcl)]; rfl
  · show popc256 (Nat.land x (cellM m c)) = cntM (x &&& cellM m c)
    rw [cntM_eq_popc _ (lt_of_le_of_lt Nat.and_le_right hcl)]; rfl

theorem profV_le27 (m x c : Nat) (hm : m < 37) (hc : c < nf m) : profV m x c ≤ 27 := by
  have := profV_le_cap m x c hm hc
  rw [capV_eq m c hm hc] at this
  exact le_trans this ((cell_facts m hm).2.1 c hc).2.1

theorem gRect_tv (g : Nat) : gRect g = tv (fun z => bop (Nat.beq (g % 2) 1) (z (fv (g / 30))) (z (fv (g / 2 % 15)))) := by
  rw [tv_bop, tv_var, tv_var]; rfl

theorem gRect_lt (g : Nat) : gRect g < 2 ^ 180 := by rw [gRect_tv]; exact tv_lt _

-- the profile lanes of packed rectangles
theorem profAcc_spec (m n : Nat) (hm : m < 37) (rc : Nat → Nat) (hr : ∀ k, k < n → rc k < 2 ^ 180) (C : Nat) (hC : C ≤ nf m) :
    profAcc m (pk rc 256 n) n C = pk (fun k => pk (fun c => profV m (rc k) c) 8 C) 256 n := by
  have hR := rep_eq 256 n (by norm_num)
  obtain ⟨_, hcf, _, _⟩ := cell_facts m hm
  induction C with
  | zero => show 0 = _; rw [show (fun k => pk (fun c => profV m (rc k) c) 8 0) = fun _ => 0 from rfl, pk_zero]
  | succ C ih =>
    have hc : C < nf m := by omega
    have hcell := (hcf C hc).1
    have F : ∀ f : Nat → Nat, (∀ k, k < n → f k < 2 ^ 180) → Fits f 256 n :=
      fun f h k hk => lt_of_lt_of_le (h k hk) (by norm_num)
    let sel := fun k => cond (Nat.blt C (npos m)) (rc k) (rc k ^^^ MV)
    have hsel : cond (Nat.blt C (npos m)) (pk rc 256 n) (Nat.xor (pk rc 256 n) (Nat.mul MV (rep 256 n))) = pk sel 256 n := by
      cases hb : Nat.blt C (npos m)
      · show pk rc 256 n ^^^ MV * rep 256 n = pk sel 256 n
        rw [hR, pk_const, pk_xor _ _ _ _ (by norm_num) (F _ hr) (F _ (fun _ _ => MV_lt))]
        apply pk_congr; intro k _; simp only [sel, hb]; rfl
      · show pk rc 256 n = pk sel 256 n
        apply pk_congr; intro k _; simp only [sel, hb]; rfl
    have fsel : ∀ k, k < n → sel k < 2 ^ 180 := fun k hk => by
      simp only [sel]; cases Nat.blt C (npos m)
      · exact Nat.xor_lt_two_pow (hr k hk) MV_lt
      · exact hr k hk
    have hand : Nat.land (pk sel 256 n) (Nat.mul (cellM m C) (rep 256 n)) = pk (fun k => sel k &&& cellM m C) 256 n := by
      show _ &&& cellM m C * rep 256 n = _
      rw [hR, pk_const, pk_land _ _ _ _ (by norm_num) (F _ fsel) (F _ (fun _ _ => hcell))]
    have fa : Fits (fun k => sel k &&& cellM m C) 256 n := F _ (fun k hk => lt_of_le_of_lt Nat.and_le_right hcell)
    have hpop := lanePop8 _ n (pk_lt _ _ _ fa)
    have hcnt : ∀ k, k < n → cntR (pk (fun k => sel k &&& cellM m C) 256 n) (256 * k) 256 = profV m (rc k) C := by
      intro k hk
      have e1 : cntR (pk (fun k => sel k &&& cellM m C) 256 n) (256 * k + 0) 256 = cntR (sel k &&& cellM m C) 0 256 :=
        cntR_off _ _ (256 * k) 0 256 (fun b hb => by
          rw [Nat.add_assoc, testBit_pk _ 256 n fa k _ (by omega)]; simp [hk])
      rw [show 256 * k = 256 * k + 0 by rfl, e1]
      have hlt : sel k &&& cellM m C < 2 ^ 180 := lt_of_le_of_lt Nat.and_le_right hcell
      have e2 : cntR (sel k &&& cellM m C) 0 256 = cntM (sel k &&& cellM m C) := by
        unfold cntM
        rw [show (256 : Nat) = 180 + 76 by rfl, cntR_add, cntR_zero_above _ (0 + 180) 76 (by rw [Nat.zero_add]; exact hlt),
          Nat.add_zero]
      rw [e2]
      unfold profV
      simp only [sel]
      cases Nat.blt C (npos m) <;> rfl
    show profAcc m (pk rc 256 n) n C + Nat.shiftLeft (pstepsR8 (Nat.land (cond (Nat.blt C (npos m)) (pk rc 256 n)
      (Nat.xor (pk rc 256 n) (Nat.mul MV (rep 256 n)))) (Nat.mul (cellM m C) (rep 256 n))) (rep 256 n)) (8 * C) = _
    rw [ih (by omega), hsel, hand, hpop]
    show _ + _ <<< (8 * C) = _
    rw [Nat.shiftLeft_eq, Nat.mul_comm, pk_mul, pk_add]
    apply pk_congr; intro k hk
    rw [hcnt k hk]
    show pk (fun c => profV m (rc k) c) 8 C + 2 ^ (8 * C) * profV m (rc k) C =
      2 ^ (8 * C) * profV m (rc k) C + pk (fun c => profV m (rc k) c) 8 C
    ring

theorem profLanes_spec (m n : Nat) (hm : m < 37) (rc : Nat → Nat) (hr : ∀ k, k < n → rc k < 2 ^ 180) :
    profLanes m (pk rc 256 n) n = Lanes (fun k c => cond (Nat.blt c (nf m)) (profV m (rc k) c) 0) n := by
  unfold profLanes Lanes
  rw [profAcc_spec m n hm rc hr (nf m) le_rfl]
  apply pk_congr; intro k _
  have hnf := (cell_facts m hm).1
  rw [pk_congr (fun c => profV m (rc k) c) (fun c => cond (Nat.blt c (nf m)) (profV m (rc k) c) 0) 8 (nf m)
    (fun c hc => by rw [show Nat.blt c (nf m) = true by rw [Nat.blt_eq]; exact hc]; rfl)]
  exact pk_pad _ 8 (nf m) 32 (by omega) (fun c h1 _ => by
    rw [show Nat.blt c (nf m) = false by
      cases h : Nat.blt c (nf m)
      · rfl
      · rw [Nat.blt_eq] at h; omega]; rfl)

-- ===== generic lane facts =====
theorem fld_lanes (v : Nat → Nat → Nat) (n k : Nat) (hv : ∀ j c, v j c < 256) (hk : k < n) :
    fld (Lanes v n) 256 k = pk (v k) 8 32 := by
  unfold Lanes
  exact fld_pk _ 256 n k (by norm_num) (fun j _ => pk_lt _ 8 32 (fun c _ => hv j c)) hk

theorem repL_lanes (w : Nat → Nat) (n : Nat) : repL (pk w 8 32) n = Lanes (fun _ => w) n := const_lanes _ w rfl n

theorem anyLE_spec (t : Nat → Nat) (y : Nat → Nat → Nat) (n : Nat) (ht : ∀ c, t c < 128) (hy : ∀ j c, y j c < 128)
    (ht31 : t 31 = 0) (hy31 : ∀ j, y j 31 = 0) (h : anyLE (pk t 8 32) (Lanes y n) n = true) :
    ∃ k, k < n ∧ ∀ c, c < 31 → t c ≤ y k c := by
  unfold anyLE at h
  simp only [Bool.not_eq_true'] at h
  have hne := Nat.ne_of_beq_eq_false h
  rw [repL_lanes] at hne
  obtain ⟨k, hk, hb⟩ := zl_nonzero _ _ hne
  refine ⟨k, hk, ?_⟩
  exact (leLanes_spec (fun _ => t) y n (fun _ c => ht c) hy (fun _ => ht31) hy31 k hk).mp hb

theorem nf_le31 (m : Nat) (hm : m < 37) : nf m ≤ 31 := (cell_facts m hm).1

theorem cond_nf (m c : Nat) (hm : m < 37) (h : 31 ≤ c) : Nat.blt c (nf m) = false := by
  have := nf_le31 m hm
  cases hb : Nat.blt c (nf m)
  · rfl
  · rw [Nat.blt_eq] at hb; omega

theorem eVal_lt (m off k c : Nat) : eVal m off k c < 32 := by
  unfold eVal; cases Nat.blt c (nf m)
  · show 0 < 32; norm_num
  · exact fld_lt _ _ _

theorem eVal_31 (m off k : Nat) (hm : m < 37) : eVal m off k 31 = 0 := by unfold eVal; rw [cond_nf m 31 hm le_rfl]; rfl

theorem e1Val_eq (m k c : Nat) (hm : m < 37) :
    e1Val m k c = cond (Nat.blt c (nf m)) (profV m (selRect m k) c) 0 := by
  unfold e1Val
  cases hb : Nat.blt c (nf m)
  · rfl
  · rw [Nat.blt_eq] at hb; show profC m (selRect m k) c = profV m (selRect m k) c
    exact profC_eq m _ c hm (gRect_lt _) hb

theorem e1Val_le (m k c : Nat) (hm : m < 37) : e1Val m k c ≤ 27 := by
  rw [e1Val_eq m k c hm]
  cases hb : Nat.blt c (nf m)
  · show 0 ≤ 27; norm_num
  · rw [Nat.blt_eq] at hb; exact profV_le27 m _ c hm hb

theorem e1Val_31 (m k : Nat) (hm : m < 37) : e1Val m k 31 = 0 := by unfold e1Val; rw [cond_nf m 31 hm le_rfl]; rfl

-- ===== V1 =====
theorem v1_spec (m : Nat) (hm : m < 37) (h : v1Check m = true) (g : Nat) (hg : g < 450) :
    ∃ k, k < nSel m ∧ ∀ c, c < 31 → cond (Nat.blt c (nf m)) (profV m (gRect g) c) 0 ≤ e1Val m k c := by
  unfold v1Check at h
  have he := Nat.eq_of_beq_eq_true h
  have hb : (orM (fun k => leLanes (profLanes m R450 450) (repL (fld (LE1 m) 256 k) 450) 450) (nSel m)).testBit (256 * g) = true := by
    have := congrArg (fun z => z.testBit (256 * g)) he
    simp only [testBit_land', rep_bit 450 g hg, Bool.and_true] at this
    exact this
  obtain ⟨k, hk, hk2⟩ := orM_bit _ _ _ hb
  refine ⟨k, hk, ?_⟩
  have hP : profLanes m R450 450 = Lanes (fun k c => cond (Nat.blt c (nf m)) (profV m (gRect k) c) 0) 450 :=
    profLanes_spec m 450 hm gRect (fun k _ => gRect_lt k)
  have hE : repL (fld (LE1 m) 256 k) 450 = Lanes (fun _ => e1Val m k) 450 := by
    unfold LE1; rw [fld_lanes _ _ _ (fun j c => lt_of_le_of_lt (e1Val_le m j c hm) (by norm_num)) hk, repL_lanes]
  rw [hP, hE] at hk2
  have hpv : ∀ j c, cond (Nat.blt c (nf m)) (profV m (gRect j) c) 0 < 128 := fun j c => by
    cases hb : Nat.blt c (nf m)
    · show 0 < 128; norm_num
    · rw [Nat.blt_eq] at hb; exact lt_of_le_of_lt (profV_le27 m _ c hm hb) (by norm_num)
  exact (leLanes_spec _ _ 450 hpv (fun _ c => lt_of_le_of_lt (e1Val_le m k c hm) (by norm_num))
    (fun j => by show cond (Nat.blt 31 (nf m)) _ 0 = 0; rw [cond_nf m 31 hm le_rfl]; rfl)
    (fun _ => e1Val_31 m k hm) g hg).mp hk2

-- ===== transitions of context data =====
def TvC (m : Nat) (op : Bool) (a b c : Nat) : Nat :=
  cond (isPosC m c) (cond op (min (capVal m c) (a + b)) (min a b)) (cond (isNegC m c) (cond op (min a b) (min (capVal m c) (a + b))) 0)

theorem capVal_le (m c : Nat) (hm : m < 37) : capVal m c ≤ 27 := by
  unfold capVal
  cases hb : Nat.blt c (nf m)
  · show 0 ≤ 27; norm_num
  · rw [Nat.blt_eq] at hb; exact ((cell_facts m hm).2.1 c hb).2.1

theorem isPos_disj (m c : Nat) (h : isPosC m c = true) : isNegC m c = false := by
  unfold isPosC at h; unfold isNegC
  rw [Nat.blt_eq] at h
  rw [show Nat.ble (npos m) c = false by
    cases hb : Nat.ble (npos m) c
    · rfl
    · rw [Nat.ble_eq] at hb; omega]
  rfl

theorem transL_spec (op : Bool) (m : Nat) (hm : m < 37) (xv : Nat → Nat) (y : Nat → Nat → Nat) (n : Nat)
    (hx : ∀ c, xv c < 32) (hy : ∀ j c, y j c < 32) :
    transL op m (pk xv 8 32) (Lanes y n) n = Lanes (fun j c => TvC m op (xv c) (y j c) c) n := by
  unfold transL
  rw [repL_lanes]
  exact trans_spec op (fun _ => xv) y (capVal m) (isPosC m) (isNegC m) n (fun _ c => by have := hx c; omega)
    (fun j c => by have := hy j c; omega) (fun c => by have := capVal_le m c hm; omega) (isPos_disj m)

theorem TvC_lt (m : Nat) (hm : m < 37) (op : Bool) (a b c : Nat) (ha : a < 32) (hb : b < 32) : TvC m op a b c < 64 := by
  have := capVal_le m c hm
  unfold TvC
  cases isPosC m c <;> cases isNegC m c <;> cases op <;> simp only [cond_true, cond_false] <;> omega

theorem TvC_31 (m : Nat) (hm : m < 37) (op : Bool) (a b : Nat) : TvC m op a b 31 = 0 := by
  have := nf_le31 m hm
  unfold TvC isPosC isNegC
  rw [show Nat.blt 31 (npos m) = false by
    cases hb : Nat.blt 31 (npos m)
    · rfl
    · rw [Nat.blt_eq] at hb; have := npos_le m; omega, cond_nf m 31 hm le_rfl]
  simp

-- ===== V2 =====
theorem v2_spec (m : Nat) (hm : m < 37) (h : v2Check m = true) (i : Nat) (hi : i < nSel m) (op : Bool) (j : Nat) (hj : j ≤ i) :
    ∃ k, k < nE2 m ∧ ∀ c, c < 31 → TvC m op (e1Val m i c) (e1Val m j c) c ≤ eVal m 0 k c := by
  have he1 : ∀ k c, e1Val m k c < 32 := fun k c => lt_of_le_of_lt (e1Val_le m k c hm) (by norm_num)
  have h1 := allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ h i hi) (cond op 1 0) (by cases op <;> decide)) j (Nat.lt_succ_of_le hj)
  rw [show Nat.beq (cond op 1 0) 1 = op by cases op <;> rfl] at h1
  have hL1 : fld (LE1 m) 256 i = pk (e1Val m i) 8 32 := by
    unfold LE1; exact fld_lanes _ _ _ (fun j c => lt_trans (he1 j c) (by norm_num)) hi
  unfold LE1 at h1
  rw [show fld (Lanes (e1Val m) (nSel m)) 256 i = pk (e1Val m i) 8 32 from hL1, transL_spec op m hm _ _ _ (he1 i) he1,
    fld_lanes _ (nSel m) j (fun j c => lt_trans (TvC_lt m hm op _ _ c (he1 i c) (he1 j c)) (by norm_num)) (show j < nSel m by omega)] at h1
  exact anyLE_spec _ _ _ (fun c => lt_trans (TvC_lt m hm op _ _ c (he1 i c) (he1 j c)) (by norm_num))
    (fun k c => lt_trans (eVal_lt m 0 k c) (by norm_num)) (TvC_31 m hm op _ _) (fun k => eVal_31 m 0 k hm) h1

theorem sumF_prefix (g : Nat → Nat) (np : Nat) (h : np ≤ 32) :
    sumF (fun t => cond (Nat.blt t np) (g t) 0) 32 = sumF g np := by
  rw [show (32 : Nat) = np + (32 - np) by omega, sumF_add]
  have e1 : sumF (fun t => cond (Nat.blt t np) (g t) 0) np = sumF g np :=
    sumF_congr _ _ _ (fun t ht => by rw [show Nat.blt t np = true by rw [Nat.blt_eq]; exact ht]; rfl)
  have e2 : sumF (fun t => cond (Nat.blt (np + t) np) (g (np + t)) 0) (32 - np) = 0 := by
    rw [sumF_congr _ (fun _ => 0) _ (fun t _ => by
      rw [show Nat.blt (np + t) np = false by
        cases hb : Nat.blt (np + t) np
        · rfl
        · rw [Nat.blt_eq] at hb; omega]; rfl)]
    induction (32 - np) with
    | zero => rfl
    | succ k ih => rw [sumF_succ, ih]
  rw [e1, e2, Nat.add_zero]

theorem sumF_periodic (f : Nat → Nat) (q : Nat) : sumF (fun t => f ((q + t) % 32)) 32 = sumF f 32 := by
  induction q with
  | zero => exact sumF_congr _ _ _ (fun t ht => by rw [Nat.zero_add, Nat.mod_eq_of_lt ht])
  | succ q ih =>
    have h1 := sumF_add (fun t => f ((q + t) % 32)) 1 32
    have h2 := sumF_add (fun t => f ((q + t) % 32)) 32 1
    rw [show (1 : Nat) + 32 = 32 + 1 by rfl, h2] at h1
    have e3 : sumF (fun t => f ((q + t) % 32)) 1 = f (q % 32) := by show 0 + f ((q + 0) % 32) = _; simp
    have e4 : sumF (fun t => (fun t => f ((q + t) % 32)) (32 + t)) 1 = f (q % 32) := by
      show 0 + f ((q + (32 + 0)) % 32) = _; rw [Nat.zero_add, Nat.add_zero, Nat.add_mod_right]
    have e5 : sumF (fun t => (fun t => f ((q + t) % 32)) (1 + t)) 32 = sumF (fun t => f ((q + 1 + t) % 32)) 32 :=
      sumF_congr _ _ _ (fun t _ => by simp only; congr 2; ring)
    rw [e3, e4, e5] at h1
    rw [← ih]; omega

theorem sumF_le (g h : Nat → Nat) (k : Nat) (hgh : ∀ t, t < k → g t ≤ h t) : sumF g k ≤ sumF h k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => rw [sumF_succ, sumF_succ]; have := ih (fun t ht => hgh t (by omega)); have := hgh k (by omega); omega

-- lane sums of bounded lanes
theorem laneSum_lanes (w : Nat → Nat → Nat) (bnd : Nat → Nat) (n : Nat) (hw : ∀ j c, w j c ≤ bnd c)
    (hb : sumF bnd 32 ≤ 255) : laneSum (Lanes w n) n = pk (fun j => sumF (w j) 32) 256 n := by
  rw [lanes_view]
  let s := fun q => cond (Nat.blt q (32 * n)) (w (q / 32) (q % 32)) 0
  rw [pk_congr _ s 8 (32 * n) (fun q hq => by simp only [s]; rw [show Nat.blt q (32 * n) = true by rw [Nat.blt_eq]; exact hq]; rfl)]
  have hs : ∀ q, s q ≤ bnd (q % 32) := fun q => by
    simp only [s]; cases Nat.blt q (32 * n)
    · exact Nat.zero_le _
    · exact hw _ _
  have hwin : ∀ q, win s 32 q < 256 := fun q => by
    have : win s 32 q ≤ sumF (fun t => bnd ((q + t) % 32)) 32 := sumF_le _ _ _ (fun t _ => hs (q + t))
    rw [sumF_periodic] at this; omega
  have hz : ∀ q, 32 * n ≤ q → s q = 0 := by
    intro q hq
    show cond (Nat.blt q (32 * n)) (w (q / 32) (q % 32)) 0 = 0
    rw [show Nat.blt q (32 * n) = false by
      cases hb : Nat.blt q (32 * n)
      · rfl
      · rw [Nat.blt_eq] at hb; omega]
    rfl
  rw [laneSum_spec s n hz hwin]
  apply pk_congr; intro j hj
  unfold win
  apply sumF_congr; intro t ht
  show cond (Nat.blt (32 * j + t) (32 * n)) (w ((32 * j + t) / 32) ((32 * j + t) % 32)) 0 = w j t
  rw [show Nat.blt (32 * j + t) (32 * n) = true by rw [Nat.blt_eq]; omega, show (32 * j + t) / 32 = j by omega,
    show (32 * j + t) % 32 = t by omega]
  rfl

theorem land_sel_lanes (w : Nat → Nat → Nat) (b : Nat → Bool) (n : Nat) (hw : ∀ j c, w j c < 256) :
    Nat.land (Lanes w n) (Lanes (fun _ c => selF (b c)) n) = Lanes (fun j c => cond (b c) (w j c) 0) n := by
  rw [lanes_view, lanes_view, lanes_view]
  show pk _ 8 (32 * n) &&& pk _ 8 (32 * n) = _
  rw [pk_land _ _ _ _ (by norm_num) (fun q _ => hw _ _) (fun q _ => by show selF _ < 2 ^ 8; cases b (q % 32) <;> decide)]
  apply pk_congr; intro q _; exact and_sel _ _ (hw _ _)

theorem xor_lanes (a b : Nat → Nat → Nat) (n : Nat) (ha : ∀ j c, a j c < 256) (hb : ∀ j c, b j c < 256) :
    Nat.xor (Lanes a n) (Lanes b n) = Lanes (fun j c => a j c ^^^ b j c) n := by
  rw [lanes_view, lanes_view, lanes_view]
  exact pk_xor _ _ _ _ (by norm_num) (fun q _ => ha _ _) (fun q _ => hb _ _)

theorem zl_lanes (z : Nat → Nat → Nat) (n j : Nat) (hz : ∀ j c, z j c < 256) (hz31 : ∀ j, z j 31 = 0) (hj : j < n) :
    (zl (Lanes z n) n).testBit (256 * j) = true ↔ ∀ c, c < 32 → z j c = 0 := by
  unfold Lanes
  have hlt : ∀ j, j < n → pk (z j) 8 32 < 2 ^ 255 := fun j _ => by
    rw [← pk_pad (z j) 8 31 32 (by norm_num) (fun c h1 h2 => by rw [show c = 31 by omega]; exact hz31 j)]
    exact lt_of_lt_of_le (pk_lt _ 8 31 (fun c _ => hz j c)) (by norm_num)
  rw [zl_spec _ n hlt j hj, decide_eq_true_iff]
  constructor
  · intro h c hc; exact pk_eq_zero _ 8 32 h (by norm_num) (fun c _ => hz j c) c hc
  · intro h; rw [pk_congr _ (fun _ => 0) 8 32 h]; exact pk_zero 8 32

theorem fld_Lanes_pk (v : Nat → Nat → Nat) (n k : Nat) (hv : ∀ j c, v j c < 256) (hk : k < n) :
    fld (Lanes v n) 256 k = pk (v k) 8 32 := fld_lanes v n k hv hk

theorem capVal_eq (m c : Nat) (hc : c < nf m) : capVal m c = capC m c := by
  unfold capVal; rw [show Nat.blt c (nf m) = true by rw [Nat.blt_eq]; exact hc]; rfl

theorem isPos_lt (m c : Nat) (h : isPosC m c = true) : c < npos m := by unfold isPosC at h; rwa [Nat.blt_eq] at h

theorem isNeg_iff (m c : Nat) : isNegC m c = true ↔ npos m ≤ c ∧ c < nf m := by
  unfold isNegC; simp [Nat.ble_eq, Nat.blt_eq]

-- positive parts of transitions of data stay below the capacities
theorem TvC_pos_le (m : Nat) (hm : m < 37) (op : Bool) (a b c : Nat) (ha : a ≤ capVal m c) :
    cond (isPosC m c) (TvC m op a b c) 0 ≤ cond (isPosC m c) (capVal m c) 0 := by
  unfold TvC
  cases hp : isPosC m c
  · rfl
  · cases op <;> simp only [cond_true, cond_false]
    · exact le_trans (min_le_left _ _) ha
    · exact min_le_left _ _

theorem posCap_sum (m : Nat) (hm : m < 37) (hd : dataCheck m = true) :
    sumF (fun c => cond (isPosC m c) (capVal m c) 0) 32 ≤ 45 := by
  have hnf := nf_le31 m hm
  have hnp := npos_le m
  simp only [dataCheck, Bool.and_eq_true, Nat.ble_eq] at hd
  have h45 := hd.1.1.1.1.1.2
  unfold isPosC
  rw [sumF_prefix (capVal m) (npos m) (by omega)]
  rw [sumF_congr _ (capC m) _ (fun c hc => capVal_eq m c (by omega))]
  exact h45

theorem eVal_shift (m q k c : Nat) : eVal m (Nat.mul q (nf m)) k c = eVal m 0 (q + k) c := by
  unfold eVal; congr 2; show q * nf m + (k * nf m + c) = 0 + ((q + k) * nf m + c); ring

theorem eVal_le_cap (m k c : Nat) (hm : m < 37) (hd : dataCheck m = true) (hk : k < nE2 m + nE3A m + nE3B m) :
    eVal m 0 k c ≤ capVal m c := by
  by_cases hc : c < nf m
  · simp only [dataCheck, Bool.and_eq_true, Nat.ble_eq] at hd
    have := allBelow_spec _ _ (allBelow_spec _ _ hd.1.1.1.1.1.1 k hk) c hc
    rw [Nat.ble_eq] at this
    rw [capVal_eq m c hc]; exact this
  · unfold eVal; rw [show Nat.blt c (nf m) = false by
      cases h : Nat.blt c (nf m)
      · rfl
      · rw [Nat.blt_eq] at h; omega]
    exact Nat.zero_le _

-- lanes of transitions of stored data and their positive sums
theorem posSum_lanes (m : Nat) (hm : m < 37) (hd : dataCheck m = true) (op : Bool) (a b : Nat → Nat → Nat) (n : Nat)
    (ha : ∀ j c, a j c ≤ capVal m c) (hb : ∀ j c, b j c < 32) (ha32 : ∀ j c, a j c < 32) :
    laneSum (Nat.land (Lanes (fun j c => TvC m op (a j c) (b j c) c) n) (POSL m n)) n =
      pk (fun j => sumF (fun c => TvC m op (a j c) (b j c) c) (npos m)) 256 n := by
  unfold POSL
  rw [land_sel_lanes _ _ _ (fun j c => lt_trans (TvC_lt m hm op _ _ c (ha32 j c) (hb j c)) (by norm_num))]
  rw [laneSum_lanes _ (fun c => cond (isPosC m c) (capVal m c) 0) n (fun j c => TvC_pos_le m hm op _ _ c (ha j c))
    (le_trans (posCap_sum m hm hd) (by norm_num))]
  apply pk_congr; intro j _
  unfold isPosC
  exact sumF_prefix _ (npos m) (by have := nf_le31 m hm; have := npos_le m; omega)

theorem negFull_lanes (m : Nat) (hm : m < 37) (op : Bool) (a b : Nat → Nat → Nat) (n j : Nat) (hj : j < n)
    (hb : ∀ j c, b j c < 32) (ha32 : ∀ j c, a j c < 32)
    (hfull : ∀ c, npos m ≤ c → c < nf m → TvC m op (a j c) (b j c) c = capC m c) :
    (zl (Nat.xor (Nat.land (Lanes (fun j c => TvC m op (a j c) (b j c) c) n) (NEGL m n)) (CAPNL m n)) n).testBit (256 * j) = true := by
  unfold NEGL CAPNL
  have hT : ∀ j c, TvC m op (a j c) (b j c) c < 256 := fun j c => lt_trans (TvC_lt m hm op _ _ c (ha32 j c) (hb j c)) (by norm_num)
  rw [land_sel_lanes _ _ _ hT]
  have hcap : ∀ (j c : Nat), cond (isNegC m c) (capC m c) 0 < 256 := fun j c => by
    cases hn : isNegC m c
    · show 0 < 256; norm_num
    · rw [isNeg_iff] at hn
      exact lt_of_le_of_lt ((cell_facts m hm).2.1 c hn.2).2.1 (by norm_num)
  rw [xor_lanes _ _ _ (fun j c => by cases isNegC m c <;> [exact (by show 0 < 256; norm_num); exact hT j c]) hcap]
  rw [zl_lanes _ n j (fun j c => Nat.xor_lt_two_pow (show _ < 2 ^ 8 by cases isNegC m c <;> [exact (by show 0 < 256; norm_num); exact hT j c])
    (hcap j c)) (fun j => by
      have : isNegC m 31 = false := by
        cases hn : isNegC m 31
        · rfl
        · rw [isNeg_iff] at hn; have := nf_le31 m hm; omega
      rw [this]; simp) hj]
  intro c _
  cases hn : isNegC m c
  · simp
  · rw [isNeg_iff] at hn
    show TvC m op (a j c) (b j c) c ^^^ capC m c = 0
    rw [hfull c hn.1 hn.2, Nat.xor_self]

theorem v3_spec (m : Nat) (hm : m < 37) (hd : dataCheck m = true) (h : v3Check m = true) (i : Nat) (hi : i < nE2 m)
    (op : Bool) (j : Nat) (hj : j ≤ i) :
    (21 ≤ sumF (fun c => TvC m op (eVal m 0 i c) (eVal m 0 j c) c) (npos m) →
      ∃ k, k < nE3A m ∧ ∀ c, c < 31 → TvC m op (eVal m 0 i c) (eVal m 0 j c) c ≤ eVal m (Nat.mul (nE2 m) (nf m)) k c) ∧
    ((∀ c, npos m ≤ c → c < nf m → TvC m op (eVal m 0 i c) (eVal m 0 j c) c = capC m c) →
      ∃ k, k < nE3B m ∧ ∀ c, c < 31 → TvC m op (eVal m 0 i c) (eVal m 0 j c) c ≤
        eVal m (Nat.mul (Nat.add (nE2 m) (nE3A m)) (nf m)) k c) := by
  have he : ∀ k c, eVal m 0 k c < 32 := fun k c => eVal_lt m 0 k c
  have h1 := allBelow_spec _ _ (allBelow_spec _ _ h i hi) (cond op 1 0) (by cases op <;> decide)
  rw [show Nat.beq (cond op 1 0) 1 = op by cases op <;> rfl] at h1
  simp only [Bool.and_eq_true] at h1
  have hL2 : fld (LE2 m) 256 i = pk (eVal m 0 i) 8 32 := by
    unfold LE2; exact fld_lanes _ _ _ (fun j c => lt_trans (he j c) (by norm_num)) hi
  have hT : transL op m (fld (LE2 m) 256 i) (LE2 m) (nE2 m) =
      Lanes (fun j c => TvC m op (eVal m 0 i c) (eVal m 0 j c) c) (nE2 m) := by
    rw [hL2]; unfold LE2; exact transL_spec op m hm _ _ _ (he i) he
  rw [hT] at h1
  have hTv : ∀ j c, TvC m op (eVal m 0 i c) (eVal m 0 j c) c < 256 := fun j c =>
    lt_trans (TvC_lt m hm op _ _ c (he i c) (he j c)) (by norm_num)
  have hfT : fld (Lanes (fun j c => TvC m op (eVal m 0 i c) (eVal m 0 j c) c) (nE2 m)) 256 j =
      pk (fun c => TvC m op (eVal m 0 i c) (eVal m 0 j c) c) 8 32 := fld_lanes _ _ j hTv (by omega)
  have hrep : (rep 256 (Nat.add i 1)).testBit (256 * j) = true := rep_bit _ j (Nat.lt_succ_of_le hj)
  constructor
  · intro hs
    have hq : (qA m (Lanes (fun j c => TvC m op (eVal m 0 i c) (eVal m 0 j c) c) (nE2 m)) (nE2 m) i).testBit (256 * j) = true := by
      unfold qA
      rw [testBit_land', hrep, Bool.and_true]
      rw [posSum_lanes m hm hd op (fun _ c => eVal m 0 i c) (fun j c => eVal m 0 j c) (nE2 m)
        (fun _ c => eVal_le_cap m i c hm hd (by omega)) (fun j c => he j c) (fun _ c => he i c)]
      rw [thrL_spec _ _ 21 (fun j' _ => by
        show sumF (fun c => TvC m op (eVal m 0 i c) (eVal m 0 j' c) c) (npos m) < 256
        have := sumF_le (fun c => TvC m op (eVal m 0 i c) (eVal m 0 j' c) c) (capVal m) (npos m)
          (fun c hc => by
            have := TvC_pos_le m hm op (eVal m 0 i c) (eVal m 0 j' c) c (eVal_le_cap m i c hm hd (by omega))
            rwa [show isPosC m c = true by unfold isPosC; rw [Nat.blt_eq]; exact hc] at this)
        have h45 := posCap_sum m hm hd
        unfold isPosC at h45
        rw [sumF_prefix (capVal m) (npos m) (by have := nf_le31 m hm; have := npos_le m; omega)] at h45
        omega) (by norm_num) j (by omega)]
      simpa using hs
    have := scanB_spec 256 (by norm_num) _ _ 9 0 (nE2 m) h1.1 j (by omega) (by omega) hq
    rw [hfT] at this
    unfold LE3A at this
    exact anyLE_spec _ _ _ (fun c => lt_trans (TvC_lt m hm op _ _ c (he i c) (he j c)) (by norm_num))
      (fun k c => lt_trans (eVal_lt _ _ k c) (by norm_num)) (TvC_31 m hm op _ _) (fun k => eVal_31 m _ k hm) this
  · intro hfull
    have hq : (qB m (Lanes (fun j c => TvC m op (eVal m 0 i c) (eVal m 0 j c) c) (nE2 m)) (nE2 m) i).testBit (256 * j) = true := by
      unfold qB
      rw [testBit_land', hrep, Bool.and_true]
      exact negFull_lanes m hm op (fun _ c => eVal m 0 i c) (fun j c => eVal m 0 j c) (nE2 m) j (by omega) he (fun _ c => he i c) hfull
    have := scanB_spec 256 (by norm_num) _ _ 9 0 (nE2 m) h1.2 j (by omega) (by omega) hq
    rw [hfT] at this
    unfold LE3B at this
    exact anyLE_spec _ _ _ (fun c => lt_trans (TvC_lt m hm op _ _ c (he i c) (he j c)) (by norm_num))
      (fun k c => lt_trans (eVal_lt _ _ k c) (by norm_num)) (TvC_31 m hm op _ _) (fun k => eVal_31 m _ k hm) this

theorem testBit_lor' (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) := Nat.testBit_or x y i
theorem testBit_xor' (x y i : Nat) : (Nat.xor x y).testBit i = (x.testBit i ^^ y.testBit i) := Nat.testBit_xor x y i

def edgeS (m : Nat) (v : Nat → Nat) (e : Nat) : Nat := sumF (fun c => cond (Nat.beq (edgeOf m c) e) (v c) 0) (npos m)

def GammaVal (m : Nat) (v : Nat → Nat) : Prop :=
  sumF v (npos m) ≤ 20 ∨ (sumF v (npos m) ≤ 22 ∧ ∃ d, d < 10 ∧ ∀ e, e < 5 → edgeS m v e ≤ omegaAt d e)

theorem edge_lanes (m : Nat) (hm : m < 37) (hd : dataCheck m = true) (op : Bool) (a b : Nat → Nat → Nat) (n e : Nat)
    (ha : ∀ j c, a j c ≤ capVal m c) (hb : ∀ j c, b j c < 32) (ha32 : ∀ j c, a j c < 32) :
    laneSum (Nat.land (Lanes (fun j c => TvC m op (a j c) (b j c) c) n) (EML m e n)) n =
      pk (fun j => edgeS m (fun c => TvC m op (a j c) (b j c) c) e) 256 n := by
  unfold EML
  rw [land_sel_lanes _ _ _ (fun j c => lt_trans (TvC_lt m hm op _ _ c (ha32 j c) (hb j c)) (by norm_num))]
  have hbnd : ∀ j c, cond (Nat.blt c (npos m) && Nat.beq (edgeOf m c) e) (TvC m op (a j c) (b j c) c) 0 ≤
      cond (isPosC m c) (capVal m c) 0 := by
    intro j c
    have := TvC_pos_le m hm op (a j c) (b j c) c (ha j c)
    unfold isPosC at this ⊢
    cases hp : Nat.blt c (npos m) <;> cases Nat.beq (edgeOf m c) e <;> simp_all
  rw [laneSum_lanes _ _ n hbnd (le_trans (posCap_sum m hm hd) (by norm_num))]
  apply pk_congr; intro j _
  unfold edgeS
  rw [← sumF_prefix _ (npos m) (by have := nf_le31 m hm; have := npos_le m; omega)]
  apply sumF_congr; intro c _
  cases Nat.blt c (npos m) <;> rfl

def edgeAcc (m T n : Nat) (E : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun e acc => Nat.add acc (Nat.shiftLeft (laneSum (Nat.land T (EML m e n)) n) (Nat.mul 8 e))) E

theorem edgeS_le (m : Nat) (hm : m < 37) (hd : dataCheck m = true) (v : Nat → Nat) (hv : ∀ c, c < npos m → v c ≤ capVal m c) (e : Nat) :
    edgeS m v e ≤ 45 := by
  have h45 := posCap_sum m hm hd
  unfold isPosC at h45
  rw [sumF_prefix (capVal m) (npos m) (by have := nf_le31 m hm; have := npos_le m; omega)] at h45
  have := sumF_le (fun c => cond (Nat.beq (edgeOf m c) e) (v c) 0) (capVal m) (npos m) (fun c hc => by
    cases Nat.beq (edgeOf m c) e
    · exact Nat.zero_le _
    · exact hv c hc)
  unfold edgeS; omega

theorem edgeAcc_spec (m : Nat) (hm : m < 37) (hd : dataCheck m = true) (op : Bool) (a b : Nat → Nat → Nat) (n : Nat)
    (ha : ∀ j c, a j c ≤ capVal m c) (hb : ∀ j c, b j c < 32) (ha32 : ∀ j c, a j c < 32) (E : Nat) :
    edgeAcc m (Lanes (fun j c => TvC m op (a j c) (b j c) c) n) n E =
      pk (fun j => pk (fun e => edgeS m (fun c => TvC m op (a j c) (b j c) c) e) 8 E) 256 n := by
  induction E with
  | zero => show 0 = _; rw [show (fun j => pk (fun e => edgeS m (fun c => TvC m op (a j c) (b j c) c) e) 8 0) = fun _ => 0 from rfl,
      pk_zero]
  | succ E ih =>
    show edgeAcc m _ n E + laneSum _ n <<< (8 * E) = _
    rw [ih, edge_lanes m hm hd op a b n E ha hb ha32, Nat.shiftLeft_eq, Nat.mul_comm, pk_mul, pk_add]
    apply pk_congr; intro j _
    show _ + 2 ^ (8 * E) * edgeS m _ E = 2 ^ (8 * E) * edgeS m _ E + _
    ring

theorem edge5_spec (m : Nat) (hm : m < 37) (hd : dataCheck m = true) (op : Bool) (a b : Nat → Nat → Nat) (n : Nat)
    (ha : ∀ j c, a j c ≤ capVal m c) (hb : ∀ j c, b j c < 32) (ha32 : ∀ j c, a j c < 32) :
    edge5 m (Lanes (fun j c => TvC m op (a j c) (b j c) c) n) n =
      Lanes (fun j c => cond (Nat.blt c 5) (edgeS m (fun c => TvC m op (a j c) (b j c) c) c) 0) n := by
  show edgeAcc m _ n 5 = _
  rw [edgeAcc_spec m hm hd op a b n ha hb ha32 5]
  unfold Lanes; apply pk_congr; intro j _
  rw [pk_congr (fun e => edgeS m (fun c => TvC m op (a j c) (b j c) c) e)
    (fun c => cond (Nat.blt c 5) (edgeS m (fun c => TvC m op (a j c) (b j c) c) c) 0) 8 5
    (fun c hc => by rw [show Nat.blt c 5 = true by rw [Nat.blt_eq]; exact hc]; rfl)]
  exact pk_pad _ 8 5 32 (by norm_num) (fun c h1 _ => by
    rw [show Nat.blt c 5 = false by
      cases h : Nat.blt c 5
      · rfl
      · rw [Nat.blt_eq] at h; omega]; rfl)

theorem omegaAt_le (d e : Nat) : omegaAt d e ≤ 9 := by
  unfold omegaAt
  generalize cond (Nat.blt d 5) (Nat.mod (Nat.sub (Nat.add d 5) e) 5) (Nat.mod (Nat.sub (Nat.add e d) 5) 5) = k
  have : ∀ k, k < 16 → fld 0x99014 4 k ≤ 9 := by decide
  by_cases hk : k < 16
  · exact this k hk
  · rw [fld_eq]
    have : (0x99014 : Nat) >>> (4 * k) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]; apply Nat.div_eq_of_lt
      exact lt_of_lt_of_le (by norm_num : (0x99014 : Nat) < 2 ^ 64) (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [this]; simp

theorem gamma_spec (m : Nat) (hm : m < 37) (hd : dataCheck m = true) (op : Bool) (a b : Nat → Nat → Nat) (n j : Nat) (hj : j < n)
    (ha : ∀ j c, a j c ≤ capVal m c) (hb : ∀ j c, b j c < 32) (ha32 : ∀ j c, a j c < 32)
    (h : (gammaLanes m (Lanes (fun j c => TvC m op (a j c) (b j c) c) n) n).testBit (256 * j) = true) :
    GammaVal m (fun c => TvC m op (a j c) (b j c) c) := by
  have hps := posSum_lanes m hm hd op a b n ha hb ha32
  have hbound : ∀ j', sumF (fun c => TvC m op (a j' c) (b j' c) c) (npos m) ≤ 45 := fun j' => by
    have h45 := posCap_sum m hm hd
    unfold isPosC at h45
    rw [sumF_prefix (capVal m) (npos m) (by have := nf_le31 m hm; have := npos_le m; omega)] at h45
    have := sumF_le (fun c => TvC m op (a j' c) (b j' c) c) (capVal m) (npos m) (fun c hc => by
      have := TvC_pos_le m hm op (a j' c) (b j' c) c (ha j' c)
      rwa [show isPosC m c = true by unfold isPosC; rw [Nat.blt_eq]; exact hc] at this)
    omega
  unfold gammaLanes at h
  rw [hps] at h
  rw [testBit_lor', testBit_xor', testBit_land', testBit_xor', rep_bit n j hj,
    thrL_spec _ n 21 (fun j' _ => lt_of_le_of_lt (hbound j') (by norm_num)) (by norm_num) j hj,
    thrL_spec _ n 23 (fun j' _ => lt_of_le_of_lt (hbound j') (by norm_num)) (by norm_num) j hj] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.true_xor, Bool.not_eq_true', decide_eq_false_iff_not, not_le] at h
  unfold GammaVal
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (by omega)
  · refine Or.inr ⟨by omega, ?_⟩
    obtain ⟨d, hd10, hb2⟩ := orM_bit _ _ _ h2
    refine ⟨d, hd10, fun e he => ?_⟩
    rw [edge5_spec m hm hd op a b n ha hb ha32, show OML d = pk (fun c => cond (Nat.blt c 5) (omegaAt d c) 0) 8 32 from rfl,
      repL_lanes] at hb2
    have hE : ∀ j c, cond (Nat.blt c 5) (edgeS m (fun c => TvC m op (a j c) (b j c) c) c) 0 < 128 := fun j c => by
      cases Nat.blt c 5
      · show 0 < 128; norm_num
      · exact lt_of_le_of_lt (edgeS_le m hm hd _ (fun c' hc' => by
          have := TvC_pos_le m hm op (a j c') (b j c') c' (ha j c')
          rwa [show isPosC m c' = true by unfold isPosC; rw [Nat.blt_eq]; exact hc'] at this) c) (by norm_num)
    have hO : ∀ (j c : Nat), cond (Nat.blt c 5) (omegaAt d c) 0 < 128 := fun j c => by
      cases Nat.blt c 5
      · show 0 < 128; norm_num
      · exact lt_of_le_of_lt (omegaAt_le d c) (by norm_num)
    have := (leLanes_spec _ _ n hE hO (fun j => rfl) (fun j => rfl) j hj).mp hb2 e (by omega)
    rwa [show Nat.blt e 5 = true by rw [Nat.blt_eq]; exact he] at this

def a3v (m k c : Nat) : Nat := eVal m (Nat.mul (nE2 m) (nf m)) k c
def b3v (m k c : Nat) : Nat := eVal m (Nat.mul (Nat.add (nE2 m) (nE3A m)) (nf m)) k c

theorem a3v_le (m k c : Nat) (hm : m < 37) (hd : dataCheck m = true) (hk : k < nE3A m) : a3v m k c ≤ capVal m c := by
  unfold a3v; rw [eVal_shift]; exact eVal_le_cap m _ c hm hd (by omega)

theorem b3v_le (m k c : Nat) (hm : m < 37) (hd : dataCheck m = true) (hk : k < nE3B m) : b3v m k c ≤ capVal m c := by
  unfold b3v; rw [eVal_shift]; exact eVal_le_cap m _ c hm hd (by show nE2 m + nE3A m + k < _; omega)

theorem bit_of_zero_and (A B p : Nat) (h : Nat.land A B = 0) (hA : A.testBit p = true) : B.testBit p = false := by
  have := congrArg (fun z => z.testBit p) h
  simp only [testBit_land', Nat.zero_testBit, hA, Bool.true_and] at this
  exact this

theorem v4_spec (m : Nat) (hm : m < 37) (hd : dataCheck m = true) (h : v4Check m = true) :
    (∀ i, i < nE3A m → ∀ j, j ≤ i → (∀ c, npos m ≤ c → c < nf m → TvC m false (a3v m i c) (a3v m j c) c = capC m c) →
      GammaVal m (fun c => TvC m false (a3v m i c) (a3v m j c) c)) ∧
    (∀ i, i < nE3B m → ∀ j, j ≤ i → GammaVal m (fun c => TvC m true (b3v m i c) (b3v m j c) c)) := by
  unfold v4Check at h
  simp only [Bool.and_eq_true] at h
  have he : ∀ off k c, eVal m off k c < 32 := fun off k c => eVal_lt m off k c
  constructor
  · intro i hi j hj hfull
    have h1 := Nat.eq_of_beq_eq_true (allBelow_spec _ _ h.1 i hi)
    have hL : fld (LE3A m) 256 i = pk (a3v m i) 8 32 := by
      unfold LE3A; exact fld_lanes _ _ _ (fun j c => lt_trans (he _ j c) (by norm_num)) hi
    have hT : transL false m (fld (LE3A m) 256 i) (LE3A m) (nE3A m) =
        Lanes (fun j c => TvC m false (a3v m i c) (a3v m j c) c) (nE3A m) := by
      rw [hL]; unfold LE3A; exact transL_spec false m hm _ _ _ (he _ i) (he _)
    rw [hT] at h1
    have hq : (qB m (Lanes (fun j c => TvC m false (a3v m i c) (a3v m j c) c) (nE3A m)) (nE3A m) i).testBit (256 * j) = true := by
      unfold qB
      rw [testBit_land', rep_bit _ j (Nat.lt_succ_of_le hj), Bool.and_true]
      exact negFull_lanes m hm false (fun _ c => a3v m i c) (fun j c => a3v m j c) (nE3A m) j (by omega)
        (fun j c => he _ j c) (fun _ c => he _ i c) hfull
    have hg := bit_of_zero_and _ _ _ h1 hq
    rw [testBit_xor', rep_bit _ j (by omega)] at hg
    have hg2 : (gammaLanes m (Lanes (fun j c => TvC m false (a3v m i c) (a3v m j c) c) (nE3A m)) (nE3A m)).testBit (256 * j) = true := by
      cases hb : (gammaLanes m _ _).testBit (256 * j)
      · rw [hb] at hg; simp at hg
      · rfl
    exact gamma_spec m hm hd false (fun _ c => a3v m i c) (fun j c => a3v m j c) (nE3A m) j (by omega)
      (fun _ c => a3v_le m i c hm hd hi) (fun j c => he _ j c) (fun _ c => he _ i c) hg2
  · intro i hi j hj
    have h1 := Nat.eq_of_beq_eq_true (allBelow_spec _ _ h.2 i hi)
    have hL : fld (LE3B m) 256 i = pk (b3v m i) 8 32 := by
      unfold LE3B; exact fld_lanes _ _ _ (fun j c => lt_trans (he _ j c) (by norm_num)) hi
    have hT : transL true m (fld (LE3B m) 256 i) (LE3B m) (nE3B m) =
        Lanes (fun j c => TvC m true (b3v m i c) (b3v m j c) c) (nE3B m) := by
      rw [hL]; unfold LE3B; exact transL_spec true m hm _ _ _ (he _ i) (he _)
    rw [hT] at h1
    have hg := bit_of_zero_and _ _ _ h1 (rep_bit _ j (Nat.lt_succ_of_le hj))
    rw [testBit_xor', rep_bit _ j (by omega)] at hg
    have hg2 : (gammaLanes m (Lanes (fun j c => TvC m true (b3v m i c) (b3v m j c) c) (nE3B m)) (nE3B m)).testBit (256 * j) = true := by
      cases hb : (gammaLanes m _ _).testBit (256 * j)
      · rw [hb] at hg; simp at hg
      · rfl
    exact gamma_spec m hm hd true (fun _ c => b3v m i c) (fun j c => b3v m j c) (nE3B m) j (by omega)
      (fun _ c => b3v_le m i c hm hd hi) (fun j c => he _ j c) (fun _ c => he _ i c) hg2

def profL (m x c : Nat) : Nat := cond (Nat.blt c (nf m)) (profV m x c) 0

theorem TvC_eq_Tf (m : Nat) (op : Bool) (a b c : Nat) (hm : m < 37) (hc : c < nf m) :
    TvC m op a b c = Tf op (Nat.blt c (npos m)) (capV m c) a b := by
  rw [capV_eq m c hm hc, ← capVal_eq m c hc]
  unfold TvC Tf
  cases hp : Nat.blt c (npos m)
  · have hn : isNegC m c = true := by
      rw [isNeg_iff]; constructor
      · by_contra hc'
        have : Nat.blt c (npos m) = true := by rw [Nat.blt_eq]; omega
        rw [hp] at this; exact absurd this (by simp)
      · exact hc
    simp only [isPosC, hp, hn, cond_false, cond_true]
  · simp only [isPosC, hp, cond_true]

theorem TvC_symm (m : Nat) (op : Bool) (a b c : Nat) : TvC m op a b c = TvC m op b a c := by
  unfold TvC; rw [Nat.add_comm a b, min_comm a b]

theorem profL_31 (m x : Nat) (hm : m < 37) : profL m x 31 = 0 := by unfold profL; rw [cond_nf m 31 hm le_rfl]; rfl

theorem profL_gate (m : Nat) (hm : m < 37) (op : Bool) (x y : Nat) (u v : Nat → Nat)
    (hu : ∀ c, c < 31 → profL m x c ≤ u c) (hv : ∀ c, c < 31 → profL m y c ≤ v c) (c : Nat) (hc : c < 31) :
    profL m (gate op x y) c ≤ TvC m op (u c) (v c) c := by
  unfold profL
  cases hb : Nat.blt c (nf m)
  · exact Nat.zero_le _
  · rw [Nat.blt_eq] at hb
    have h1 := hu c hc; have h2 := hv c hc
    unfold profL at h1 h2
    rw [show Nat.blt c (nf m) = true by rw [Nat.blt_eq]; exact hb] at h1 h2
    simp only [cond_true] at h1 h2 ⊢
    rw [TvC_eq_Tf m op _ _ c hm hb]
    exact le_trans (prof_gate m hm op x y c hb) (Tf_mono _ _ _ _ _ _ _ h1 h2)

theorem profL_pos (m x c : Nat) (hc : c < npos m) : profL m x c = profV m x c := by
  unfold profL; rw [show Nat.blt c (nf m) = true by rw [Nat.blt_eq]; have := npos_le m; omega]; rfl

theorem profL_neg (m x c : Nat) (hc : c < nf m) : profL m x c = profV m x c := by
  unfold profL; rw [show Nat.blt c (nf m) = true by rw [Nat.blt_eq]; exact hc]; rfl

theorem TvC_neg_le (m : Nat) (hm : m < 37) (op : Bool) (a b c : Nat) (ha : a ≤ capVal m c) (h1 : npos m ≤ c) (h2 : c < nf m) :
    TvC m op a b c ≤ capC m c := by
  rw [← capVal_eq m c h2]
  unfold TvC
  rw [show isPosC m c = false by
    unfold isPosC; cases hb : Nat.blt c (npos m)
    · rfl
    · rw [Nat.blt_eq] at hb; omega,
    show isNegC m c = true by rw [isNeg_iff]; exact ⟨h1, h2⟩]
  cases op <;> simp only [cond_true, cond_false]
  · exact min_le_left _ _
  · exact le_trans (min_le_left _ _) ha

theorem gamma_of_val (m : Nat) (hm : m < 37) (t : Nat) (v : Nat → Nat) (hv : ∀ c, c < npos m → profV m t c ≤ v c)
    (hg : GammaVal m v) : Gamma (t &&& targetT m) := by
  have hA : cA (t &&& targetT m) ≤ sumF v (npos m) := by
    rw [← pos_sum m t hm]; exact sumF_le _ _ _ hv
  have hE : ∀ e, e < 5 → aE e (t &&& targetT m) ≤ edgeS m v e := fun e he => by
    rw [edge_sum m t e hm he]; unfold edgeS
    exact sumF_le _ _ _ (fun c hc => by cases Nat.beq (edgeOf m c) e <;> [exact le_rfl; exact hv c hc])
  rcases hg with hg | ⟨hg1, d, hd, hg2⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, d, hd, fun e he => le_trans (hE e he) (hg2 e he)⟩

section
variable (hcomp : ∀ m, m < 37 → compCheck m = true)
include hcomp

theorem comp_parts (m : Nat) (hm : m < 37) :
    dataCheck m = true ∧ v1Check m = true ∧ v2Check m = true ∧ v3Check m = true ∧ v4Check m = true := by
  have h := hcomp m hm
  simp only [compCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem chain1 (m : Nat) (hm : m < 37) (g : F) (hg : g ∈ DF 1) :
    ∃ k, k < nSel m ∧ ∀ c, c < 31 → profL m (tv g) c ≤ e1Val m k c := by
  obtain ⟨b, x, y, hx, hy, rfl⟩ := DF1_form g hg
  let G := (x * 15 + y) * 2 + cond b 1 0
  have hG : G < 450 := by cases b <;> simp [G] <;> omega
  have e : tv (fun z => bop b (z (fv x)) (z (fv y))) = gRect G := by
    rw [gRect_tv]
    have h1 : G / 30 = x := by cases b <;> simp [G] <;> omega
    have h2 : G / 2 % 15 = y := by cases b <;> simp [G] <;> omega
    have h3 : Nat.beq (G % 2) 1 = b := by cases b <;> simp [G] <;> decide
    rw [h1, h2, h3]
  obtain ⟨k, hk, hle⟩ := v1_spec m hm (comp_parts hcomp m hm).2.1 G hG
  exact ⟨k, hk, fun c hc => by rw [e]; exact hle c hc⟩

theorem chain2 (m : Nat) (hm : m < 37) (g : F) (hg : g ∈ DF 2) :
    ∃ k, k < nE2 m ∧ ∀ c, c < 31 → profL m (tv g) c ≤ eVal m 0 k c := by
  obtain ⟨a, ha, b, hb, h⟩ := hg
  have hop : ∃ op : Bool, g = fun z => bop op (a z) (b z) := by
    rcases h with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  obtain ⟨op, rfl⟩ := hop
  rw [tv_bop]
  obtain ⟨ka, hka, hla⟩ := chain1 hcomp m hm a ha
  obtain ⟨kb, hkb, hlb⟩ := chain1 hcomp m hm b hb
  have hv2 := (comp_parts hcomp m hm).2.2.1
  rcases Nat.le_total kb ka with hle | hle
  · obtain ⟨k, hk, hk2⟩ := v2_spec m hm hv2 ka hka op kb hle
    exact ⟨k, hk, fun c hc => le_trans (profL_gate m hm op _ _ _ _ hla hlb c hc) (hk2 c hc)⟩
  · obtain ⟨k, hk, hk2⟩ := v2_spec m hm hv2 kb hkb op ka hle
    exact ⟨k, hk, fun c hc => le_trans (profL_gate m hm op _ _ _ _ hla hlb c hc) (by rw [TvC_symm]; exact hk2 c hc)⟩

theorem chain3 (m : Nat) (hm : m < 37) (g : F) (hg : g ∈ DF 3) :
    (21 ≤ cA (tv g &&& targetT m) → ∃ k, k < nE3A m ∧ ∀ c, c < 31 → profL m (tv g) c ≤ a3v m k c) ∧
    ((∀ c, npos m ≤ c → c < nf m → profV m (tv g) c = capV m c) →
      ∃ k, k < nE3B m ∧ ∀ c, c < 31 → profL m (tv g) c ≤ b3v m k c) := by
  obtain ⟨op, a, b, ha, hb, rfl⟩ := DF3_form g hg
  rw [tv_bop]
  obtain ⟨hd, -, -, hv3, -⟩ := comp_parts hcomp m hm
  obtain ⟨ka, hka, hla⟩ := chain2 hcomp m hm a ha
  obtain ⟨kb, hkb, hlb⟩ := chain2 hcomp m hm b hb
  -- order the two indices
  obtain ⟨i, j, hi, hji, hbound⟩ : ∃ i j, i < nE2 m ∧ j ≤ i ∧
      ∀ c, c < 31 → profL m (gate op (tv a) (tv b)) c ≤ TvC m op (eVal m 0 i c) (eVal m 0 j c) c := by
    rcases Nat.le_total kb ka with hle | hle
    · exact ⟨ka, kb, hka, hle, fun c hc => profL_gate m hm op _ _ _ _ hla hlb c hc⟩
    · exact ⟨kb, ka, hkb, hle, fun c hc => by rw [TvC_symm]; exact profL_gate m hm op _ _ _ _ hla hlb c hc⟩
  have hs := v3_spec m hm hd hv3 i hi op j hji
  constructor
  · intro h21
    rw [← pos_sum m _ hm] at h21
    have : sumF (profV m (gate op (tv a) (tv b))) (npos m) ≤ sumF (fun c => TvC m op (eVal m 0 i c) (eVal m 0 j c) c) (npos m) :=
      sumF_le _ _ _ (fun c hc => by
        rw [← profL_pos m _ c hc]; exact hbound c (by have := nf_le31 m hm; have := npos_le m; omega))
    obtain ⟨k, hk, hk2⟩ := hs.1 (by omega)
    exact ⟨k, hk, fun c hc => le_trans (hbound c hc) (hk2 c hc)⟩
  · intro hfull
    obtain ⟨k, hk, hk2⟩ := hs.2 (fun c h1 h2 => by
      have e1 := hfull c h1 h2
      have hle := hbound c (by have := nf_le31 m hm; omega)
      rw [profL_neg m _ c h2, e1, capV_eq m c hm h2] at hle
      have hup := TvC_neg_le m hm op (eVal m 0 i c) (eVal m 0 j c) c (eVal_le_cap m i c hm hd (by omega)) h1 h2
      omega)
    exact ⟨k, hk, fun c hc => le_trans (hbound c hc) (hk2 c hc)⟩

theorem cond4 (m : Nat) (hm : m < 37) (op : Bool) (a b : F) (ha : a ∈ DF 3) (hb : b ∈ DF 3)
    (hrej : ∀ p, 45 ≤ p → p < 180 → (targetT m).testBit p = true → (gate op (tv a) (tv b)).testBit p = false) :
    Gamma (gate op (tv a) (tv b) &&& targetT m) := by
  obtain ⟨hd, -, -, -, hv4⟩ := comp_parts hcomp m hm
  have hfull := neg_full m _ hm hrej
  have hnp := npos_le m
  have hnf := nf_le31 m hm
  have hga := fun c (hc : c < nf m) => prof_gate m hm op (tv a) (tv b) c hc
  cases op
  · -- AND completion
    by_cases h20 : cA (gate false (tv a) (tv b) &&& targetT m) ≤ 20
    · exact Or.inl h20
    have hposA : 21 ≤ cA (tv a &&& targetT m) := by
      have h1 := pos_sum m (gate false (tv a) (tv b)) hm
      have h2 := pos_sum m (tv a) hm
      have : sumF (profV m (gate false (tv a) (tv b))) (npos m) ≤ sumF (profV m (tv a)) (npos m) :=
        sumF_le _ _ _ (fun c hc => by
          have := hga c (by omega)
          simp only [Tf, show Nat.blt c (npos m) = true by rw [Nat.blt_eq]; exact hc, cond_true, cond_false] at this
          exact le_trans this (min_le_left _ _))
      omega
    have hposB : 21 ≤ cA (tv b &&& targetT m) := by
      have h1 := pos_sum m (gate false (tv a) (tv b)) hm
      have h2 := pos_sum m (tv b) hm
      have : sumF (profV m (gate false (tv a) (tv b))) (npos m) ≤ sumF (profV m (tv b)) (npos m) :=
        sumF_le _ _ _ (fun c hc => by
          have := hga c (by omega)
          simp only [Tf, show Nat.blt c (npos m) = true by rw [Nat.blt_eq]; exact hc, cond_true, cond_false] at this
          exact le_trans this (min_le_right _ _))
      omega
    obtain ⟨ka, hka, hla⟩ := (chain3 hcomp m hm a ha).1 hposA
    obtain ⟨kb, hkb, hlb⟩ := (chain3 hcomp m hm b hb).1 hposB
    have key : ∀ i j, i < nE3A m → (∀ c, c < 31 → profL m (gate false (tv a) (tv b)) c ≤ TvC m false (a3v m i c) (a3v m j c) c) →
        (∀ c, npos m ≤ c → c < nf m → TvC m false (a3v m i c) (a3v m j c) c = capC m c) →
        j < nE3A m → Gamma (gate false (tv a) (tv b) &&& targetT m) := by
      intro i j hi hbnd hneg hj
      have hgv : GammaVal m (fun c => TvC m false (a3v m i c) (a3v m j c) c) := by
        rcases Nat.le_total j i with hle | hle
        · exact (v4_spec m hm hd hv4).1 i hi j hle hneg
        · have := (v4_spec m hm hd hv4).1 j hj i hle (fun c h1 h2 => by rw [TvC_symm]; exact hneg c h1 h2)
          unfold GammaVal edgeS at this ⊢
          simp only [TvC_symm m false (a3v m j _) (a3v m i _)] at this
          exact this
      exact gamma_of_val m hm _ _ (fun c hc => by rw [← profL_pos m _ c hc]; exact hbnd c (by omega)) hgv
    apply key ka kb hka (fun c hc => profL_gate m hm false _ _ _ _ hla hlb c hc) _ hkb
    intro c h1 h2
    have hle := profL_gate m hm false _ _ _ _ hla hlb c (by omega)
    rw [profL_neg m _ c h2, hfull c h1 h2, capV_eq m c hm h2] at hle
    have hup := TvC_neg_le m hm false (a3v m ka c) (a3v m kb c) c (a3v_le m ka c hm hd hka) h1 h2
    omega
  · -- OR completion
    have hfa : ∀ c, npos m ≤ c → c < nf m → profV m (tv a) c = capV m c := fun c h1 h2 => by
      have := hga c h2
      simp only [Tf, show Nat.blt c (npos m) = false by
        cases hb : Nat.blt c (npos m)
        · rfl
        · rw [Nat.blt_eq] at hb; omega, cond_true, cond_false] at this
      rw [hfull c h1 h2] at this
      have := le_trans this (min_le_left _ _)
      have := profV_le_cap m (tv a) c hm h2
      omega
    have hfb : ∀ c, npos m ≤ c → c < nf m → profV m (tv b) c = capV m c := fun c h1 h2 => by
      have := hga c h2
      simp only [Tf, show Nat.blt c (npos m) = false by
        cases hb : Nat.blt c (npos m)
        · rfl
        · rw [Nat.blt_eq] at hb; omega, cond_true, cond_false] at this
      rw [hfull c h1 h2] at this
      have := le_trans this (min_le_right _ _)
      have := profV_le_cap m (tv b) c hm h2
      omega
    obtain ⟨ka, hka, hla⟩ := (chain3 hcomp m hm a ha).2 hfa
    obtain ⟨kb, hkb, hlb⟩ := (chain3 hcomp m hm b hb).2 hfb
    have hgv : GammaVal m (fun c => TvC m true (b3v m ka c) (b3v m kb c) c) := by
      rcases Nat.le_total kb ka with hle | hle
      · exact (v4_spec m hm hd hv4).2 ka hka kb hle
      · have := (v4_spec m hm hd hv4).2 kb hkb ka hle
        unfold GammaVal edgeS at this ⊢
        simp only [TvC_symm m true (b3v m kb _) (b3v m ka _)] at this
        exact this
    exact gamma_of_val m hm _ _ (fun c hc => by
      rw [← profL_pos m _ c hc]; exact profL_gate m hm true _ _ _ _ hla hlb c (by omega)) hgv

end

def P4 (t : Nat) : Prop :=
  (cB t = 135 → S4P t) ∧ (cA t = 45 → cB t ≤ 33) ∧
  (21 ≤ cA t → 68 ≤ cB t → cA t ≤ 24 ∧ cB t ≤ 86 ∧ ∃ w m, m < 58 ∧ dom (permW w t) (targetT m)) ∧
  (∀ m, m < 37 → (∀ p, 45 ≤ p → p < 180 → (targetT m).testBit p = true → t.testBit p = false) → Gamma (t &&& targetT m))

theorem P4_gate (hall : HallP) (hcomp : ∀ m, m < 37 → compCheck m = true)
    (op : Bool) (a b : F) (ha : a ∈ DF 3) (hb : b ∈ DF 3) : P4 (gate op (tv a) (tv b)) :=
  ⟨lemmaA hall op a b ha hb, lemmaB hall op a b ha hb, fun h1 h2 => lemmaC hall op a b ha hb h1 h2,
    fun m hm hrej => cond4 hcomp m hm op a b ha hb hrej⟩

theorem actW_bop (w : List Nat) (op : Bool) (a b : F) :
    actW w (fun z => bop op (a z) (b z)) = fun z => bop op (actW w a z) (actW w b z) := by
  rw [actW_sig, actW_sig, actW_sig]; rfl

theorem L34 (hall : HallP) (hcomp : ∀ m, m < 37 → compCheck m = true)
    (op : Bool) (a b : F) (ha : a ∈ DF 3) (hb : b ∈ DF 3) (w : List Nat) :
    P4 (permW w (tv (fun z => bop op (a z) (b z)))) := by
  rw [← tv_actW, actW_bop, tv_bop]
  exact P4_gate hall hcomp op _ _ (actW_DF w 3 a ha) (actW_DF w 3 b hb)

-- ===== block actions of words =====
def blkAW : List Nat → Nat → Nat
  | [], e => e
  | k :: w, e => cond (Nat.blt k 19) (blkA k (blkAW w e)) (blkAW w e)
def blkBW : List Nat → Nat → Nat
  | [], j => j
  | k :: w, j => cond (Nat.blt k 19) (blkB k (blkBW w j)) (blkBW w j)

theorem aE_word (w : List Nat) (X e : Nat) (he : e < 5) : blkAW w e < 5 ∧ aE e (permW w X) = aE (blkAW w e) X := by
  induction w generalizing X with
  | nil => exact ⟨he, rfl⟩
  | cons k w ih =>
    obtain ⟨h1, h2⟩ := ih (permP (genP k) X)
    show _ ∧ aE e (permW w (permP (genP k) X)) = _
    rw [h2]
    by_cases hk : k < 19
    · simp only [blkAW, show Nat.blt k 19 = true by rw [Nat.blt_eq]; exact hk, cond_true]
      exact ⟨(blk_lt k _ hk h1).1, aE_gen k _ X hk h1⟩
    · simp only [blkAW, show Nat.blt k 19 = false by
        cases h : Nat.blt k 19
        · rfl
        · rw [Nat.blt_eq] at h; omega, cond_false]
      refine ⟨h1, ?_⟩
      exact (sameProf_of_bits _ _ (fun p hp => by rw [testBit_permP]; simp [genP, hk, hp]) _ h1).1

theorem bE_word (w : List Nat) (X j : Nat) (hj : j < 5) : blkBW w j < 5 ∧ bE j (permW w X) = bE (blkBW w j) X := by
  induction w generalizing X with
  | nil => exact ⟨hj, rfl⟩
  | cons k w ih =>
    obtain ⟨h1, h2⟩ := ih (permP (genP k) X)
    show _ ∧ bE j (permW w (permP (genP k) X)) = _
    rw [h2]
    by_cases hk : k < 19
    · simp only [blkBW, show Nat.blt k 19 = true by rw [Nat.blt_eq]; exact hk, cond_true]
      exact ⟨(blk_lt k _ hk h1).2, bE_gen k _ X hk h1⟩
    · simp only [blkBW, show Nat.blt k 19 = false by
        cases h : Nat.blt k 19
        · rfl
        · rw [Nat.blt_eq] at h; omega, cond_false]
      refine ⟨h1, ?_⟩
      exact (sameProf_of_bits _ _ (fun p hp => by rw [testBit_permP]; simp [genP, hk, hp]) _ h1).2

-- the ten dihedral block actions are closed under the generators
def dA (d e : Nat) : Nat := blkAW (wDih d) e
def dB (d j : Nat) : Nat := blkBW (wDih d) j
def dNext (k d : Nat) : Nat :=
  srch (fun d' => allBelow 5 (fun e => Nat.beq (cond (Nat.blt k 19) (blkA k (dA d e)) (dA d e)) (dA d' e)) &&
    allBelow 5 (fun j => Nat.beq (cond (Nat.blt k 19) (blkB k (dB d j)) (dB d j)) (dB d' j))) 10

def dClose : Bool :=
  allBelow 20 (fun k => allBelow 10 (fun d => Nat.blt (dNext k d) 10 &&
    allBelow 5 (fun e => Nat.beq (cond (Nat.blt k 19) (blkA k (dA d e)) (dA d e)) (dA (dNext k d) e)) &&
    allBelow 5 (fun j => Nat.beq (cond (Nat.blt k 19) (blkB k (dB d j)) (dB d j)) (dB (dNext k d) j)))) &&
  allBelow 5 (fun e => Nat.beq (dA 5 e) e && Nat.beq (dB 5 e) e)

set_option maxRecDepth 100000 in
theorem dClose_ok : dClose = true := by decide +kernel

theorem word_blocks (w : List Nat) : ∃ d, d < 10 ∧ ∀ e, e < 5 → blkAW w e = dA d e ∧ blkBW w e = dB d e := by
  have h := dClose_ok
  simp only [dClose, Bool.and_eq_true] at h
  induction w with
  | nil =>
    refine ⟨5, by norm_num, fun e he => ?_⟩
    have := allBelow_spec _ _ h.2 e he
    simp only [Bool.and_eq_true] at this
    exact ⟨(Nat.eq_of_beq_eq_true this.1).symm, (Nat.eq_of_beq_eq_true this.2).symm⟩
  | cons k w ih =>
    obtain ⟨d, hd, hw⟩ := ih
    by_cases hk : k < 19
    · have hc := allBelow_spec _ _ (allBelow_spec _ _ h.1 k (by omega)) d hd
      simp only [Bool.and_eq_true, Nat.blt_eq] at hc
      refine ⟨dNext k d, hc.1.1, fun e he => ?_⟩
      have e1 := Nat.eq_of_beq_eq_true (allBelow_spec _ _ hc.1.2 e he)
      have e2 := Nat.eq_of_beq_eq_true (allBelow_spec _ _ hc.2 e he)
      simp only [blkAW, blkBW]
      rw [(hw e he).1, (hw e he).2]
      exact ⟨e1, e2⟩
    · have hb : Nat.blt k 19 = false := by
        cases hb : Nat.blt k 19
        · rfl
        · rw [Nat.blt_eq] at hb; omega
      refine ⟨d, hd, fun e he => ?_⟩
      simp only [blkAW, blkBW, hb, cond_false]
      exact hw e he
-- ===== the majorant check on the 58 targets =====
def aT (m e : Nat) : Nat := aE e (targetT m)
def bT (m j : Nat) : Nat := bE j (targetT m)

def majCheck : Bool :=
  allBelow 58 (fun m1 => allBelow 58 (fun m2 => allBelow 10 (fun d =>
    !(allBelow 5 (fun e => Nat.ble 9 (aT m1 e + aT m2 (dA d e)))) ||
      Nat.ble (sumF (fun j => min (bT m1 j) (bT m2 (dB d j))) 5) 57)))

def trivCheck : Bool :=
  allBelow 21 (fun q => let m := 37 + q
    Nat.ble (cA (targetT m)) 20 ||
      (Nat.ble (cA (targetT m)) 22 && anyK 10 (fun d => allBelow 5 (fun e => Nat.ble (aT m e) (omegaAt d e)))))

set_option maxRecDepth 100000 in
theorem majCheck_ok : majCheck = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem trivCheck_ok : trivCheck = true := by decide +kernel

theorem allBelow_intro (n : Nat) (p : Nat → Bool) (h : ∀ j, j < n → p j = true) : allBelow n p = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (allBelow n p && p n) = true
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]; rfl

theorem targetT_lt (m : Nat) : targetT m < 2 ^ 180 := Nat.xor_lt_two_pow (fld_lt _ _ _) MV_lt

def S4S4 (t : Nat) : Prop :=
  ∃ x y, S4P x ∧ S4P y ∧ ∀ p, p < 45 → t.testBit p = true → x.testBit p = true ∨ y.testBit p = true

def P5 (t : Nat) : Prop := (cA t = 45 → cB t ≤ 67) ∧ (cB t = 135 → Gamma t ∨ S4S4 t)

theorem cntR_full (x lo n : Nat) (h : cntR x lo n = n) (i : Nat) (hi : i < n) : x.testBit (lo + i) = true := by
  rw [cntR_card] at h
  have hsub : (Finset.range n).filter (fun i => x.testBit (lo + i) = true) = Finset.range n :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [h, Finset.card_range])
  have : i ∈ (Finset.range n).filter (fun i => x.testBit (lo + i) = true) := by rw [hsub]; exact Finset.mem_range.mpr hi
  exact (Finset.mem_filter.mp this).2

theorem cB_full_bits (x : Nat) (h : cB x = 135) (p : Nat) (h1 : 45 ≤ p) (h2 : p < 180) : x.testBit p = false := by
  have := cntR_full _ _ _ h (p - 45) (by omega)
  rw [show 45 + (p - 45) = p by omega, rect_bit _ _ h1 h2] at this
  simpa using this

theorem cA_full_bits (x : Nat) (h : cA x = 45) (p : Nat) (hp : p < 45) : x.testBit p = true := by
  have := cntR_full _ _ _ h p hp; simpa using this

theorem sumF5 (g : Nat → Nat) : sumF g 5 = g 0 + g 1 + g 2 + g 3 + g 4 := by
  show 0 + g 0 + g 1 + g 2 + g 3 + g 4 = _; omega

theorem triv_gamma (m : Nat) (h1 : 37 ≤ m) (h2 : m < 58) : Gamma (targetT m) := by
  have h := allBelow_spec _ _ trivCheck_ok (m - 37) (by omega)
  rw [show 37 + (m - 37) = m by omega] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
  rcases h with h | ⟨h3, h4⟩
  · exact Or.inl h
  · obtain ⟨d, hd, hd2⟩ := anyK_spec _ _ h4
    exact Or.inr ⟨h3, d, hd, fun e he => by
      have := allBelow_spec _ _ hd2 e he; rw [Nat.ble_eq] at this; exact this⟩

theorem Gamma_back (w : List Nat) (t : Nat) (ht : t < 2 ^ 180) (h : Gamma (permW w t)) : Gamma t := by
  have := Gamma_permW (invW w) _ h
  rwa [permW_inv w t ht] at this

-- an AND gate whose output rejects all of V while one input is critical
theorem and_minorant (t1 t2 : Nat) (ht1 : t1 < 2 ^ 180) (ht2 : t2 < 2 ^ 180) (h1 : P4 t1) (h2 : ∀ w, P4 (permW w t2))
    (ha : 21 ≤ cA t1) (hb : 68 ≤ cB t1) (hc : cB (gate false t1 t2) = 135) : Gamma (gate false t1 t2) := by
  obtain ⟨-, -, ⟨w, m, hm, hd⟩⟩ := h1.2.2.1 ha hb
  have ht : gate false t1 t2 < 2 ^ 180 := gate_lt_pow _ _ _ _ ht1 ht2
  apply Gamma_back w _ ht
  have hpw : permW w (gate false t1 t2) = gate false (permW w t1) (permW w t2) := permW_gate _ _ _ _
  rw [hpw]
  have hsub : ∀ p, p < 45 → (gate false (permW w t1) (permW w t2)).testBit p = true →
      (permW w t2 &&& targetT m).testBit p = true := by
    intro p hp hb2
    change ((permW w t1) &&& (permW w t2)).testBit p = true at hb2
    rw [Nat.testBit_and, Bool.and_eq_true] at hb2
    rw [Nat.testBit_and, hb2.2, (hd p (by omega)).1 hp hb2.1]; rfl
  by_cases hm37 : m < 37
  · have hrej : ∀ p, 45 ≤ p → p < 180 → (targetT m).testBit p = true → (permW w t2).testBit p = false := by
      intro p hp1 hp2 htp
      have hfull : (permW w (gate false t1 t2)).testBit p = false := by
        apply cB_full_bits _ _ p hp1 hp2; rw [cB_permW]; exact hc
      rw [hpw] at hfull
      change ((permW w t1) &&& (permW w t2)).testBit p = false at hfull
      rw [Nat.testBit_and, (hd p hp2).2 hp1 htp, Bool.true_and] at hfull
      exact hfull
    exact Gamma_mono hsub ((h2 w).2.2.2 m hm37 hrej)
  · have hg := triv_gamma m (by omega) hm
    exact Gamma_mono (fun p hp hb2 => by
      have := hsub p hp hb2
      rw [Nat.testBit_and, Bool.and_eq_true] at this; exact this.2) hg

theorem L45 (op : Bool) (t1 t2 : Nat) (ht1 : t1 < 2 ^ 180) (ht2 : t2 < 2 ^ 180)
    (h1 : ∀ w, P4 (permW w t1)) (h2 : ∀ w, P4 (permW w t2)) : P5 (gate op t1 t2) := by
  have h1' : P4 t1 := h1 []
  have h2' : P4 t2 := h2 []
  have hA1 : cA t1 ≤ 45 := cntR_le _ _ _
  have hA2 : cA t2 ≤ 45 := cntR_le _ _ _
  have hB1 : cB t1 ≤ 135 := cntR_le _ _ _
  have hB2 : cB t2 ≤ 135 := cntR_le _ _ _
  cases op
  · have la := cA_gate_le false t1 t2
    have la2 := cA_gate_le false t2 t1
    have lb := cB_gate_le false t1 t2
    rw [gate_comm] at la2
    simp only [cond_false] at la lb la2
    constructor
    · intro hA
      have := h1'.2.1 (by omega); have := h2'.2.1 (by omega); omega
    · intro hB
      by_cases h20 : cA (gate false t1 t2) ≤ 20
      · exact Or.inl (Or.inl h20)
      left
      by_cases h68 : 68 ≤ cB t1
      · exact and_minorant t1 t2 ht1 ht2 h1' h2 (by omega) h68 hB
      · have h68' : 68 ≤ cB t2 := by omega
        have hc2 : 21 ≤ cA t2 := by omega
        rw [gate_comm] at hB ⊢
        exact and_minorant t2 t1 ht2 ht1 h2' h1 hc2 h68' hB
  · have la := cA_gate_le true t1 t2
    have lb := cB_gate_le true t1 t2
    have lb2 := cB_gate_le true t2 t1
    rw [gate_comm] at lb2
    simp only [cond_true] at la lb lb2
    constructor
    · intro hA
      by_contra hB
      push_neg at hB
      -- both inputs are critical
      have c1 : 21 ≤ cA t1 := by
        by_contra hc; have := (h2'.2.2.1 (by omega) (by omega)).1; omega
      have c2 : 21 ≤ cA t2 := by
        by_contra hc; have := (h1'.2.2.1 (by omega) (by omega)).1; omega
      obtain ⟨-, -, ⟨w1, m1, hm1, hd1⟩⟩ := h1'.2.2.1 c1 (by omega)
      obtain ⟨-, -, ⟨w2, m2, hm2, hd2⟩⟩ := h2'.2.2.1 c2 (by omega)
      have hx1 : dom t1 (permW (invW w1) (targetT m1)) := by
        have := dom_permW (invW w1) hd1; rwa [permW_inv w1 t1 ht1] at this
      have hx2 : dom t2 (permW (invW w2) (targetT m2)) := by
        have := dom_permW (invW w2) hd2; rwa [permW_inv w2 t2 ht2] at this
      let u := invW w2 ++ w1
      let Z := gate true (targetT m1) (permW u (targetT m2))
      have hZ : permW w1 (gate true (permW (invW w1) (targetT m1)) (permW (invW w2) (targetT m2))) = Z := by
        rw [permW_gate, permW_inv' w1 _ (targetT_lt m1), ← permW_append]
      have hdom := dom_gate true hx1 hx2
      have hcA : cA Z = 45 := by
        have h1 := cA_mono hdom
        have h2 : cA (gate true (permW (invW w1) (targetT m1)) (permW (invW w2) (targetT m2))) ≤ 45 := cntR_le _ _ _
        rw [← hZ, cA_permW]; omega
      have hcB : cB (gate true t1 t2) ≤ cB Z := by have := cB_mono hdom; rw [← hZ, cB_permW]; exact this
      obtain ⟨d, hd, hdw⟩ := word_blocks u
      have hm := allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ majCheck_ok m1 hm1) m2 hm2) d hd
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hm
      -- edge coverage
      have hcov : ∀ e, e < 5 → 9 ≤ aT m1 e + aT m2 (dA d e) := by
        intro e he
        have hz : aE e Z ≤ combA true (aE e (targetT m1)) (aE e (permW u (targetT m2))) := aE_gate true _ _ e
        have hfull : aE e Z = 9 := by
          have hs := cA_split Z
          have := aE_le 0 Z; have := aE_le 1 Z; have := aE_le 2 Z; have := aE_le 3 Z; have := aE_le 4 Z
          interval_cases e <;> omega
        have hw := aE_word u (targetT m2) e he
        rw [hw.2, (hdw e he).1] at hz
        simp only [combA, cond_true] at hz
        unfold aT; have := min_le_right 9 (aE e (targetT m1) + aE (dA d e) (targetT m2)); omega
      rcases hm with hm | hm
      · have : allBelow 5 (fun e => Nat.ble 9 (aT m1 e + aT m2 (dA d e))) = true :=
          allBelow_intro _ _ (fun e he => by rw [Nat.ble_eq]; exact hcov e he)
        rw [this] at hm; exact absurd hm (by simp)
      · rw [Nat.ble_eq, sumF5] at hm
        have hsB := cB_split Z
        have hb : ∀ j, j < 5 → bE j Z ≤ min (bT m1 j) (bT m2 (dB d j)) := by
          intro j hj
          have : bE j Z ≤ combB true (bE j (targetT m1)) (bE j (permW u (targetT m2))) := bE_gate true _ _ j hj
          simp only [combB, cond_true] at this
          rw [(bE_word u (targetT m2) j hj).2, (hdw j hj).2] at this
          exact this
        have := hb 0 (by norm_num); have := hb 1 (by norm_num); have := hb 2 (by norm_num); have := hb 3 (by norm_num)
        have := hb 4 (by norm_num)
        omega
    · intro hB
      right
      have e1 : cB t1 = 135 := by omega
      have e2 : cB t2 = 135 := by omega
      refine ⟨t1, t2, h1'.1 e1, h2'.1 e2, fun p hp hb => ?_⟩
      change (t1 ||| t2).testBit p = true at hb
      rw [Nat.testBit_or, Bool.or_eq_true] at hb
      exact hb

-- ===== star data facts =====
def sA (m : Nat) : Nat := fld starPack 45 m
def cA9 (x : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.add (pop9 (fld x 9 0)) (pop9 (fld x 9 1))) (pop9 (fld x 9 2))) (pop9 (fld x 9 3))) (pop9 (fld x 9 4))
def aE9 (e x : Nat) : Nat := pop9 (fld x 9 e)

def starSizeCheck : Bool := allBelow 75 (fun m => Nat.beq (cA9 (sA m)) 12)

def wStarCheck : Bool :=
  allBelow 75 (fun s1 => allBelow (Nat.add s1 1) (fun s2 => allBelow 10 (fun d =>
    Nat.ble (sumF (fun e => min 9 (omegaAt d e + aE9 e (Nat.lor (sA s1) (sA s2)))) 5) 44)))

def tripleBody (s1 : Nat) : Bool :=
  allBelow (Nat.add s1 1) (fun s2 => Nat.ble (cA9 (Nat.lor (sA s1) (sA s2))) 20 || allBelow (Nat.add s2 1) (fun s3 =>
    Nat.ble (cA9 (Nat.lor (Nat.lor (sA s1) (sA s2)) (sA s3))) 35 &&
    (Nat.ble (cA9 (Nat.lor (Nat.lor (sA s1) (sA s2)) (sA s3))) 32 ||
      allBelow 75 (fun s4 => !Nat.beq (Nat.land (Nat.xor (Nat.land (Nat.lor (Nat.lor (sA s1) (sA s2)) (sA s3)) MA) MA)
        (Nat.xor (sA s4) MA)) 0))))

set_option maxRecDepth 100000 in
theorem starSizeCheck_ok : starSizeCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem wStarCheck_ok : wStarCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem tripleA_ok : allBelow 40 tripleBody = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem tripleB_ok : allBelow 35 (fun k => tripleBody (Nat.add 40 k)) = true := by decide +kernel

theorem triple_body (a : Nat) (ha : a < 75) : tripleBody a = true := by
  by_cases h : a < 40
  · exact allBelow_spec _ _ tripleA_ok a h
  · have e : Nat.add 40 (a - 40) = a := by show 40 + (a - 40) = a; omega
    have := allBelow_spec _ _ tripleB_ok (a - 40) (by omega)
    rw [e] at this
    exact this

theorem aE9_eq (e x : Nat) : aE9 e x = aE e x := by
  unfold aE9 aE; rw [pop9_eq _ (fld_lt _ _ _), cntR_fld9]

theorem cA9_eq (x : Nat) : cA9 x = cA x := by
  rw [cA_split]
  show aE9 0 x + aE9 1 x + aE9 2 x + aE9 3 x + aE9 4 x = _
  rw [aE9_eq, aE9_eq, aE9_eq, aE9_eq, aE9_eq]

theorem sA_eq (m : Nat) (hm : m < 75) : sA m = starAt m := starFld m hm

theorem star_size (m : Nat) (hm : m < 75) : cA (starAt m) = 12 := by
  rw [← sA_eq m hm, ← cA9_eq]; exact Nat.eq_of_beq_eq_true (allBelow_spec _ _ starSizeCheck_ok m hm)

-- counting unions on the accepted side
def coversA (x : Nat) : Prop := ∀ p, p < 45 → x.testBit p = true

theorem cA_or_le (x y : Nat) : cA (x ||| y) ≤ cA x + cA y := cntR_or_le x y 0 45

theorem cA_of_cover (x : Nat) (h : coversA x) : cA x = 45 := by
  unfold cA; rw [cntR_card]
  rw [show (Finset.range 45).filter (fun i => x.testBit (0 + i) = true) = Finset.range 45 by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_add]; constructor
    · exact fun h => h.1
    · exact fun hi => ⟨hi, h i hi⟩]
  simp

theorem cA_le_subA (x s : Nat) (h : subA x s) : cA x ≤ cA s := cntR_subA _ _ _ _ (fun p _ h2 => h p (by omega))

theorem S4P_le (x : Nat) (h : S4P x) : cA x ≤ 12 := by
  rcases h with h | ⟨m, hm, hs⟩
  · omega
  · have := cA_le_subA x _ hs; rw [star_size m hm] at this; exact this

theorem Gamma_le (x : Nat) (h : Gamma x) : cA x ≤ 22 := by rcases h with h | ⟨h, _⟩ <;> omega

-- three stars, sorted
theorem tri_sorted (a b c : Nat) (ha : a < 75) (hb : b ≤ a) (hc : c ≤ b) :
    cA (sA a ||| sA b ||| sA c) ≤ 35 ∧
    (33 ≤ cA (sA a ||| sA b ||| sA c) → ∀ d, d < 75 → ¬ (∀ p, p < 45 → (sA a ||| sA b ||| sA c ||| sA d).testBit p = true)) := by
  have hab := allBelow_spec _ _ (triple_body a ha) b (Nat.lt_succ_of_le hb)
  have el : ∀ x y : Nat, Nat.lor x y = x ||| y := fun _ _ => rfl
  simp only [Bool.or_eq_true, Nat.ble_eq, cA9_eq, el] at hab
  have h : cA (sA a ||| sA b ||| sA c) ≤ 35 ∧
      (cA (sA a ||| sA b ||| sA c) ≤ 32 ∨ allBelow 75 (fun s4 => !Nat.beq (Nat.land (Nat.xor (Nat.land
        (Nat.lor (Nat.lor (sA a) (sA b)) (sA c)) MA) MA) (Nat.xor (sA s4) MA)) 0) = true) := by
    rcases hab with hab | hab
    · have h1 := cA_or_le (sA a ||| sA b) (sA c)
      have h2 := star_size c (by omega)
      rw [← sA_eq c (by omega)] at h2
      exact ⟨by omega, Or.inl (by omega)⟩
    · have h3 := allBelow_spec _ _ hab c (Nat.lt_succ_of_le hc)
      simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, cA9_eq, el] at h3
      exact h3
  refine ⟨h.1, fun h33 d hd hcov => ?_⟩
  rcases h.2 with h2 | h2
  · omega
  · have h3 := allBelow_spec _ _ h2 d hd
    simp only [Bool.not_eq_true'] at h3
    apply Nat.ne_of_beq_eq_false h3
    apply Nat.eq_of_testBit_eq; intro p
    simp only [Nat.zero_testBit]
    change (((((sA a ||| sA b) ||| sA c) &&& MA) ^^^ MA) &&& (sA d ^^^ MA)).testBit p = false
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_xor, testBit_MA]
    by_cases hp : p < 45
    · have := hcov p hp
      simp only [Nat.testBit_or, Bool.or_eq_true] at this
      simp only [hp, decide_true, Bool.and_true, Nat.testBit_or]
      rcases this with ((h4 | h4) | h4) | h4 <;> simp [h4]
    · simp [hp]

theorem lor3_comm (x y z : Nat) : x ||| y ||| z = z ||| y ||| x ∧ x ||| y ||| z = y ||| x ||| z ∧ x ||| y ||| z = x ||| z ||| y := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro p <;> simp only [Nat.testBit_or] <;>
    cases x.testBit p <;> cases y.testBit p <;> cases z.testBit p <;> rfl

theorem tri_any (a b c : Nat) (ha : a < 75) (hb : b < 75) (hc : c < 75) :
    ∃ a' b' c', a' < 75 ∧ b' ≤ a' ∧ c' ≤ b' ∧ sA a' ||| sA b' ||| sA c' = sA a ||| sA b ||| sA c := by
  have e := fun x y z => lor3_comm (sA x) (sA y) (sA z)
  rcases Nat.le_total b a with h1 | h1 <;> rcases Nat.le_total c b with h2 | h2 <;> rcases Nat.le_total c a with h3 | h3
  · exact ⟨a, b, c, ha, h1, h2, rfl⟩
  · exact ⟨a, b, c, ha, h1, h2, rfl⟩
  · exact ⟨a, c, b, ha, h3, h2, (e a b c).2.2.symm⟩
  · exact ⟨c, a, b, hc, h3, h1, by rw [(e c a b).2.1, (e a c b).2.2]⟩
  · exact ⟨b, a, c, hb, h1, h3, (e a b c).2.1.symm⟩
  · exact ⟨b, c, a, hb, h2, h3, by rw [(e b c a).2.2, (e b a c).2.1]⟩
  · exact ⟨c, b, a, hc, h2, h1, (e a b c).1.symm⟩
  · exact ⟨c, b, a, hc, h2, h1, (e a b c).1.symm⟩

theorem subA_or (x y s t : Nat) (h1 : subA x s) (h2 : subA y t) : subA (x ||| y) (s ||| t) := by
  intro p hp h
  rw [Nat.testBit_or, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (h1 p hp h)
  · exact Or.inr (h2 p hp h)

theorem subA_refl (x : Nat) : subA x x := fun _ _ h => h

theorem regroup (q1 q2 q3 q4 : Nat) :
    q1 ||| q2 ||| q3 ||| q4 = q1 ||| (q2 ||| q3 ||| q4) ∧ q1 ||| q2 ||| q3 ||| q4 = q2 ||| (q1 ||| q3 ||| q4) ∧
    q1 ||| q2 ||| q3 ||| q4 = q3 ||| (q1 ||| q2 ||| q4) ∧ q1 ||| q2 ||| q3 ||| q4 = (q1 ||| q2 ||| q3) ||| q4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro p <;> simp only [Nat.testBit_or] <;>
    cases q1.testBit p <;> cases q2.testBit p <;> cases q3.testBit p <;> cases q4.testBit p <;> rfl

theorem three_pieces (q1 q2 q3 : Nat) (h1 : S4P q1) (h2 : S4P q2) (h3 : S4P q3) : cA (q1 ||| q2 ||| q3) ≤ 35 := by
  have b1 := S4P_le q1 h1; have b2 := S4P_le q2 h2; have b3 := S4P_le q3 h3
  have u1 := cA_or_le (q1 ||| q2) q3; have u2 := cA_or_le q1 q2
  rcases h1 with h1 | ⟨a, ha, sa⟩
  · omega
  rcases h2 with h2 | ⟨b, hb, sb⟩
  · omega
  rcases h3 with h3 | ⟨c, hc, sc⟩
  · omega
  obtain ⟨a', b', c', ha', hb', hc', he⟩ := tri_any a b c ha hb hc
  have hsub : subA (q1 ||| q2 ||| q3) (sA a ||| sA b ||| sA c) := by
    rw [sA_eq a ha, sA_eq b hb, sA_eq c hc]; exact subA_or _ _ _ _ (subA_or _ _ _ _ sa sb) sc
  rw [← he] at hsub
  exact le_trans (cA_le_subA _ _ hsub) (tri_sorted a' b' c' ha' hb' hc').1

theorem four_pieces (q1 q2 q3 q4 : Nat) (h1 : S4P q1) (h2 : S4P q2) (h3 : S4P q3) (h4 : S4P q4) :
    cA (q1 ||| q2 ||| q3 ||| q4) ≤ 44 := by
  obtain ⟨r1, r2, r3, r4⟩ := regroup q1 q2 q3 q4
  rcases h4 with s4 | ⟨d, hd, sd⟩
  · rw [r4]; have := cA_or_le (q1 ||| q2 ||| q3) q4; have := three_pieces q1 q2 q3 h1 h2 h3; omega
  rcases h1 with s1 | ⟨a, ha, sa⟩
  · rw [r1]; have := cA_or_le q1 (q2 ||| q3 ||| q4)
    have := three_pieces q2 q3 q4 h2 h3 (Or.inr ⟨d, hd, sd⟩); omega
  rcases h2 with s2 | ⟨b, hb, sb⟩
  · rw [r2]; have := cA_or_le q2 (q1 ||| q3 ||| q4)
    have := three_pieces q1 q3 q4 (Or.inr ⟨a, ha, sa⟩) h3 (Or.inr ⟨d, hd, sd⟩); omega
  rcases h3 with s3 | ⟨c, hc, sc⟩
  · rw [r3]; have := cA_or_le q3 (q1 ||| q2 ||| q4)
    have := three_pieces q1 q2 q4 (Or.inr ⟨a, ha, sa⟩) (Or.inr ⟨b, hb, sb⟩) (Or.inr ⟨d, hd, sd⟩); omega
  -- four stars
  by_contra hc45
  push_neg at hc45
  have hle : cA (q1 ||| q2 ||| q3 ||| q4) ≤ 45 := cntR_le _ _ _
  have hfull : cA (q1 ||| q2 ||| q3 ||| q4) = 45 := by omega
  obtain ⟨a', b', c', ha', hb', hc', he⟩ := tri_any a b c ha hb hc
  have hsub : subA (q1 ||| q2 ||| q3 ||| q4) (sA a' ||| sA b' ||| sA c' ||| sA d) := by
    rw [he, sA_eq a ha, sA_eq b hb, sA_eq c hc, sA_eq d hd]
    exact subA_or _ _ _ _ (subA_or _ _ _ _ (subA_or _ _ _ _ sa sb) sc) sd
  have hcov : ∀ p, p < 45 → (sA a' ||| sA b' ||| sA c' ||| sA d).testBit p = true :=
    fun p hp => hsub p hp (cA_full_bits _ hfull p hp)
  have ts := tri_sorted a' b' c' ha' hb' hc'
  by_cases h33 : 33 ≤ cA (sA a' ||| sA b' ||| sA c')
  · exact ts.2 h33 d hd hcov
  · have h1 := cA_le_subA _ _ hsub
    have h2 := cA_or_le (sA a' ||| sA b' ||| sA c') (sA d)
    have h3 := star_size d hd
    rw [← sA_eq d hd] at h3
    omega

-- W set plus two stars
theorem w_two_stars (X : Nat) (hX : cA X ≤ 22) (d : Nat) (hd : d < 10) (hw : ∀ e, e < 5 → aE e X ≤ omegaAt d e)
    (m1 m2 : Nat) (h1 : m1 < 75) (h2 : m2 < 75) (hcov : ∀ p, p < 45 → (X ||| (sA m1 ||| sA m2)).testBit p = true) : False := by
  obtain ⟨a, b, hab, ha, hb, he⟩ : ∃ a b, b ≤ a ∧ a < 75 ∧ b < 75 ∧ sA a ||| sA b = sA m1 ||| sA m2 := by
    rcases Nat.le_total m2 m1 with h | h
    · exact ⟨m1, m2, h, h1, h2, rfl⟩
    · exact ⟨m2, m1, h, h2, h1, Nat.lor_comm _ _⟩
  rw [← he] at hcov
  have hc := Nat.le_of_ble_eq_true (allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ wStarCheck_ok a ha) b
    (Nat.lt_succ_of_le hab)) d hd)
  rw [sumF5] at hc
  have hfull := cA_of_cover _ hcov
  rw [cA_split] at hfull
  have be : ∀ e, e < 5 → aE e (X ||| (sA a ||| sA b)) ≤ min 9 (omegaAt d e + aE9 e (Nat.lor (sA a) (sA b))) := by
    intro e he5
    rw [aE9_eq]
    exact le_min (aE_le _ _) (le_trans (cntR_or_le _ _ _ _) (by
      have := hw e he5
      show aE e X + aE e (sA a ||| sA b) ≤ omegaAt d e + aE e (sA a ||| sA b); omega))
  have := be 0 (by norm_num); have := be 1 (by norm_num); have := be 2 (by norm_num); have := be 3 (by norm_num)
  have := be 4 (by norm_num)
  omega

theorem no_cover (X1 X2 : Nat) (h1 : Gamma X1 ∨ S4S4 X1) (h2 : Gamma X2 ∨ S4S4 X2)
    (hcov : ∀ p, p < 45 → (X1 ||| X2).testBit p = true) : False := by
  have hf := cA_of_cover _ hcov
  have hu := cA_or_le X1 X2
  -- one Gamma set and one union of two S4 sets
  have gs : ∀ Y1 Y2, Gamma Y1 → S4S4 Y2 → (∀ p, p < 45 → (Y1 ||| Y2).testBit p = true) → False := by
    intro Y1 Y2 hg ⟨x, y, sx, sy, hxy⟩ hc
    have hsub : subA (Y1 ||| Y2) (Y1 ||| (x ||| y)) := subA_or _ _ _ _ (subA_refl _) (fun p hp hb => by
      rw [Nat.testBit_or, Bool.or_eq_true]; exact hxy p hp hb)
    have hc' : ∀ p, p < 45 → (Y1 ||| (x ||| y)).testBit p = true := fun p hp => hsub p hp (hc p hp)
    have hf' := cA_of_cover _ hc'
    have u1 := cA_or_le Y1 (x ||| y); have u2 := cA_or_le x y
    have bx := S4P_le x sx; have bY := S4P_le y sy
    rcases hg with hg | ⟨hg1, d, hd, hgw⟩
    · omega
    rcases sx with sx | ⟨m1, hm1, s1⟩
    · rcases sy with sy | ⟨m2, hm2, s2⟩
      · omega
      · omega
    rcases sy with sy | ⟨m2, hm2, s2⟩
    · omega
    apply w_two_stars Y1 hg1 d hd hgw m1 m2 hm1 hm2
    intro p hp
    have hs : subA (Y1 ||| (x ||| y)) (Y1 ||| (sA m1 ||| sA m2)) := by
      rw [sA_eq m1 hm1, sA_eq m2 hm2]; exact subA_or _ _ _ _ (subA_refl _) (subA_or _ _ _ _ s1 s2)
    exact hs p hp (hc' p hp)
  rcases h1 with g1 | s1 <;> rcases h2 with g2 | s2
  · have := Gamma_le X1 g1; have := Gamma_le X2 g2; omega
  · exact gs X1 X2 g1 s2 hcov
  · exact gs X2 X1 g2 s1 (fun p hp => by rw [Nat.lor_comm]; exact hcov p hp)
  · obtain ⟨x1, y1, sx1, sy1, h1⟩ := s1
    obtain ⟨x2, y2, sx2, sy2, h2⟩ := s2
    have hsub : subA (X1 ||| X2) (x1 ||| y1 ||| x2 ||| y2) := by
      intro p hp hb
      rw [Nat.testBit_or, Bool.or_eq_true] at hb
      simp only [Nat.testBit_or, Bool.or_eq_true]
      rcases hb with hb | hb
      · rcases h1 p hp hb with h | h <;> simp [h]
      · rcases h2 p hp hb with h | h <;> simp [h]
    have := cA_le_subA _ _ hsub
    have := four_pieces x1 y1 x2 y2 sx1 sy1 sx2 sy2
    omega

def P6 (t : Nat) : Prop := ¬ (cA t = 45 ∧ cB t = 135)

theorem L56 (op : Bool) (t1 t2 : Nat) (h1 : P5 t1) (h2 : P5 t2) : P6 (gate op t1 t2) := by
  rintro ⟨hA, hB⟩
  have hA1 : cA t1 ≤ 45 := cntR_le _ _ _
  have hA2 : cA t2 ≤ 45 := cntR_le _ _ _
  have hB1 : cB t1 ≤ 135 := cntR_le _ _ _
  have hB2 : cB t2 ≤ 135 := cntR_le _ _ _
  cases op
  · have la := cA_gate_le false t1 t2
    have la2 := cA_gate_le false t2 t1
    have lb := cB_gate_le false t1 t2
    rw [gate_comm] at la2
    simp only [cond_false] at la lb la2
    have := h1.1 (by omega); have := h2.1 (by omega); omega
  · have lb := cB_gate_le true t1 t2
    have lb2 := cB_gate_le true t2 t1
    rw [gate_comm] at lb2
    simp only [cond_true] at lb lb2
    exact no_cover t1 t2 (h1.2 (by omega)) (h2.2 (by omega)) (fun p hp => cA_full_bits _ hA p hp)

-- ===== the layered family =====
def Tfam : Nat → Set F
  | 0 => DF 0
  | 1 => DF 1
  | 2 => DF 2
  | 3 => DF 3
  | 4 => {g | ∀ w, P4 (permW w (tv g))}
  | 5 => {g | P5 (tv g)}
  | 6 => {g | P6 (tv g)}
  | _ => Set.univ

section
variable (hall : HallP) (hcomp : ∀ m, m < 37 → compCheck m = true)
include hall hcomp

theorem Tfam_closed (k : Nat) (f g : F) (hf : f ∈ Tfam k) (hg : g ∈ Tfam k) :
    (fun y => f y && g y) ∈ Tfam (k + 1) ∧ (fun y => f y || g y) ∈ Tfam (k + 1) := by
  match k with
  | 0 => exact ⟨⟨f, hf, g, hg, Or.inl rfl⟩, ⟨f, hf, g, hg, Or.inr rfl⟩⟩
  | 1 => exact ⟨⟨f, hf, g, hg, Or.inl rfl⟩, ⟨f, hf, g, hg, Or.inr rfl⟩⟩
  | 2 => exact ⟨⟨f, hf, g, hg, Or.inl rfl⟩, ⟨f, hf, g, hg, Or.inr rfl⟩⟩
  | 3 =>
    have hf3 : f ∈ DF 3 := hf
    have hg3 : g ∈ DF 3 := hg
    exact ⟨fun w => L34 hall hcomp false f g hf3 hg3 w, fun w => L34 hall hcomp true f g hf3 hg3 w⟩
  | 4 =>
    have hf4 : ∀ w, P4 (permW w (tv f)) := hf
    have hg4 : ∀ w, P4 (permW w (tv g)) := hg
    have e0 := tv_bop false f g
    have e1 := tv_bop true f g
    have h0 := L45 false _ _ (tv_lt f) (tv_lt g) hf4 hg4
    have h1 := L45 true _ _ (tv_lt f) (tv_lt g) hf4 hg4
    rw [← e0] at h0
    rw [← e1] at h1
    exact ⟨h0, h1⟩
  | 5 =>
    have hf5 : P5 (tv f) := hf
    have hg5 : P5 (tv g) := hg
    have e0 := tv_bop false f g
    have e1 := tv_bop true f g
    have h0 := L56 false _ _ hf5 hg5
    have h1 := L56 true _ _ hf5 hg5
    rw [← e0] at h0
    rw [← e1] at h1
    exact ⟨h0, h1⟩
  | k + 6 => exact ⟨Set.mem_univ _, Set.mem_univ _⟩

theorem Tfam_mono (k : Nat) (f : F) (hf : f ∈ Tfam k) : f ∈ Tfam (k + 1) := by
  have h := (Tfam_closed hall hcomp k f f hf hf).1
  have e : (fun y => f y && f y) = f := funext fun y => by simp
  rw [e] at h; exact h

end

theorem Tfam_base (i : Fin 15) : (fun x : Fin 15 → Bool => x i) ∈ Tfam 0 := ⟨i, rfl⟩

def fTarget : F := fun z => (((z 0 && z 5) || (z 0 && z 10) || (z 5 && z 10)) && ((z 1 && z 6) || (z 1 && z 11) || (z 6 && z 11))) || (((z 1 && z 6) || (z 1 && z 11) || (z 6 && z 11)) && ((z 2 && z 7) || (z 2 && z 12) || (z 7 && z 12))) || (((z 2 && z 7) || (z 2 && z 12) || (z 7 && z 12)) && ((z 3 && z 8) || (z 3 && z 13) || (z 8 && z 13))) || (((z 3 && z 8) || (z 3 && z 13) || (z 8 && z 13)) && ((z 4 && z 9) || (z 4 && z 14) || (z 9 && z 14))) || (((z 4 && z 9) || (z 4 && z 14) || (z 9 && z 14)) && ((z 0 && z 5) || (z 0 && z 10) || (z 5 && z 10)))

set_option maxRecDepth 100000 in
theorem fTarget_A : cA (tv fTarget) = 45 := by decide +kernel
set_option maxRecDepth 100000 in
theorem fTarget_B : cB (tv fTarget) = 135 := by decide +kernel

theorem fTarget_not6 : fTarget ∉ Tfam 6 := fun h => h ⟨fTarget_A, fTarget_B⟩

-- ===== the finite checks =====
def chunkPack : Nat := 0x13802803800000002040c010808f0c308c0822cb0c024300000509014534000f0463101c018c3000052071c800601030e15010034000018d18820000009000a00038000900800100500500000000900500000000000000000000500000008d0000000001400000000000032090010060002c00001c00003c01821420082c700b00040d0000100000000420000c000038000000108034000d00000000224b3cd00100000000000700000000000001018400018014820400018f00140001000200000000001000500c0003c00001800060000000003000003851461802ca00000400000a34a0002400002842002c001000024338000500b00018e20008d04008004d34e00000000800400c00000c0000004003cf0003c02460003030053c00000020000001c000d1c600814300000f00d40000000100000010e2870090000002080000000d00000c000000b0002c038000008b0073c114310000a34f01034f00000040d1803c100000000000000600004000018008528f04a20314800424024300010008014e00024000000000d00a0000003032813cd00838020c0063420000000001862800000001c00002802000040003003c50c00ca0004010052003c00070000000090000000002862890000002cb1c93800000000000860052c900004428f00000000c00000f1c80cb00000024e2800003002900001c400008500e0c100000028210000000a00000000008b3c024028b08b0000001c900000f00000400400300c0cb00000700000020d10e04038e10810024400e3500000030000000000000050403c01cc1010001c000814d08529041000000429000f28010938814a00001038000c04000014800020000300f00324a40024f04a00700100b08000d0003410010000000003003c214b0c100000a04e34004018b00000000e30920024010034300000000018e30e2800400033c00001c00001c900018800000000024f00200004200010000400424028700c20000b1ca3440cb04d0c000a00730200c0002801400002880ce00000c01000200030100004c01000f00000534018530040d10200038024f24020000000004008038014b0003cb0000000000800090070030000020c840e0001431c00083441450001400001c30070000c000000f00e14000f04100000b1002c308d3032c004000024c4093c31c010e00300000000000c00800e00e0050020ca1c014724c00e00f3c628000e00700e30000100800700a3851003ce20024a00e18c0002400803000880cd10c0001463c400b1c01401422d00404001c008b34238024e08000f1c01c100040c30018d4062471002cc04a1902c00812843c91000003043cb0c000b0003090031c130a10008b40800700000e2cb3c138400c2460001c600200300618000700f00000100100024040b00a04a34000808728e34000000d00000f20000000010d3400001082c000330200400934e30d30b18228b0000002001ca31000000d00c08f3400100003cf0004000000000c50001c60101082800004061c00002d000e0002000000030060100040091800000000c71400002481002001c000008024908600c00810a04000400904c3900001400003c04090002cc2c000c1470100070c03401000001842c02cd00000000d34000e0cc0003802c000000000600000600001004004624040f00e34628040f00810f0030000062ce00040014d0ca24500a00900b0021cb1c02cd20834540018c1c00003cd38000901000018000e283
def chunkOf (i c : Nat) : Nat := fld chunkPack 6 (Nat.add (Nat.mul 41 i) c)
def chunkOK (k : Nat) : Bool :=
  allBelow 41 (fun i => allBelow 41 (fun c => !Nat.beq (chunkOf i c) (Nat.add k 1) || pairOK i c))
def codeBound : Bool :=
  allBelow 41 (fun i => allBelow 41 (fun c => !ocheck i c || (Nat.blt 0 (chunkOf i c) && Nat.ble (chunkOf i c) 16)))

set_option maxRecDepth 100000 in
theorem codeBound_ok : codeBound = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck0 : chunkOK 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck1 : chunkOK 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck2 : chunkOK 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck3 : chunkOK 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck4 : chunkOK 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck5 : chunkOK 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck6 : chunkOK 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck7 : chunkOK 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck8 : chunkOK 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck9 : chunkOK 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck10 : chunkOK 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck11 : chunkOK 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck12 : chunkOK 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck13 : chunkOK 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck14 : chunkOK 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck15 : chunkOK 15 = true := by decide +kernel

theorem allChunks : forall k, k < 16 -> chunkOK k = true := by
  intro k hk
  interval_cases k
  exacts [ck0, ck1, ck2, ck3, ck4, ck5, ck6, ck7, ck8, ck9, ck10, ck11, ck12, ck13, ck14, ck15]

theorem allPairs : HallP := by
  intro i c hi hc ho
  have hb : (!ocheck i c || (Nat.blt 0 (chunkOf i c) && Nat.ble (chunkOf i c) 16)) = true :=
    allBelow_spec _ _ (allBelow_spec _ _ codeBound_ok i hi) c hc
  rw [ho, Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hb
  have h : (!Nat.beq (chunkOf i c) (Nat.add (chunkOf i c - 1) 1) || pairOK i c) = true :=
    allBelow_spec _ _ (allBelow_spec _ _ (allChunks (chunkOf i c - 1) (by omega)) i hi) c hc
  have e : Nat.add (chunkOf i c - 1) 1 = chunkOf i c := by show chunkOf i c - 1 + 1 = chunkOf i c; omega
  rw [e, Nat.beq_refl] at h
  simpa using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc0 : compCheck 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc1 : compCheck 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc2 : compCheck 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc3 : compCheck 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc4 : compCheck 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc5 : compCheck 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc6 : compCheck 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc7 : compCheck 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc8 : compCheck 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc9 : compCheck 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc10 : compCheck 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc11 : compCheck 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc12 : compCheck 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc13 : compCheck 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc14 : compCheck 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc15 : compCheck 15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc16 : compCheck 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc17 : compCheck 17 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc18 : compCheck 18 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc19 : compCheck 19 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc20 : compCheck 20 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc21 : compCheck 21 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc22 : compCheck 22 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc23 : compCheck 23 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc24 : compCheck 24 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc25 : compCheck 25 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc26 : compCheck 26 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc27 : compCheck 27 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc28 : compCheck 28 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc29 : compCheck 29 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc30 : compCheck 30 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc31 : compCheck 31 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc32 : compCheck 32 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc33 : compCheck 33 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc34 : compCheck 34 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc35 : compCheck 35 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cc36 : compCheck 36 = true := by decide +kernel

theorem allComp : forall m, m < 37 -> compCheck m = true := by
  intro m hm
  interval_cases m
  exacts [cc0, cc1, cc2, cc3, cc4, cc5, cc6, cc7, cc8, cc9, cc10, cc11, cc12, cc13, cc14, cc15, cc16, cc17, cc18, cc19, cc20, cc21, cc22, cc23, cc24, cc25, cc26, cc27, cc28, cc29, cc30, cc31, cc32, cc33, cc34, cc35, cc36]

end PEqualNP.Outside.L_meta_1404

theorem PEqualNP.Outside.L_meta_1404 : ¬ (∀ T : ℕ → Set ((Fin 15 → Bool) → Bool), (∀ i : Fin 15, (fun x : Fin 15 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 15 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 15 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 15 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 15 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 15 → Bool => (((z 0 && z 5) || (z 0 && z 10) || (z 5 && z 10)) && ((z 1 && z 6) || (z 1 && z 11) || (z 6 && z 11))) || (((z 1 && z 6) || (z 1 && z 11) || (z 6 && z 11)) && ((z 2 && z 7) || (z 2 && z 12) || (z 7 && z 12))) || (((z 2 && z 7) || (z 2 && z 12) || (z 7 && z 12)) && ((z 3 && z 8) || (z 3 && z 13) || (z 8 && z 13))) || (((z 3 && z 8) || (z 3 && z 13) || (z 8 && z 13)) && ((z 4 && z 9) || (z 4 && z 14) || (z 9 && z 14))) || (((z 4 && z 9) || (z 4 && z 14) || (z 9 && z 14)) && ((z 0 && z 5) || (z 0 && z 10) || (z 5 && z 10)))) ∈ T 6) := by
  intro h
  exact PEqualNP.Outside.L_meta_1404.fTarget_not6 (h PEqualNP.Outside.L_meta_1404.Tfam
    PEqualNP.Outside.L_meta_1404.Tfam_base
    (PEqualNP.Outside.L_meta_1404.Tfam_mono PEqualNP.Outside.L_meta_1404.allPairs PEqualNP.Outside.L_meta_1404.allComp)
    (PEqualNP.Outside.L_meta_1404.Tfam_closed PEqualNP.Outside.L_meta_1404.allPairs PEqualNP.Outside.L_meta_1404.allComp))
