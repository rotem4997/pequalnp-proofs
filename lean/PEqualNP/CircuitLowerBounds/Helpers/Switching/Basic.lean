import PEqualNP.CircuitLowerBounds.Helpers.Switching.Plan

/-!
# The parts of the plan for L-lib-034 that need neither interface

The base case, parity under a restriction, the arithmetic, the iteration from `Round`, and
the assembly. Nothing here is checked until L-lib-034 is.
-/

namespace PEqualNP.CircuitLowerBounds.Switching.Plan

open PEqualNP.CircuitLowerBounds

theorem zmod2_flip (c : ZMod 2) : decide (c + 1 = 1) = !decide (c = 1) := by
  revert c; decide

theorem cnt_update {V : Type} [Fintype V] [DecidableEq V] (x : V → Bool) (v : V) :
    cnt (Function.update x v (!x v)) = cnt x + 1 := by
  unfold cnt
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  have h : ∑ u ∈ Finset.univ.erase v, (if Function.update x v (!x v) u = true then (1 : ZMod 2) else 0)
      = ∑ u ∈ Finset.univ.erase v, (if x u = true then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]
  rw [h, Function.update_self]
  generalize (∑ u ∈ Finset.univ.erase v, (if x u = true then (1 : ZMod 2) else 0)) = s
  cases x v <;> revert s <;> decide

theorem par_update {V : Type} [Fintype V] [DecidableEq V] (x : V → Bool) (v : V) :
    par (Function.update x v (!x v)) = !par x := by
  unfold par; rw [cnt_update, zmod2_flip]

theorem exists_notMem_of_card_lt {V : Type} [Fintype V] (S : Finset V)
    (h : S.card < Fintype.card V) : ∃ v, v ∉ S := by
  by_contra hc
  push_neg at hc
  have : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hc
  rw [this, Finset.card_univ] at h
  exact lt_irrefl _ h

/-- The base case: a function that is parity or its negation and has certificates of size `w`
for its true points, or for its false points, lives on at most `w` variables. -/
theorem base {V : Type} [Fintype V] [DecidableEq V] (w : ℕ) (f : BF V) (hp : IsPar f)
    (hc : Cert1 w f ∨ Cert0 w f) : Fintype.card V ≤ w := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨b, hb⟩ := hp
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v0⟩ := hne
  -- a point of each parity
  have hx : ∀ c : Bool, ∃ x : V → Bool, f x = c := by
    intro c
    by_cases h0 : f (fun _ => false) = c
    · exact ⟨_, h0⟩
    · refine ⟨Function.update (fun _ => false) v0 (!((fun _ : V => false) v0)), ?_⟩
      rw [hb, par_update]
      have := hb (fun _ => false)
      rw [this] at h0
      revert h0
      cases b <;> cases par (fun _ : V => false) <;> cases c <;> simp
  rcases hc with hc | hc
  · obtain ⟨x, hx1⟩ := hx true
    obtain ⟨S, hS, hcert⟩ := hc x hx1
    obtain ⟨v, hv⟩ := exists_notMem_of_card_lt S (by omega)
    have h1 := hcert (Function.update x v (!x v)) (fun i hi => by
      rw [Function.update_of_ne]; rintro rfl; exact hv hi)
    rw [hb, par_update] at h1
    rw [hb] at hx1
    revert h1 hx1
    cases b <;> cases par x <;> simp
  · obtain ⟨x, hx1⟩ := hx false
    obtain ⟨S, hS, hcert⟩ := hc x hx1
    obtain ⟨v, hv⟩ := exists_notMem_of_card_lt S (by omega)
    have h1 := hcert (Function.update x v (!x v)) (fun i hi => by
      rw [Function.update_of_ne]; rintro rfl; exact hv hi)
    rw [hb, par_update] at h1
    rw [hb] at hx1
    revert h1 hx1
    cases b <;> cases par x <;> simp

/-! ## Parity under a restriction -/

theorem zmod2_shift (a c : ZMod 2) : decide (a + c = 1) = xor (decide (c = 1)) (decide (a = 1)) := by
  revert a c; decide

theorem cnt_fill {V : Type} [Fintype V] [DecidableEq V] (ρ : Restr V) (y : Stars ρ → Bool) :
    cnt (fill ρ y) = cnt y +
      ∑ v ∈ Finset.univ.filter (fun v => ¬ ρ v = none), (if (ρ v).getD false = true then 1 else 0) := by
  unfold cnt
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => ρ v = none)]
  congr 1
  · rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [fill, x.2]
  · refine Finset.sum_congr rfl fun v hv => ?_
    have h := (Finset.mem_filter.mp hv).2
    simp [fill, h]

/-- Parity (or its negation) restricted is parity (or its negation) of the stars. -/
theorem isPar_restr {V : Type} [Fintype V] [DecidableEq V] (ρ : Restr V) (f : BF V)
    (hp : IsPar f) : IsPar (restr ρ f) := by
  obtain ⟨b, hb⟩ := hp
  refine ⟨xor b (decide ((∑ v ∈ Finset.univ.filter (fun v => ¬ ρ v = none),
    (if (ρ v).getD false = true then (1 : ZMod 2) else 0)) = 1)), fun y => ?_⟩
  unfold restr
  rw [hb]
  unfold par
  rw [cnt_fill, zmod2_shift, Bool.xor_assoc]

/-! ## Gates over certified inputs -/

theorem cert1_or {V : Type} {w : ℕ} {g : BF V} {I : Set (BF V)} (hI : ∀ h ∈ I, Cert1 w h)
    (hg : ∀ x, g x = true ↔ ∃ h ∈ I, h x = true) : Cert1 w g := by
  intro x hx
  obtain ⟨h, hh, hhx⟩ := (hg x).mp hx
  obtain ⟨S, hS, hc⟩ := hI h hh x hhx
  exact ⟨S, hS, fun y hy => (hg y).mpr ⟨h, hh, hc y hy⟩⟩

theorem cert0_and {V : Type} {w : ℕ} {g : BF V} {I : Set (BF V)} (hI : ∀ h ∈ I, Cert0 w h)
    (hg : ∀ x, g x = true ↔ ∀ h ∈ I, h x = true) : Cert0 w g := by
  intro x hx
  have : ¬ ∀ h ∈ I, h x = true := fun hall => by rw [(hg x).mpr hall] at hx; cases hx
  push_neg at this
  obtain ⟨h, hh, hhx⟩ := this
  obtain ⟨S, hS, hc⟩ := hI h hh x (by simpa using hhx)
  refine ⟨S, hS, fun y hy => ?_⟩
  by_contra hgy
  have hgy' : g y = true := by simpa using hgy
  have := (hg y).mp hgy' h hh
  rw [hc y hy] at this; cases this

/-- A gate of level two has certificates of one kind. -/
theorem level_two {V : Type} {w k : ℕ} {G : Finset (BF V)} {lev : BF V → ℕ}
    (hG : IsCirc w k G lev) {g : BF V} (hg : g ∈ G) (h2 : lev g ≤ 2) : Cert1 w g ∨ Cert0 w g := by
  obtain ⟨-, -, I, hI, hor | hand⟩ := hG g hg
  · left
    refine cert1_or (fun h hh => ?_) hor
    rcases hI h hh with ⟨hh', hlt⟩ | hl
    · have := (hG h hh').1; omega
    · exact hl.1
  · right
    refine cert0_and (fun h hh => ?_) hand
    rcases hI h hh with ⟨hh', hlt⟩ | hl
    · have := (hG h hh').1; omega
    · exact hl.2

/-! ## The iteration, from one round -/

theorem iterateGen (hR : Round) : ∀ (j : ℕ) (V : Type) [Fintype V] [DecidableEq V] (w t : ℕ)
    (G : Finset (BF V)) (lev : BF V → ℕ) (f : BF V), 1 ≤ t → w ≤ t → IsCirc w (j + 2) G lev →
    G.card < 2 ^ t → (f ∈ G ∨ Low w f) → IsPar f → Fintype.card V / (16 * t + 1) ^ j ≤ t := by
  intro j
  induction j with
  | zero =>
    intro V _ _ w t G lev f ht hw hG hcard hf hp
    have hc : Cert1 w f ∨ Cert0 w f := by
      rcases hf with hf | hf
      · exact level_two hG hf (hG f hf).2.1
      · exact Or.inl hf.1
    have := base w f hp hc
    simp only [pow_zero, Nat.div_one]
    omega
  | succ j ih =>
    intro V _ _ w t G lev f ht hw hG hcard hf hp
    set N := Fintype.card V with hN
    set l := N / (16 * t + 1) with hl
    have h1 : l ≤ N := Nat.div_le_self _ _
    have h2 : (16 * t + 1) * l ≤ N := by rw [mul_comm]; exact Nat.div_mul_le_self _ _
    have h3 : 16 * w * l ≤ N - l := by
      have : 16 * w * l ≤ 16 * t * l := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hw)
      have : (16 * t + 1) * l = 16 * t * l + l := by ring
      omega
    obtain ⟨ρ, G', lev', hst, hc', hG', hf'⟩ :=
      hR V w t (j + 1 + 2) l G lev ht hw (by omega) hG hcard h1 h3
    have := ih (Stars ρ) t t G' lev' (restr ρ f) ht le_rfl hG' (lt_of_le_of_lt hc' hcard)
      (hf' f hf) (isPar_restr ρ f hp)
    rw [hst] at this
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    exact this

theorem iterate_of_round : IterateOfRound := by
  intro hR V _ _ K t G lev f hK ht hG hcard hf hp
  obtain ⟨j, rfl⟩ : ∃ j, K = j + 3 := ⟨K - 3, by omega⟩
  set N := Fintype.card V with hN
  have h1 : N / 17 ≤ N := Nat.div_le_self _ _
  have h2 : 17 * (N / 17) ≤ N := by rw [mul_comm]; exact Nat.div_mul_le_self _ _
  obtain ⟨ρ, G', lev', hst, hc', hG', hf'⟩ :=
    hR V 1 t (j + 3) (N / 17) G lev ht ht (by omega) hG hcard h1 (by omega)
  have := iterateGen hR j (Stars ρ) t t G' lev' (restr ρ f) ht le_rfl hG'
    (lt_of_le_of_lt hc' hcard) (hf' f hf) (isPar_restr ρ f hp)
  rw [hst] at this
  rw [← Nat.div_div_eq_div_mul]
  simpa using this

/-! ## The arithmetic -/

theorem polylog_lt (k C : ℕ) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (C * (Nat.log 2 n + 4)) ^ k < n := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)
  have hε : (0 : ℝ) < 1 / ((5 * C : ℝ) ^ k + 1) := by positivity
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨2 ^ (L₀ + 1), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by
    have : 0 < 2 ^ (L₀ + 1) := by positivity
    omega
  set L := Nat.log 2 n with hL
  have hLge : L₀ + 1 ≤ L := (Nat.le_log_iff_pow_le (by norm_num) hn0).mpr hn
  have hpow : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn0
  have hreal := hL₀ L (by omega)
  have h2pos : (0 : ℝ) < 2 ^ L := by positivity
  have hD : ((5 * C : ℝ) ^ k + 1) * (L : ℝ) ^ k < 2 ^ L := by
    have h := hreal
    rw [div_lt_iff₀ h2pos] at h
    have hpos : (0 : ℝ) < (5 * C : ℝ) ^ k + 1 := by positivity
    calc ((5 * C : ℝ) ^ k + 1) * (L : ℝ) ^ k
        < ((5 * C : ℝ) ^ k + 1) * (1 / ((5 * C : ℝ) ^ k + 1) * 2 ^ L) :=
          mul_lt_mul_of_pos_left h hpos
      _ = 2 ^ L := by field_simp
  have hle : ((C * (L + 4) : ℕ) : ℝ) ^ k ≤ ((5 * C : ℝ) ^ k + 1) * (L : ℝ) ^ k := by
    have h5 : ((C * (L + 4) : ℕ) : ℝ) ≤ (5 * C : ℝ) * L := by
      have : C * (L + 4) ≤ 5 * C * L := by nlinarith
      exact_mod_cast this
    calc ((C * (L + 4) : ℕ) : ℝ) ^ k ≤ ((5 * C : ℝ) * L) ^ k :=
          pow_le_pow_left₀ (by positivity) h5 k
      _ = (5 * C : ℝ) ^ k * (L : ℝ) ^ k := mul_pow _ _ _
      _ ≤ ((5 * C : ℝ) ^ k + 1) * (L : ℝ) ^ k := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
  have hfin : ((C * (L + 4)) ^ k : ℕ) < 2 ^ L := by
    have : (((C * (L + 4)) ^ k : ℕ) : ℝ) < ((2 ^ L : ℕ) : ℝ) := by
      push_cast
      push_cast at hle
      linarith
    exact_mod_cast this
  omega

theorem pre_arith (t d n : ℕ) (ht : 1 ≤ t) (hd : 2 ≤ d)
    (h : n / (17 * (16 * t + 1) ^ (d - 2)) ≤ t) : n ≤ (34 * t) ^ (d - 1) := by
  have hpos : 0 < 17 * (16 * t + 1) ^ (d - 2) := by positivity
  have h1 : n < (t + 1) * (17 * (16 * t + 1) ^ (d - 2)) :=
    (Nat.div_lt_iff_lt_mul hpos).mp (by omega)
  have h2 : (16 * t + 1) ^ (d - 2) ≤ (34 * t) ^ (d - 2) := Nat.pow_le_pow_left (by omega) _
  have h3 : (t + 1) * 17 ≤ 34 * t := by omega
  have h4 : (34 * t) ^ (d - 1) = 34 * t * (34 * t) ^ (d - 2) := by
    have : d - 1 = (d - 2) + 1 := by omega
    rw [this, pow_succ']
  calc n ≤ (t + 1) * (17 * (16 * t + 1) ^ (d - 2)) := h1.le
    _ = (t + 1) * 17 * (16 * t + 1) ^ (d - 2) := by ring
    _ ≤ 34 * t * (34 * t) ^ (d - 2) := Nat.mul_le_mul h3 h2
    _ = (34 * t) ^ (d - 1) := h4.symm

theorem finalArith : FinalArith := by
  refine ⟨170, fun d hd => ?_⟩
  obtain ⟨n₀, hn₀⟩ := polylog_lt (d - 1) 34
  refine ⟨max n₀ 2, fun n hn s h => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hpre := pre_arith _ d n (by omega) hd h
  have hlog : Nat.log 2 (2 * (n + s) + 2) ≤ Nat.log 2 (n + s) + 2 := by
    have : 2 * (n + s) + 2 ≤ (n + s) * 2 * 2 := by omega
    calc Nat.log 2 (2 * (n + s) + 2) ≤ Nat.log 2 ((n + s) * 2 * 2) := Nat.log_mono_right this
      _ = Nat.log 2 (n + s) + 2 := by
          rw [Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega)]
  by_cases hs : n ≤ s
  · have h1 : Nat.log 2 (n + s) ≤ Nat.log 2 s + 1 := by
      calc Nat.log 2 (n + s) ≤ Nat.log 2 (s * 2) := Nat.log_mono_right (by omega)
        _ = Nat.log 2 s + 1 := Nat.log_mul_base (by norm_num) (by omega)
    have h2 : 1 ≤ Nat.log 2 s := Nat.log_pos (by norm_num) (by omega)
    calc n ≤ (34 * (Nat.log 2 (2 * (n + s) + 2) + 1)) ^ (d - 1) := hpre
      _ ≤ (170 * Nat.log 2 s) ^ (d - 1) := Nat.pow_le_pow_left (by omega) _
  · exfalso
    have h1 : Nat.log 2 (n + s) ≤ Nat.log 2 n + 1 := by
      calc Nat.log 2 (n + s) ≤ Nat.log 2 (n * 2) := Nat.log_mono_right (by omega)
        _ = Nat.log 2 n + 1 := Nat.log_mul_base (by norm_num) (by omega)
    have h3 := hn₀ n (le_trans (le_max_left _ _) hn)
    have : n ≤ (34 * (Nat.log 2 n + 4)) ^ (d - 1) :=
      le_trans hpre (Nat.pow_le_pow_left (by omega) _)
    omega

/-! ## The assembly -/

theorem assembly : Assembly := by
  intro hB hI ⟨c, hc⟩
  refine ⟨c, fun d hd => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hc d hd
  refine ⟨n₀, fun n hn C hops hdep hdec => ?_⟩
  obtain ⟨G, lev, f, hcard, hG, hf, hp⟩ := hB d n C hops hdep hdec
  have hlt : G.card < 2 ^ (Nat.log 2 (2 * (n + C.size) + 2) + 1) :=
    lt_of_le_of_lt hcard (Nat.lt_pow_succ_log_self (by norm_num) _)
  have := hI (Fin n) (d + 1) (Nat.log 2 (2 * (n + C.size) + 2) + 1) G lev f (by omega) (by omega)
    hG hlt hf hp
  have hd2 : d + 1 - 3 = d - 2 := by omega
  rw [hd2, Fintype.card_fin] at this
  exact hn₀ n hn C.size this

end PEqualNP.CircuitLowerBounds.Switching.Plan
