import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_9427_417
    (safe :
      let I : Finset ℕ := ([2147418115, 663661903884, 34144976944, 728266375360, 21653750532,
        103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] :
        List ℕ).toFinset
      let M : ℕ := 1099511562240
      let R : ℕ := 1099511627775
      ∀ (d e : ℕ) (D B : Finset ℕ),
        let X := insert (d ||| 1099511627776) (insert (e ||| 2199023255552) I)
        let P := D.filter (· ≤ R)
        let A := Finset.image₂ (· &&& ·) P P
        let F := Finset.image₂ (fun a b : ℕ =>
          (a &&& b &&& R) |||
          (if (a ||| b) &&& 3298534883328 = 3298534883328 then 1099511627776 else 0)) D D
        d ∈ A → e ∈ A → d &&& M ≠ 0 → e &&& M ≠ 0 → d &&& e &&& M = 0 →
        (∀ w ∈ D \ X, ∃ a ∈ D, ∃ b ∈ D, a < w ∧ b < w ∧ w = a ||| b) →
        (∀ w ∈ D, w < 4398046511104 ∧ w ≠ 0 ∧
          ∀ r < 42, w.testBit r = true → ∃ a ∈ D ∩ X, a ||| w = w ∧ a.testBit r = true) →
        1 ≤ (D \ X).card → (D \ X).card + 2 * B.card ≤ 20 → B.card ≤ 9 →
        (∀ r ∈ insert 40 (Finset.range 16), ∃ b ∈ B, b.testBit r = true) →
        (∀ b ∈ B, b ∈ F ∧ b &&& M = 0 ∧
          ∀ c ∈ F, c &&& M = 0 → b ||| c = c → c = b) →
        (∀ b ∈ B, ∃ r < 41, b.testBit r = true ∧ ∀ c ∈ B, c.testBit r = true → c = b) →
        False)
    (overlapLow :
      let I : Finset ℕ := ([2147418115, 663661903884, 34144976944, 728266375360, 21653750532,
        103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] :
        List ℕ).toFinset
      let M : ℕ := 1099511562240
      let R : ℕ := 1099511627775
      ∀ (d e : ℕ) (D B : Finset ℕ),
        let X := insert (d ||| 1099511627776) (insert (e ||| 2199023255552) I)
        let P := D.filter (· ≤ R)
        let A := Finset.image₂ (· &&& ·) P P
        let F := Finset.image₂ (fun a b : ℕ =>
          (a &&& b &&& R) |||
          (if (a ||| b) &&& 3298534883328 = 3298534883328 then 1099511627776 else 0)) D D
        d ∈ A → e ∈ A → d &&& M ≠ 0 → e &&& M ≠ 0 → d &&& e &&& M ≠ 0 →
        (∃ v ∈ I, (d ||| e) &&& v &&& M = 0) →
        (∃ w ∈ D \ X, w &&& 3298534883328 = 3298534883328) →
        (∀ w ∈ D \ X, ∃ a ∈ D, ∃ b ∈ D, a < w ∧ b < w ∧ w = a ||| b) →
        (∀ w ∈ D, w < 4398046511104 ∧ w ≠ 0 ∧
          ∀ r < 42, w.testBit r = true → ∃ a ∈ D ∩ X, a ||| w = w ∧ a.testBit r = true) →
        1 ≤ (D \ X).card → (D \ X).card + 2 * B.card ≤ 20 → B.card ≤ 6 →
        (∀ r ∈ insert 40 (Finset.range 16), ∃ b ∈ B, b.testBit r = true) →
        (∀ b ∈ B, b ∈ F ∧ b &&& M = 0 ∧
          ∀ c ∈ F, c &&& M = 0 → b ||| c = c → c = b) →
        (∀ b ∈ B, ∃ r < 41, b.testBit r = true ∧ ∀ c ∈ B, c.testBit r = true → c = b) →
        False)
    (overlapHigh :
      let I : Finset ℕ := ([2147418115, 663661903884, 34144976944, 728266375360, 21653750532,
        103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] :
        List ℕ).toFinset
      let M : ℕ := 1099511562240
      let R : ℕ := 1099511627775
      ∀ (d e : ℕ) (D B : Finset ℕ),
        let X := insert (d ||| 1099511627776) (insert (e ||| 2199023255552) I)
        let P := D.filter (· ≤ R)
        let A := Finset.image₂ (· &&& ·) P P
        let F := Finset.image₂ (fun a b : ℕ =>
          (a &&& b &&& R) |||
          (if (a ||| b) &&& 3298534883328 = 3298534883328 then 1099511627776 else 0)) D D
        d ∈ A → e ∈ A → d &&& M ≠ 0 → e &&& M ≠ 0 → d &&& e &&& M ≠ 0 →
        (∃ v ∈ I, (d ||| e) &&& v &&& M = 0) →
        (∃ w ∈ D \ X, w &&& 3298534883328 = 3298534883328) →
        (∀ w ∈ D \ X, ∃ a ∈ D, ∃ b ∈ D, a < w ∧ b < w ∧ w = a ||| b) →
        (∀ w ∈ D, w < 4398046511104 ∧ w ≠ 0 ∧
          ∀ r < 42, w.testBit r = true → ∃ a ∈ D ∩ X, a ||| w = w ∧ a.testBit r = true) →
        1 ≤ (D \ X).card → (D \ X).card + 2 * B.card ≤ 20 → 7 ≤ B.card → B.card ≤ 9 →
        (∀ r ∈ insert 40 (Finset.range 16), ∃ b ∈ B, b.testBit r = true) →
        (∀ b ∈ B, b ∈ F ∧ b &&& M = 0 ∧
          ∀ c ∈ F, c &&& M = 0 → b ||| c = c → c = b) →
        (∀ b ∈ B, ∃ r < 41, b.testBit r = true ∧ ∀ c ∈ B, c.testBit r = true → c = b) →
        False)
    : have x1 : Finset ℕ := Finset.range (40 : ℕ); have x2 : List ℕ := [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)]; have x3 : Finset (Finset ℕ) := Finset.image (fun (x3 : ℕ) => {x4 ∈ x1 | x3.testBit x4 = Bool.true}) x2.toFinset; have x4 : Finset ℕ := Insert.insert (40 : ℕ) (Finset.range (16 : ℕ)); ∀ (x5 x6 : Finset ℕ) (x7 x8 : Finset (Finset ℕ)),   have x9 : Finset (Finset ℕ) := Insert.insert (Insert.insert (40 : ℕ) x5) (Insert.insert (Insert.insert (41 : ℕ) x6) x3);   have x10 : Finset (Finset ℕ) := {x10 ∈ x7 | x10 ⊆ x1};   have x11 : Finset (Finset ℕ) := Finset.image₂ (fun (x11 x12 : Finset ℕ) => x11 ∩ x12) x10 x10;   have x12 : Finset ℕ → Finset ℕ → Finset ℕ := fun (x12 x13 : Finset ℕ) => x12 ∩ x13 ∩ x1 ∪ if {(40 : ℕ), (41 : ℕ)} ⊆ x12 ∪ x13 then {(40 : ℕ)} else ∅;   have x13 : Finset (Finset ℕ) := Finset.image₂ x12 x7 x7;   x5 ∈ x11 → x6 ∈ x11 → ¬x5 ⊆ Finset.range (16 : ℕ) → ¬x6 ⊆ Finset.range (16 : ℕ) → (∀ x18 ∈ x7 \ x9, ∃ x20 ∈ x7, ∃ x21 ∈ x7, x20 ⊂ x18 ∧ x21 ⊂ x18 ∧ x18 = x20 ∪ x21) → x7 ⊆ (Finset.range (42 : ℕ)).powerset → (1 : ℕ) ≤ (x7 \ x9).card → (x7 \ x9).card ≤ (18 : ℕ) → x8.card ≤ (9 : ℕ) → x8.biUnion id = x4 → (∀ x24 ∈ x8, x24 ∈ x13 ∧ x24 ⊆ x4 ∧ ∀ x26 ∈ x13, x26 ⊆ x4 → x24 ⊆ x26 → x26 = x24) → (∀ x25 ∈ x8, ∃ x27 ∈ x25, ∀ x28 ∈ x8, x27 ∈ x28 → x28 = x25) → (21 : ℕ) ≤ (x7 \ x9).card + (2 : ℕ) * x8.card := by
  dsimp only
  intro d e D B hd he hdn hen build hDsub h1 h18 hB9 hBcov hBmax hBpriv
  by_contra! hlt
  have hsum : (D \ insert (insert 40 d) (insert (insert 41 e)
      (([2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128,
        26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] : List ℕ).toFinset.image
        (fun v => (Finset.range 40).filter (fun i => v.testBit i = true))))).card + 2 * B.card ≤ 20 := by
    omega
  clear h18 hlt
  let V : List ℕ := [2147418115, 663661903884, 34144976944, 728266375360, 21653750532,
    103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146]
  let R : Finset ℕ := Finset.range 40
  let I : Finset (Finset ℕ) := V.toFinset.image (fun v => R.filter (fun i => v.testBit i = true))
  let T : Finset ℕ := insert 40 (Finset.range 16)
  let X : Finset (Finset ℕ) := insert (insert 40 d) (insert (insert 41 e) I)
  let P : Finset (Finset ℕ) := D.filter (· ⊆ R)
  let A : Finset (Finset ℕ) := Finset.image₂ (· ∩ ·) P P
  let x12 : Finset ℕ → Finset ℕ → Finset ℕ :=
    fun a b => a ∩ b ∩ R ∪ if {40, 41} ⊆ a ∪ b then {40} else ∅
  let F : Finset (Finset ℕ) := Finset.image₂ x12 D D
  change d ∈ A at hd
  change e ∈ A at he
  change ∀ w ∈ D \ X, ∃ a ∈ D, ∃ b ∈ D, a ⊂ w ∧ b ⊂ w ∧ w = a ∪ b at build
  change 1 ≤ (D \ X).card at h1
  change (D \ X).card + 2 * B.card ≤ 20 at hsum
  change B.biUnion id = T at hBcov
  change ∀ b ∈ B, b ∈ F ∧ b ⊆ T ∧ ∀ c ∈ F, c ⊆ T → b ⊆ c → c = b at hBmax

  have hseeds : ∀ n : ℕ, ∀ w ∈ D, w.card ≤ n →
      ∀ r ∈ w, ∃ a ∈ D ∩ X, a ⊆ w ∧ r ∈ a := by
    refine Nat.rec ?_ ?_
    · intro w hw hc r hr
      change w.card ≤ 0 at hc
      have hne : w.Nonempty := ⟨r, hr⟩
      have hpos := Finset.card_pos.mpr hne
      omega
    · intro n ih w hw hc r hr
      by_cases hwx : w ∈ X
      · exact ⟨w, Finset.mem_inter.mpr ⟨hw, hwx⟩, Finset.Subset.rfl, hr⟩
      · obtain ⟨a, ha, b, hb, haw, hbw, hwab⟩ := build w (Finset.mem_sdiff.mpr ⟨hw, hwx⟩)
        have hca : a.card ≤ n := by
          have := Finset.card_lt_card haw; omega
        have hcb : b.card ≤ n := by
          have := Finset.card_lt_card hbw; omega
        rw [hwab] at hr
        rcases Finset.mem_union.mp hr with hra | hrb
        · obtain ⟨s, hs, hsa, hrs⟩ := ih a ha hca r hra
          exact ⟨s, hs, hsa.trans haw.1, hrs⟩
        · obtain ⟨s, hs, hsb, hrs⟩ := ih b hb hcb r hrb
          exact ⟨s, hs, hsb.trans hbw.1, hrs⟩

  have hV_nonempty : ∀ v ∈ V, ∃ i < 40, v.testBit i = true := by decide +kernel
  have hV_lt : ∀ v ∈ V, v < 2 ^ 40 := by decide +kernel
  have hD_nonempty : ∀ n : ℕ, ∀ w ∈ D, w.card ≤ n → w.Nonempty := by
    refine Nat.rec ?_ ?_
    · intro w hw hc
      by_cases hwx : w ∈ X
      · simp only [X, Finset.mem_insert] at hwx
        rcases hwx with rfl | rfl | hwI
        · exact ⟨40, Finset.mem_insert_self _ _⟩
        · exact ⟨41, Finset.mem_insert_self _ _⟩
        · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwI
          obtain ⟨i, hi, hbit⟩ := hV_nonempty v (List.mem_toFinset.mp hv)
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hbit⟩⟩
      · obtain ⟨a, _, _, _, haw, _, _⟩ := build w (Finset.mem_sdiff.mpr ⟨hw, hwx⟩)
        change w.card ≤ 0 at hc
        have := Finset.card_lt_card haw
        omega
    · intro n ih w hw hc
      by_cases hwx : w ∈ X
      · simp only [X, Finset.mem_insert] at hwx
        rcases hwx with rfl | rfl | hwI
        · exact ⟨40, Finset.mem_insert_self _ _⟩
        · exact ⟨41, Finset.mem_insert_self _ _⟩
        · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwI
          obtain ⟨i, hi, hbit⟩ := hV_nonempty v (List.mem_toFinset.mp hv)
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hbit⟩⟩
      · obtain ⟨a, ha, _, _, haw, _, _⟩ := build w (Finset.mem_sdiff.mpr ⟨hw, hwx⟩)
        have hca : a.card ≤ n := by have := Finset.card_lt_card haw; omega
        exact (ih a ha hca).mono haw.1

  have hdR : d ⊆ R := by
    obtain ⟨p, hp, q, _, rfl⟩ := Finset.mem_image₂.mp hd
    exact Finset.inter_subset_left.trans (Finset.mem_filter.mp hp).2
  have heR : e ⊆ R := by
    obtain ⟨p, hp, q, _, rfl⟩ := Finset.mem_image₂.mp he
    exact Finset.inter_subset_left.trans (Finset.mem_filter.mp hp).2
  have hIR : ∀ s ∈ I, s ⊆ R := by
    intro s hs
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.filter_subset _ _
  have h40_sub : ∀ w ∈ D, 40 ∈ w → d ⊆ w := by
    intro w hw h40
    obtain ⟨s, hs, hsw, h40s⟩ := hseeds w.card w hw le_rfl 40 h40
    have hsx := (Finset.mem_inter.mp hs).2
    simp only [X, Finset.mem_insert] at hsx
    rcases hsx with rfl | rfl | hsI
    · exact (Finset.subset_insert 40 d).trans hsw
    · exfalso
      rcases Finset.mem_insert.mp h40s with h | h
      · omega
      · have := Finset.mem_range.mp (heR h); omega
    · exfalso
      have := Finset.mem_range.mp (hIR s hsI h40s); omega
  have h41_sub : ∀ w ∈ D, 41 ∈ w → e ⊆ w := by
    intro w hw h41
    obtain ⟨s, hs, hsw, h41s⟩ := hseeds w.card w hw le_rfl 41 h41
    have hsx := (Finset.mem_inter.mp hs).2
    simp only [X, Finset.mem_insert] at hsx
    rcases hsx with rfl | rfl | hsI
    · exfalso
      rcases Finset.mem_insert.mp h41s with h | h
      · omega
      · have := Finset.mem_range.mp (hdR h); omega
    · exact (Finset.subset_insert 41 e).trans hsw
    · exfalso
      have := Finset.mem_range.mp (hIR s hsI h41s); omega

  let enc : Finset ℕ → ℕ := fun s => s.sum (fun k => 2 ^ k)
  have htestBit_add_pow : ∀ (a n i : ℕ), n.testBit a = false →
      (2 ^ a + n).testBit i = (decide (a = i) || n.testBit i) := by
    intro a n i hna
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    rw [Nat.testBit_eq_decide_div_mod_eq] at hna
    have hna0 : (n / 2 ^ a) % 2 = 0 := by
      have : ¬ (n / 2 ^ a) % 2 = 1 := by simpa using hna
      omega
    rcases lt_trichotomy i a with hia | rfl | hai
    · have hpow : 2 ^ a = 2 ^ i * (2 * 2 ^ (a - i - 1)) := by
        rw [← Nat.pow_succ', ← Nat.pow_add]
        congr 1; omega
      rw [hpow, Nat.mul_add_div (Nat.two_pow_pos i)]
      have hne : a ≠ i := by omega
      simp [hne, Nat.add_mod]
    · have hdiv : (2 ^ i + n) / 2 ^ i = 1 + n / 2 ^ i := by
        rw [Nat.add_div_left n (Nat.two_pow_pos i)]; omega
      rw [hdiv]
      have h1 : (1 + n / 2 ^ i) % 2 = 1 := by omega
      simp [h1]
    · have hmod_lt : 2 ^ a + n % 2 ^ i < 2 ^ i := by
        have hdiv_pow : 2 ^ (a + 1) ∣ 2 ^ i := Nat.pow_dvd_pow 2 (by omega)
        obtain ⟨m, hm⟩ := hdiv_pow
        have hlt_i : n % 2 ^ i < 2 ^ i := Nat.mod_lt n (Nat.two_pow_pos i)
        have hbit_mod : ((n % 2 ^ i) / 2 ^ a) % 2 = 0 := by
          obtain ⟨t, ht⟩ := Nat.pow_dvd_pow 2 (show a + 1 ≤ i by omega)
          have h1 : n = 2 ^ a * (2 * (t * (n / 2 ^ i))) + n % 2 ^ i := by
            calc n = 2 ^ i * (n / 2 ^ i) + n % 2 ^ i := (Nat.div_add_mod n (2 ^ i)).symm
              _ = 2 ^ (a + 1) * t * (n / 2 ^ i) + n % 2 ^ i := by rw [ht]
              _ = 2 ^ a * (2 * (t * (n / 2 ^ i))) + n % 2 ^ i := by rw [Nat.pow_succ]; ring
          have h2 : n / 2 ^ a = 2 * (t * (n / 2 ^ i)) + (n % 2 ^ i) / 2 ^ a := by
            conv_lhs => rw [h1]
            rw [Nat.mul_add_div (Nat.two_pow_pos a)]
          rw [h2] at hna0
          omega
        set r := n % 2 ^ i
        have hq : r / 2 ^ (a + 1) < m := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (a + 1))]
          rw [mul_comm, ← hm]
          exact hlt_i
        have hrem : r % 2 ^ (a + 1) < 2 ^ a := by
          have h3 : r % 2 ^ (a + 1) / 2 ^ a = (r / 2 ^ a) % 2 := by
            rw [Nat.pow_succ, Nat.mod_mul_right_div_self]
          have h4 : r % 2 ^ (a + 1) / 2 ^ a = 0 := by rw [h3, hbit_mod]
          exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos a)).mp h4
        have hr_eq : r = 2 ^ (a + 1) * (r / 2 ^ (a + 1)) + r % 2 ^ (a + 1) :=
          (Nat.div_add_mod r (2 ^ (a + 1))).symm
        have hpow2 : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ']
        have hstep : 2 ^ a + r < 2 ^ (a + 1) * (r / 2 ^ (a + 1) + 1) := by
          rw [mul_add, mul_one]
          omega
        have hle : 2 ^ (a + 1) * (r / 2 ^ (a + 1) + 1) ≤ 2 ^ (a + 1) * m :=
          Nat.mul_le_mul_left _ hq
        omega
      have hdiv : (2 ^ a + n) / 2 ^ i = n / 2 ^ i := by
        have h1 : 2 ^ a + n = 2 ^ i * (n / 2 ^ i) + (2 ^ a + n % 2 ^ i) := by
          have := Nat.div_add_mod n (2 ^ i); omega
        rw [h1, Nat.mul_add_div (Nat.two_pow_pos i), Nat.div_eq_of_lt hmod_lt, Nat.add_zero]
      rw [hdiv]
      have hne : a ≠ i := by omega
      simp [hne]
  have enc_testBit : ∀ (s : Finset ℕ) (i : ℕ), (enc s).testBit i = decide (i ∈ s) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro i; simp [enc]
    · intro a s ha ih i
      change (Finset.sum (insert a s) (fun k => 2 ^ k)).testBit i = _
      rw [Finset.sum_insert ha]
      have hna : (enc s).testBit a = false := by rw [ih a]; simpa using ha
      change (2 ^ a + enc s).testBit i = _
      rw [htestBit_add_pow a (enc s) i hna, ih i]
      by_cases h : i = a
      · subst h; simp
      · simp [h, Ne.symm h]
  have enc_inj : Function.Injective enc := by
    intro s t hst
    ext i
    have h := congrArg (fun x => x.testBit i) hst
    simpa [enc_testBit] using h
  have enc_union : ∀ s t : Finset ℕ, enc (s ∪ t) = enc s ||| enc t := by
    intro s t
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_or, enc_testBit, enc_testBit, enc_testBit]
    by_cases hs : k ∈ s <;> by_cases ht : k ∈ t <;> simp [hs, ht]
  have enc_inter : ∀ s t : Finset ℕ, enc (s ∩ t) = enc s &&& enc t := by
    intro s t
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, enc_testBit, enc_testBit, enc_testBit]
    by_cases hs : k ∈ s <;> by_cases ht : k ∈ t <;> simp [hs, ht]
  have enc_subset_iff : ∀ s t : Finset ℕ, s ⊆ t ↔ enc s ||| enc t = enc t := by
    intro s t
    rw [← enc_union, enc_inj.eq_iff, Finset.union_eq_right]
  have enc_ssubset : ∀ s t : Finset ℕ, s ⊂ t → enc s < enc t := by
    intro s t hst
    have hsum_st : enc t = enc s + enc (t \ s) := by
      dsimp only [enc]
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hst.1]
    obtain ⟨k, hk⟩ := Finset.exists_of_ssubset hst
    have hk_mem : k ∈ t \ s := Finset.mem_sdiff.mpr ⟨hk.1, hk.2⟩
    have hpos : 0 < enc (t \ s) := by
      calc 0 < 2 ^ k := Nat.two_pow_pos k
        _ ≤ enc (t \ s) := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk_mem
    omega
  have enc_lt_pow : ∀ (s : Finset ℕ) (n : ℕ), s ⊆ Finset.range n → enc s < 2 ^ n := by
    intro s n hs
    have hle : enc s ≤ enc (Finset.range n) :=
      Finset.sum_le_sum_of_subset hs
    have hgeom : ∀ m : ℕ, enc (Finset.range m) + 1 = 2 ^ m := by
      refine Nat.rec ?_ ?_
      · simp [enc]
      · intro m ihm
        change (Finset.range (m + 1)).sum (fun k => 2 ^ k) + 1 = 2 ^ (m + 1)
        rw [Finset.sum_range_succ, Nat.pow_succ]
        dsimp only [enc] at ihm
        omega
    have := hgeom n
    omega
  have enc_le_Rm_iff : ∀ s : Finset ℕ, enc s ≤ 1099511627775 ↔ s ⊆ R := by
    intro s
    constructor
    · intro hle k hk
      have hpow : 2 ^ k ≤ enc s := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk
      have hlt : 2 ^ k < 2 ^ 40 := by omega
      exact Finset.mem_range.mpr ((Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hlt)
    · intro hs
      have hlt := enc_lt_pow s 40 hs
      omega
  have enc_filter_eq : ∀ v : ℕ, v < 2 ^ 40 →
      enc (R.filter (fun i => v.testBit i = true)) = v := by
    intro v hv
    apply Nat.eq_of_testBit_eq
    intro k
    rw [enc_testBit]
    by_cases hk : k < 40
    · simp [R, hk]
    · have hfalse : v.testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [R, hk, hfalse]

  let M : ℕ := 1099511562240
  let Rm : ℕ := 1099511627775
  let b40 : ℕ := 1099511627776
  let b41 : ℕ := 2199023255552
  let b401 : ℕ := 3298534883328
  have hRm_bit : ∀ k : ℕ, Rm.testBit k = decide (k < 40) := by
    intro k
    have hRm : Rm = 2 ^ 40 - 1 := by decide
    rw [hRm, Nat.testBit_two_pow_sub_one]
  have hM_bit : ∀ k : ℕ, M.testBit k = decide (16 ≤ k ∧ k < 40) := by
    intro k
    have hM : M = (2 ^ 24 - 1) <<< 16 := by decide
    rw [hM, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases h1 : 16 ≤ k <;> by_cases h2 : k < 40 <;> simp [h1, h2] <;> omega
  have hb40_bit : ∀ k : ℕ, b40.testBit k = decide (40 = k) := by
    intro k
    have : b40 = 2 ^ 40 := by decide
    rw [this, Nat.testBit_two_pow]
  have hb41_bit : ∀ k : ℕ, b41.testBit k = decide (41 = k) := by
    intro k
    have : b41 = 2 ^ 41 := by decide
    rw [this, Nat.testBit_two_pow]
  have hb401_bit : ∀ k : ℕ, b401.testBit k = decide (40 = k ∨ 41 = k) := by
    intro k
    have : b401 = b40 ||| b41 := by decide
    rw [this, Nat.testBit_or, hb40_bit, hb41_bit]
    by_cases h1 : 40 = k <;> by_cases h2 : 41 = k <;> simp [h1, h2]
  have hand_M_eq_zero : ∀ s : Finset ℕ, enc s &&& M = 0 ↔ ∀ k ∈ s, k < 16 ∨ 40 ≤ k := by
    intro s
    constructor
    · intro h k hk
      have hb := congrArg (fun x => x.testBit k) h
      rw [Nat.testBit_and, Nat.zero_testBit, enc_testBit, hM_bit] at hb
      simp only [hk, decide_true, Bool.true_and, decide_eq_false_iff_not, not_and] at hb
      omega
    · intro h
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.zero_testBit, enc_testBit, hM_bit]
      by_cases hk : k ∈ s
      · have := h k hk
        simp only [hk, decide_true, Bool.true_and, decide_eq_false_iff_not]
        omega
      · simp [hk]
  have hand_b401_eq : ∀ s : Finset ℕ, enc s &&& b401 = b401 ↔ {40, 41} ⊆ s := by
    intro s
    constructor
    · intro h
      have h40 := congrArg (fun x => x.testBit 40) h
      have h41 := congrArg (fun x => x.testBit 41) h
      rw [Nat.testBit_and, enc_testBit, hb401_bit] at h40 h41
      simp only [true_or, or_true, decide_true, Bool.and_true, decide_eq_true_eq] at h40 h41
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> assumption
    · intro h
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, enc_testBit, hb401_bit]
      by_cases h1 : 40 = k
      · subst h1
        have : 40 ∈ s := h (by simp)
        simp [this]
      · by_cases h2 : 41 = k
        · subst h2
          have : 41 ∈ s := h (by simp)
          simp [this]
        · simp [h1, h2]

  let Im : Finset ℕ := V.toFinset
  let Dm : Finset ℕ := D.image enc
  let Bm : Finset ℕ := B.image enc
  let dm : ℕ := enc d
  let em : ℕ := enc e
  let Xm : Finset ℕ := insert (dm ||| b40) (insert (em ||| b41) Im)
  let Pm : Finset ℕ := Dm.filter (· ≤ Rm)
  let Am : Finset ℕ := Finset.image₂ (· &&& ·) Pm Pm
  let fm : ℕ → ℕ → ℕ := fun a b =>
    (a &&& b &&& Rm) ||| (if (a ||| b) &&& b401 = b401 then b40 else 0)
  let Fm : Finset ℕ := Finset.image₂ fm Dm Dm
  have enc_I_eq : I.image enc = Im := by
    ext x
    simp only [I, Finset.mem_image]
    constructor
    · rintro ⟨s, ⟨v, hv, rfl⟩, rfl⟩
      rw [enc_filter_eq v (hV_lt v (List.mem_toFinset.mp hv))]
      exact hv
    · intro hx
      refine ⟨R.filter (fun i => x.testBit i = true), ⟨x, hx, rfl⟩, ?_⟩
      exact enc_filter_eq x (hV_lt x (List.mem_toFinset.mp hx))
  have enc_ins40 : enc (insert 40 d) = dm ||| b40 := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_or, enc_testBit, enc_testBit, hb40_bit]
    by_cases h : k = 40
    · subst h; simp
    · simp [h, Ne.symm h]
  have enc_ins41 : enc (insert 41 e) = em ||| b41 := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_or, enc_testBit, enc_testBit, hb41_bit]
    by_cases h : k = 41
    · subst h; simp
    · simp [h, Ne.symm h]
  have enc_X_eq : X.image enc = Xm := by
    simp only [X, Xm, Finset.image_insert, enc_ins40, enc_ins41, enc_I_eq]
  have enc_P_eq : P.image enc = Pm := by
    ext x
    simp only [P, Pm, Dm, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨s, ⟨hsD, hsR⟩, rfl⟩
      exact ⟨⟨s, hsD, rfl⟩, (enc_le_Rm_iff s).mpr hsR⟩
    · rintro ⟨⟨s, hsD, rfl⟩, hle⟩
      exact ⟨s, ⟨hsD, (enc_le_Rm_iff s).mp hle⟩, rfl⟩
  have enc_A_eq : A.image enc = Am := by
    ext x
    simp only [A, Am, ← enc_P_eq, Finset.mem_image, Finset.mem_image₂]
    constructor
    · rintro ⟨s, ⟨p, hp, q, hq, rfl⟩, rfl⟩
      exact ⟨enc p, ⟨p, hp, rfl⟩, enc q, ⟨q, hq, rfl⟩, (enc_inter p q).symm⟩
    · rintro ⟨u, ⟨p, hp, rfl⟩, v, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨p ∩ q, ⟨p, hp, q, hq, rfl⟩, enc_inter p q⟩
  have enc_x12 : ∀ a b : Finset ℕ, enc (x12 a b) = fm (enc a) (enc b) := by
    intro a b
    dsimp only [x12, fm]
    rw [← enc_union a b]
    by_cases h : {40, 41} ⊆ a ∪ b
    · have hm : enc (a ∪ b) &&& b401 = b401 := (hand_b401_eq (a ∪ b)).mpr h
      simp only [h, hm, ↓reduceIte]
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, enc_testBit, enc_testBit, enc_testBit, hRm_bit, hb40_bit]
      by_cases hk40 : k = 40
      · subst hk40; simp [R]
      · simp [R, hk40, Ne.symm hk40, Bool.and_assoc]
    · have hm : ¬ (enc (a ∪ b) &&& b401 = b401) := fun h' => h ((hand_b401_eq (a ∪ b)).mp h')
      simp only [h, hm, ↓reduceIte]
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, enc_testBit, enc_testBit, enc_testBit, hRm_bit]
      simp [R, Bool.and_assoc]
  have enc_F_eq : F.image enc = Fm := by
    ext x
    simp only [F, Fm, Dm, Finset.mem_image, Finset.mem_image₂]
    constructor
    · rintro ⟨s, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨enc a, ⟨a, ha, rfl⟩, enc b, ⟨b, hb, rfl⟩, (enc_x12 a b).symm⟩
    · rintro ⟨u, ⟨a, ha, rfl⟩, v, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨x12 a b, ⟨a, ha, b, hb, rfl⟩, enc_x12 a b⟩
  have enc_sdiff_eq : (D \ X).image enc = Dm \ Xm := by
    ext x
    simp only [Dm, ← enc_X_eq, Finset.mem_image, Finset.mem_sdiff]
    constructor
    · rintro ⟨s, ⟨hsD, hsX⟩, rfl⟩
      refine ⟨⟨s, hsD, rfl⟩, ?_⟩
      rintro ⟨t, htX, hts⟩
      exact hsX (enc_inj hts ▸ htX)
    · rintro ⟨⟨s, hsD, rfl⟩, hnot⟩
      exact ⟨s, ⟨hsD, fun hsX => hnot ⟨s, hsX, rfl⟩⟩, rfl⟩
  have enc_inter_DX : (D ∩ X).image enc = Dm ∩ Xm := by
    ext x
    simp only [Dm, ← enc_X_eq, Finset.mem_image, Finset.mem_inter]
    constructor
    · rintro ⟨s, ⟨hsD, hsX⟩, rfl⟩
      exact ⟨⟨s, hsD, rfl⟩, ⟨s, hsX, rfl⟩⟩
    · rintro ⟨⟨s, hsD, rfl⟩, ⟨t, htX, hts⟩⟩
      exact ⟨s, ⟨hsD, enc_inj hts ▸ htX⟩, rfl⟩

  have hdmA : dm ∈ Am := by rw [← enc_A_eq]; exact Finset.mem_image_of_mem enc hd
  have hemA : em ∈ Am := by rw [← enc_A_eq]; exact Finset.mem_image_of_mem enc he
  have hdmM : dm &&& M ≠ 0 := by
    intro h0
    apply hdn
    intro k hk
    have hk40 := Finset.mem_range.mp (hdR hk)
    have := (hand_M_eq_zero d).mp h0 k hk
    exact Finset.mem_range.mpr (by omega)
  have hemM : em &&& M ≠ 0 := by
    intro h0
    apply hen
    intro k hk
    have hk40 := Finset.mem_range.mp (heR hk)
    have := (hand_M_eq_zero e).mp h0 k hk
    exact Finset.mem_range.mpr (by omega)
  have hbuild_m : ∀ w ∈ Dm \ Xm, ∃ a ∈ Dm, ∃ b ∈ Dm, a < w ∧ b < w ∧ w = a ||| b := by
    intro w hw
    rw [← enc_sdiff_eq] at hw
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨a, ha, b, hb, has, hbs, hsab⟩ := build s hs
    exact ⟨enc a, Finset.mem_image_of_mem enc ha, enc b, Finset.mem_image_of_mem enc hb,
      enc_ssubset a s has, enc_ssubset b s hbs, by rw [hsab, enc_union]⟩
  have hD_m : ∀ w ∈ Dm, w < 4398046511104 ∧ w ≠ 0 ∧
      ∀ r < 42, w.testBit r = true → ∃ a ∈ Dm ∩ Xm, a ||| w = w ∧ a.testBit r = true := by
    intro w hw
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
    have hs42 : s ⊆ Finset.range 42 := Finset.mem_powerset.mp (hDsub hs)
    refine ⟨?_, ?_, ?_⟩
    · have := enc_lt_pow s 42 hs42; omega
    · obtain ⟨k, hk⟩ := hD_nonempty s.card s hs le_rfl
      have hpos : 0 < enc s :=
        lt_of_lt_of_le (Nat.two_pow_pos k) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk)
      omega
    · intro r _ hbit
      have hrs : r ∈ s := by simpa [enc_testBit] using hbit
      obtain ⟨t, ht, hts, hrt⟩ := hseeds s.card s hs le_rfl r hrs
      refine ⟨enc t, ?_, (enc_subset_iff t s).mp hts, by simp [enc_testBit, hrt]⟩
      rw [← enc_inter_DX]
      exact Finset.mem_image_of_mem enc ht
  have hcard_sdiff : (Dm \ Xm).card = (D \ X).card := by
    rw [← enc_sdiff_eq, Finset.card_image_of_injective _ enc_inj]
  have hcard_B : Bm.card = B.card := Finset.card_image_of_injective _ enc_inj
  have h1_m : 1 ≤ (Dm \ Xm).card := by omega
  have hsum_m : (Dm \ Xm).card + 2 * Bm.card ≤ 20 := by omega
  have hB9_m : Bm.card ≤ 9 := by omega
  have hBcov_m : ∀ r ∈ insert 40 (Finset.range 16), ∃ b ∈ Bm, b.testBit r = true := by
    intro r hr
    have hr' : r ∈ B.biUnion id := by rw [hBcov]; exact hr
    obtain ⟨s, hsB, hrs⟩ := Finset.mem_biUnion.mp hr'
    change r ∈ s at hrs
    exact ⟨enc s, Finset.mem_image_of_mem enc hsB, by simp [enc_testBit, hrs]⟩
  have hBmax_m : ∀ b ∈ Bm, b ∈ Fm ∧ b &&& M = 0 ∧
      ∀ c ∈ Fm, c &&& M = 0 → b ||| c = c → c = b := by
    intro b hb
    obtain ⟨s, hsB, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hsF, hsT, hmax⟩ := hBmax s hsB
    refine ⟨?_, ?_, ?_⟩
    · rw [← enc_F_eq]; exact Finset.mem_image_of_mem enc hsF
    · rw [hand_M_eq_zero]
      intro k hk
      have hkT := hsT hk
      simp only [T, Finset.mem_insert, Finset.mem_range] at hkT
      omega
    · intro c hcF hcM hbc
      rw [← enc_F_eq] at hcF
      obtain ⟨t, htF, rfl⟩ := Finset.mem_image.mp hcF
      have htT : t ⊆ T := by
        obtain ⟨a, _, b', _, rfl⟩ := Finset.mem_image₂.mp htF
        intro k hk
        have hkm := (hand_M_eq_zero _).mp hcM k hk
        dsimp only [x12] at hk
        rcases Finset.mem_union.mp hk with h1 | h2
        · have hk40 := Finset.mem_range.mp (Finset.mem_inter.mp h1).2
          exact Finset.mem_insert_of_mem (Finset.mem_range.mpr (by omega))
        · by_cases hif : {40, 41} ⊆ a ∪ b'
          · simp only [hif, ↓reduceIte] at h2
            have hk40 : k = 40 := Finset.mem_singleton.mp h2
            subst hk40; exact Finset.mem_insert_self _ _
          · simp only [hif, ↓reduceIte] at h2
            exact (Finset.notMem_empty k h2).elim
      have hst : s ⊆ t := (enc_subset_iff s t).mpr hbc
      exact congrArg enc (hmax t htF htT hst)
  have hBpriv_m : ∀ b ∈ Bm, ∃ r < 41, b.testBit r = true ∧ ∀ c ∈ Bm, c.testBit r = true → c = b := by
    intro b hb
    obtain ⟨s, hsB, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨r, hrs, huniq⟩ := hBpriv s hsB
    have hrT := (hBmax s hsB).2.1 hrs
    have hr41 : r < 41 := by
      simp only [T, Finset.mem_insert, Finset.mem_range] at hrT; omega
    refine ⟨r, hr41, by simp [enc_testBit, hrs], ?_⟩
    intro c hcB hcr
    obtain ⟨t, htB, rfl⟩ := Finset.mem_image.mp hcB
    have hrt : r ∈ t := by simpa [enc_testBit] using hcr
    exact congrArg enc (huniq t htB hrt)
  by_cases hsafe : dm &&& em &&& M = 0
  · exact safe dm em Dm Bm hdmA hemA hdmM hemM hsafe hbuild_m hD_m
      h1_m hsum_m hB9_m hBcov_m hBmax_m hBpriv_m
  · have h40cov : 40 ∈ B.biUnion id := by rw [hBcov]; exact Finset.mem_insert_self _ _
    obtain ⟨b0, hb0B, h40b0⟩ := Finset.mem_biUnion.mp h40cov
    obtain ⟨hb0F, hb0T, _⟩ := hBmax b0 hb0B
    obtain ⟨a1, ha1D, a2, ha2D, hb0eq⟩ := Finset.mem_image₂.mp hb0F
    have h401_union : {40, 41} ⊆ a1 ∪ a2 := by
      rw [← hb0eq] at h40b0
      dsimp only [x12] at h40b0
      rcases Finset.mem_union.mp h40b0 with h1 | h2
      · exfalso; have := Finset.mem_range.mp (Finset.mem_inter.mp h1).2; omega
      · by_cases hif : {40, 41} ⊆ a1 ∪ a2
        · exact hif
        · simp only [hif, ↓reduceIte] at h2
          exact (Finset.notMem_empty 40 h2).elim
    have hclean : a1 ∩ a2 ∩ R ⊆ Finset.range 16 := by
      intro k hk
      have hk_in : k ∈ b0 := by
        rw [← hb0eq]; exact Finset.mem_union_left _ hk
      have hkT := hb0T hk_in
      have hk40 := Finset.mem_range.mp (Finset.mem_inter.mp hk).2
      simp only [T, Finset.mem_insert, Finset.mem_range] at hkT
      exact Finset.mem_range.mpr (by omega)
    have hnot_de_sub : ¬ (d ∩ e ⊆ Finset.range 16) := by
      intro hsub
      apply hsafe
      rw [← enc_inter d e, hand_M_eq_zero]
      intro k hk
      exact Or.inl (Finset.mem_range.mp (hsub hk))
    have hside : ({40, 41} ⊆ a1 ∧ 40 ∉ a2 ∧ 41 ∉ a2) ∨ ({40, 41} ⊆ a2 ∧ 40 ∉ a1 ∧ 41 ∉ a1) := by
      have h40u : 40 ∈ a1 ∨ 40 ∈ a2 := Finset.mem_union.mp (h401_union (by simp))
      have h41u : 41 ∈ a1 ∨ 41 ∈ a2 := Finset.mem_union.mp (h401_union (by simp))
      have hno40 : ¬ (40 ∈ a1 ∧ 40 ∈ a2) := by
        rintro ⟨h1, h2⟩
        apply hdn
        intro k hk
        exact hclean (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h40_sub a1 ha1D h1 hk, h40_sub a2 ha2D h2 hk⟩, hdR hk⟩)
      have hno41 : ¬ (41 ∈ a1 ∧ 41 ∈ a2) := by
        rintro ⟨h1, h2⟩
        apply hen
        intro k hk
        exact hclean (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h41_sub a1 ha1D h1 hk, h41_sub a2 ha2D h2 hk⟩, heR hk⟩)
      have hno4041 : ¬ (40 ∈ a1 ∧ 41 ∈ a2) := by
        rintro ⟨h1, h2⟩
        apply hnot_de_sub
        intro k hk
        obtain ⟨hkd, hke⟩ := Finset.mem_inter.mp hk
        exact hclean (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h40_sub a1 ha1D h1 hkd, h41_sub a2 ha2D h2 hke⟩, hdR hkd⟩)
      have hno4140 : ¬ (41 ∈ a1 ∧ 40 ∈ a2) := by
        rintro ⟨h1, h2⟩
        apply hnot_de_sub
        intro k hk
        obtain ⟨hkd, hke⟩ := Finset.mem_inter.mp hk
        exact hclean (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h41_sub a1 ha1D h1 hke, h40_sub a2 ha2D h2 hkd⟩, hdR hkd⟩)
      rcases h40u with h40a1 | h40a2 <;> rcases h41u with h41a1 | h41a2
      · left
        refine ⟨?_, fun h => hno40 ⟨h40a1, h⟩, fun h => hno4041 ⟨h40a1, h⟩⟩
        intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> assumption
      · exact (hno4041 ⟨h40a1, h41a2⟩).elim
      · exact (hno4140 ⟨h41a1, h40a2⟩).elim
      · right
        refine ⟨?_, fun h => hno40 ⟨h, h40a2⟩, fun h => hno41 ⟨h, h41a2⟩⟩
        intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> assumption
    have hex_both : ∃ w ∈ Dm \ Xm, w &&& b401 = b401 := by
      have extract : ∀ u ∈ D, {40, 41} ⊆ u → ∃ w ∈ Dm \ Xm, w &&& b401 = b401 := by
        intro u huD hu401
        have huNotX : u ∉ X := by
          intro huX
          simp only [X, Finset.mem_insert] at huX
          rcases huX with rfl | rfl | huI
          · have h41 : 41 ∈ insert 40 d := hu401 (by simp)
            rcases Finset.mem_insert.mp h41 with h | h
            · omega
            · have := Finset.mem_range.mp (hdR h); omega
          · have h40 : 40 ∈ insert 41 e := hu401 (by simp)
            rcases Finset.mem_insert.mp h40 with h | h
            · omega
            · have := Finset.mem_range.mp (heR h); omega
          · have h40 : 40 ∈ u := hu401 (by simp)
            have := Finset.mem_range.mp (hIR u huI h40); omega
        refine ⟨enc u, ?_, (hand_b401_eq u).mpr hu401⟩
        rw [← enc_sdiff_eq]
        exact Finset.mem_image_of_mem enc (Finset.mem_sdiff.mpr ⟨huD, huNotX⟩)
      rcases hside with ⟨h, _, _⟩ | ⟨h, _, _⟩
      · exact extract a1 ha1D h
      · exact extract a2 ha2D h
    have hex_v : ∃ v ∈ Im, (dm ||| em) &&& v &&& M = 0 := by
      have extractV : ∀ u p : Finset ℕ, u ∈ D → p ∈ D → {40, 41} ⊆ u →
          40 ∉ p → 41 ∉ p → u ∩ p ∩ R ⊆ Finset.range 16 →
          ∃ v ∈ Im, (dm ||| em) &&& v &&& M = 0 := by
        intro u p huD hpD hu401 h40p h41p hcl
        obtain ⟨r, hrp⟩ := hD_nonempty p.card p hpD le_rfl
        obtain ⟨s, hsDX, hsp, _⟩ := hseeds p.card p hpD le_rfl r hrp
        have hsX := (Finset.mem_inter.mp hsDX).2
        simp only [X, Finset.mem_insert] at hsX
        have hsI : s ∈ I := by
          rcases hsX with rfl | rfl | hsI
          · exact (h40p (hsp (Finset.mem_insert_self _ _))).elim
          · exact (h41p (hsp (Finset.mem_insert_self _ _))).elim
          · exact hsI
        refine ⟨enc s, ?_, ?_⟩
        · rw [← enc_I_eq]; exact Finset.mem_image_of_mem enc hsI
        · rw [← enc_union d e, ← enc_inter (d ∪ e) s, hand_M_eq_zero]
          intro k hk
          obtain ⟨hkde, hks⟩ := Finset.mem_inter.mp hk
          have hku : k ∈ u := by
            rcases Finset.mem_union.mp hkde with hkd | hke
            · exact h40_sub u huD (hu401 (by simp)) hkd
            · exact h41_sub u huD (hu401 (by simp)) hke
          have hkp : k ∈ p := hsp hks
          have hkR : k ∈ R := hIR s hsI hks
          exact Or.inl (Finset.mem_range.mp (hcl (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hku, hkp⟩, hkR⟩)))
      rcases hside with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact extractV a1 a2 ha1D ha2D h1 h2 h3 hclean
      · exact extractV a2 a1 ha2D ha1D h1 h2 h3 (by simpa [Finset.inter_comm] using hclean)
    by_cases hB6 : Bm.card ≤ 6
    · exact overlapLow dm em Dm Bm hdmA hemA hdmM hemM hsafe hex_v hex_both
        hbuild_m hD_m h1_m hsum_m hB6 hBcov_m hBmax_m hBpriv_m
    · have hB7 : 7 ≤ Bm.card := by omega
      exact overlapHigh dm em Dm Bm hdmA hemA hdmM hemM hsafe hex_v hex_both
        hbuild_m hD_m h1_m hsum_m hB7 hB9_m hBcov_m hBmax_m hBpriv_m
