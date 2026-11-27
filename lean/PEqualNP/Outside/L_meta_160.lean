import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_160 : ∀ (k : ℕ) (A : Fin k → Finset (Sym2 (Fin 6))) (B : Fin k → Finset (Finset (Fin 6)))
    (t : Fin k → Fin 6),
    (∀ i, ∀ e ∈ A i, e ∈ (SimpleGraph.fromRel (fun a b : Fin 6 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 5))).edgeFinset ∧ t i ∈ e) →
    (∀ i, ∀ I ∈ B i, t i ∉ I) →
    (∀ e ∈ (SimpleGraph.fromRel (fun a b : Fin 6 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 5))).edgeFinset,
      ∀ I : Finset (Fin 6), (∀ u ∈ I, ∀ w ∈ I, ¬ (SimpleGraph.fromRel (fun a b : Fin 6 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 5))).Adj u w) →
        ∃! i : Fin k, e ∈ A i ∧ I ∈ B i) →
    9 ≤ k := by
  intro k A B t hA hB hC
  have T : ∀ i e I, e ∈ A i → I ∈ B i → t i ∈ e ∧ t i ∉ I :=
    fun i e I h1 h2 => ⟨(hA i e h1).2, hB i I h2⟩
  -- the cells used: edges a = 01, b = 02, c = 12, p = 03, q = 14, r = 25,
  -- independent sets {0}, {1}, {2} and {3,4,5}
  obtain ⟨a0, ⟨a0A, a0B⟩, -⟩ := hC s(0,1) (by decide) {0} (by decide)
  obtain ⟨a1, ⟨a1A, a1B⟩, -⟩ := hC s(0,1) (by decide) {1} (by decide)
  obtain ⟨a2, -, a2U⟩ := hC s(0,1) (by decide) {2} (by decide)
  obtain ⟨aT, ⟨aTA, aTB⟩, aTU⟩ := hC s(0,1) (by decide) {3,4,5} (by decide)
  obtain ⟨b0, ⟨b0A, b0B⟩, -⟩ := hC s(0,2) (by decide) {0} (by decide)
  obtain ⟨b1, -, b1U⟩ := hC s(0,2) (by decide) {1} (by decide)
  obtain ⟨b2, ⟨b2A, b2B⟩, -⟩ := hC s(0,2) (by decide) {2} (by decide)
  obtain ⟨bT, ⟨bTA, bTB⟩, bTU⟩ := hC s(0,2) (by decide) {3,4,5} (by decide)
  obtain ⟨c0, -, c0U⟩ := hC s(1,2) (by decide) {0} (by decide)
  obtain ⟨c1, ⟨c1A, c1B⟩, -⟩ := hC s(1,2) (by decide) {1} (by decide)
  obtain ⟨c2, ⟨c2A, c2B⟩, -⟩ := hC s(1,2) (by decide) {2} (by decide)
  obtain ⟨cT, ⟨cTA, cTB⟩, cTU⟩ := hC s(1,2) (by decide) {3,4,5} (by decide)
  obtain ⟨p0, ⟨p0A, p0B⟩, -⟩ := hC s(0,3) (by decide) {0} (by decide)
  obtain ⟨pT, ⟨pTA, pTB⟩, -⟩ := hC s(0,3) (by decide) {3,4,5} (by decide)
  obtain ⟨q1, ⟨q1A, q1B⟩, -⟩ := hC s(1,4) (by decide) {1} (by decide)
  obtain ⟨qT, ⟨qTA, qTB⟩, -⟩ := hC s(1,4) (by decide) {3,4,5} (by decide)
  obtain ⟨r2, ⟨r2A, r2B⟩, -⟩ := hC s(2,5) (by decide) {2} (by decide)
  obtain ⟨rT, ⟨rTA, rTB⟩, -⟩ := hC s(2,5) (by decide) {3,4,5} (by decide)
  -- the labels forced by the cells
  have ta0 : t a0 = 1 := (by decide : ∀ x : Fin 6, x ∈ s(0,1) ∧ x ∉ ({0} : Finset (Fin 6)) → x = 1) _ (T _ _ _ a0A a0B)
  have ta1 : t a1 = 0 := (by decide : ∀ x : Fin 6, x ∈ s(0,1) ∧ x ∉ ({1} : Finset (Fin 6)) → x = 0) _ (T _ _ _ a1A a1B)
  have taT : t aT = 0 ∨ t aT = 1 := (by decide : ∀ x : Fin 6, x ∈ s(0,1) ∧ x ∉ ({3,4,5} : Finset (Fin 6)) → x = 0 ∨ x = 1) _ (T _ _ _ aTA aTB)
  have tb0 : t b0 = 2 := (by decide : ∀ x : Fin 6, x ∈ s(0,2) ∧ x ∉ ({0} : Finset (Fin 6)) → x = 2) _ (T _ _ _ b0A b0B)
  have tb2 : t b2 = 0 := (by decide : ∀ x : Fin 6, x ∈ s(0,2) ∧ x ∉ ({2} : Finset (Fin 6)) → x = 0) _ (T _ _ _ b2A b2B)
  have tbT : t bT = 0 ∨ t bT = 2 := (by decide : ∀ x : Fin 6, x ∈ s(0,2) ∧ x ∉ ({3,4,5} : Finset (Fin 6)) → x = 0 ∨ x = 2) _ (T _ _ _ bTA bTB)
  have tc1 : t c1 = 2 := (by decide : ∀ x : Fin 6, x ∈ s(1,2) ∧ x ∉ ({1} : Finset (Fin 6)) → x = 2) _ (T _ _ _ c1A c1B)
  have tc2 : t c2 = 1 := (by decide : ∀ x : Fin 6, x ∈ s(1,2) ∧ x ∉ ({2} : Finset (Fin 6)) → x = 1) _ (T _ _ _ c2A c2B)
  have tcT : t cT = 1 ∨ t cT = 2 := (by decide : ∀ x : Fin 6, x ∈ s(1,2) ∧ x ∉ ({3,4,5} : Finset (Fin 6)) → x = 1 ∨ x = 2) _ (T _ _ _ cTA cTB)
  have tp0 : t p0 = 3 := (by decide : ∀ x : Fin 6, x ∈ s(0,3) ∧ x ∉ ({0} : Finset (Fin 6)) → x = 3) _ (T _ _ _ p0A p0B)
  have tpT : t pT = 0 := (by decide : ∀ x : Fin 6, x ∈ s(0,3) ∧ x ∉ ({3,4,5} : Finset (Fin 6)) → x = 0) _ (T _ _ _ pTA pTB)
  have tq1 : t q1 = 4 := (by decide : ∀ x : Fin 6, x ∈ s(1,4) ∧ x ∉ ({1} : Finset (Fin 6)) → x = 4) _ (T _ _ _ q1A q1B)
  have tqT : t qT = 1 := (by decide : ∀ x : Fin 6, x ∈ s(1,4) ∧ x ∉ ({3,4,5} : Finset (Fin 6)) → x = 1) _ (T _ _ _ qTA qTB)
  have tr2 : t r2 = 5 := (by decide : ∀ x : Fin 6, x ∈ s(2,5) ∧ x ∉ ({2} : Finset (Fin 6)) → x = 5) _ (T _ _ _ r2A r2B)
  have trT : t rT = 2 := (by decide : ∀ x : Fin 6, x ∈ s(2,5) ∧ x ∉ ({3,4,5} : Finset (Fin 6)) → x = 2) _ (T _ _ _ rTA rTB)
  -- count the rectangles by label
  have hk : k = ∑ v : Fin 6, (Finset.univ.filter (fun i => t i = v)).card := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
    simp
  rw [Fin.sum_univ_six] at hk
  have one : ∀ i v, t i = v → 1 ≤ (Finset.univ.filter (fun i => t i = v)).card :=
    fun i v h => Finset.card_pos.2 ⟨i, by simp [h]⟩
  have two : ∀ i j v, t i = v → t j = v → i ≠ j →
      2 ≤ (Finset.univ.filter (fun i => t i = v)).card :=
    fun i j v hi hj hij => Finset.one_lt_card.2 ⟨i, by simp [hi], j, by simp [hj], hij⟩
  have three : ∀ i j l v, t i = v → t j = v → t l = v → i ≠ j → i ≠ l → j ≠ l →
      3 ≤ (Finset.univ.filter (fun i => t i = v)).card :=
    fun i j l v hi hj hl hij hil hjl =>
      Finset.two_lt_card.2 ⟨i, by simp [hi], j, by simp [hj], l, by simp [hl], hij, hil, hjl⟩
  have le1 : ∀ v, (Finset.univ.filter (fun i => t i = v)).card ≤ 1 →
      ∀ i j, t i = v → t j = v → i = j := by
    intro v h i j hi hj
    exact Finset.card_le_one.1 h i (by simp [hi]) j (by simp [hj])
  have L3 := one p0 3 tp0
  have L4 := one q1 4 tq1
  have L5 := one r2 5 tr2
  by_cases h0 : 2 ≤ (Finset.univ.filter (fun i => t i = 0)).card
  · by_cases h1 : 2 ≤ (Finset.univ.filter (fun i => t i = 1)).card
    · by_cases h2 : 2 ≤ (Finset.univ.filter (fun i => t i = 2)).card
      · omega
      · -- at most one rectangle carries label 2
        have e := le1 2 (by omega)
        have hcb : c1 = b0 := e c1 b0 tc1 tb0
        have hrc : rT = c1 := e rT c1 trT tc1
        have hxy : c2 ≠ a0 := by
          intro h
          have u1 := c0U c2 ⟨c2A, h ▸ a0B⟩
          have u2 := c0U c1 ⟨c1A, hcb ▸ b0B⟩
          have : t c2 = t c1 := by rw [u1, u2]
          rw [tc2, tc1] at this; exact absurd this (by decide)
        have huw : b2 ≠ a1 := by
          intro h
          have u1 := b1U b2 ⟨b2A, h ▸ a1B⟩
          have u2 := b1U c1 ⟨hcb ▸ b0A, c1B⟩
          have : t b2 = t c1 := by rw [u1, u2]
          rw [tb2, tc1] at this; exact absurd this (by decide)
        rcases taT with ha | ha
        · -- the cell (a, {3,4,5}) carries label 0: a third label-1 rectangle
          have hz1 : qT ≠ c2 := by
            intro h
            have u1 := cTU c2 ⟨c2A, h ▸ qTB⟩
            have u2 := cTU c1 ⟨c1A, hrc ▸ rTB⟩
            have : t c2 = t c1 := by rw [u1, u2]
            rw [tc2, tc1] at this; exact absurd this (by decide)
          have hz2 : qT ≠ a0 := by
            intro h
            have u1 := aTU a0 ⟨a0A, h ▸ qTB⟩
            have : t a0 = t aT := by rw [u1]
            rw [ta0, ha] at this; exact absurd this (by decide)
          have N1 := three c2 a0 qT 1 tc2 ta0 tqT hxy hz1.symm hz2.symm
          have N0 := two b2 a1 0 tb2 ta1 huw
          have N2 := one c1 2 tc1
          omega
        · -- the cell (a, {3,4,5}) carries label 1: a third label-0 rectangle
          have hz1 : pT ≠ b2 := by
            intro h
            have u1 := bTU b2 ⟨b2A, h ▸ pTB⟩
            have u2 := bTU c1 ⟨hcb ▸ b0A, hrc ▸ rTB⟩
            have : t b2 = t c1 := by rw [u1, u2]
            rw [tb2, tc1] at this; exact absurd this (by decide)
          have hz2 : pT ≠ a1 := by
            intro h
            have u1 := aTU a1 ⟨a1A, h ▸ pTB⟩
            have : t a1 = t aT := by rw [u1]
            rw [ta1, ha] at this; exact absurd this (by decide)
          have N0 := three b2 a1 pT 0 tb2 ta1 tpT huw hz1.symm hz2.symm
          have N1 := two c2 a0 1 tc2 ta0 hxy
          have N2 := one c1 2 tc1
          omega
    · -- at most one rectangle carries label 1
      have e := le1 1 (by omega)
      have hac : a0 = c2 := e a0 c2 ta0 tc2
      have hqa : qT = a0 := e qT a0 tqT ta0
      have hxy : a1 ≠ b2 := by
        intro h
        have u1 := a2U a1 ⟨a1A, h ▸ b2B⟩
        have u2 := a2U a0 ⟨a0A, hac ▸ c2B⟩
        have : t a1 = t a0 := by rw [u1, u2]
        rw [ta1, ta0] at this; exact absurd this (by decide)
      have huw : c1 ≠ b0 := by
        intro h
        have u1 := c0U c1 ⟨c1A, h ▸ b0B⟩
        have u2 := c0U a0 ⟨hac ▸ c2A, a0B⟩
        have : t c1 = t a0 := by rw [u1, u2]
        rw [tc1, ta0] at this; exact absurd this (by decide)
      rcases tbT with hb | hb
      · have hz1 : rT ≠ c1 := by
          intro h
          have u1 := cTU c1 ⟨c1A, h ▸ rTB⟩
          have u2 := cTU a0 ⟨hac ▸ c2A, hqa ▸ qTB⟩
          have : t c1 = t a0 := by rw [u1, u2]
          rw [tc1, ta0] at this; exact absurd this (by decide)
        have hz2 : rT ≠ b0 := by
          intro h
          have u1 := bTU b0 ⟨b0A, h ▸ rTB⟩
          have : t b0 = t bT := by rw [u1]
          rw [tb0, hb] at this; exact absurd this (by decide)
        have N2 := three c1 b0 rT 2 tc1 tb0 trT huw hz1.symm hz2.symm
        have N0 := two a1 b2 0 ta1 tb2 hxy
        have N1 := one a0 1 ta0
        omega
      · have hz1 : pT ≠ a1 := by
          intro h
          have u1 := aTU a1 ⟨a1A, h ▸ pTB⟩
          have u2 := aTU a0 ⟨a0A, hqa ▸ qTB⟩
          have : t a1 = t a0 := by rw [u1, u2]
          rw [ta1, ta0] at this; exact absurd this (by decide)
        have hz2 : pT ≠ b2 := by
          intro h
          have u1 := bTU b2 ⟨b2A, h ▸ pTB⟩
          have : t b2 = t bT := by rw [u1]
          rw [tb2, hb] at this; exact absurd this (by decide)
        have N0 := three a1 b2 pT 0 ta1 tb2 tpT hxy hz1.symm hz2.symm
        have N2 := two c1 b0 2 tc1 tb0 huw
        have N1 := one a0 1 ta0
        omega
  · -- at most one rectangle carries label 0
    have e := le1 0 (by omega)
    have hab : a1 = b2 := e a1 b2 ta1 tb2
    have hpa : pT = a1 := e pT a1 tpT ta1
    have hxy : a0 ≠ c2 := by
      intro h
      have u1 := a2U a0 ⟨a0A, h ▸ c2B⟩
      have u2 := a2U a1 ⟨a1A, hab ▸ b2B⟩
      have : t a0 = t a1 := by rw [u1, u2]
      rw [ta0, ta1] at this; exact absurd this (by decide)
    have huw : b0 ≠ c1 := by
      intro h
      have u1 := b1U b0 ⟨b0A, h ▸ c1B⟩
      have u2 := b1U a1 ⟨hab ▸ b2A, a1B⟩
      have : t b0 = t a1 := by rw [u1, u2]
      rw [tb0, ta1] at this; exact absurd this (by decide)
    rcases tcT with hc | hc
    · have hz1 : rT ≠ b0 := by
        intro h
        have u1 := bTU b0 ⟨b0A, h ▸ rTB⟩
        have u2 := bTU a1 ⟨hab ▸ b2A, hpa ▸ pTB⟩
        have : t b0 = t a1 := by rw [u1, u2]
        rw [tb0, ta1] at this; exact absurd this (by decide)
      have hz2 : rT ≠ c1 := by
        intro h
        have u1 := cTU c1 ⟨c1A, h ▸ rTB⟩
        have : t c1 = t cT := by rw [u1]
        rw [tc1, hc] at this; exact absurd this (by decide)
      have N2 := three b0 c1 rT 2 tb0 tc1 trT huw hz1.symm hz2.symm
      have N1 := two a0 c2 1 ta0 tc2 hxy
      have N0 := one a1 0 ta1
      omega
    · have hz1 : qT ≠ a0 := by
        intro h
        have u1 := aTU a0 ⟨a0A, h ▸ qTB⟩
        have u2 := aTU a1 ⟨a1A, hpa ▸ pTB⟩
        have : t a0 = t a1 := by rw [u1, u2]
        rw [ta0, ta1] at this; exact absurd this (by decide)
      have hz2 : qT ≠ c2 := by
        intro h
        have u1 := cTU c2 ⟨c2A, h ▸ qTB⟩
        have : t c2 = t cT := by rw [u1]
        rw [tc2, hc] at this; exact absurd this (by decide)
      have N1 := three a0 c2 qT 1 ta0 tc2 tqT hxy hz1.symm hz2.symm
      have N2 := two b0 c1 2 tb0 tc1 huw
      have N0 := one a1 0 ta1
      omega
