import PEqualNP.Defs

-- Decompose non-rectangle AND gates below the output by whether each operand is
-- point-only, line-only, or mixed; same-side ANDs are eliminated via monotonicity
-- and soundness on 0 and 1 lines.
theorem PEqualNP.Outside.R_meta_4305_1
    (h_pt_mix :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
        let V := Fin N → Bool
        let twoN := N + N
        let e1 : Fin N → Fin N → Bool := fun p r => decide (r = p)
        100 < q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
        (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
        ∀ (m out : ℕ) (W : ℕ → Set (V × V)),
          out < twoN + m →
          (∀ k : ℕ, W k ≠ ∅) →
          (∀ i : Fin N, W ↑i = {z : V × V | z.1 i = true} ∧ W (N + ↑i) = {z : V × V | z.2 i = true}) →
          (∀ g < m, ∃ a b : ℕ, max a b < twoN + g ∧ (W (twoN + g) = W a ∪ W b ∨ W (twoN + g) = W a ∩ W b)) →
          (∀ p l : Fin N, I p l → (e1 p, e1 l) ∈ W out) →
          (∀ v : V, Fintype.card { l : Fin N // v l = true } ≤ q →
            (fun p : Fin N => decide (¬ ∃ l : Fin N, I p l ∧ v l = true), v) ∉ W out) →
          100 * m < N * q →
          let ptOnly (k : ℕ) := ∃ A : Set V, W k = A ×ˢ Set.univ
          let lnOnly (k : ℕ) := ∃ B : Set V, W k = Set.univ ×ˢ B
          {z : Fin N × Fin N | I z.1 z.2 ∧ ∃ g < m, W (twoN + g) ⊆ W out ∧ (e1 z.1, e1 z.2) ∈ W (twoN + g) ∧
            ∃ a b : ℕ, max a b < twoN + g ∧ W (twoN + g) = W a ∩ W b ∧
              ptOnly a ∧ ¬ ptOnly b ∧ ¬ lnOnly b}.ncard ≤ 32 * m)
    (h_ln_mix :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
        let V := Fin N → Bool
        let twoN := N + N
        let e1 : Fin N → Fin N → Bool := fun p r => decide (r = p)
        100 < q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
        (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
        ∀ (m out : ℕ) (W : ℕ → Set (V × V)),
          out < twoN + m →
          (∀ k : ℕ, W k ≠ ∅) →
          (∀ i : Fin N, W ↑i = {z : V × V | z.1 i = true} ∧ W (N + ↑i) = {z : V × V | z.2 i = true}) →
          (∀ g < m, ∃ a b : ℕ, max a b < twoN + g ∧ (W (twoN + g) = W a ∪ W b ∨ W (twoN + g) = W a ∩ W b)) →
          (∀ p l : Fin N, I p l → (e1 p, e1 l) ∈ W out) →
          (∀ v : V, Fintype.card { l : Fin N // v l = true } ≤ q →
            (fun p : Fin N => decide (¬ ∃ l : Fin N, I p l ∧ v l = true), v) ∉ W out) →
          100 * m < N * q →
          let ptOnly (k : ℕ) := ∃ A : Set V, W k = A ×ˢ Set.univ
          let lnOnly (k : ℕ) := ∃ B : Set V, W k = Set.univ ×ˢ B
          {z : Fin N × Fin N | I z.1 z.2 ∧ ∃ g < m, W (twoN + g) ⊆ W out ∧ (e1 z.1, e1 z.2) ∈ W (twoN + g) ∧
            ∃ a b : ℕ, max a b < twoN + g ∧ W (twoN + g) = W a ∩ W b ∧
              lnOnly a ∧ ¬ ptOnly b ∧ ¬ lnOnly b}.ncard ≤ 32 * m)
    (h_both_mix :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
        let V := Fin N → Bool
        let twoN := N + N
        let e1 : Fin N → Fin N → Bool := fun p r => decide (r = p)
        100 < q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
        (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
        ∀ (m out : ℕ) (W : ℕ → Set (V × V)),
          out < twoN + m →
          (∀ k : ℕ, W k ≠ ∅) →
          (∀ i : Fin N, W ↑i = {z : V × V | z.1 i = true} ∧ W (N + ↑i) = {z : V × V | z.2 i = true}) →
          (∀ g < m, ∃ a b : ℕ, max a b < twoN + g ∧ (W (twoN + g) = W a ∪ W b ∨ W (twoN + g) = W a ∩ W b)) →
          (∀ p l : Fin N, I p l → (e1 p, e1 l) ∈ W out) →
          (∀ v : V, Fintype.card { l : Fin N // v l = true } ≤ q →
            (fun p : Fin N => decide (¬ ∃ l : Fin N, I p l ∧ v l = true), v) ∉ W out) →
          100 * m < N * q →
          let ptOnly (k : ℕ) := ∃ A : Set V, W k = A ×ˢ Set.univ
          let lnOnly (k : ℕ) := ∃ B : Set V, W k = Set.univ ×ˢ B
          {z : Fin N × Fin N | I z.1 z.2 ∧ ∃ g < m, W (twoN + g) ⊆ W out ∧ (e1 z.1, e1 z.2) ∈ W (twoN + g) ∧
            ∃ a b : ℕ, max a b < twoN + g ∧ W (twoN + g) = W a ∩ W b ∧
              ¬ ptOnly a ∧ ¬ lnOnly a ∧ ¬ ptOnly b ∧ ¬ lnOnly b}.ncard ≤ 32 * m) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   let x5 : Type := Fin x2 → Bool;   have x6 : ℕ := x2 + x2;   have x7 : Fin x2 → Fin x2 → Bool := fun (x7 x8 : Fin x2) => Decidable.decide (x8 = x7);   (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x10 : Fin x2), Fintype.card { x11 : Fin x2 // x3 x11 x10 } = x1 + (1 : ℕ)) → (∀ (x11 x12 : Fin x2), x11 ≠ x12 → ∃! x14 : Fin x2, x3 x11 x14 ∧ x3 x12 x14) → ∀ (x12 x13 : ℕ) (x14 : ℕ → Set (x5 × x5)), x13 < x6 + x12 → (∀ (x16 : ℕ), x14 x16 ≠ ∅) → (∀ (x17 : Fin x2), x14 ↑x17 = {x18 : x5 × x5 | x18.1 x17 = Bool.true} ∧ x14 (x2 + ↑x17) = {x18 : x5 × x5 | x18.2 x17 = Bool.true}) → (∀ x18 < x12, ∃ (x20 : ℕ) (x21 : ℕ), Max.max x20 x21 < x6 + x18 ∧ (x14 (x6 + x18) = x14 x20 ∪ x14 x21 ∨ x14 (x6 + x18) = x14 x20 ∩ x14 x21)) → (∀ (x19 x20 : Fin x2), x3 x19 x20 → (x7 x19, x7 x20) ∈ x14 x13) → (∀ (x20 : x5), Fintype.card { x21 : Fin x2 // x20 x21 = Bool.true } ≤ x1 → (fun (x22 : Fin x2) => Decidable.decide ¬∃ (x23 : Fin x2), x3 x22 x23 ∧ x20 x23 = Bool.true, x20) ∉ x14 x13) → {x21 : Fin x2 × Fin x2 | x3 x21.1 x21.2 ∧ ∃ x22 < x12, x14 (x6 + x22) ⊆ x14 x13 ∧ (x7 x21.1, x7 x21.2) ∈ x14 (x6 + x22) ∧ ∃ (x23 : ℕ) (x24 : ℕ), Max.max x23 x24 < x6 + x22 ∧ x14 (x6 + x22) = x14 x23 ∩ x14 x24 ∧ ∃ (x25 : Set x5) (x26 : Set x5), x14 x23 = x25 ×ˢ Set.univ ∧ x14 x24 = Set.univ ×ˢ x26}.ncard ≤ (4 : ℕ) * x12 → x2 * x1 ≤ (100 : ℕ) * x12 := by
  intro q N I _ V twoN e1 hq hN hline hjoin m out W hout hne hbase hgate hinc hsound hrect
  by_cases hgoal : N * q ≤ 100 * m
  · exact hgoal
  · have hsmall : 100 * m < N * q := Nat.lt_of_not_ge hgoal
    have hmono : ∀ w, w < twoN + m → ∀ (u1 u2 v1 v2 : V),
        (∀ i, u1 i = true → u2 i = true) → (∀ i, v1 i = true → v2 i = true) →
        (u1, v1) ∈ W w → (u2, v2) ∈ W w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw u1 u2 v1 v2 hu hv hmem
        by_cases h1 : w < N
        · have hb := (hbase ⟨w, h1⟩).1
          rw [hb] at hmem ⊢
          exact hu ⟨w, h1⟩ hmem
        · by_cases h2 : w < twoN
          · have hsub : w - N < N := by omega
            have heq : N + (w - N) = w := by omega
            have hb := (hbase ⟨w - N, hsub⟩).2
            change W (N + (w - N)) = _ at hb
            rw [heq] at hb
            rw [hb] at hmem ⊢
            exact hv ⟨w - N, hsub⟩ hmem
          · have hg : w - twoN < m := by omega
            have heq : twoN + (w - twoN) = w := by omega
            obtain ⟨a, b, hmax, hop⟩ := hgate (w - twoN) hg
            rw [heq] at hmax hop
            have ha : a < w := lt_of_le_of_lt (le_max_left a b) hmax
            have hb : b < w := lt_of_le_of_lt (le_max_right a b) hmax
            rcases hop with hunion | hinter
            · rw [hunion] at hmem ⊢
              rcases hmem with hma | hmb
              · exact Or.inl (ih a ha (by omega) u1 u2 v1 v2 hu hv hma)
              · exact Or.inr (ih b hb (by omega) u1 u2 v1 v2 hu hv hmb)
            · rw [hinter] at hmem ⊢
              exact ⟨ih a ha (by omega) u1 u2 v1 v2 hu hv hmem.1,
                     ih b hb (by omega) u1 u2 v1 v2 hu hv hmem.2⟩
    have hno_pt : ∀ w < twoN + m, ∀ A : Set V, W w = A ×ˢ Set.univ → ¬ W w ⊆ W out := by
      intro w hw A hA hsub
      have hnon : (W w).Nonempty := Set.nonempty_iff_ne_empty.mpr (hne w)
      obtain ⟨⟨u, v⟩, huv⟩ := hnon
      have htop : (fun _ : Fin N => true, v) ∈ W w :=
        hmono w hw u (fun _ => true) v v (fun _ _ => rfl) (fun _ h => h) huv
      rw [hA] at htop
      have hmem_out : (fun _ : Fin N => true, fun _ : Fin N => false) ∈ W out := by
        apply hsub
        rw [hA]
        exact ⟨htop.1, trivial⟩
      have hcard0 : Fintype.card { l : Fin N // (fun _ : Fin N => false) l = true } ≤ q := by
        have hempty : IsEmpty { l : Fin N // (fun _ : Fin N => false) l = true } :=
          ⟨fun x => Bool.false_ne_true x.2⟩
        rw [Fintype.card_eq_zero]
        exact Nat.zero_le q
      have hbad := hsound (fun _ => false) hcard0
      have hfun : (fun p : Fin N => decide (¬ ∃ l : Fin N, I p l ∧ (fun _ : Fin N => false) l = true)) =
          (fun _ : Fin N => true) := by
        funext p
        rw [decide_eq_true_iff]
        intro hex
        obtain ⟨_, _, hf⟩ := hex
        exact Bool.false_ne_true hf
      rw [hfun] at hbad
      exact hbad hmem_out
    have hno_ln : ∀ w < twoN + m, ∀ B : Set V, ∀ p l : Fin N,
        W w = Set.univ ×ˢ B → (e1 p, e1 l) ∈ W w → ¬ W w ⊆ W out := by
      intro w _ B p l hB hmem hsub
      rw [hB] at hmem
      have hmem_out : (fun p' : Fin N => decide (¬ ∃ l' : Fin N, I p' l' ∧ e1 l l' = true), e1 l) ∈ W out := by
        apply hsub
        rw [hB]
        exact ⟨trivial, hmem.2⟩
      have hcard1 : Fintype.card { l' : Fin N // e1 l l' = true } ≤ q := by
        have heq : Fintype.card { l' : Fin N // e1 l l' = true } = Fintype.card { l' : Fin N // l' = l } := by
          apply Fintype.card_congr
          exact Equiv.subtypeEquivRight (fun l' => decide_eq_true_iff)
        rw [heq, Fintype.card_unique]
        omega
      exact hsound (e1 l) hcard1 hmem_out
    have hevery_and : ∀ w, w < twoN + m → ∀ p l : Fin N,
        W w ⊆ W out → (e1 p, e1 l) ∈ W w →
        ∃ g < m, W (twoN + g) ⊆ W out ∧ (e1 p, e1 l) ∈ W (twoN + g) ∧
          ∃ a b : ℕ, max a b < twoN + g ∧ W (twoN + g) = W a ∩ W b := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw p l hsub hmem
        by_cases h1 : w < N
        · have hb := (hbase ⟨w, h1⟩).1
          have hprod : W w = {u : V | u ⟨w, h1⟩ = true} ×ˢ Set.univ := by
            rw [hb]; ext z; simp
          exact False.elim (hno_pt w hw _ hprod hsub)
        · by_cases h2 : w < twoN
          · have hsubN : w - N < N := by omega
            have heq : N + (w - N) = w := by omega
            have hb := (hbase ⟨w - N, hsubN⟩).2
            change W (N + (w - N)) = _ at hb
            rw [heq] at hb
            have hprod : W w = Set.univ ×ˢ {v : V | v ⟨w - N, hsubN⟩ = true} := by
              rw [hb]; ext z; simp
            exact False.elim (hno_ln w hw _ p l hprod hmem hsub)
          · have hg : w - twoN < m := by omega
            have heq : twoN + (w - twoN) = w := by omega
            obtain ⟨a, b, hmax, hop⟩ := hgate (w - twoN) hg
            rw [heq] at hmax hop
            have ha : a < w := lt_of_le_of_lt (le_max_left a b) hmax
            have hb : b < w := lt_of_le_of_lt (le_max_right a b) hmax
            rcases hop with hunion | hinter
            · rw [hunion] at hmem
              rcases hmem with hma | hmb
              · have hsubA : W a ⊆ W out := by
                  intro z hz; apply hsub; rw [hunion]; exact Or.inl hz
                exact ih a ha (by omega) p l hsubA hma
              · have hsubB : W b ⊆ W out := by
                  intro z hz; apply hsub; rw [hunion]; exact Or.inr hz
                exact ih b hb (by omega) p l hsubB hmb
            · exact ⟨w - twoN, hg, by rw [heq]; exact hsub, by rw [heq]; exact hmem,
                a, b, by rw [heq]; exact hmax, by rw [heq]; exact hinter⟩
    let ptOnly (k : ℕ) := ∃ A : Set V, W k = A ×ˢ Set.univ
    let lnOnly (k : ℕ) := ∃ B : Set V, W k = Set.univ ×ˢ B
    let E_all : Set (Fin N × Fin N) := {z : Fin N × Fin N | I z.1 z.2}
    let E_rect : Set (Fin N × Fin N) :=
      {z : Fin N × Fin N | I z.1 z.2 ∧ ∃ g < m, W (twoN + g) ⊆ W out ∧ (e1 z.1, e1 z.2) ∈ W (twoN + g) ∧
        ∃ a b : ℕ, max a b < twoN + g ∧ W (twoN + g) = W a ∩ W b ∧ ∃ A B : Set V, W a = A ×ˢ Set.univ ∧ W b = Set.univ ×ˢ B}
    let E_pt : Set (Fin N × Fin N) :=
      {z : Fin N × Fin N | I z.1 z.2 ∧ ∃ g < m, W (twoN + g) ⊆ W out ∧ (e1 z.1, e1 z.2) ∈ W (twoN + g) ∧
        ∃ a b : ℕ, max a b < twoN + g ∧ W (twoN + g) = W a ∩ W b ∧ ptOnly a ∧ ¬ ptOnly b ∧ ¬ lnOnly b}
    let E_ln : Set (Fin N × Fin N) :=
      {z : Fin N × Fin N | I z.1 z.2 ∧ ∃ g < m, W (twoN + g) ⊆ W out ∧ (e1 z.1, e1 z.2) ∈ W (twoN + g) ∧
        ∃ a b : ℕ, max a b < twoN + g ∧ W (twoN + g) = W a ∩ W b ∧ lnOnly a ∧ ¬ ptOnly b ∧ ¬ lnOnly b}
    let E_both : Set (Fin N × Fin N) :=
      {z : Fin N × Fin N | I z.1 z.2 ∧ ∃ g < m, W (twoN + g) ⊆ W out ∧ (e1 z.1, e1 z.2) ∈ W (twoN + g) ∧
        ∃ a b : ℕ, max a b < twoN + g ∧ W (twoN + g) = W a ∩ W b ∧ ¬ ptOnly a ∧ ¬ lnOnly a ∧ ¬ ptOnly b ∧ ¬ lnOnly b}
    have hcover : E_all ⊆ E_rect ∪ (E_pt ∪ (E_ln ∪ E_both)) := by
      intro z hpl
      rcases z with ⟨p, l⟩
      obtain ⟨g, hg, hsub, hmem, a, b, hmax, hinter⟩ :=
        hevery_and out hout p l (fun _ h => h) (hinc p l hpl)
      have hmax_sym : max b a < twoN + g := by rw [max_comm]; exact hmax
      have hinter_sym : W (twoN + g) = W b ∩ W a := by rw [Set.inter_comm]; exact hinter
      by_cases hpa : ptOnly a
      · by_cases hpb : ptOnly b
        · obtain ⟨A1, hA1⟩ := hpa
          obtain ⟨A2, hA2⟩ := hpb
          have hprod : W (twoN + g) = (A1 ∩ A2) ×ˢ Set.univ := by
            rw [hinter, hA1, hA2]; ext z; simp
          exact False.elim (hno_pt (twoN + g) (by omega) (A1 ∩ A2) hprod hsub)
        · by_cases hlb : lnOnly b
          · obtain ⟨A, hA⟩ := hpa
            obtain ⟨B, hB⟩ := hlb
            exact Or.inl ⟨hpl, g, hg, hsub, hmem, a, b, hmax, hinter, A, B, hA, hB⟩
          · exact Or.inr (Or.inl ⟨hpl, g, hg, hsub, hmem, a, b, hmax, hinter, hpa, hpb, hlb⟩)
      · by_cases hla : lnOnly a
        · by_cases hpb : ptOnly b
          · obtain ⟨A, hA⟩ := hpb
            obtain ⟨B, hB⟩ := hla
            exact Or.inl ⟨hpl, g, hg, hsub, hmem, b, a, hmax_sym, hinter_sym, A, B, hA, hB⟩
          · by_cases hlb : lnOnly b
            · obtain ⟨B1, hB1⟩ := hla
              obtain ⟨B2, hB2⟩ := hlb
              have hprod : W (twoN + g) = Set.univ ×ˢ (B1 ∩ B2) := by
                rw [hinter, hB1, hB2]; ext z; simp
              exact False.elim (hno_ln (twoN + g) (by omega) (B1 ∩ B2) p l hprod hmem hsub)
            · exact Or.inr (Or.inr (Or.inl ⟨hpl, g, hg, hsub, hmem, a, b, hmax, hinter, hla, hpb, hlb⟩))
        · by_cases hpb : ptOnly b
          · exact Or.inr (Or.inl ⟨hpl, g, hg, hsub, hmem, b, a, hmax_sym, hinter_sym, hpb, hpa, hla⟩)
          · by_cases hlb : lnOnly b
            · exact Or.inr (Or.inr (Or.inl ⟨hpl, g, hg, hsub, hmem, b, a, hmax_sym, hinter_sym, hlb, hpa, hla⟩))
            · exact Or.inr (Or.inr (Or.inr ⟨hpl, g, hg, hsub, hmem, a, b, hmax, hinter, hpa, hla, hpb, hlb⟩))
    have hcard_all : E_all.ncard = N * (q + 1) := by
      let S : Finset (Fin N × Fin N) := Finset.univ.filter (fun z => I z.1 z.2)
      have hS_coe : (S : Set (Fin N × Fin N)) = E_all := by
        ext z; simp [S, E_all]
      rw [← hS_coe, Set.ncard_coe_finset]
      have hfib : S.card = ∑ l : Fin N, (S.filter (fun z => z.2 = l)).card :=
        Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      rw [hfib]
      have hterm : ∀ l : Fin N, (S.filter (fun z => z.2 = l)).card = q + 1 := by
        intro l
        have heq : S.filter (fun z => z.2 = l) = (Finset.univ.filter (fun p => I p l)).image (fun p => (p, l)) := by
          apply Finset.ext; intro z; rcases z with ⟨p, l'⟩
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
          constructor
          · rintro ⟨h1, rfl⟩; exact ⟨p, h1, rfl, rfl⟩
          · rintro ⟨_, h1, rfl, rfl⟩; exact ⟨h1, rfl⟩
        rw [heq, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h), ← Fintype.card_subtype]
        exact hline l
      simp [hterm]
    have h1 : E_pt.ncard ≤ 32 * m :=
      h_pt_mix q N I hq hN hline hjoin m out W hout hne hbase hgate hinc hsound hsmall
    have h2 : E_ln.ncard ≤ 32 * m :=
      h_ln_mix q N I hq hN hline hjoin m out W hout hne hbase hgate hinc hsound hsmall
    have h3 : E_both.ncard ≤ 32 * m :=
      h_both_mix q N I hq hN hline hjoin m out W hout hne hbase hgate hinc hsound hsmall
    have hle0 : E_all.ncard ≤ (E_rect ∪ (E_pt ∪ (E_ln ∪ E_both))).ncard :=
      Set.ncard_le_ncard hcover (Set.toFinite _)
    have hle1 : (E_rect ∪ (E_pt ∪ (E_ln ∪ E_both))).ncard ≤ E_rect.ncard + (E_pt ∪ (E_ln ∪ E_both)).ncard :=
      Set.ncard_union_le _ _
    have hle2 : (E_pt ∪ (E_ln ∪ E_both)).ncard ≤ E_pt.ncard + (E_ln ∪ E_both).ncard :=
      Set.ncard_union_le _ _
    have hle3 : (E_ln ∪ E_both).ncard ≤ E_ln.ncard + E_both.ncard :=
      Set.ncard_union_le _ _
    have hrect' : E_rect.ncard ≤ 4 * m := hrect
    have hmul : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (Nat.le_succ q)
    omega
