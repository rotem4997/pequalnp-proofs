import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2794_556
    (topUnion :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
        100 < q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
        (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
        ∀ (s out : ℕ) (bad : Finset ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
          N + N ≤ out → out < N + N + s →
          (∀ i : Fin N, W i.val = {z | z.1 i = true} ∧ W (N + i.val) = {z | z.2 i = true}) →
          (∀ g < s, ∃ a < N + N + g, ∃ b < N + N + g,
            let wg := W (N + N + g);
            wg = W a ∪ W b ∨ wg = W a ∨ wg = ∅ ∨
              (wg = W a ∩ W b ∧ (g ∈ bad ∨ ∃ A B, W a = A ×ˢ Set.univ ∧ W b = Set.univ ×ˢ B))) →
          (∃ a < out, ∃ b < out, W out = W a ∪ W b ∧ W a ≠ W out ∧ W b ≠ W out) →
          (∀ p l : Fin N, I p l → ((fun i => decide (i = p)), (fun j => decide (j = l))) ∈ W out) →
          (∀ y : Fin N → Bool, Fintype.card { l : Fin N // y l = true } ≤ q →
            ((fun p => decide (¬ ∃ l : Fin N, I p l ∧ y l = true)), y) ∉ W out) →
          100 * bad.card < N * q → N * q ≤ 100 * s)
    (topBadInter :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
        100 < q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
        (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
        ∀ (s out : ℕ) (bad : Finset ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
          N + N ≤ out → out < N + N + s → out - (N + N) ∈ bad →
          (∀ i : Fin N, W i.val = {z | z.1 i = true} ∧ W (N + i.val) = {z | z.2 i = true}) →
          (∀ g < s, ∃ a < N + N + g, ∃ b < N + N + g,
            let wg := W (N + N + g);
            wg = W a ∪ W b ∨ wg = W a ∨ wg = ∅ ∨
              (wg = W a ∩ W b ∧ (g ∈ bad ∨ ∃ A B, W a = A ×ˢ Set.univ ∧ W b = Set.univ ×ˢ B))) →
          (∃ a < out, ∃ b < out, W out = W a ∩ W b ∧ W a ≠ W out ∧ W b ≠ W out) →
          (∀ p l : Fin N, I p l → ((fun i => decide (i = p)), (fun j => decide (j = l))) ∈ W out) →
          (∀ y : Fin N → Bool, Fintype.card { l : Fin N // y l = true } ≤ q →
            ((fun p => decide (¬ ∃ l : Fin N, I p l ∧ y l = true)), y) ∉ W out) →
          100 * bad.card < N * q → N * q ≤ 100 * s) :
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x9) := by
  classical
  intro q N I hdec hq hN hline huniq s out bad W hout hWin hWgate hpos hneg hbad
  have hNpos : 0 < N := by
    have : 0 ≤ q ^ 2 := Nat.zero_le _
    omega
  have hEx : ∃ w, w ≤ out ∧ W w = W out := ⟨out, le_rfl, rfl⟩
  let w0 : ℕ := Nat.find hEx
  have hw0_spec : w0 ≤ out ∧ W w0 = W out := Nat.find_spec hEx
  have hw0_le : w0 ≤ out := hw0_spec.1
  have hw0_eq : W w0 = W out := hw0_spec.2
  have hw0_lt : w0 < N + N + s := by omega
  have hw0_min : ∀ w < w0, W w ≠ W out := by
    intro w hlt heq
    exact Nat.find_min hEx hlt ⟨by omega, heq⟩
  have hpos0 : ∀ p l : Fin N, I p l →
      ((fun i => decide (i = p)), (fun j => decide (j = l))) ∈ W w0 := by
    intro p l hpl; rw [hw0_eq]; exact hpos p l hpl
  have hneg0 : ∀ y : Fin N → Bool, Fintype.card { l : Fin N // y l = true } ≤ q →
      ((fun p => decide (¬ ∃ l : Fin N, I p l ∧ y l = true)), y) ∉ W w0 := by
    intro y hy; rw [hw0_eq]; exact hneg y hy
  have card_single : ∀ l : Fin N, Fintype.card { j : Fin N // decide (j = l) = true } = 1 := by
    intro l
    have hEq : ∀ j : Fin N, (decide (j = l) = true) ↔ j = l := fun j => by simp
    simp [hEq]
  have hw0_ge : N + N ≤ w0 := by
    by_contra hlt
    by_cases h1 : w0 < N
    · let p : Fin N := ⟨w0, h1⟩
      have hcard0 : Fintype.card { j : Fin N // (fun _ : Fin N => false) j = true } ≤ q := by
        have hzero : Fintype.card { j : Fin N // (fun _ : Fin N => false) j = true } = 0 := by
          simp
        omega
      have hno := hneg0 (fun _ => false) hcard0
      have hin : ((fun p => decide (¬ ∃ l : Fin N, I p l ∧ false = true)), fun _ => false) ∈ W w0 := by
        have hp := (hWin p).1
        change W w0 = {z | z.1 p = true} at hp
        rw [hp]
        simp
      exact hno hin
    · have hl_lt : w0 - N < N := by omega
      let l : Fin N := ⟨w0 - N, hl_lt⟩
      have hcard1 : Fintype.card { j : Fin N // decide (j = l) = true } ≤ q := by
        rw [card_single l]; omega
      have hno := hneg0 (fun j => decide (j = l)) hcard1
      have hin : ((fun p => decide (¬ ∃ j : Fin N, I p j ∧ decide (j = l) = true)), fun j => decide (j = l)) ∈ W w0 := by
        have hl := (hWin l).2
        have hweq : N + l.val = w0 := by change N + (w0 - N) = w0; omega
        rw [hweq] at hl
        rw [hl]
        simp
      exact hno hin
  have hmono : ∀ w < N + N + s, ∀ x y x' y' : Fin N → Bool,
      (x, y) ∈ W w → (∀ i, x i = true → x' i = true) → (∀ j, y j = true → y' j = true) →
      (x', y') ∈ W w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw x y x' y' hxy hx hy
      by_cases h1 : w < N
      · have hp := (hWin ⟨w, h1⟩).1
        change W w = {z | z.1 ⟨w, h1⟩ = true} at hp
        rw [hp] at hxy ⊢
        exact hx ⟨w, h1⟩ hxy
      · by_cases h2 : w < N + N
        · have hl := (hWin ⟨w - N, by omega⟩).2
          have hweq : N + (⟨w - N, by omega⟩ : Fin N).val = w := by simp; omega
          rw [hweq] at hl
          rw [hl] at hxy ⊢
          exact hy ⟨w - N, by omega⟩ hxy
        · let g := w - (N + N)
          have hg : g < s := by omega
          have hweq : N + N + g = w := by omega
          obtain ⟨a, ha, b, hb, hcase⟩ := hWgate g hg
          dsimp only at hcase
          rw [hweq] at ha hb hcase
          rcases hcase with hor | hcopy | hemp | ⟨hand, _⟩
          · rw [hor] at hxy ⊢
            rcases hxy with hxa | hxb
            · exact Or.inl (ih a ha (by omega) x y x' y' hxa hx hy)
            · exact Or.inr (ih b hb (by omega) x y x' y' hxb hx hy)
          · rw [hcopy] at hxy ⊢
            exact ih a ha (by omega) x y x' y' hxy hx hy
          · rw [hemp] at hxy
            exact hxy.elim
          · rw [hand] at hxy ⊢
            exact ⟨ih a ha (by omega) x y x' y' hxy.1 hx hy,
              ih b hb (by omega) x y x' y' hxy.2 hx hy⟩
  let g0 : ℕ := w0 - (N + N)
  have hg0 : g0 < s := by omega
  have hw0_g0 : N + N + g0 = w0 := by omega
  obtain ⟨a, ha, b, hb, hcase⟩ := hWgate g0 hg0
  dsimp only at hcase
  rw [hw0_g0] at ha hb hcase
  have hnonempty : (W w0).Nonempty := by
    let l0 : Fin N := ⟨0, hNpos⟩
    have hpos_card : 0 < Fintype.card { p : Fin N // I p l0 } := by rw [hline l0]; omega
    obtain ⟨⟨p0, hp0⟩⟩ := Fintype.card_pos_iff.mp hpos_card
    exact ⟨_, hpos0 p0 l0 hp0⟩
  rcases hcase with hor | hcopy | hemp | ⟨hand, hbad_or_rect⟩
  · have hneA : W a ≠ W w0 := fun he => hw0_min a ha (he.trans hw0_eq)
    have hneB : W b ≠ W w0 := fun he => hw0_min b hb (he.trans hw0_eq)
    exact topUnion q N I hq hN hline huniq s w0 bad W hw0_ge hw0_lt hWin hWgate
      ⟨a, ha, b, hb, hor, hneA, hneB⟩ hpos0 hneg0 hbad
  · exact (hw0_min a ha (hcopy.symm.trans hw0_eq)).elim
  · rw [hemp] at hnonempty
    exact (Set.not_nonempty_empty hnonempty).elim
  · rcases hbad_or_rect with hg0bad | ⟨A, B, hWa, hWb⟩
    · have hneA : W a ≠ W w0 := fun he => hw0_min a ha (he.trans hw0_eq)
      have hneB : W b ≠ W w0 := fun he => hw0_min b hb (he.trans hw0_eq)
      exact topBadInter q N I hq hN hline huniq s w0 bad W hw0_ge hw0_lt hg0bad hWin hWgate
        ⟨a, ha, b, hb, hand, hneA, hneB⟩ hpos0 hneg0 hbad
    · exfalso
      let l0 : Fin N := ⟨0, hNpos⟩
      have hpos_card : 0 < Fintype.card { p : Fin N // I p l0 } := by rw [hline l0]; omega
      obtain ⟨⟨p0, hp0⟩⟩ := Fintype.card_pos_iff.mp hpos_card
      have hp0_mem := hpos0 p0 l0 hp0
      rw [hand, hWa, hWb] at hp0_mem
      have hl0B : (fun j : Fin N => decide (j = l0)) ∈ B := hp0_mem.2.2
      have hex_non : ∃ p1 : Fin N, ¬ I p1 l0 := by
        by_contra hall
        push Not at hall
        have hfull : Fintype.card { p : Fin N // I p l0 } = N := by
          have heq : (Finset.univ.filter fun p : Fin N => I p l0) = Finset.univ := by
            ext p; simp [hall p]
          rw [Fintype.card_subtype, heq, Finset.card_univ, Fintype.card_fin]
        rw [hline l0] at hfull
        have hq2 : q * q = q ^ 2 := by ring
        nlinarith
      obtain ⟨p1, hp1n⟩ := hex_non
      have hex_p2 : ∃ p2 : Fin N, p1 ≠ p2 := by
        have hN2 : 1 < N := by nlinarith
        by_cases h0 : p1.val = 0
        · refine ⟨⟨1, hN2⟩, ?_⟩
          intro he
          have := congrArg Fin.val he
          simp [h0] at this
        · refine ⟨⟨0, hNpos⟩, ?_⟩
          intro he
          have := congrArg Fin.val he
          simp at this
          exact h0 this
      obtain ⟨p2, hp12⟩ := hex_p2
      obtain ⟨l1, ⟨hp1l1, _⟩, _⟩ := huniq p1 p2 hp12
      have hp1_mem := hpos0 p1 l1 hp1l1
      rw [hand, hWa, hWb] at hp1_mem
      have hp1A : (fun i : Fin N => decide (i = p1)) ∈ A := hp1_mem.1.1
      have hcross : ((fun i : Fin N => decide (i = p1)), (fun j : Fin N => decide (j = l0))) ∈ W w0 := by
        rw [hand, hWa, hWb]
        exact ⟨⟨hp1A, Set.mem_univ _⟩, ⟨Set.mem_univ _, hl0B⟩⟩
      let y0 : Fin N → Bool := fun j => decide (j = l0)
      have hcard1 : Fintype.card { j : Fin N // y0 j = true } ≤ q := by
        rw [card_single l0]; omega
      have hleX : ∀ i : Fin N, decide (i = p1) = true →
          decide (¬ ∃ l : Fin N, I i l ∧ y0 l = true) = true := by
        intro i hi
        have hieq : i = p1 := of_decide_eq_true hi
        subst hieq
        apply decide_eq_true
        rintro ⟨l, hil, hyl⟩
        have hleq : l = l0 := of_decide_eq_true hyl
        subst hleq
        exact hp1n hil
      have hbad_mem := hmono w0 hw0_lt _ _ _ _ hcross hleX (fun _ h => h)
      exact hneg0 y0 hcard1 hbad_mem
