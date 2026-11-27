import Mathlib
import PEqualNP.Defs

-- Expand the dense C4-free core, normalize the circuit trace to nonempty binary gates,
-- prove the dependency frontier to restrict to q >= 200 and 2N <= s + 1, and extract a
-- minimal sound mixed-AND gate witness for every core edge.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5339_319
    (coreExpansion : ∀ (N d : ℕ) (E : Finset (Fin N × Fin N)) (A B : Finset (Fin N)),
      (∀ p p' l l' : Fin N,
        (p, l) ∈ E → (p, l') ∈ E → (p', l) ∈ E → (p', l') ∈ E → p = p' ∨ l = l') →
      A.Nonempty → B.Nonempty →
      (∀ p ∈ A, d < (B.filter fun l => (p, l) ∈ E).card) →
      (∀ l ∈ B, d < (A.filter fun p => (p, l) ∈ E).card) →
      d * (d + 1) < A.card ∧ d * (d + 1) < B.card ∧
        (d + 1) * (d * (d + 1) + 1) ≤ (E.filter fun e => e.1 ∈ A ∧ e.2 ∈ B).card)
    (mixedCoreLower : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      let V := Fin N → Bool
      let m := N + N
      let atom := fun (a b : Fin N) => decide (b = a)
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (U : ℕ → Set (V × V)),
        o < m + s → m ≤ s + 1 → 100 * s < N * q →
        (∀ w, U w ≠ ∅) →
        (∀ p : Fin N, U p.val = {z | z.1 p = true} ∧ U (N + p.val) = {z | z.2 p = true}) →
        (∀ k < s, ∃ a < m + k, ∃ b < m + k, U (m + k) = U a ∪ U b ∨ U (m + k) = U a ∩ U b) →
        (∀ p l, I p l → (atom p, atom l) ∈ U o) →
        (∀ L : V, Fintype.card {l : Fin N // L l = true} ≤ q →
          (fun p => decide (¬ ∃ l, I p l ∧ L l = true), L) ∉ U o) →
        ∀ (A B : Finset (Fin N)) (C : Finset (Fin N × Fin N)),
          (∀ e ∈ C, e.1 ∈ A ∧ e.2 ∈ B ∧ I e.1 e.2) →
          N < 5 * A.card → N < 5 * B.card → N * q < 10 * C.card →
          (∀ p ∈ A, 12 * q / 25 < (B.filter fun l => (p, l) ∈ C).card) →
          (∀ l ∈ B, 12 * q / 25 < (A.filter fun p => (p, l) ∈ C).card) →
          (∀ e ∈ C, ∃ k < s, U (m + k) ⊆ U o ∧ (atom e.1, atom e.2) ∈ U (m + k) ∧
            ∃ a < m + k, ∃ b < m + k, U (m + k) = U a ∩ U b ∧
              ¬ U a ⊆ U o ∧ ¬ U b ⊆ U o ∧
              (∀ P, U a ≠ P ×ˢ Set.univ) ∧ (∀ Q, U a ≠ Set.univ ×ˢ Q)) →
          False) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             have x14 : Set (Fin x2 × Fin x2) := {x14 : Fin x2 × Fin x2 | x3 x14.1 x14.2 ∧ ∃ x15 < x9, x11 (x12 + x15) ⊆ x11 x10 ∧ (x13 x14.1, x13 x14.2) ∈ x11 (x12 + x15) ∧ ∃ (x16 : ℕ) (x17 : ℕ), Max.max x16 x17 < x12 + x15 ∧ x11 (x12 + x15) = x11 x16 ∩ x11 x17 ∧ ∃ (x18 : Set (Fin x2 → Bool)) (x19 : Set (Fin x2 → Bool)), x11 x16 = x18 ×ˢ Set.univ ∧ x11 x17 = Set.univ ×ˢ x19};             x10 < x12 + x9 → (∀ (x16 : Fin x2), x11 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x11 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) → (∀ x17 < x9, ∃ (x19 : ℕ) (x20 : ℕ), Max.max x19 x20 < x12 + x17 ∧ x11 (x12 + x17) ∈ [x11 x19 ∪ x11 x20, x11 x19, ∅, x11 x19 ∩ x11 x20]) → (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x13 x18, x13 x19) ∈ x11 x10) → (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x11 x10) → x14.ncard ≤ (4 : ℕ) * x9 → ∀ (x21 : Finset (Fin x2 × Fin x2)), (∀ (x22 : Fin x2 × Fin x2), x22 ∈ x21 ↔ x3 x22.1 x22.2 ∧ x22 ∉ x14) → ∀ (x23 x24 : Finset (Fin x2)), x23.Nonempty → x24.Nonempty → (∀ x27 ∈ x23, (12 : ℕ) * x1 / (25 : ℕ) < {x29 ∈ x24 | (x27, x29) ∈ x21}.card) → (∀ x28 ∈ x24, (12 : ℕ) * x1 / (25 : ℕ) < {x30 ∈ x23 | (x30, x28) ∈ x21}.card) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I _ hq hN hDeg hUniq s o W
  dsimp only
  intro hOut hIn hGate hPos hNeg _ E hE A B hA hB hDegA hDegB
  let V := Fin N → Bool
  let m := N + N
  let atom : Fin N → Fin N → Bool := fun a b => decide (b = a)
  have hNpos : 0 < N := by omega
  -- Step 1: Dependency frontier gives m <= s + 1 and eliminates q < 200.
  have hChoice (i : Fin s) : ∃ a b : ℕ, a < m + i.val ∧ b < m + i.val ∧
      (W (m + i.val) = W a ∪ W b ∨ W (m + i.val) = W a ∨
        W (m + i.val) = ∅ ∨ W (m + i.val) = W a ∩ W b) := by
    obtain ⟨a, b, hmax, hmem⟩ := hGate i.val i.isLt
    obtain ⟨ha, hb⟩ := max_lt_iff.mp hmax
    exact ⟨a, b, ha, hb, by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hmem⟩
  choose fa fb hOp using hChoice
  have frontier (k : ℕ) (hk : k ≤ s) (T : Finset ℕ) (hT : ∀ w ∈ T, w < m + k) :
      ∃ S : Finset ℕ, S.card ≤ T.card + k ∧ (∀ w ∈ S, w < m) ∧
        ∀ x y : V × V, (∀ w ∈ S, x ∈ W w → y ∈ W w) → ∀ t ∈ T, x ∈ W t → y ∈ W t := by
    induction k generalizing T with
    | zero =>
      refine ⟨T, by simp, fun w hw => by simpa using hT w hw, fun x y h t ht => h t ht⟩
    | succ k ih =>
      let w := m + k
      by_cases hw : w ∈ T
      · let i : Fin s := ⟨k, by omega⟩
        obtain ⟨ha, hb, hop⟩ := hOp i
        let T' := insert (fa i) (insert (fb i) (T.erase w))
        have hT' : ∀ u ∈ T', u < m + k := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact ha
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact hb
          obtain ⟨hne, hin⟩ := Finset.mem_erase.mp hu
          have := hT u hin
          dsimp [w] at hne
          omega
        obtain ⟨S, hSc, hSm, hFlow⟩ := ih (by omega) T' hT'
        have hCard : T'.card ≤ T.card + 1 := by
          have c1 := Finset.card_insert_le (fa i) (insert (fb i) (T.erase w))
          have c2 := Finset.card_insert_le (fb i) (T.erase w)
          rw [Finset.card_erase_of_mem hw] at c2
          have hp := Finset.card_pos.mpr ⟨w, hw⟩
          dsimp [T']
          omega
        refine ⟨S, by omega, hSm, fun x y hs t ht hin => ?_⟩
        by_cases he : t = w
        · subst t
          have hA' := hFlow x y hs (fa i) (by simp [T'])
          have hB' := hFlow x y hs (fb i) (by simp [T'])
          rcases hop with h | h | h | h
          · rw [h] at hin ⊢; exact hin.imp hA' hB'
          · rw [h] at hin ⊢; exact hA' hin
          · rw [h] at hin; exact False.elim (Set.notMem_empty _ hin)
          · rw [h] at hin ⊢; exact ⟨hA' hin.1, hB' hin.2⟩
        · exact hFlow x y hs t (by simp [T', he, ht]) hin
      · have hT' : ∀ u ∈ T, u < m + k := by
          intro u hu
          have hn : u ≠ w := fun e => hw (e ▸ hu)
          have := hT u hu
          dsimp [w] at hn
          omega
        obtain ⟨S, hSc, hSm, hFlow⟩ := ih (by omega) T hT'
        exact ⟨S, by omega, hSm, hFlow⟩
  obtain ⟨S, hSc, hSm, hFlow⟩ := frontier s le_rfl {o} (by simpa using hOut)
  have preserve (bad : ℕ) (x y : V × V)
      (hp : ∀ p : Fin N, p.val ≠ bad → x.1 p = true → y.1 p = true)
      (hl : ∀ l : Fin N, N + l.val ≠ bad → x.2 l = true → y.2 l = true)
      (hNo : bad ∉ S) : x ∈ W o → y ∈ W o := by
    apply hFlow x y ?_ o (by simp)
    intro w hw hx
    have hn : w ≠ bad := fun he => hNo (he ▸ hw)
    have hb := hSm w hw
    by_cases hpw : w < N
    · let p : Fin N := ⟨w, hpw⟩
      rw [(hIn p).1] at hx ⊢
      exact hp p hn hx
    · let l : Fin N := ⟨w - N, by omega⟩
      have hL : N + l.val = w := by dsimp [l]; omega
      rw [← hL, (hIn l).2] at hx ⊢
      exact hl l (hL ▸ hn) hx
  have hPoint (p : Fin N) : ∃ l, I p l := by
    have hN2 : 1 < N := by nlinarith
    by_cases hp : p.val = 0
    · let r : Fin N := ⟨1, hN2⟩
      have hpr : p ≠ r := by
        intro he; have hv := congrArg Fin.val he; change p.val = 1 at hv; omega
      obtain ⟨l, h, _⟩ := hUniq p r hpr
      exact ⟨l, h.1⟩
    · let r : Fin N := ⟨0, hNpos⟩
      have hpr : p ≠ r := by
        intro he; have hv := congrArg Fin.val he; change p.val = 0 at hv; omega
      obtain ⟨l, h, _⟩ := hUniq p r hpr
      exact ⟨l, h.1⟩
  have hLine (l : Fin N) : ∃ p, I p l := by
    obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.mp (by rw [hDeg l]; omega : 0 < Fintype.card {p : Fin N // I p l})
    exact ⟨p, hp⟩
  have hCover : Finset.range m ⊆ S := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    by_contra hn
    by_cases hpk : k < N
    · let p : Fin N := ⟨k, hpk⟩
      obtain ⟨l, hpl⟩ := hPoint p
      let z : V := atom l
      have cardZ : Fintype.card {l' : Fin N // z l' = true} ≤ q := by
        simpa [z, atom] using (show 1 ≤ q by omega)
      apply hNeg z cardZ
      apply preserve k (atom p, z) (fun p' => decide (¬ ∃ l', I p' l' ∧ z l' = true), z)
        ?_ (fun _ _ h => h) hn (hPos p l hpl)
      intro p' hNot' hYes
      exact (hNot' (congrArg Fin.val (of_decide_eq_true hYes))).elim
    · let l : Fin N := ⟨k - N, by omega⟩
      obtain ⟨p, hpl⟩ := hLine l
      let z : V := fun _ => false
      have cardZ : Fintype.card {l' : Fin N // z l' = true} ≤ q := by simp [z]
      apply hNeg z cardZ
      apply preserve k (atom p, atom l) (fun p' => decide (¬ ∃ l', I p' l' ∧ z l' = true), z)
        (fun p' _ _ => by simp [z]) ?_ hn (hPos p l hpl)
      intro l' hNot' hYes
      have he : l' = l := of_decide_eq_true hYes
      subst l'
      exact (hNot' (by dsimp [l]; omega)).elim
  have hRaw := Finset.card_le_card hCover
  rw [Finset.card_range] at hRaw
  simp only [Finset.card_singleton] at hSc
  have hSize : m ≤ s + 1 := by omega
  by_cases hSmallQ : q < 200
  · have hUpper : N * q ≤ N * 199 := Nat.mul_le_mul_left N (by omega)
    have hBigN : 100 ≤ N := by nlinarith
    dsimp [m] at hSize
    omega
  have hq200 : 200 ≤ q := by omega
  by_contra! hSmallS
  -- Step 2: Normalize W to U with all wires nonempty and only binary union/inter gates.
  let zer : Fin N := ⟨0, hNpos⟩
  have hW_in_ne : ∀ i < m, W i ≠ ∅ := by
    intro i hi hEmp
    have zmem : ((fun _ : Fin N => true), (fun _ : Fin N => true)) ∈ W i := by
      by_cases h : i < N
      · let j : Fin N := ⟨i, h⟩
        change ((fun _ : Fin N => true), (fun _ : Fin N => true)) ∈ W j.val
        rw [(hIn j).1]; rfl
      · let j : Fin N := ⟨i - N, by dsimp [m] at hi; omega⟩
        have e : i = N + j.val := by dsimp [j]; omega
        rw [e, (hIn j).2]; rfl
    rw [hEmp] at zmem
    exact zmem
  have hW0_ne : W 0 ≠ ∅ := hW_in_ne 0 (by dsimp [m]; omega)
  have hWo_ne : W o ≠ ∅ := by
    obtain ⟨p, hp⟩ := hLine zer
    intro hEmp
    have := hPos p zer hp
    rw [hEmp] at this
    exact this
  have hNotW0 : ¬ W 0 ⊆ W o := by
    intro hSub
    have hmem : ((fun _ : Fin N => true), (fun _ : Fin N => false)) ∈ W 0 := by
      change ((fun _ : Fin N => true), (fun _ : Fin N => false)) ∈ W zer.val
      rw [(hIn zer).1]; rfl
    have hrej := hNeg (fun _ => false) (by simp)
    have hsame : (fun p : Fin N => decide (¬ ∃ l, I p l ∧ false = true)) = fun _ => true := by
      funext p; simp
    rw [hsame] at hrej
    exact hrej (hSub hmem)
  let U : ℕ → Set (V × V) := fun w => if W w = ∅ then W 0 else W w
  have hU_ne (w : ℕ) : U w ≠ ∅ := by
    by_cases h : W w = ∅
    · simp [U, h, hW0_ne]
    · simp [U, h]
  have hU_prim (i : ℕ) (hi : i < m) : U i = W i := by
    simp [U, hW_in_ne i hi]
  have hU_out : U o = W o := by
    simp [U, hWo_ne]
  have hU_in (p : Fin N) : U p.val = {z | z.1 p = true} ∧ U (N + p.val) = {z | z.2 p = true} := by
    rw [hU_prim p.val (by dsimp [m]; have := p.isLt; omega),
        hU_prim (N + p.val) (by dsimp [m]; have := p.isLt; omega)]
    exact hIn p
  have hU_gate (k : ℕ) (hk : k < s) :
      ∃ a < m + k, ∃ b < m + k, U (m + k) = U a ∪ U b ∨ U (m + k) = U a ∩ U b := by
    obtain ⟨a, b, hmax, hmem⟩ := hGate k hk
    obtain ⟨ha, hb⟩ := max_lt_iff.mp hmax
    have hop : W (m + k) = W a ∪ W b ∨ W (m + k) = W a ∨ W (m + k) = ∅ ∨ W (m + k) = W a ∩ W b := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hmem
    have h0 : 0 < m + k := by dsimp [m]; omega
    rcases hop with h | h | h | h
    · by_cases hae : W a = ∅
      · have heq : W (m + k) = W b := by rw [h, hae, Set.empty_union]
        refine ⟨b, hb, b, hb, Or.inl ?_⟩
        simp [U, heq]
      · by_cases hbe : W b = ∅
        · have heq : W (m + k) = W a := by rw [h, hbe, Set.union_empty]
          refine ⟨a, ha, a, ha, Or.inl ?_⟩
          simp [U, heq]
        · refine ⟨a, ha, b, hb, Or.inl ?_⟩
          have hne : W a ∪ W b ≠ ∅ := fun he =>
            hae (Set.subset_empty_iff.mp (he ▸ Set.subset_union_left))
          simp [U, h, hne, hae, hbe]
    · refine ⟨a, ha, a, ha, Or.inl ?_⟩
      simp [U, h]
    · refine ⟨0, h0, 0, h0, Or.inl ?_⟩
      simp [U, h]
    · by_cases hne : W (m + k) = ∅
      · refine ⟨0, h0, 0, h0, Or.inl ?_⟩
        simp [U, hne]
      · have hne' : W a ∩ W b ≠ ∅ := h ▸ hne
        have hae : W a ≠ ∅ := fun e => hne' (by rw [e, Set.empty_inter])
        have hbe : W b ≠ ∅ := fun e => hne' (by rw [e, Set.inter_empty])
        refine ⟨a, ha, b, hb, Or.inr ?_⟩
        simp [U, h, hne', hae, hbe]
  have hU_no_rect (p l : Fin N) (hNotR : (p, l) ∉ {x14 : Fin N × Fin N | I x14.1 x14.2 ∧ ∃ x15 < s, W (m + x15) ⊆ W o ∧ (atom x14.1, atom x14.2) ∈ W (m + x15) ∧ ∃ (x16 : ℕ) (x17 : ℕ), Max.max x16 x17 < m + x15 ∧ W (m + x15) = W x16 ∩ W x17 ∧ ∃ (x18 : Set V) (x19 : Set V), W x16 = x18 ×ˢ Set.univ ∧ W x17 = Set.univ ×ˢ x19})
      (hIpl : I p l) (k : ℕ) (hk : k < s) (hSub : U (m + k) ⊆ U o)
      (hMem : (atom p, atom l) ∈ U (m + k)) (a b : ℕ) (ha : a < m + k) (hb : b < m + k)
      (hEq : U (m + k) = U a ∩ U b) (P Q : Set V)
      (hP : U a = P ×ˢ Set.univ) (hQ : U b = Set.univ ×ˢ Q) : False := by
    apply hNotR
    have hWmk_ne : W (m + k) ≠ ∅ := by
      intro hEmp
      have : U (m + k) = W 0 := by simp [U, hEmp]
      rw [this, hU_out] at hSub
      exact hNotW0 hSub
    have hUmk : U (m + k) = W (m + k) := by simp [U, hWmk_ne]
    let a' := if W a = ∅ then 0 else a
    let b' := if W b = ∅ then 0 else b
    have h0 : 0 < m + k := by dsimp [m]; omega
    have ha' : a' < m + k := by by_cases h : W a = ∅ <;> simp [a', h, h0, ha]
    have hb' : b' < m + k := by by_cases h : W b = ∅ <;> simp [b', h, h0, hb]
    have hWa' : W a' = U a := by by_cases h : W a = ∅ <;> simp [a', U, h]
    have hWb' : W b' = U b := by by_cases h : W b = ∅ <;> simp [b', U, h]
    refine ⟨hIpl, k, hk, hU_out ▸ hUmk ▸ hSub, hUmk ▸ hMem, a', b',
      max_lt_iff.mpr ⟨ha', hb'⟩, ?_, P, Q, hWa'.trans hP, hWb'.trans hQ⟩
    rw [hWa', hWb', ← hEq, hUmk]
  -- Step 3: Monotonicity of U and soundness of U o on singletons and axes.
  have hU_mono (w : ℕ) (hw : w < m + s) :
      ∀ x y : V × V, (∀ p, x.1 p = true → y.1 p = true) →
        (∀ l, x.2 l = true → y.2 l = true) → x ∈ U w → y ∈ U w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro x y h1 h2 hx
      by_cases hlt : w < m
      · by_cases hp : w < N
        · let p : Fin N := ⟨w, hp⟩
          change x ∈ U p.val at hx
          change y ∈ U p.val
          rw [(hU_in p).1] at hx ⊢
          exact h1 p hx
        · let l : Fin N := ⟨w - N, by dsimp [m] at hlt; omega⟩
          have he : N + l.val = w := by dsimp [l]; omega
          rw [← he, (hU_in l).2] at hx ⊢
          exact h2 l hx
      · have he : m + (w - m) = w := by omega
        obtain ⟨a, ha, b, hb, hop⟩ := hU_gate (w - m) (by omega)
        rw [he] at ha hb hop
        rcases hop with h | h
        · rw [h] at hx ⊢
          exact hx.imp (ih a ha (by omega) x y h1 h2) (ih b hb (by omega) x y h1 h2)
        · rw [h] at hx ⊢
          exact ⟨ih a ha (by omega) x y h1 h2 hx.1, ih b hb (by omega) x y h1 h2 hx.2⟩
  -- Step 4: Expand the C4-free core (A, B, E) using coreExpansion.
  have hC4 : ∀ p p' l l' : Fin N,
      (p, l) ∈ E → (p, l') ∈ E → (p', l) ∈ E → (p', l') ∈ E → p = p' ∨ l = l' := by
    intro p p' l l' h1 h2 h3 h4
    by_cases hp : p = p'
    · exact Or.inl hp
    · exact Or.inr ((hUniq p p' hp).unique ⟨((hE _).mp h1).1, ((hE _).mp h3).1⟩
        ⟨((hE _).mp h2).1, ((hE _).mp h4).1⟩)
  let d := 12 * q / 25
  obtain ⟨hCardA, hCardB, hCardC⟩ := coreExpansion N d E A B hC4 hA hB hDegA hDegB
  let C := E.filter fun e => e.1 ∈ A ∧ e.2 ∈ B
  have hd_lo : 12 * q < 25 * (d + 1) := by
    dsimp [d]
    have := Nat.lt_div_mul_add (a := 12 * q) (b := 25) (by omega)
    omega
  have h5A : N < 5 * A.card := by
    have hA1 : d * (d + 1) + 1 ≤ A.card := hCardA
    nlinarith
  have h5B : N < 5 * B.card := by
    have hB1 : d * (d + 1) + 1 ≤ B.card := hCardB
    nlinarith
  have h10C : N * q < 10 * C.card := by
    have hC1 : (d + 1) * (d * (d + 1) + 1) ≤ C.card := hCardC
    have h1 : 12 * q * (12 * q) < 25 * (d + 1) * (25 * (d + 1)) :=
      Nat.mul_lt_mul'' hd_lo hd_lo
    have h2 : 12 * q ≤ 25 * d + 24 := by omega
    have h3 : (12 * q - 24) * (12 * q + 1) ≤ (25 * d) * (25 * d + 25) := by
      have ha' : 12 * q - 24 ≤ 25 * d := by omega
      have hb' : 12 * q + 1 ≤ 25 * d + 25 := by omega
      exact Nat.mul_le_mul ha' hb'
    have h4 : (25 * (d + 1)) * ((25 * d) * (25 * d + 25) + 625) =
        15625 * ((d + 1) * (d * (d + 1) + 1)) := by ring
    have h5 : (12 * q + 1) * ((12 * q - 24) * (12 * q + 1) + 625) ≤
        15625 * C.card := by
      have hsub := Nat.mul_le_mul (show 12 * q + 1 ≤ 25 * (d + 1) by omega)
        (Nat.add_le_add_right h3 625)
      rw [h4] at hsub
      exact hsub.trans (Nat.mul_le_mul_left 15625 hC1)
    have hqsub : 12 * q - 24 + 24 = 12 * q := by omega
    nlinarith
  have hC_mem : ∀ e ∈ C, e.1 ∈ A ∧ e.2 ∈ B ∧ I e.1 e.2 := by
    intro e he
    obtain ⟨heE, heA, heB⟩ := Finset.mem_filter.mp he
    exact ⟨heA, heB, ((hE e).mp heE).1⟩
  have hDegAC : ∀ p ∈ A, 12 * q / 25 < (B.filter fun l => (p, l) ∈ C).card := by
    intro p hp
    have hEqF : (B.filter fun l => (p, l) ∈ C) = (B.filter fun l => (p, l) ∈ E) := by
      ext l
      simp only [Finset.mem_filter, C]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hp, h.1⟩⟩
    rw [hEqF]; exact hDegA p hp
  have hDegBC : ∀ l ∈ B, 12 * q / 25 < (A.filter fun p => (p, l) ∈ C).card := by
    intro l hl
    have hEqF : (A.filter fun p => (p, l) ∈ C) = (A.filter fun p => (p, l) ∈ E) := by
      ext p
      simp only [Finset.mem_filter, C]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h.1, hl⟩⟩
    rw [hEqF]; exact hDegB l hl
  -- Step 5: Extract a minimal sound mixed-AND gate witness for every core edge.
  have hMixed : ∀ e ∈ C, ∃ k < s, U (m + k) ⊆ U o ∧ (atom e.1, atom e.2) ∈ U (m + k) ∧
      ∃ a < m + k, ∃ b < m + k, U (m + k) = U a ∩ U b ∧
        ¬ U a ⊆ U o ∧ ¬ U b ⊆ U o ∧
        (∀ P, U a ≠ P ×ˢ Set.univ) ∧ (∀ Q, U a ≠ Set.univ ×ˢ Q) := by
    rintro ⟨p, l⟩ heC
    obtain ⟨heE, _, _⟩ := Finset.mem_filter.mp heC
    obtain ⟨hIpl, hNotR⟩ := (hE (p, l)).mp heE
    have hEx : ∃ w, w < m + s ∧ U w ⊆ U o ∧ (atom p, atom l) ∈ U w :=
      ⟨o, hOut, le_rfl, hU_out.symm ▸ hPos p l hIpl⟩
    let w := Nat.find hEx
    have hwSpec : w < m + s ∧ U w ⊆ U o ∧ (atom p, atom l) ∈ U w := Nat.find_spec hEx
    have hwMin : ∀ u < w, ¬ (u < m + s ∧ U u ⊆ U o ∧ (atom p, atom l) ∈ U u) :=
      fun u hu => Nat.find_min hEx hu
    have hNotPt (x : V) : (x, fun _ : Fin N => false) ∉ U o := by
      intro hmem
      have htop : ((fun _ : Fin N => true), (fun _ : Fin N => false)) ∈ U o :=
        hU_mono o hOut _ _ (fun _ _ => rfl) (fun _ h => Bool.noConfusion h) hmem
      rw [hU_out] at htop
      have hrej := hNeg (fun _ => false) (by simp)
      have hsame : (fun p' : Fin N => decide (¬ ∃ l', I p' l' ∧ false = true)) = fun _ => true := by
        funext p'; simp
      rw [hsame] at hrej
      exact hrej htop
    have hNotLn : (fun p' => decide (¬ ∃ l', I p' l' ∧ atom l l' = true), atom l) ∉ U o := by
      rw [hU_out]
      exact hNeg (atom l) (by simpa [atom] using (show 1 ≤ q by omega))
    have hwGe : m ≤ w := by
      by_contra! hlt
      by_cases hp : w < N
      · let p' : Fin N := ⟨w, hp⟩
        have hmem : ((fun _ : Fin N => true), (fun _ : Fin N => false)) ∈ U w := by
          change _ ∈ U p'.val
          rw [(hU_in p').1]; rfl
        exact hNotPt (fun _ => true) (hwSpec.2.1 hmem)
      · let l' : Fin N := ⟨w - N, by dsimp [m] at hlt; omega⟩
        have hew : N + l'.val = w := by dsimp [l']; omega
        have h1 := hwSpec.2.2
        rw [← hew, (hU_in l').2] at h1
        have hmem : (fun p' => decide (¬ ∃ l'', I p' l'' ∧ atom l l'' = true), atom l) ∈ U w := by
          rw [← hew, (hU_in l').2]
          exact h1
        exact hNotLn (hwSpec.2.1 hmem)
    let k := w - m
    have hmk : m + k = w := by dsimp [k]; omega
    have hk : k < s := by dsimp [k]; omega
    obtain ⟨a, ha, b, hb, hop⟩ := hU_gate k hk
    rw [hmk] at ha hb hop
    have hInter : U w = U a ∩ U b := by
      rcases hop with hUnion | hInter
      · exfalso
        have hSubA : U a ⊆ U o := (hUnion ▸ Set.subset_union_left).trans hwSpec.2.1
        have hSubB : U b ⊆ U o := (hUnion ▸ Set.subset_union_right).trans hwSpec.2.1
        rw [hUnion] at hwSpec
        rcases hwSpec.2.2 with hInA | hInB
        · exact hwMin a ha ⟨by omega, hSubA, hInA⟩
        · exact hwMin b hb ⟨by omega, hSubB, hInB⟩
      · exact hInter
    have hMemA : (atom p, atom l) ∈ U a := (hInter ▸ hwSpec.2.2).1
    have hMemB : (atom p, atom l) ∈ U b := (hInter ▸ hwSpec.2.2).2
    have hNotSubA : ¬ U a ⊆ U o := fun h => hwMin a ha ⟨by omega, h, hMemA⟩
    have hNotSubB : ¬ U b ⊆ U o := fun h => hwMin b hb ⟨by omega, h, hMemB⟩
    have hOneMixed : ((∀ P, U a ≠ P ×ˢ Set.univ) ∧ (∀ Q, U a ≠ Set.univ ×ˢ Q)) ∨
        ((∀ P, U b ≠ P ×ˢ Set.univ) ∧ (∀ Q, U b ≠ Set.univ ×ˢ Q)) := by
      by_contra hBothPure
      push Not at hBothPure
      have hPureA : (∃ P, U a = P ×ˢ Set.univ) ∨ (∃ Q, U a = Set.univ ×ˢ Q) := by
        by_cases h1 : ∀ P, U a ≠ P ×ˢ Set.univ
        · exact Or.inr (hBothPure.1 h1)
        · push Not at h1; exact Or.inl h1
      have hPureB : (∃ P, U b = P ×ˢ Set.univ) ∨ (∃ Q, U b = Set.univ ×ˢ Q) := by
        by_cases h1 : ∀ P, U b ≠ P ×ˢ Set.univ
        · exact Or.inr (hBothPure.2 h1)
        · push Not at h1; exact Or.inl h1
      rcases hPureA with ⟨P1, hP1⟩ | ⟨Q1, hQ1⟩ <;> rcases hPureB with ⟨P2, hP2⟩ | ⟨Q2, hQ2⟩
      · have h1 : atom p ∈ P1 := by
          have := hP1 ▸ hMemA; exact this.1
        have h2 : atom p ∈ P2 := by
          have := hP2 ▸ hMemB; exact this.1
        have hZero : (atom p, fun _ : Fin N => false) ∈ U w := by
          rw [hInter, hP1, hP2]
          exact ⟨⟨h1, trivial⟩, ⟨h2, trivial⟩⟩
        exact hNotPt (atom p) (hwSpec.2.1 hZero)
      · exact hU_no_rect p l hNotR hIpl k hk (hmk.symm ▸ hwSpec.2.1) (hmk.symm ▸ hwSpec.2.2)
          a b (hmk.symm ▸ ha) (hmk.symm ▸ hb) (hmk.symm ▸ hInter) P1 Q2 hP1 hQ2
      · exact hU_no_rect p l hNotR hIpl k hk (hmk.symm ▸ hwSpec.2.1) (hmk.symm ▸ hwSpec.2.2)
          b a (hmk.symm ▸ hb) (hmk.symm ▸ ha) (hmk.symm ▸ (hInter.trans (Set.inter_comm _ _)))
          P2 Q1 hP2 hQ1
      · have h1 : atom l ∈ Q1 := by
          have := hQ1 ▸ hMemA; exact this.2
        have h2 : atom l ∈ Q2 := by
          have := hQ2 ▸ hMemB; exact this.2
        have hNegIn : (fun p' => decide (¬ ∃ l', I p' l' ∧ atom l l' = true), atom l) ∈ U w := by
          rw [hInter, hQ1, hQ2]
          exact ⟨⟨trivial, h1⟩, ⟨trivial, h2⟩⟩
        exact hNotLn (hwSpec.2.1 hNegIn)
    rcases hOneMixed with ⟨hAP, hAQ⟩ | ⟨hBP, hBQ⟩
    · exact ⟨k, hk, hmk.symm ▸ hwSpec.2.1, hmk.symm ▸ hwSpec.2.2,
        a, hmk.symm ▸ ha, b, hmk.symm ▸ hb, hmk.symm ▸ hInter, hNotSubA, hNotSubB, hAP, hAQ⟩
    · exact ⟨k, hk, hmk.symm ▸ hwSpec.2.1, hmk.symm ▸ hwSpec.2.2,
        b, hmk.symm ▸ hb, a, hmk.symm ▸ ha, hmk.symm ▸ (hInter.trans (Set.inter_comm _ _)),
        hNotSubB, hNotSubA, hBP, hBQ⟩
  exact mixedCoreLower q N I hq200 hN hDeg hUniq s o U hOut hSize hSmallS hU_ne hU_in hU_gate
    (fun p l h => hU_out.symm ▸ hPos p l h) (fun L hL => hU_out.symm ▸ hNeg L hL)
    A B C hC_mem h5A h5B h10C hDegAC hDegBC hMixed
