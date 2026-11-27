import PEqualNP.Defs

-- The line-star cover and density formulation follow PR #6838.
theorem PEqualNP.Outside.R_meta_3364_67
    (stars : ∀ (q N s : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      N ≤ s → N * (q + 1) ≤ 100 * s →
      ∃ (P L : Fin s → Finset (Fin N)),
        (∀ i p, p ∈ P i → ∀ l, l ∈ L i → I p l) ∧
        (∀ p l, I p l → ∃ i, p ∈ P i ∧ l ∈ L i) ∧
        ∑ i, ((P i).card + (L i).card) ≤ 100 * s + N)
    (floorBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      let U := Fin N → Bool
      let e := fun p r : Fin N => decide (r = p)
      100 < q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (M : Finset ℕ) (W : ℕ → Set (U × U)),
        o < N + N + s →
        (∀ p : Fin N, W p.val = {x | x.1 p = true} ∧ W (N + p.val) = {x | x.2 p = true}) →
        (∀ i < s, ∃ a < N + N + i, ∃ b < N + N + i,
          let z := W (N + N + i)
          z ∈ [W a ∪ W b, W a, ∅] ∨
            z = W a ∩ W b ∧ (i ∈ M ∨ ∃ P L : Set U, W a = P ×ˢ Set.univ ∧ W b = Set.univ ×ˢ L)) →
        (∀ p l, I p l → (e p, e l) ∈ W o) →
        (∀ y : U, Fintype.card {l : Fin N // y l = true} ≤ q →
          (fun p => decide (¬ ∃ l, I p l ∧ y l = true), y) ∉ W o) →
        3 * N ≤ s + 1)
    (density : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      let U := Fin N → Bool
      let e := fun p r : Fin N => decide (r = p)
      299 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (M : Finset ℕ) (W : ℕ → Set (U × U)),
        o < N + N + s →
        (∀ p : Fin N, W p.val = {x | x.1 p = true} ∧ W (N + p.val) = {x | x.2 p = true}) →
        (∀ i < s, ∃ a < N + N + i, ∃ b < N + N + i,
          let z := W (N + N + i)
          z ∈ [W a ∪ W b, W a, ∅] ∨
            z = W a ∩ W b ∧ (i ∈ M ∨ ∃ P L : Set U, W a = P ×ˢ Set.univ ∧ W b = Set.univ ×ˢ L)) →
        (∀ p l, I p l → (e p, e l) ∈ W o) →
        (∀ y : U, Fintype.card {l : Fin N // y l = true} ≤ q →
          (fun p => decide (¬ ∃ l, I p l ∧ y l = true), y) ∉ W o) →
        100 * M.card < N * q → N * (q + 1) ≤ 100 * s) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → ∃ (x19 : Fin x9 → Finset (Fin x2)) (x20 : Fin x9 → Finset (Fin x2)), (∀ (x21 : Fin x9), ∀ x22 ∈ x19 x21, ∀ x24 ∈ x20 x21, x3 x22 x24) ∧ (∀ (x21 x22 : Fin x2), x3 x21 x22 → ∃ (x24 : Fin x9), x21 ∈ x19 x24 ∧ x22 ∈ x20 x24) ∧ ∑ x21 : Fin x9, ((x19 x21).card + (x20 x21).card) ≤ (100 : ℕ) * x9 + x2 := by
  classical
  intro q N I _ hq hN col unique s o M W bound raw step pos neg marks
  have gates : ∀ i < s, ∃ a < N+N+i, ∃ b < N+N+i, W (N+N+i) ∈ [W a ∪ W b,W a,∅] ∨ W (N+N+i)=W a ∩ W b ∧ (i∈M ∨ ∃ P L, W a=P ×ˢ Set.univ ∧ W b=Set.univ ×ˢ L) := by
    intro i hi
    obtain ⟨a,ha,b,hb,gate⟩ := step i hi
    exact ⟨a,ha,b,hb,by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] using gate⟩
  have lower := floorBound q N I hq hN col unique s o M W bound raw gates pos neg
  apply stars q N s I col (by omega)
  by_cases small : q≤298
  · have bigN : 100 ≤ N := by omega
    have scale := Nat.mul_le_mul_left N (show q+1≤299 by omega)
    omega
  · exact density q N I (by omega) hN col unique s o M W bound raw gates pos neg marks
