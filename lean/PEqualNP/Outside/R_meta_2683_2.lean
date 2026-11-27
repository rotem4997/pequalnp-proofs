import Mathlib

-- The output depends on every input cofactor, so its last gate cannot read a raw variable.
-- Trimming the unused suffix preserves source indices and the signed-wire budget.
theorem PEqualNP.Outside.R_meta_2683_2 :
  (let f := fun (x : Fin 9 → Bool) =>
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
        (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).foldl
        (fun t e => t || (x e.1 && x e.2)) false
    ∀ (i : Fin 9) (b : Bool),
      f (fun j => decide (j = i) && b) = false ∧ f (fun j => !(decide (j = i)) || b) = true) →
  (∀ f : (Fin 9 → Bool) → Bool, (∀ (i : Fin 9) (b : Bool),
      f (fun j => decide (j = i) && b) = false ∧ f (fun j => !(decide (j = i)) || b) = true) →
    ∀ (n : ℕ) (op : Fin n → Bool) (a b : Fin n → ℕ × Bool) (out : ℕ × Bool)
        (w : (Fin 9 → Bool) → ℕ → Bool),
      out.1 < 10 + n → (∀ (x : Fin 9 → Bool) (i : Fin 9), w x i.val = x i) → (∀ x : Fin 9 → Bool, w x 9 = false) →
      (∀ (x : Fin 9 → Bool) (i : Fin n), let v := fun (p : ℕ × Bool) => w x p.1 ^^ p.2;
      w x (10 + i.val) = if op i = true then v (a i) && v (b i) else v (a i) || v (b i)) →
      (∀ x, (w x out.1 ^^ out.2) = f x) →
      ∃ j : Fin n, out.1 = 10 + j.val ∧ 9 ≤ (a j).1 ∧ 9 ≤ (b j).1) →
  (let f := fun (x : Fin 9 → Bool) =>
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
        (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).foldl
        (fun t e => t || (x e.1 && x e.2)) false
    ∀ (m : ℕ) (op : Fin (m + 1) → Bool) (a b : Fin (m + 1) → ℕ × Bool)
        (neg : Bool) (S : Finset ℕ) (w : (Fin 9 → Bool) → ℕ → Bool),
      S.card ≤ 3 → m + 1 + S.card ≤ 14 →
      (∀ i, (a i).1 < 10 + i.val ∧ (b i).1 < 10 + i.val) →
      (let allowed := fun (p : ℕ × Bool) => p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ S;
        allowed (10 + m, neg) ∧ ∀ i, allowed (a i) ∧ allowed (b i)) →
      (∀ (x : Fin 9 → Bool) (i : Fin 9), w x i.val = x i) → (∀ x : Fin 9 → Bool, w x 9 = false) →
      (∀ (x : Fin 9 → Bool) (i : Fin (m + 1)), let v := fun (p : ℕ × Bool) => w x p.1 ^^ p.2;
      w x (10 + i.val) = if op i = true then v (a i) && v (b i) else v (a i) || v (b i)) →
      9 ≤ (a (Fin.last m)).1 → 9 ≤ (b (Fin.last m)).1 →
      ¬ ∀ x, (w x (10 + m) ^^ neg) = f x) →
  ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x6.card ≤ (3 : ℕ) →     x1 + x6.card ≤ (14 : ℕ) →       (∀ (x10 : Fin x1), (x3 x10).1 < (10 : ℕ) + ↑x10 ∧ (x4 x10).1 < (10 : ℕ) + ↑x10) →         x5.1 < (10 : ℕ) + x1 →           (have x12 : ℕ × Bool → Prop := fun (x12 : ℕ × Bool) => x12.2 = Bool.true → x12.1 = (0 : ℕ) ∨ x12.1 = (9 : ℕ) ∨ x12.1 ∈ x6;             x12 x5 ∧ ∀ (x13 : Fin x1), x12 (x3 x13) ∧ x12 (x4 x13)) →             (∀ (x13 : Fin (9 : ℕ) → Bool) (x14 : Fin (9 : ℕ)), x7 x13 ↑x14 = x13 x14) →               (∀ (x14 : Fin (9 : ℕ) → Bool), x7 x14 (9 : ℕ) = Bool.false) →                 (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin x1),                     have x17 : ℕ × Bool → Bool := fun (x17 : ℕ × Bool) => x7 x15 x17.1 ^^ x17.2;                     x7 x15 ((10 : ℕ) + ↑x16) = if x2 x16 = Bool.true then x17 (x3 x16) && x17 (x4 x16) else x17 (x3 x16) || x17 (x4 x16)) →                   ∃ (x16 : Fin (9 : ℕ) → Bool), (x7 x16 x5.1 ^^ x5.2) ≠ (x16 (0 : Fin (9 : ℕ)) && x16 (1 : Fin (9 : ℕ)) || x16 (1 : Fin (9 : ℕ)) && x16 (2 : Fin (9 : ℕ)) || x16 (2 : Fin (9 : ℕ)) && x16 (3 : Fin (9 : ℕ)) || x16 (3 : Fin (9 : ℕ)) && x16 (4 : Fin (9 : ℕ)) || x16 (4 : Fin (9 : ℕ)) && x16 (0 : Fin (9 : ℕ)) || x16 (0 : Fin (9 : ℕ)) && x16 (5 : Fin (9 : ℕ)) || x16 (1 : Fin (9 : ℕ)) && x16 (6 : Fin (9 : ℕ)) || x16 (2 : Fin (9 : ℕ)) && x16 (7 : Fin (9 : ℕ)) || x16 (3 : Fin (9 : ℕ)) && x16 (8 : Fin (9 : ℕ)) || x16 (5 : Fin (9 : ℕ)) && x16 (7 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ)) && x16 (8 : Fin (9 : ℕ)) || x16 (8 : Fin (9 : ℕ)) && x16 (5 : Fin (9 : ℕ))) := by
  intro nonconstant locate exclude n op a b out S w signs budget reads output allowed inputs constant gates
  by_contra failed
  let f := fun (x : Fin 9 → Bool) =>
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
        (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).foldl
        (fun t e => t || (x e.1 && x e.2)) false
  have correct (x : Fin 9 → Bool) : (w x out.1 ^^ out.2) = f x := by
    by_contra different
    exact failed ⟨x, different⟩
  obtain ⟨j, houtput, hleft, hright⟩ := locate f nonconstant n op a b out w output inputs constant gates correct
  let trim (i : Fin (j.val + 1)) : Fin n := ⟨i.val, i.isLt.trans_le (Nat.succ_le_of_lt j.isLt)⟩
  have last : trim (Fin.last j.val) = j := Fin.ext rfl
  refine exclude j.val (op ∘ trim) (a ∘ trim) (b ∘ trim) out.2 S w signs (by omega)
    (fun i => reads (trim i)) ?_ inputs constant (fun x i => gates x (trim i))
    ?_ ?_ (fun x => ?_)
  · exact ⟨houtput ▸ allowed.1, fun i => allowed.2 (trim i)⟩
  · simpa only [Function.comp_apply, last] using hleft
  · simpa only [Function.comp_apply, last] using hright
  · simpa only [← houtput] using correct x
