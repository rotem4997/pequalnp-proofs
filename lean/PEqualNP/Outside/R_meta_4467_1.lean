import Mathlib.Data.Set.Card
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4467_1
    (sensitive : ∀ (n : ℕ) (G : Finset (Finset (Fin (n + n)))) (t : Bool) (u : Fin n → Bool),
      let row : Bool → List Bool := fun b =>
        if t = true then List.ofFn u ++ List.replicate n b else List.replicate n b ++ List.ofFn u
      let sat : Bool → Prop := fun b => ∀ A ∈ G, ∃ i ∈ A, (row b).getD i.val false = true
      ¬ (sat false ↔ sat true) → ∃ A ∈ G, (∀ B ∈ G, B ⊆ A → B = A) ∧
          ∃ i ∈ A, (if t = true then n ≤ i.val else i.val < n))
    (counting :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 x6 : ℕ) (x7 : ℕ → Finset (Finset (Fin (x2 + x2)))),
      (∃ j < x5, ∃ a b : ℕ, a < b ∧ b < x2 + x2 + j ∧ x7 (x2 + x2 + j) = x7 a ∪ x7 b ∧
        ∃ t : Bool, ∀ w ∈ [a, b], ∃ A ∈ x7 w, (∀ B ∈ x7 w, B ⊆ A → B = A) ∧
          ∃ i ∈ A, (if t = true then x2 ≤ i.val else i.val < x2)) →
      (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
  (∀ x11 : Fin x2, Fintype.card { x12 : Fin x2 // x3 x12 x11 } = x1 + (1 : ℕ)) →
  (∀ x12 x13 : Fin x2, x12 ≠ x13 → ∃! x15 : Fin x2, x3 x12 x15 ∧ x3 x13 x15) →
  (3 : ℕ) * x2 ≤ x5 + (1 : ℕ) → x6 < x2 + x2 + x5 →
  (∀ x15 : Fin (x2 + x2), x7 ↑x15 = {{x15}}) →
  (∀ x16 < x5, ∃ x18 x19 : ℕ, x18 < x19 ∧ x19 < x2 + x2 + x16 ∧
    (x7 (x2 + x2 + x16) = x7 x18 ∪ x7 x19 ∨ x7 (x2 + x2 + x16) =
    (x7 x18).biUnion fun x20 : Finset (Fin (x2 + x2)) => Finset.image (fun x21 : Finset (Fin (x2 + x2)) => x20 ∪ x21) (x7 x19))) →
  (∀ x17 ∈ x7 x6, ∀ x19 x20 : Fin x2, x3 x19 x20 → Fin.castAdd x2 x19 ∈ x17 ∨ Fin.natAdd x2 x20 ∈ x17) →
  (∀ x18 : Finset (Fin x2), x18.card ≤ x1 → ∃ x20 ∈ x7 x6, (∀ x21 : Fin x2, Fin.castAdd x2 x21 ∈ x20 ↔ ∃ x22 ∈ x18, x3 x21 x22) ∧ ∀ x21 : Fin x2, Fin.natAdd x2 x21 ∈ x20 ↔ x21 ∉ x18) →
  x2 * x1 ≤ (100 : ℕ) * x5) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 x6 : ℕ) (x7 : ℕ → Finset (Finset (Fin (x2 + x2)))),
  (∃ x8 < x5, ∃ (x9 : ℕ) (x10 : ℕ), x9 < x10 ∧ x10 < x2 + x2 + x8 ∧
    x7 (x2 + x2 + x8) = x7 x9 ∪ x7 x10 ∧ ∃ x11 : Bool, ∀ x12 ∈ [x9, x10],
    ∃ x14 : Fin x2 → Bool,
      have x15 : Bool → List Bool := fun x15 => if x11 = Bool.true then List.ofFn x14 ++ List.replicate x2 x15 else List.replicate x2 x15 ++ List.ofFn x14
      have x16 : Bool → Prop := fun x16 => ∀ x17 ∈ x7 x12, ∃ x19 ∈ x17, (x15 x16).getD (↑x19) Bool.false = Bool.true
      ¬ (x16 Bool.false ↔ x16 Bool.true)) →
  (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
  (∀ x11 : Fin x2, Fintype.card { x12 : Fin x2 // x3 x12 x11 } = x1 + (1 : ℕ)) →
  (∀ x12 x13 : Fin x2, x12 ≠ x13 → ∃! x15 : Fin x2, x3 x12 x15 ∧ x3 x13 x15) →
  (3 : ℕ) * x2 ≤ x5 + (1 : ℕ) → x6 < x2 + x2 + x5 →
  (∀ x15 : Fin (x2 + x2), x7 ↑x15 = {{x15}}) →
  (∀ x16 < x5, ∃ x18 x19 : ℕ, x18 < x19 ∧ x19 < x2 + x2 + x16 ∧
    (x7 (x2 + x2 + x16) = x7 x18 ∪ x7 x19 ∨ x7 (x2 + x2 + x16) =
    (x7 x18).biUnion fun x20 : Finset (Fin (x2 + x2)) => Finset.image (fun x21 : Finset (Fin (x2 + x2)) => x20 ∪ x21) (x7 x19))) →
  (∀ x17 ∈ x7 x6, ∀ x19 x20 : Fin x2, x3 x19 x20 → Fin.castAdd x2 x19 ∈ x17 ∨ Fin.natAdd x2 x20 ∈ x17) →
  (∀ x18 : Finset (Fin x2), x18.card ≤ x1 → ∃ x20 ∈ x7 x6, (∀ x21 : Fin x2, Fin.castAdd x2 x21 ∈ x20 ↔ ∃ x22 ∈ x18, x3 x21 x22) ∧ ∀ x21 : Fin x2, Fin.natAdd x2 x21 ∈ x20 ↔ x21 ∉ x18) →
  x2 * x1 ≤ (100 : ℕ) * x5 := by
  intro q n I dec s out F hmixed
  obtain ⟨j, hj, a, b, hab, hb, hg, t, ht⟩ := hmixed
  exact counting q n I s out F (by
    refine ⟨j, hj, a, b, hab, hb, hg, t, ?_⟩
    intro w hw
    obtain ⟨u, hu⟩ := ht w hw
    exact sensitive n (F w) t u hu)
