import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3332_aux

def probe (i : Fin 9) (b high : Bool) (j : Fin 9) : Bool :=
  if high then !decide (j = i) || b else decide (j = i) && b

lemma probe_at (i : Fin 9) (b high : Bool) : probe i b high i = b := by
  cases high <;> simp [probe]

lemma probe_eval (f : (Fin 9 → Bool) → Bool)
    (h : ∀ (i : Fin 9) (b : Bool),
      f (fun j => decide (j = i) && b) = false ∧
        f (fun j => !decide (j = i) || b) = true)
    (i : Fin 9) (b high : Bool) : f (probe i b high) = high := by
  cases high
  · exact (h i b).1
  · exact (h i b).2

lemma force (isAnd w : Bool) :
    (if isAnd = true then !isAnd && w else !isAnd || w) = !isAnd ∧
      (if isAnd = true then w && !isAnd else w || !isAnd) = !isAnd := by
  cases isAnd <;> cases w <;> decide

lemma xor_twice (b s : Bool) : (b ^^ s ^^ s) = b := by
  cases b <;> cases s <;> decide

lemma ne_not (b : Bool) : b ≠ !b := by
  cases b <;> decide

end PEqualNP.Outside.L_meta_3332_aux

open PEqualNP.Outside.L_meta_3332_aux

theorem PEqualNP.Outside.L_meta_3332 :
    ∀ (x1 : (Fin (9 : ℕ) → Bool) → Bool),   (∀ (x2 : Fin (9 : ℕ)) (x3 : Bool), (x1 fun (x4 : Fin (9 : ℕ)) => Decidable.decide (x4 = x2) && x3) = Bool.false ∧ (x1 fun (x4 : Fin (9 : ℕ)) => !Decidable.decide (x4 = x2) || x3) = Bool.true) →     ∀ (x3 : ℕ) (x4 : Fin x3 → Bool) (x5 x6 : Fin x3 → ℕ × Bool) (x7 : ℕ × Bool) (x8 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),       x7.1 < (10 : ℕ) + x3 →         (∀ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ)), x8 x10 ↑x11 = x10 x11) →           (∀ (x11 : Fin (9 : ℕ) → Bool), x8 x11 (9 : ℕ) = Bool.false) →             (∀ (x12 : Fin (9 : ℕ) → Bool) (x13 : Fin x3),                 have x14 : ℕ × Bool → Bool := fun (x14 : ℕ × Bool) => x8 x12 x14.1 ^^ x14.2;                 x8 x12 ((10 : ℕ) + ↑x13) = if x4 x13 = Bool.true then x14 (x5 x13) && x14 (x6 x13) else x14 (x5 x13) || x14 (x6 x13)) →               (∀ (x13 : Fin (9 : ℕ) → Bool), (x8 x13 x7.1 ^^ x7.2) = x1 x13) → ∃ (x14 : Fin x3), x7.1 = (10 : ℕ) + ↑x14 ∧ (9 : ℕ) ≤ (x5 x14).1 ∧ (9 : ℕ) ≤ (x6 x14).1 := by
  intro f small k ops left right out wire hout raw constant gates computes
  by_cases hraw : out.1 < 9
  · let i : Fin 9 := ⟨out.1, hraw⟩
    let x := probe i false (!out.2)
    have hw : wire x out.1 = false := (raw x i).trans (probe_at i false (!out.2))
    have hf : f x = !out.2 := probe_eval f small i false _
    have he := computes x
    rw [hw, hf] at he
    exact (ne_not out.2 (by simpa only [Bool.false_xor] using he)).elim
  by_cases hz : out.1 = 9
  · let x := probe 0 false (!out.2)
    have hf : f x = !out.2 := probe_eval f small 0 false _
    have he := computes x
    rw [hz, constant, hf] at he
    exact (ne_not out.2 (by simpa only [Bool.false_xor] using he)).elim
  let i : Fin k := ⟨out.1 - 10, by omega⟩
  have ho : out.1 = 10 + i.val := by
    dsimp only [i]
    omega
  have exclude (p : ℕ × Bool) (hp : p = left i ∨ p = right i) : 9 ≤ p.1 := by
    by_contra! hlt
    let v : Fin 9 := ⟨p.1, hlt⟩
    let forced := !ops i
    let x := probe v (forced ^^ p.2) (!(forced ^^ out.2))
    have hw : (wire x p.1 ^^ p.2) = forced := by
      have he : wire x p.1 = (forced ^^ p.2) :=
        (raw x v).trans (probe_at v _ _)
      rw [he]
      exact xor_twice forced p.2
    have hg := gates x i
    change wire x (10 + i.val) =
      (if ops i = true then (wire x (left i).1 ^^ (left i).2) && (wire x (right i).1 ^^ (right i).2)
        else (wire x (left i).1 ^^ (left i).2) || (wire x (right i).1 ^^ (right i).2)) at hg
    have hgate : wire x (10 + i.val) = forced := by
      rcases hp with hr | hr
      · rw [hr] at hw
        rw [hg, hw]
        exact (force (ops i) _).1
      · rw [hr] at hw
        rw [hg, hw]
        exact (force (ops i) _).2
    have hf : f x = !(forced ^^ out.2) := probe_eval f small v _ _
    have he := computes x
    rw [ho, hgate, hf] at he
    exact ne_not _ he
  exact ⟨i, ho, exclude (left i) (Or.inl rfl), exclude (right i) (Or.inr rfl)⟩
