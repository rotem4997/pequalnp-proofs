import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7830

def Adj (a b : Fin 13) : Prop := a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9

def opp (f : Fin 13 → Bool) (j : Fin 13) : Bool := !(f j || f (j + 1) || f (j + 3) || f (j + 9))

def acc (x : Fin 26 → Bool) : Prop :=
  ∃ a b : Fin 13, Adj a b ∧ x (Fin.castAdd 13 a) = true ∧ x (Fin.natAdd 13 b) = true

lemma opp_true_iff (f : Fin 13 → Bool) (j : Fin 13) :
    opp f j = true ↔ ∀ a, Adj a j → f a = false := by
  unfold opp Adj
  constructor
  · intro h a ha
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at h
    obtain ⟨⟨⟨h0, h1⟩, h3⟩, h9⟩ := h
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  · intro h
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff]
    exact ⟨⟨⟨h _ (Or.inl rfl), h _ (Or.inr (Or.inl rfl))⟩, h _ (Or.inr (Or.inr (Or.inl rfl)))⟩,
      h _ (Or.inr (Or.inr (Or.inr rfl)))⟩

lemma le_of_true_imp {a b : Bool} (h : a = true → b = true) : a ≤ b := by
  cases a <;> cases b <;> simp_all

lemma true_of_le {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  subst a
  cases b with
  | false => exact False.elim ((by decide : ¬ (true ≤ false)) h)
  | true => rfl

lemma main (x : Fin 26 → Bool) (hmax : Maximal (fun z => ¬ acc z) x) :
    ∃ x6 : Fin 13 → Bool, x = Fin.append x6 (opp x6) ∧
      ∀ a, x6 a = false → ∃ b, Adj a b ∧ opp x6 b = true := by
  obtain ⟨x6, y, rfl⟩ : ∃ (x6 : Fin 13 → Bool) (y : Fin 13 → Bool), x = Fin.append x6 y := by
    refine ⟨fun a => x (Fin.castAdd 13 a), fun b => x (Fin.natAdd 13 b), ?_⟩
    funext i
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
    · intro a; rw [Fin.append_left]
    · intro b; rw [Fin.append_right]
  obtain ⟨hna, hmx⟩ := hmax
  have hy : ∀ b, y b = true → opp x6 b = true := by
    intro b hb
    rw [opp_true_iff]
    intro a hab
    by_contra h
    apply hna
    refine ⟨a, b, hab, ?_, ?_⟩
    · simp only [Fin.append_left]; simpa using h
    · simp only [Fin.append_right]; exact hb
  have hz : ¬ acc (Fin.append x6 (opp x6)) := by
    rintro ⟨a, b, hab, ha, hb⟩
    simp only [Fin.append_left, Fin.append_right] at ha hb
    rw [opp_true_iff] at hb
    rw [hb a hab] at ha
    exact Bool.false_ne_true ha
  have hle : Fin.append x6 y ≤ Fin.append x6 (opp x6) := by
    intro i
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
    · intro a; simp only [Fin.append_left]; exact le_refl _
    · intro b; simp only [Fin.append_right]; exact le_of_true_imp (hy b)
  have hge := hmx hz hle
  have hyeq : y = opp x6 := by
    funext b
    apply le_antisymm (le_of_true_imp (hy b))
    have := hge (Fin.natAdd 13 b)
    simpa only [Fin.append_right] using this
  subst hyeq
  refine ⟨x6, rfl, ?_⟩
  intro a ha
  by_contra hno
  push_neg at hno
  have hacc : ¬ acc (Fin.append (Function.update x6 a true) (opp x6)) := by
    rintro ⟨u, b, hub, hu, hb⟩
    simp only [Fin.append_left, Fin.append_right] at hu hb
    by_cases hua : u = a
    · subst hua
      exact hno b hub hb
    · rw [Function.update_of_ne hua] at hu
      exact hz ⟨u, b, hub, by simpa only [Fin.append_left] using hu,
        by simpa only [Fin.append_right] using hb⟩
  have hle2 : Fin.append x6 (opp x6) ≤ Fin.append (Function.update x6 a true) (opp x6) := by
    intro i
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
    · intro c
      simp only [Fin.append_left]
      by_cases hca : c = a
      · subst hca
        rw [Function.update_self]
        exact le_top
      · rw [Function.update_of_ne hca]
    · intro b; simp only [Fin.append_right]; exact le_refl _
  have h3 := hmx hacc hle2 (Fin.castAdd 13 a)
  simp only [Fin.append_left, Function.update_self] at h3
  rw [ha] at h3
  exact Bool.false_ne_true (true_of_le h3 rfl)

end PEqualNP.Outside.L_meta_7830

open PEqualNP.Outside.L_meta_7830 in
theorem PEqualNP.Outside.L_meta_7830 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); have x3 : (Fin (26 : ℕ) → Bool) → Prop := fun (x3 : Fin (26 : ℕ) → Bool) => ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true; ∀ (x4 : Fin (26 : ℕ) → Bool), Maximal (fun (x5 : Fin (26 : ℕ) → Bool) => ¬x3 x5) x4 → ∃ (x6 : Fin (13 : ℕ) → Bool), x4 = Fin.append x6 (x2 x6) ∧ ∀ (x7 : Fin (13 : ℕ)), x6 x7 = Bool.false → ∃ (x9 : Fin (13 : ℕ)), x1 x7 x9 ∧ x2 x6 x9 = Bool.true := by
  exact main
