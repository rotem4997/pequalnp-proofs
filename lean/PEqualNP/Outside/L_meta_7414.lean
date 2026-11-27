import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7414_aux

def step (S : Finset ℕ) (t : ℕ × ℕ × ℕ) : Finset ℕ :=
  Insert.insert t.2.1 (Insert.insert t.2.2 (S.erase t.1))

theorem aux (A : List ℕ) : ∀ (L : List (ℕ × ℕ × ℕ)) (S : Finset ℕ),
    (∀ i : Fin L.length, (L.get i).1 ∈ List.foldl step S (List.take i L) ∧
      ((L.get i).1 = (L.get i).2.1 &&& (L.get i).2.2 ∨ (L.get i).1 = (L.get i).2.1 ||| (L.get i).2.2)) →
    (∀ x ∈ List.foldl step S L, x ∈ A) →
    (List.foldl step S L).card ≤ S.card + L.length ∧ ∃ R : List ℕ, R.length ≤ L.length ∧
      (∀ i : Fin R.length, ∃ p ∈ A ++ List.take i R, ∃ q ∈ A ++ List.take i R,
        R.get i = p &&& q ∨ R.get i = p ||| q) ∧ ∀ x ∈ S, x ∈ A ++ R := by
  intro L
  induction L with
  | nil =>
    intro S _ h2
    exact ⟨by simp, [], by simp, fun i => i.elim0, fun x hx => by simpa using h2 x (by simpa using hx)⟩
  | cons t tl ih =>
    intro S h1 h2
    have h0 := h1 ⟨0, by simp⟩
    have hmem : t.1 ∈ S := by simpa using h0.1
    have hop : t.1 = t.2.1 &&& t.2.2 ∨ t.1 = t.2.1 ||| t.2.2 := by simpa using h0.2
    obtain ⟨hc, R, hRl, hR3, hRS⟩ := ih (step S t) (fun i => by
      have := h1 ⟨i.1 + 1, by simp⟩
      simpa using this) (by simpa using h2)
    have hb : t.2.1 ∈ A ++ R := hRS _ (by unfold step; simp)
    have hcc : t.2.2 ∈ A ++ R := hRS _ (by unfold step; simp)
    refine ⟨?_, R ++ [t.1], by simp; omega, ?_, ?_⟩
    · have : (step S t).card ≤ S.card + 1 := by
        unfold step
        have e := Finset.card_erase_of_mem hmem
        have p := Finset.card_pos.mpr ⟨_, hmem⟩
        have a1 := Finset.card_insert_le t.2.1 (insert t.2.2 (S.erase t.1))
        have a2 := Finset.card_insert_le t.2.2 (S.erase t.1)
        omega
      simp only [List.foldl_cons, List.length_cons] at *
      omega
    · intro i
      rcases Nat.lt_or_ge i.1 R.length with hi | hi
      · obtain ⟨p, hp, q, hq, h⟩ := hR3 ⟨i.1, hi⟩
        refine ⟨p, ?_, q, ?_, ?_⟩
        · rw [List.take_append_of_le_length (Nat.le_of_lt hi)]; exact hp
        · rw [List.take_append_of_le_length (Nat.le_of_lt hi)]; exact hq
        · simpa [List.getElem_append_left hi] using h
      · have hl : i.1 < R.length + 1 := by simpa using i.2
        have hi2 : i.1 = R.length := by omega
        refine ⟨t.2.1, ?_, t.2.2, ?_, ?_⟩
        · rw [hi2]; simpa using hb
        · rw [hi2]; simpa using hcc
        · simpa [hi2] using hop
    · intro x hx
      by_cases hxa : x = t.1
      · simp [hxa]
      · have := hRS x (by unfold step; simp [Finset.mem_erase, hxa, hx])
        simp at this ⊢
        tauto

end PEqualNP.Outside.L_meta_7414_aux

theorem PEqualNP.Outside.L_meta_7414 : have x1 : Finset ℕ → ℕ × ℕ × ℕ → Finset ℕ := fun (x1 : Finset ℕ) (x2 : ℕ × ℕ × ℕ) => Insert.insert x2.2.1 (Insert.insert x2.2.2 (x1.erase x2.1)); have x2 : Finset ℕ → List (ℕ × ℕ × ℕ) → Prop := fun (x2 : Finset ℕ) (x3 : List (ℕ × ℕ × ℕ)) =>   ∀ (x4 : Fin x3.length),     have x5 : ℕ × ℕ × ℕ := x3.get x4;     x5.1 ∈ List.foldl x1 x2 (List.take (↑x4) x3) ∧ (x5.1 = x5.2.1 &&& x5.2.2 ∨ x5.1 = x5.2.1 ||| x5.2.2); have x3 : List ℕ → List ℕ → Prop := fun (x3 x4 : List ℕ) => ∀ (x5 : Fin x4.length), ∃ x6 ∈ x3 ++ List.take (↑x5) x4, ∃ x7 ∈ x3 ++ List.take (↑x5) x4, x4.get x5 = x6 &&& x7 ∨ x4.get x5 = x6 ||| x7; ∀ (x4 : List ℕ) (x5 : Finset ℕ) (x6 : List (ℕ × ℕ × ℕ)), x2 x5 x6 → (∀ x8 ∈ List.foldl x1 x5 x6, x8 ∈ x4) → (List.foldl x1 x5 x6).card ≤ x5.card + x6.length ∧ ∃ (x9 : List ℕ), x9.length ≤ x6.length ∧ x3 x4 x9 ∧ ∀ x10 ∈ x5, x10 ∈ x4 ++ x9 := by
  exact fun x4 x5 x6 h1 h2 => PEqualNP.Outside.L_meta_7414_aux.aux x4 x6 x5 h1 h2
