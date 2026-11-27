import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3765

def V (n m : ℕ) (a b ty : ℕ → ℕ) (c : ℕ → Bool) (w : ℕ) : Finset ℕ :=
  if w < n then {w}
  else if h : w - n < m ∧ a (w - n) < w ∧ b (w - n) < w then
    if ty (w - n) = 0 then V n m a b ty c (a (w - n)) ∪ V n m a b ty c (b (w - n))
    else if ty (w - n) = 1 then
      (if c (w - n) = true then V n m a b ty c (a (w - n)) else V n m a b ty c (b (w - n)))
    else ∅
  else ∅
termination_by w
decreasing_by all_goals first | exact h.2.1 | exact h.2.2

theorem V_in {n m : ℕ} {a b ty : ℕ → ℕ} {c : ℕ → Bool} {w : ℕ} (h : w < n) :
    V n m a b ty c w = {w} := by
  rw [V, if_pos h]

theorem V_gate {n m : ℕ} {a b ty : ℕ → ℕ} {c : ℕ → Bool} {j : ℕ} (hj : j < m)
    (ha : a j < n + j) (hb : b j < n + j) : V n m a b ty c (n + j) =
    if ty j = 0 then V n m a b ty c (a j) ∪ V n m a b ty c (b j)
    else if ty j = 1 then (if c j = true then V n m a b ty c (a j) else V n m a b ty c (b j))
    else ∅ := by
  have e : n + j - n = j := by omega
  rw [V, if_neg (by omega), e, dif_pos ⟨hj, ha, hb⟩]

end PEqualNP.Outside.L_meta_3765

theorem PEqualNP.Outside.L_meta_3765 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Set (Finset ℕ)), x3 < x1 + x2 → (∀ x6 < x1, x4 x6 = {{x6}}) → (∀ x7 < x2, ∃ x9 < x1 + x7, ∃ x10 < x1 + x7, x4 (x1 + x7) = Set.image2 (fun (x11 x12 : Finset ℕ) => x11 ∪ x12) (x4 x9) (x4 x10) ∨ x4 (x1 + x7) = x4 x9 ∨ x4 (x1 + x7) = {∅} ∨ x4 (x1 + x7) = x4 x9 ∪ x4 x10) → ∃ (x8 : (Fin x2 → Bool) → ℕ → Finset ℕ), (∀ (x9 : Fin x2 → Bool), ∀ x10 < x1, x8 x9 x10 = {x10}) ∧ (∀ (x9 : Fin x2), ∃ x10 < x1 + ↑x9, ∃ x11 < x1 + ↑x9, (∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = x8 x12 x10 ∪ x8 x12 x11) ∨ (∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = if x12 x9 = Bool.true then x8 x12 x10 else x8 x12 x11) ∨ ∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = ∅) ∧ (∀ (x9 : Fin x2 → Bool), x8 x9 x3 ∈ x4 x3) ∧ ∀ x9 ∈ x4 x3, ∃ (x11 : Fin x2 → Bool), x8 x11 x3 ⊆ x9 := by
  intro n m o F ho hin hg
  classical
  have hdata : ∀ j, ∃ a b t : ℕ, j < m → a < n + j ∧ b < n + j ∧
      ((t = 0 ∧ F (n + j) = Set.image2 (fun x y : Finset ℕ => x ∪ y) (F a) (F b)) ∨
        (t = 1 ∧ F (n + j) = F a ∪ F b) ∨ (t = 2 ∧ F (n + j) = {∅})) := by
    intro j
    by_cases hj : j < m
    · obtain ⟨a, ha, b, hb, h | h | h | h⟩ := hg j hj
      · exact ⟨a, b, 0, fun _ => ⟨ha, hb, Or.inl ⟨rfl, h⟩⟩⟩
      · exact ⟨a, a, 1, fun _ => ⟨ha, ha, Or.inr (Or.inl ⟨rfl, by rw [h, Set.union_self]⟩)⟩⟩
      · exact ⟨a, b, 2, fun _ => ⟨ha, hb, Or.inr (Or.inr ⟨rfl, h⟩)⟩⟩
      · exact ⟨a, b, 1, fun _ => ⟨ha, hb, Or.inr (Or.inl ⟨rfl, h⟩)⟩⟩
    · exact ⟨0, 0, 0, fun h => absurd h hj⟩
  choose a b t ht using hdata
  let ex : (Fin m → Bool) → ℕ → Bool := fun c j => if h : j < m then c ⟨j, h⟩ else false
  have hex : ∀ (c : Fin m → Bool) (j : Fin m), ex c j = c j := fun c j => dif_pos j.2
  refine ⟨fun c w => PEqualNP.Outside.L_meta_3765.V n m a b t (ex c) w, fun c w hw => PEqualNP.Outside.L_meta_3765.V_in hw, fun j => ?_, fun c => ?_,
    fun s hs => ?_⟩
  · obtain ⟨ha, hb, hty⟩ := ht j j.2
    refine ⟨a j, ha, b j, hb, ?_⟩
    rcases hty with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨h2, -⟩
    · left; intro c
      dsimp only
      rw [PEqualNP.Outside.L_meta_3765.V_gate j.2 ha hb, if_pos h0]
    · right; left; intro c
      dsimp only
      rw [PEqualNP.Outside.L_meta_3765.V_gate j.2 ha hb, if_neg (by omega), if_pos h1, hex]
    · right; right; intro c
      dsimp only
      rw [PEqualNP.Outside.L_meta_3765.V_gate j.2 ha hb, if_neg (by omega), if_neg (by omega)]
  · have key : ∀ w < n + m, PEqualNP.Outside.L_meta_3765.V n m a b t (ex c) w ∈ F w := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw
        rcases Nat.lt_or_ge w n with h | h
        · rw [PEqualNP.Outside.L_meta_3765.V_in h, hin w h]; rfl
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
          have hj : j < m := by omega
          obtain ⟨ha, hb, hty⟩ := ht j hj
          have ia := ih (a j) ha (by omega)
          have ib := ih (b j) hb (by omega)
          rw [PEqualNP.Outside.L_meta_3765.V_gate hj ha hb]
          rcases hty with ⟨h0, hF⟩ | ⟨h1, hF⟩ | ⟨h2, hF⟩
          · rw [if_pos h0, hF]; exact Set.mem_image2_of_mem ia ib
          · rw [if_neg (by omega), if_pos h1, hF]
            split_ifs
            · exact Or.inl ia
            · exact Or.inr ib
          · rw [if_neg (by omega), if_neg (by omega), hF]; rfl
    exact key o ho
  · refine ⟨fun j => decide (∃ u ∈ F (a j), u ⊆ s), ?_⟩
    have key : ∀ w < n + m, (∃ u ∈ F w, u ⊆ s) → PEqualNP.Outside.L_meta_3765.V n m a b t
        (ex fun j => decide (∃ u ∈ F (a j), u ⊆ s)) w ⊆ s := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        rintro hw ⟨u, hu, hus⟩
        rcases Nat.lt_or_ge w n with h | h
        · rw [PEqualNP.Outside.L_meta_3765.V_in h]
          rw [hin w h] at hu
          rw [Set.mem_singleton_iff.1 hu] at hus
          exact hus
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
          have hj : j < m := by omega
          obtain ⟨ha, hb, hty⟩ := ht j hj
          rw [PEqualNP.Outside.L_meta_3765.V_gate hj ha hb]
          rcases hty with ⟨h0, hF⟩ | ⟨h1, hF⟩ | ⟨h2, hF⟩
          · rw [hF] at hu
            obtain ⟨p, hp, q, hq, rfl⟩ := hu
            rw [if_pos h0]
            exact Finset.union_subset
              (ih (a j) ha (by omega) ⟨p, hp, Finset.subset_union_left.trans hus⟩)
              (ih (b j) hb (by omega) ⟨q, hq, Finset.subset_union_right.trans hus⟩)
          · rw [if_neg (by omega), if_pos h1]
            have hc : ex (fun j => decide (∃ u ∈ F (a j), u ⊆ s)) j =
                decide (∃ u ∈ F (a j), u ⊆ s) := dif_pos hj
            rw [hc]
            by_cases hA : ∃ u ∈ F (a j), u ⊆ s
            · rw [if_pos (decide_eq_true hA)]
              exact ih (a j) ha (by omega) hA
            · rw [if_neg (by simpa using hA)]
              refine ih (b j) hb (by omega) ?_
              rw [hF] at hu
              rcases hu with hu | hu
              · exact absurd ⟨u, hu, hus⟩ hA
              · exact ⟨u, hu, hus⟩
          · rw [if_neg (by omega), if_neg (by omega)]
            exact Finset.empty_subset _
    exact key o ho ⟨s, hs, Finset.Subset.refl _⟩
