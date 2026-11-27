import Mathlib
import PEqualNP.Defs

-- Splicing two build sequences: if p is built from s, every element of w lies in
-- s ++ p, and t is built from w, then p ++ t is built from s.
namespace PEqualNP.Outside.L_meta_4534

-- Every entry of l is one bitwise step from s and the entries before it.
def Builds (s l : List ℕ) : Prop :=
  ∀ i : Fin l.length, ∃ a ∈ s ++ l.take i.val, ∃ b ∈ s ++ l.take i.val,
    l.get i = a &&& b ∨ l.get i = a ||| b

theorem splice_main (s p w t : List ℕ) (hp : Builds s p) (hw : ∀ x ∈ w, x ∈ s ++ p)
    (ht : Builds w t) : Builds s (p ++ t) := by
  intro i
  obtain ⟨k, hk⟩ := i
  by_cases hkp : k < p.length
  · obtain ⟨a, ha, b, hb, hab⟩ := hp ⟨k, hkp⟩
    have htake : (p ++ t).take k = p.take k :=
      List.take_append_of_le_length (Nat.le_of_lt hkp)
    have hget : (p ++ t).get ⟨k, hk⟩ = p.get ⟨k, hkp⟩ := by
      simp [List.getElem_append_left hkp]
    refine ⟨a, ?_, b, ?_, ?_⟩
    · show a ∈ s ++ (p ++ t).take k
      rw [htake]; exact ha
    · show b ∈ s ++ (p ++ t).take k
      rw [htake]; exact hb
    · rw [hget]; exact hab
  · have hkp' : p.length ≤ k := Nat.le_of_not_lt hkp
    have hlen : (p ++ t).length = p.length + t.length := List.length_append
    have hj : k - p.length < t.length := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := ht ⟨k - p.length, hj⟩
    have htake : (p ++ t).take k = p ++ t.take (k - p.length) := by
      rw [List.take_append, List.take_of_length_le hkp']
    have hget : (p ++ t).get ⟨k, hk⟩ = t.get ⟨k - p.length, hj⟩ := by
      simp [List.getElem_append_right hkp']
    have hin : ∀ c, c ∈ w ++ t.take (k - p.length) → c ∈ s ++ (p ++ t).take k := by
      intro c hc
      rw [htake]
      rcases List.mem_append.mp hc with hcw | hct
      · rcases List.mem_append.mp (hw c hcw) with hcs | hcp
        · exact List.mem_append_left _ hcs
        · exact List.mem_append_right _ (List.mem_append_left _ hcp)
      · exact List.mem_append_right _ (List.mem_append_right _ hct)
    refine ⟨a, hin a ha, b, hin b hb, ?_⟩
    rw [hget]; exact hab

end PEqualNP.Outside.L_meta_4534

theorem PEqualNP.Outside.L_meta_4534 : ∀ (x1 x2 x3 x4 : List ℕ),   have x5 : List ℕ → List ℕ → Prop := fun (x5 x6 : List ℕ) => ∀ (x7 : Fin x6.length), ∃ x8 ∈ x5 ++ List.take (↑x7) x6, ∃ x9 ∈ x5 ++ List.take (↑x7) x6, x6.get x7 = x8 &&& x9 ∨ x6.get x7 = x8 ||| x9;   x5 x1 x2 → (∀ x7 ∈ x3, x7 ∈ x1 ++ x2) → x5 x3 x4 → x5 x1 (x2 ++ x4) := by
  intro s p w t builds hp hw ht
  exact PEqualNP.Outside.L_meta_4534.splice_main s p w t hp hw ht
