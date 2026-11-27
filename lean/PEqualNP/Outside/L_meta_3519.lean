import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3519

theorem filt_le (l : List (ℕ × List ℕ)) :
    ((l.filter (fun s => !s.2.isEmpty)).map (fun s => s.2.length)).sum
      + (l.filter (fun s => !s.2.isEmpty)).length
      ≤ (l.map (fun s => s.2.length)).sum + l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    by_cases h : x.2.isEmpty = true
    · simp [List.filter_cons, h]
      omega
    · simp [List.filter_cons, h]
      omega

end PEqualNP.Outside.L_meta_3519

theorem PEqualNP.Outside.L_meta_3519 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : List (ℕ × List ℕ)), (∀ x8 ∈ x7, x8.2 ≠ [] ∧ ((x8.1 < x1 ∧ ∀ x10 ∈ x8.2, x1 ≤ x10 ∧ x10 < x1 + x2) ∨ x1 ≤ x8.1 ∧ x8.1 < x1 + x2 ∧ ∀ x10 ∈ x8.2, x10 < x1)) ∧ (∀ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ↔ ∃ x10 ∈ x7, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) ∧ (List.map (fun (x8 : ℕ × List ℕ) => x8.2.length) x7).sum + x7.length - (1 : ℕ) ≤ x3.card + x4.card + x5.card - (1 : ℕ) := by
  intro a b E P L hcov
  classical
  set A := E.filter (fun e => e.1 ∈ P) with hA
  set B := E.filter (fun e => e.1 ∉ P) with hB
  let ps : Fin a → ℕ × List ℕ := fun p =>
    (p.val, ((A.filter (fun e => e.1 = p)).toList.map (fun e => a + e.2.val)))
  let ls : Fin b → ℕ × List ℕ := fun l =>
    (a + l.val, ((B.filter (fun e => e.2 = l)).toList.map (fun e => e.1.val)))
  let full : List (ℕ × List ℕ) := P.toList.map ps ++ L.toList.map ls
  have hfull : ∀ s ∈ full, (∃ p ∈ P, s = ps p) ∨ (∃ l ∈ L, s = ls l) := by
    intro s hs
    simp only [full, List.mem_append, List.mem_map, Finset.mem_toList] at hs
    rcases hs with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
    · exact Or.inl ⟨p, hp, rfl⟩
    · exact Or.inr ⟨l, hl, rfl⟩
  refine ⟨full.filter (fun s => !s.2.isEmpty), ?_, ?_, ?_⟩
  · intro s hs
    rw [List.mem_filter] at hs
    obtain ⟨hs, hne⟩ := hs
    refine ⟨?_, ?_⟩
    · intro h
      rw [h] at hne
      simp at hne
    rcases hfull s hs with ⟨p, _, rfl⟩ | ⟨l, _, rfl⟩
    · left
      refine ⟨p.isLt, ?_⟩
      intro x hx
      simp only [ps, List.mem_map, Finset.mem_toList] at hx
      obtain ⟨e, _, rfl⟩ := hx
      have := e.2.isLt
      omega
    · right
      refine ⟨show a ≤ a + l.val from Nat.le_add_right _ _, show a + l.val < a + b by have := l.isLt; omega, ?_⟩
      intro x hx
      simp only [ls, List.mem_map, Finset.mem_toList] at hx
      obtain ⟨e, _, rfl⟩ := hx
      exact e.1.isLt
  · intro p l
    constructor
    · intro he
      by_cases hp : p ∈ P
      · refine ⟨ps p, ?_, Or.inl ⟨rfl, ?_⟩⟩
        · rw [List.mem_filter]
          refine ⟨?_, ?_⟩
          · simp only [full, List.mem_append, List.mem_map, Finset.mem_toList]
            exact Or.inl ⟨p, hp, rfl⟩
          · have hmem : (p, l) ∈ A.filter (fun e => e.1 = p) := by
              simp [hA, he, hp]
            have : (A.filter (fun e => e.1 = p)).toList ≠ [] := by
              intro h0
              have := (Finset.mem_toList).2 hmem
              rw [h0] at this
              simp at this
            simp only [ps]
            simpa using this
        · simp only [ps, List.mem_map, Finset.mem_toList]
          exact ⟨(p, l), by simp [hA, he, hp], rfl⟩
      · have hl : l ∈ L := by
          rcases hcov _ he with h | h
          · exact absurd h hp
          · exact h
        refine ⟨ls l, ?_, Or.inr ⟨rfl, ?_⟩⟩
        · rw [List.mem_filter]
          refine ⟨?_, ?_⟩
          · simp only [full, List.mem_append, List.mem_map, Finset.mem_toList]
            exact Or.inr ⟨l, hl, rfl⟩
          · have hmem : (p, l) ∈ B.filter (fun e => e.2 = l) := by
              simp [hB, he, hp]
            have : (B.filter (fun e => e.2 = l)).toList ≠ [] := by
              intro h0
              have := (Finset.mem_toList).2 hmem
              rw [h0] at this
              simp at this
            simp only [ls]
            simpa using this
        · simp only [ls, List.mem_map, Finset.mem_toList]
          exact ⟨(p, l), by simp [hB, he, hp], rfl⟩
    · rintro ⟨s, hs, hcase⟩
      rw [List.mem_filter] at hs
      rcases hfull s hs.1 with ⟨p', _, rfl⟩ | ⟨l', _, rfl⟩
      · rcases hcase with ⟨h1, h2⟩ | ⟨h1, _⟩
        · simp only [ps, List.mem_map, Finset.mem_toList] at h1 h2
          obtain ⟨e, he, he2⟩ := h2
          have hp' : p' = p := Fin.ext h1
          subst hp'
          simp only [hA, Finset.mem_filter] at he
          have h2' : e.2 = l := Fin.ext (by omega)
          have : e = (p', l) := Prod.ext he.2 h2'
          rw [← this]
          exact he.1.1
        · simp only [ps] at h1
          have := p'.isLt
          omega
      · rcases hcase with ⟨h1, _⟩ | ⟨h1, h2⟩
        · simp only [ls] at h1
          have := p.isLt
          omega
        · simp only [ls, List.mem_map, Finset.mem_toList] at h1 h2
          obtain ⟨e, he, he2⟩ := h2
          have hl' : l' = l := Fin.ext (by omega)
          subst hl'
          simp only [hB, Finset.mem_filter] at he
          have h1' : e.1 = p := Fin.ext he2
          have : e = (p, l') := Prod.ext h1' he.2
          rw [← this]
          exact he.1.1
  · have hsum : (full.map (fun s => s.2.length)).sum + full.length = E.card + P.card + L.card := by
      have hPs : ∑ p ∈ P, (A.filter (fun e => e.1 = p)).card = A.card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := P)]
        intro e he
        simp only [hA, Finset.coe_filter, Set.mem_ofPred_eq] at he
        exact he.2
      have hLs : ∑ l ∈ L, (B.filter (fun e => e.2 = l)).card = B.card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := L)]
        intro e he
        simp only [hB, Finset.coe_filter, Set.mem_ofPred_eq] at he
        rcases hcov e he.1 with h | h
        · exact absurd h he.2
        · exact h
      have hAB : A.card + B.card = E.card := Finset.card_filter_add_card_filter_not _
      simp only [full, List.map_append, List.sum_append, List.length_append, List.map_map,
        List.length_map, Finset.length_toList]
      have e1 : ((P.toList.map ((fun s : ℕ × List ℕ => s.2.length) ∘ ps))).sum
          = ∑ p ∈ P, (A.filter (fun e => e.1 = p)).card := by
        rw [Finset.sum_map_toList]
        apply Finset.sum_congr rfl
        intro p _
        simp [ps]
      have e2 : ((L.toList.map ((fun s : ℕ × List ℕ => s.2.length) ∘ ls))).sum
          = ∑ l ∈ L, (B.filter (fun e => e.2 = l)).card := by
        rw [Finset.sum_map_toList]
        apply Finset.sum_congr rfl
        intro l _
        simp [ls]
      rw [e1, e2, hPs, hLs]
      omega
    have := PEqualNP.Outside.L_meta_3519.filt_le full
    omega
