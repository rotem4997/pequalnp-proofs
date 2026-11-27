import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6172

-- Without a 4-cycle a complete bipartite piece has a single vertex on one side.
theorem bic {n m : ℕ} (R : Fin n → Fin m → Prop)
    (hC : ∀ (a a' : Fin n) (b b' : Fin m), a ≠ a' → b ≠ b' → ¬(R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (A : Finset (Fin n)) (B : Finset (Fin m)) (hA : A.Nonempty) (hB : B.Nonempty)
    (h : ∀ a ∈ A, ∀ b ∈ B, R a b) : (∃ a, A = {a}) ∨ (∃ b, B = {b}) := by
  by_contra hcon
  obtain ⟨hcA, hcB⟩ := not_or.mp hcon
  have hA1 : 1 < A.card := by
    by_contra h1
    have h0 := hA.card_pos
    have h2 : A.card = 1 := by omega
    exact hcA (Finset.card_eq_one.mp h2)
  have hB1 : 1 < B.card := by
    by_contra h1
    have h0 := hB.card_pos
    have h2 : B.card = 1 := by omega
    exact hcB (Finset.card_eq_one.mp h2)
  obtain ⟨a, ha, a', ha', haa⟩ := Finset.one_lt_card.mp hA1
  obtain ⟨b, hb, b', hb', hbb⟩ := Finset.one_lt_card.mp hB1
  exact hC a a' b b' haa hbb ⟨h a ha b hb, h a ha b' hb', h a' ha' b hb, h a' ha' b' hb'⟩

theorem stars {n m : ℕ} (R : Fin n → Fin m → Prop)
    (hC : ∀ (a a' : Fin n) (b b' : Fin m), a ≠ a' → b ≠ b' → ¬(R a b ∧ R a b' ∧ R a' b ∧ R a' b')) :
    ∀ L : List (Finset (Fin n) × Finset (Fin m)),
      (∀ p ∈ L, p.1.Nonempty ∧ p.2.Nonempty ∧ ∀ a ∈ p.1, ∀ b ∈ p.2, R a b) →
      ∃ S : List (ℕ × List ℕ),
        (∀ s ∈ S, s.2 ≠ [] ∧ ((s.1 < n ∧ ∀ w ∈ s.2, n ≤ w ∧ w < n + m) ∨
          (n ≤ s.1 ∧ s.1 < n + m ∧ ∀ w ∈ s.2, w < n))) ∧
        (∀ (u : Fin n) (v : Fin m),
          (∃ s ∈ S, s.1 = u.val ∧ n + v.val ∈ s.2 ∨ s.1 = n + v.val ∧ u.val ∈ s.2) ↔
            ∃ p ∈ L, u ∈ p.1 ∧ v ∈ p.2) ∧
        (S.map (fun s => s.2.length)).sum + S.length =
          (L.map (fun p => p.1.card + p.2.card)).sum := by
  intro L
  induction L with
  | nil => intro _; exact ⟨[], by simp, by simp, by simp⟩
  | cons p L ih =>
    intro h
    obtain ⟨S, hwf, hiff, hsum⟩ := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    obtain ⟨hA, hB, hAB⟩ := h p List.mem_cons_self
    rcases bic R hC p.1 p.2 hA hB hAB with ⟨a, ha⟩ | ⟨b, hb⟩
    · refine ⟨(a.val, p.2.toList.map (fun b => n + b.val)) :: S, ?_, ?_, ?_⟩
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · refine ⟨?_, Or.inl ⟨a.isLt, ?_⟩⟩
          · intro hnil
            have := List.map_eq_nil_iff.mp hnil
            exact hB.ne_empty (Finset.toList_eq_nil.mp this)
          · intro w hw
            obtain ⟨b, _, rfl⟩ := List.mem_map.mp hw
            have := b.isLt
            exact ⟨by omega, by omega⟩
        · exact hwf s hs
      · intro u v
        constructor
        · rintro ⟨s, hs, hor⟩
          rcases List.mem_cons.mp hs with rfl | hs'
          · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · obtain ⟨b, hb, hbe⟩ := List.mem_map.mp h2
              have hbv : b = v := Fin.ext (by omega)
              rw [hbv] at hb
              refine ⟨p, List.mem_cons_self, ?_, Finset.mem_toList.mp hb⟩
              rw [ha]
              exact Finset.mem_singleton.mpr (Fin.ext h1.symm)
            · exfalso
              have := a.isLt
              simp only at h1
              omega
          · obtain ⟨q, hq, hqq⟩ := (hiff u v).mp ⟨s, hs', hor⟩
            exact ⟨q, List.mem_cons_of_mem _ hq, hqq⟩
        · rintro ⟨q, hq, hu, hv⟩
          rcases List.mem_cons.mp hq with rfl | hq'
          · rw [ha] at hu
            have hua : u = a := Finset.mem_singleton.mp hu
            refine ⟨_, List.mem_cons_self, Or.inl ⟨by rw [hua], ?_⟩⟩
            exact List.mem_map.mpr ⟨v, Finset.mem_toList.mpr hv, rfl⟩
          · obtain ⟨s, hs, hor⟩ := (hiff u v).mpr ⟨q, hq', hu, hv⟩
            exact ⟨s, List.mem_cons_of_mem _ hs, hor⟩
      · have h1 : p.1.card = 1 := by rw [ha]; exact Finset.card_singleton a
        simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_map,
          Finset.length_toList]
        omega
    · refine ⟨(n + b.val, p.1.toList.map (fun a => a.val)) :: S, ?_, ?_, ?_⟩
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · have hbl := b.isLt
          refine ⟨?_, Or.inr ⟨by simp, by simp only; omega, ?_⟩⟩
          · intro hnil
            have := List.map_eq_nil_iff.mp hnil
            exact hA.ne_empty (Finset.toList_eq_nil.mp this)
          · intro w hw
            obtain ⟨a, _, rfl⟩ := List.mem_map.mp hw
            exact a.isLt
        · exact hwf s hs
      · intro u v
        constructor
        · rintro ⟨s, hs, hor⟩
          rcases List.mem_cons.mp hs with rfl | hs'
          · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exfalso
              have := u.isLt
              simp only at h1
              omega
            · obtain ⟨a, ha, hae⟩ := List.mem_map.mp h2
              have hau : a = u := Fin.ext hae
              rw [hau] at ha
              simp only at h1
              have hbv : v = b := Fin.ext (by omega)
              refine ⟨p, List.mem_cons_self, Finset.mem_toList.mp ha, ?_⟩
              rw [hb, hbv]
              exact Finset.mem_singleton_self b
          · obtain ⟨q, hq, hqq⟩ := (hiff u v).mp ⟨s, hs', hor⟩
            exact ⟨q, List.mem_cons_of_mem _ hq, hqq⟩
        · rintro ⟨q, hq, hu, hv⟩
          rcases List.mem_cons.mp hq with rfl | hq'
          · rw [hb] at hv
            have hvb : v = b := Finset.mem_singleton.mp hv
            refine ⟨_, List.mem_cons_self, Or.inr ⟨by rw [hvb], ?_⟩⟩
            exact List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hu, rfl⟩
          · obtain ⟨s, hs, hor⟩ := (hiff u v).mpr ⟨q, hq', hu, hv⟩
            exact ⟨s, List.mem_cons_of_mem _ hs, hor⟩
      · have h1 : p.2.card = 1 := by rw [hb]; exact Finset.card_singleton b
        simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_map,
          Finset.length_toList]
        omega

end PEqualNP.Outside.L_meta_6172

theorem PEqualNP.Outside.L_meta_6172 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : List (Finset (Fin x1) × Finset (Fin x2))), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → (∀ x7 ∈ x5, x7.1.Nonempty ∧ x7.2.Nonempty ∧ ∀ x9 ∈ x7.1, ∀ x11 ∈ x7.2, x3 x9 x11) → (∀ (x8 : Fin x1) (x9 : Fin x2), x3 x8 x9 ↔ ∃ x10 ∈ x5, x8 ∈ x10.1 ∧ x9 ∈ x10.2) → ∃ (x9 : List (ℕ × List ℕ)), (∀ x10 ∈ x9, x10.2 ≠ [] ∧ ((x10.1 < x1 ∧ ∀ x12 ∈ x10.2, x1 ≤ x12 ∧ x12 < x1 + x2) ∨ x1 ≤ x10.1 ∧ x10.1 < x1 + x2 ∧ ∀ x12 ∈ x10.2, x12 < x1)) ∧ (∀ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ↔ ∃ x12 ∈ x9, x12.1 = ↑x10 ∧ x1 + ↑x11 ∈ x12.2 ∨ x12.1 = x1 + ↑x11 ∧ ↑x10 ∈ x12.2) ∧ (List.map (fun (x10 : ℕ × List ℕ) => x10.2.length) x9).sum + x9.length - (1 : ℕ) ≤ (List.map (fun (x10 : Finset (Fin x1) × Finset (Fin x2)) => x10.1.card + x10.2.card) x5).sum - (1 : ℕ) := by
  intro n m R _ L hC hL hcov
  obtain ⟨S, hwf, hiff, hsum⟩ := PEqualNP.Outside.L_meta_6172.stars R hC L hL
  refine ⟨S, hwf, fun u v => (hcov u v).trans (hiff u v).symm, ?_⟩
  omega
