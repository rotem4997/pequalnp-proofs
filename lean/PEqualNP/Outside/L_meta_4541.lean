import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4541

theorem cn_ne {a b : ℕ} (p : Fin a) (l : Fin b) : Fin.castAdd b p ≠ Fin.natAdd a l := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem nc_ne {a b : ℕ} (p : Fin a) (l : Fin b) : Fin.natAdd a l ≠ Fin.castAdd b p :=
  fun h => cn_ne p l h.symm

theorem cc {a b : ℕ} (p q : Fin a) : Fin.castAdd b p = Fin.castAdd b q ↔ p = q :=
  (Fin.castAdd_injective a b).eq_iff

theorem nn {a b : ℕ} (p q : Fin b) : Fin.natAdd a p = Fin.natAdd a q ↔ p = q :=
  (Fin.natAdd_injective b a).eq_iff

def Gr (a b : ℕ) (E : Finset (Fin a × Fin b)) : SimpleGraph (Fin (a + b)) where
  Adj u v := ∃ p l, (p, l) ∈ E ∧
    ((u = Fin.castAdd b p ∧ v = Fin.natAdd a l) ∨ (v = Fin.castAdd b p ∧ u = Fin.natAdd a l))
  symm := ⟨fun _ _ h => by
    obtain ⟨p, l, hE, h⟩ := h
    exact ⟨p, l, hE, h.symm⟩⟩
  loopless := ⟨fun u h => by
    obtain ⟨p, l, _, h⟩ := h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact cn_ne p l (h1.symm.trans h2)
    · exact cn_ne p l (h1.symm.trans h2)⟩

end PEqualNP.Outside.L_meta_4541

open PEqualNP.Outside.L_meta_4541 in
theorem PEqualNP.Outside.L_meta_4541 : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → x4 ⊆ x3 → (∀ x7 ∈ x4, ∀ x9 ∈ x4, x7.1 = x9.1 → x7 = x9) → (∀ x8 ∈ x4, ∀ x10 ∈ x4, x8.2 = x10.2 → x8 = x10) → (∀ x9 ∈ x3, ¬((∀ x11 ∈ x3, x11.1 = x9.1 → x11 = x9) ∨ ∀ x11 ∈ x3, x11.2 = x9.2 → x11 = x9)) → ∃ (x10 : SimpleGraph (Fin (x1 + x2))) (x11 : Finset (Fin (x1 + x2) × Fin (x1 + x2))), ∀ [x12 : DecidableRel x10.Adj], x10.edgeFinset.card = x3.card ∧ x11.card = x4.card ∧ PEqualNP.TopForm.NoFourCycle x10 ∧ (∃ (x13 : Fin (x1 + x2) → Bool), ∀ (x14 x15 : Fin (x1 + x2)), x10.Adj x14 x15 → x13 x14 ≠ x13 x15) ∧ (∀ (x13 : Fin (x1 + x2)), (x10.neighborSet x13).ncard ≠ (1 : ℕ)) ∧ (∀ x13 ∈ x11, x10.Adj x13.1 x13.2) ∧ (∀ x13 ∈ x11, ∀ x15 ∈ x11, x13.1 = x15.1 → x13 = x15) ∧ (∀ x13 ∈ x11, ∀ x15 ∈ x11, x13.2 = x15.2 → x13 = x15) ∧ (∀ x13 ∈ x11, ∀ x15 ∈ x11, x13.1 ≠ x15.2) ∧ ∀ (x13 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.NestedCover.graphFun x10 ∅ x13 = Decidable.decide (∃ (x14 : Fin x1) (x15 : Fin x2), (x14, x15) ∈ x3 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x1 x15) = Bool.true) := by
  intro a b E M hC hMs hM1 hM2 hdeg
  refine ⟨Gr a b E, M.image (fun e => (Fin.castAdd b e.1, Fin.natAdd a e.2)), ?_⟩
  intro inst
  have hinjF : Function.Injective (fun e : Fin a × Fin b => (Fin.castAdd b e.1, Fin.natAdd a e.2)) := by
    intro e f h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.castAdd_injective _ _ h.1) (Fin.natAdd_injective _ _ h.2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hE : (Gr a b E).edgeFinset = E.image (fun e => s(Fin.castAdd b e.1, Fin.natAdd a e.2)) := by
      ext s
      induction s using Sym2.ind with
      | h u v =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image]
        constructor
        · rintro ⟨p, l, hE, h⟩
          refine ⟨(p, l), hE, ?_⟩
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · subst h1 h2; rfl
          · subst h1 h2; exact Sym2.eq_swap
        · rintro ⟨⟨p, l⟩, hE, h⟩
          refine ⟨p, l, hE, ?_⟩
          rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1.symm, h2.symm⟩
          · exact Or.inr ⟨h1.symm, h2.symm⟩
    rw [hE, Finset.card_image_of_injective]
    intro e f h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact Prod.ext (Fin.castAdd_injective _ _ h1) (Fin.natAdd_injective _ _ h2)
    · exact absurd h1 (cn_ne _ _)
  · exact Finset.card_image_of_injective _ hinjF
  · intro u v huv
    rw [Finset.card_le_one]
    intro w hw w' hw'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    obtain ⟨⟨p1, l1, hE1, h1⟩, ⟨p2, l2, hE2, h2⟩⟩ := hw
    obtain ⟨⟨p3, l3, hE3, h3⟩, ⟨p4, l4, hE4, h4⟩⟩ := hw'
    by_contra hne
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, e2⟩ | ⟨e2, rfl⟩ <;>
      rcases h3 with ⟨e3, rfl⟩ | ⟨rfl, e3⟩ <;> rcases h4 with ⟨e4, e4'⟩ | ⟨e4, e4'⟩ <;>
      simp only [ne_eq, cc, nn, cn_ne, nc_ne] at e2 e3 e4 e4' huv hne <;> subst_vars
    · exact hC _ _ _ _ huv hne ⟨hE1, hE3, hE2, hE4⟩
    · exact hC _ _ _ _ hne huv ⟨hE1, hE2, hE3, hE4⟩
  · refine ⟨fun v => decide (v.val < a), ?_⟩
    intro u v h
    obtain ⟨p, l, _, h⟩ := h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · intro v hv
    rw [Set.ncard_eq_one] at hv
    obtain ⟨z, hz⟩ := hv
    have hz' : ∀ w, (Gr a b E).Adj v w → w = z := by
      intro w hw
      have : w ∈ (Gr a b E).neighborSet v := hw
      rw [hz] at this
      exact this
    have hvz : (Gr a b E).Adj v z := by
      have : z ∈ (Gr a b E).neighborSet v := by rw [hz]; rfl
      exact this
    obtain ⟨p, l, hE, h⟩ := hvz
    have hd := hdeg (p, l) hE
    rw [not_or] at hd
    obtain ⟨hd1, hd2⟩ := hd
    push_neg at hd1 hd2
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨⟨q, m⟩, hf, hq, hne⟩ := hd1
      simp only at hq
      subst hq
      have := hz' (Fin.natAdd a m) ⟨q, m, hf, Or.inl ⟨rfl, rfl⟩⟩
      rw [nn] at this
      exact hne (by rw [this])
    · obtain ⟨⟨q, m⟩, hf, hq, hne⟩ := hd2
      simp only at hq
      subst hq
      have := hz' (Fin.castAdd b q) ⟨q, m, hf, Or.inr ⟨rfl, rfl⟩⟩
      rw [cc] at this
      exact hne (by rw [this])
  · intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact ⟨f.1, f.2, hMs hf, Or.inl ⟨rfl, rfl⟩⟩
  · intro e he e' he' h
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp he'
    rw [hM1 f hf f' hf' (Fin.castAdd_injective _ _ h)]
  · intro e he e' he' h
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp he'
    rw [hM2 f hf f' hf' (Fin.natAdd_injective _ _ h)]
  · intro e he e' he'
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp he'
    exact cn_ne _ _
  · intro x
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨y, hy, _⟩ | ⟨u, v, ⟨p, l, hE, h⟩, hu, hv⟩)
      · simp at hy
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨p, l, hE, hu, hv⟩
        · exact ⟨p, l, hE, hv, hu⟩
    · rintro ⟨p, l, hE, h1, h2⟩
      exact Or.inr ⟨_, _, ⟨p, l, hE, Or.inl ⟨rfl, rfl⟩⟩, h1, h2⟩
