import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4121

noncomputable section
open Classical

variable {n s : ℕ}

def vec (A : Fin s → Prop) (lab : Fin s → Fin n) (h : Fin n) : Fin s → ℚ :=
  fun i => if A i ∧ lab i = h then 1 else 0

def fn (B : Fin s → Prop) (lab : Fin s → Fin n) (h : Fin n) : (Fin s → ℚ) →ₗ[ℚ] ℚ :=
  ∑ i, (if B i ∧ lab i = h then (1 : ℚ) else 0) • LinearMap.proj i

theorem fn_vec (A B : Fin s → Prop) (lab : Fin s → Fin n) (h h' : Fin n) (i0 : Fin s)
    (h0 : A i0 ∧ B i0) (hu : ∀ i, A i → B i → i = i0) :
    fn B lab h' (vec A lab h) = if lab i0 = h ∧ lab i0 = h' then 1 else 0 := by
  have e : fn B lab h' (vec A lab h) =
      ∑ i, (if B i ∧ lab i = h' then (1 : ℚ) else 0) * vec A lab h i := by
    simp only [fn, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  rw [e, Finset.sum_eq_single i0]
  · simp only [vec, h0.1, h0.2, true_and]
    by_cases h1 : lab i0 = h <;> by_cases h2 : lab i0 = h' <;> simp [h1, h2]
  · intro i _ hi
    by_cases hA : A i
    · have hB : ¬ B i := fun hB => hi (hu i hA hB)
      simp [hB]
    · simp [vec, hA]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem core {E : Type} [Fintype E] (hd tl : E → Fin n) (hne : ∀ e, hd e ≠ tl e)
    (A : E → Fin s → Prop) (V : Fin n → Fin s → Prop) (B : E → Fin s → Prop)
    (lab : Fin s → Fin n)
    (hV : ∀ e w, (w = hd e ∨ w = tl e) → ∃ i0, (A e i0 ∧ V w i0) ∧
      (∀ i, A e i → V w i → i = i0) ∧ lab i0 = w)
    (hS : ∀ e, ∃ i0, (A e i0 ∧ B e i0) ∧ (∀ i, A e i → B e i → i = i0) ∧ lab i0 = hd e)
    (hB : ∀ e e' u, e ≠ e' → (u = hd e ∨ u = tl e) → (u = tl e') → ∃ i0, (A e i0 ∧ B e' i0) ∧
      (∀ i, A e i → B e' i → i = i0) ∧ lab i0 = u) :
    Fintype.card E + (Finset.univ.image hd).card ≤ s := by
  have hf : ∀ u : (Finset.univ.image hd : Finset (Fin n)), ∃ e, hd e = u.1 := fun u => by
    obtain ⟨e, _, he⟩ := Finset.mem_image.1 u.2
    exact ⟨e, he⟩
  choose f hf using hf
  let w : E ⊕ (Finset.univ.image hd : Finset (Fin n)) → (Fin s → ℚ) :=
    Sum.elim (fun e => vec (A e) lab (tl e)) (fun u => vec (A (f u)) lab u.1)
  have pV : ∀ e h w', (h = hd e ∨ h = tl e) →
      fn (V w') lab w' (vec (A e) lab h) = if h = w' then 1 else 0 := by
    intro e h w' hh
    by_cases hw : h = w'
    · subst hw
      obtain ⟨i0, h1, h2, h3⟩ := hV e h hh
      rw [fn_vec _ _ _ _ _ i0 h1 h2]
      simp [h3]
    · rw [if_neg hw]
      simp only [fn, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, vec,
        smul_eq_mul]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h1 : lab i = h
      · have : ¬ lab i = w' := fun h2 => hw (h1.symm.trans h2)
        simp [this]
      · simp [h1]
  have pB : ∀ e h e0, (h = hd e ∨ h = tl e) → fn (B e0) lab (tl e0) (vec (A e) lab h) =
      if h = tl e0 ∧ e ≠ e0 then 1 else 0 := by
    intro e h e0 hh
    by_cases hw : h = tl e0
    · by_cases he : e = e0
      · subst he
        obtain ⟨i0, h1, h2, h3⟩ := hS e
        rw [fn_vec _ _ _ _ _ i0 h1 h2, h3]
        simp [hne e]
      · obtain ⟨i0, h1, h2, h3⟩ := hB e e0 h he hh hw
        rw [fn_vec _ _ _ _ _ i0 h1 h2, h3]
        simp [hw, he]
    · rw [if_neg (fun h => hw h.1)]
      simp only [fn, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, vec,
        smul_eq_mul]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h1 : lab i = h
      · have : ¬ lab i = tl e0 := fun h2 => hw (h1.symm.trans h2)
        simp [this]
      · simp [h1]
  have hli : LinearIndependent ℚ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    have hE : ∀ e0, g (Sum.inl e0) = 0 := by
      intro e0
      have h := congrArg (fun v => fn (V (tl e0)) lab (tl e0) v - fn (B e0) lab (tl e0) v) hg
      simp only [map_add, map_sum, map_smul, map_zero, sub_zero, w, Sum.elim_inl, Sum.elim_inr,
        smul_eq_mul] at h
      have r1 : ∀ e, fn (V (tl e0)) lab (tl e0) (vec (A e) lab (tl e)) =
          if tl e = tl e0 then 1 else 0 := fun e => pV e _ _ (Or.inr rfl)
      have r2 : ∀ e, fn (B e0) lab (tl e0) (vec (A e) lab (tl e)) =
          if tl e = tl e0 ∧ e ≠ e0 then 1 else 0 := fun e => pB e _ _ (Or.inr rfl)
      have r3 : ∀ u, fn (V (tl e0)) lab (tl e0) (vec (A (f u)) lab u.1) =
          if u.1 = tl e0 then 1 else 0 := fun u => pV (f u) _ _ (Or.inl (hf u).symm)
      have r4 : ∀ u, fn (B e0) lab (tl e0) (vec (A (f u)) lab u.1) =
          if u.1 = tl e0 then 1 else 0 := fun u => by
        rw [pB (f u) _ _ (Or.inl (hf u).symm)]
        by_cases hu : u.1 = tl e0
        · have : f u ≠ e0 := fun h => hne e0 (by rw [← hu, ← hf u, h])
          simp [hu, this]
        · simp [hu]
      simp only [r1, r2, r3, r4] at h
      rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib, Finset.sum_eq_single e0] at h
      · simpa using h
      · intro e _ he
        simp [he]
      · intro h; exact absurd (Finset.mem_univ _) h
    intro i
    rcases i with e | u0
    · exact hE e
    · have h := congrArg (fun v => fn (V u0.1) lab u0.1 v) hg
      simp only [map_add, map_sum, map_smul, map_zero, w, Sum.elim_inl, Sum.elim_inr,
        smul_eq_mul, hE, zero_mul, Finset.sum_const_zero, zero_add] at h
      have r3 : ∀ u, fn (V u0.1) lab u0.1 (vec (A (f u)) lab u.1) =
          if u.1 = u0.1 then 1 else 0 := fun u => pV (f u) _ _ (Or.inl (hf u).symm)
      simp only [r3] at h
      rw [Finset.sum_eq_single u0] at h
      · simpa using h
      · intro u _ hu
        have hn : ¬ u.1 = u0.1 := fun h => hu (Subtype.ext h)
        rw [if_neg hn, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hc := hli.fintype_card_le_finrank
  rw [Fintype.card_sum, Fintype.card_coe, Module.finrank_fin_fun] at hc
  exact hc

end

end PEqualNP.Outside.L_meta_4121

open PEqualNP.Outside.L_meta_4121 in
theorem PEqualNP.Outside.L_meta_4121 : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 x5 : Fin x2 → Fin x1 → Fin x1 → Prop) (x6 : Fin x2 → Fin x1), (∀ (x7 x8 x9 x10 : Fin x1), x3.Adj x7 x8 → x9 = x10 ∨ x3.Adj x9 x10 → (∃! x13 : Fin x2, x4 x13 x7 x8 ∧ x5 x13 x9 x10) ∧ ∀ (x13 : Fin x2), x4 x13 x7 x8 → x5 x13 x9 x10 → (x6 x13 = x7 ∨ x6 x13 = x8) ∧ ¬((x3.Adj x9 (x6 x13) ∨ x3.Adj x10 (x6 x13)) ∧ x6 x13 ≠ x9 ∧ x6 x13 ≠ x10)) → ∃ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∈ x8 ∨ x10 ∈ x8) ∧ x3.edgeSet.ncard + x8.card ≤ x2 := by
  classical
  intro n s G A B lab H
  have hout : ∀ e : G.edgeSet, ∃ a b, e.1 = s(a, b) ∧ G.Adj a b := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b => exact ⟨a, b, rfl, he⟩
  choose a b hab hadj using hout
  have hI : ∀ (e : G.edgeSet) (x y : Fin n), x = y ∨ G.Adj x y → ∃ i0,
      (A i0 (a e) (b e) ∧ B i0 x y) ∧ (∀ i, A i (a e) (b e) → B i x y → i = i0) ∧
      (lab i0 = a e ∨ lab i0 = b e) ∧
      ¬((G.Adj x (lab i0) ∨ G.Adj y (lab i0)) ∧ lab i0 ≠ x ∧ lab i0 ≠ y) := by
    intro e x y hxy
    obtain ⟨⟨i0, h1, h2⟩, h3⟩ := H (a e) (b e) x y (hadj e) hxy
    obtain ⟨h4, h5⟩ := h3 i0 h1.1 h1.2
    exact ⟨i0, h1, fun i hA hB => h2 i ⟨hA, hB⟩, h4, h5⟩
  have hhd : ∀ e : G.edgeSet, ∃ h t : Fin n, e.1 = s(h, t) ∧ G.Adj h t ∧
      ∃ i0, (A i0 (a e) (b e) ∧ B i0 (a e) (b e)) ∧
      (∀ i, A i (a e) (b e) → B i (a e) (b e) → i = i0) ∧ lab i0 = h := by
    intro e
    obtain ⟨i0, h1, h2, h3, _⟩ := hI e (a e) (b e) (Or.inr (hadj e))
    rcases h3 with h3 | h3
    · exact ⟨a e, b e, hab e, hadj e, i0, h1, h2, h3⟩
    · exact ⟨b e, a e, (hab e).trans Sym2.eq_swap, (hadj e).symm, i0, h1, h2, h3⟩
  choose hd tl hdt hadj2 hdi using hhd
  have hmem : ∀ (e : G.edgeSet) (u : Fin n), (u = hd e ∨ u = tl e) ↔ u ∈ e.1 := fun e u => by
    rw [hdt e, Sym2.mem_iff]
  have hmem2 : ∀ (e : G.edgeSet) (u : Fin n), (u = a e ∨ u = b e) ↔ u ∈ e.1 := fun e u => by
    rw [hab e, Sym2.mem_iff]
  have hadjm : ∀ (e : G.edgeSet) (u v : Fin n), u ∈ e.1 → v ∈ e.1 → u ≠ v →
      G.Adj u v ∧ e.1 = s(u, v) := by
    intro e u v hu hv huv
    have := (Sym2.mem_and_mem_iff huv).1 ⟨hu, hv⟩
    exact ⟨(SimpleGraph.mem_edgeSet G).1 (this ▸ e.2), this⟩
  have hfin := core (s := s) hd tl (fun e => (hadj2 e).ne) (fun e i => A i (a e) (b e))
    (fun w i => B i w w) (fun e i => B i (a e) (b e)) lab ?_ ?_ ?_
  · refine ⟨Finset.univ.image hd, fun u v huv => ?_, ?_⟩
    · let e : G.edgeSet := ⟨s(u, v), (SimpleGraph.mem_edgeSet G).2 huv⟩
      have h1 : hd e ∈ Finset.univ.image hd := Finset.mem_image_of_mem _ (Finset.mem_univ _)
      have h2 : hd e ∈ s(u, v) := (hmem e (hd e)).1 (Or.inl rfl)
      rcases Sym2.mem_iff.1 h2 with h | h
      · left; rw [← h]; exact h1
      · right; rw [← h]; exact h1
    · rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      exact hfin
  · intro e w hw
    obtain ⟨i0, h1, h2, h3, h4⟩ := hI e w w (Or.inl rfl)
    refine ⟨i0, h1, h2, ?_⟩
    by_contra hne
    exact h4 ⟨Or.inl (hadjm e w (lab i0) ((hmem e w).1 hw) ((hmem2 e _).1 h3) (Ne.symm hne)).1,
      hne, hne⟩
  · intro e
    exact hdi e
  · intro e e' u hee hu hu'
    obtain ⟨i0, h1, h2, h3, h4⟩ := hI e (a e') (b e') (Or.inr (hadj e'))
    refine ⟨i0, h1, h2, ?_⟩
    by_contra hne
    have hue : u ∈ e.1 := (hmem e u).1 hu
    have hue' : u ∈ e'.1 := (hmem e' u).1 (Or.inr hu')
    have hl := (hmem2 e _).1 h3
    obtain ⟨k1, k2⟩ := hadjm e u (lab i0) hue hl (Ne.symm hne)
    have hn : lab i0 ∉ e'.1 := fun hm => by
      obtain ⟨_, k3⟩ := hadjm e' u (lab i0) hue' hm (Ne.symm hne)
      exact hee (Subtype.ext (k2.trans k3.symm))
    refine h4 ⟨?_, fun h => hn ((hmem2 e' _).1 (Or.inl h)), fun h => hn ((hmem2 e' _).1 (Or.inr h))⟩
    rcases (hmem2 e' u).2 hue' with h | h
    · left; rw [← h]; exact k1
    · right; rw [← h]; exact k1
