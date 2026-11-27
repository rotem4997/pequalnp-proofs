import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1840

theorem arith1 (s q k m : ℕ) (hs : s ≤ q + 1) (hmq : m ≤ q) (hmk : m ≤ k) :
    s * m ≤ q * min (s - 1) k + m := by
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · subst h0
    simp
  · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hs' : s' ≤ q := by omega
    have e : (s' + 1) * m = s' * m + m := by ring
    rw [Nat.add_sub_cancel, e]
    rcases le_total s' k with h | h
    · rw [min_eq_left h]
      have h1 : s' * m ≤ q * s' := by
        rw [Nat.mul_comm q s']
        exact Nat.mul_le_mul_left _ hmq
      omega
    · rw [min_eq_right h]
      have h1 : s' * m ≤ q * k := Nat.mul_le_mul hs' hmk
      omega

end PEqualNP.Outside.L_meta_1840

theorem PEqualNP.Outside.L_meta_1840 : (∀ (n1 m1 k1 : ℕ) (U1 S1 : Fin m1 → Finset (Fin n1)) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (o1 c1 : Fin m1 → ℕ), (∀ i1 j1 : Fin m1, i1 ≠ j1 → (U1 i1 ∩ U1 j1).card ≤ 1) → (∀ i1a : Fin m1, S1 i1a ⊆ U1 i1a) → (∀ i1b : Fin m1, 2 ≤ (S1 i1b).card) → (∀ g1 ∈ C1.gates, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g1.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack n1 C1 → (∀ (i1c : Fin m1) (p1 : Fin n1), (C1.wires (List.ofFn (fun a1 : Fin n1 => decide (a1 = p1)))).getD (o1 i1c) false = true ↔ p1 ∈ S1 i1c) → (∀ (i1d : Fin m1) (x1 : Fin n1 → Bool), (Finset.univ.filter (fun b1 : Fin n1 => x1 b1 = true)).card ≤ k1 → (∀ b1a ∈ U1 i1d, x1 b1a = false) → (C1.wires (List.ofFn x1)).getD (o1 i1d) false = false) → (∀ i1e : Fin m1, c1 i1e ≤ k1) → (∀ i1f : Fin m1, c1 i1f + 1 ≤ (S1 i1f).card) → ∑ i1g : Fin m1, c1 i1g ≤ C1.size) → ∀ (qlv17c Nlv17c Rlv17c : ℕ) (Ilv17c : Fin Nlv17c → Fin Nlv17c → Prop) [DecidableRel Ilv17c] (Xlv17c : PEqualNP.CircuitLowerBounds.Circuit) (pslv17c : Fin Nlv17c → ℕ) (Slv17c Wlv17c : Finset (Fin Nlv17c)), 2 ≤ qlv17c → Nlv17c = qlv17c ^ 2 + qlv17c + 1 → (∀ llv17c : Fin Nlv17c, (Finset.univ.filter (fun plv17cx2 => Ilv17c plv17cx2 llv17c)).card = qlv17c + 1) → (∀ palv17c pblv17c : Fin Nlv17c, palv17c ≠ pblv17c → ∃! lblv17c : Fin Nlv17c, Ilv17c palv17c lblv17c ∧ Ilv17c pblv17c lblv17c) → 1 ≤ Rlv17c → Rlv17c ≤ qlv17c → ((∀ glv17c ∈ Xlv17c.gates, (glv17c.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17c.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17c.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack Nlv17c Xlv17c) → (∀ (wlv17c : Fin Nlv17c) (xlv17c xlv17cx1 : Fin Nlv17c → Bool), (∀ plv17c ∈ Slv17c, xlv17c plv17c = xlv17cx1 plv17c) → (Xlv17c.wires (List.ofFn xlv17c)).getD (pslv17c wlv17c) false = (Xlv17c.wires (List.ofFn xlv17cx1)).getD (pslv17c wlv17c) false) → (∀ wlv17cx1 ∈ Wlv17c, ∀ Xslv17c : Finset (Fin Nlv17c), Xslv17c ⊆ Slv17c → (∀ plv17cx1 ∈ Xslv17c, ¬ Ilv17c plv17cx1 wlv17cx1) → Xslv17c.card ≤ Rlv17c → (Xlv17c.wires (List.ofFn (fun alv17c : Fin Nlv17c => decide (alv17c ∈ Xslv17c)))).getD (pslv17c wlv17cx1) false = false) → Rlv17c * ∑ wlv17cx2 ∈ Wlv17c, (Slv17c.filter (fun ulv17c : Fin Nlv17c => (Xlv17c.wires (List.ofFn (fun alv17cx1 : Fin Nlv17c => decide (alv17cx1 = ulv17c)))).getD (pslv17c wlv17cx2) false = true)).card ≤ Rlv17c * Wlv17c.card + qlv17c * Xlv17c.size := by
  intro H1 q N R I inst X ps S W hq hN hl hu hR1 hRq hgr hdep hsound
  obtain ⟨hXg, hXr⟩ := hgr
  obtain ⟨SX, hSXe⟩ : ∃ SX : Fin N → Finset (Fin N), ∀ w, SX w = S.filter (fun u : Fin N => (X.wires (List.ofFn (fun a : Fin N => decide (a = u)))).getD (ps w) false = true) :=
    ⟨fun w => S.filter (fun u : Fin N => (X.wires (List.ofFn (fun a : Fin N => decide (a = u)))).getD (ps w) false = true), fun w => rfl⟩
  have hSX : ∀ w u, u ∈ SX w ↔ u ∈ S ∧ (X.wires (List.ofFn (fun a : Fin N => decide (a = u)))).getD (ps w) false = true := fun w u => by
    rw [hSXe, Finset.mem_filter]
  obtain ⟨UX, hUXe⟩ : ∃ UX : Fin N → Finset (Fin N), ∀ w, UX w = Finset.univ.filter (fun p => I p w) :=
    ⟨fun w => Finset.univ.filter (fun p => I p w), fun w => rfl⟩
  have hUX : ∀ w p, p ∈ UX w ↔ I p w := fun w p => by rw [hUXe]; simp
  have hUXc : ∀ w, (UX w).card = q + 1 := fun w => by rw [hUXe]; exact hl w
  have hUXint : ∀ i j : Fin N, i ≠ j → (UX i ∩ UX j).card ≤ 1 := by
    intro i j hij
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    rw [Finset.mem_inter, hUX, hUX] at ha hb
    exact hij ((hu a b hab).unique ⟨ha.1, hb.1⟩ ⟨ha.2, hb.2⟩)
  have hempty : ∀ w ∈ W, (X.wires (List.ofFn (fun _ : Fin N => false))).getD (ps w) false = false := by
    intro w hw
    have h := hsound w hw ∅ (Finset.empty_subset _) (fun p hp => absurd hp (by simp)) (by simp)
    have e : (fun a : Fin N => decide (a ∈ (∅ : Finset (Fin N)))) = (fun _ => false) := by
      funext a
      simp
    rw [e] at h
    exact h
  have hoff : ∀ w ∈ W, ∀ u, u ∉ S →
      (X.wires (List.ofFn (fun a : Fin N => decide (a = u)))).getD (ps w) false = false := by
    intro w hw u hu'
    refine (hdep w (fun a : Fin N => decide (a = u)) (fun _ => false) (fun a ha => ?_)).trans (hempty w hw)
    have hne : a ≠ u := fun h => hu' (h ▸ ha)
    simp [hne]
  have hSUX : ∀ w ∈ W, SX w ⊆ UX w := by
    intro w hw u hp
    rw [hSX] at hp
    rw [hUX]
    by_contra hI
    have h := hsound w hw {u} (Finset.singleton_subset_iff.mpr hp.1)
      (fun a ha => by
        rw [Finset.mem_singleton] at ha
        rw [ha]
        exact hI)
      (by rw [Finset.card_singleton]; exact hR1)
    have e : (fun a : Fin N => decide (a ∈ ({u} : Finset (Fin N)))) = (fun a => decide (a = u)) := by
      funext a
      simp
    rw [e] at h
    exact Bool.false_ne_true (h.symm.trans hp.2)
  have hex : ∀ w ∈ W, ∀ u : Fin N, (X.wires (List.ofFn (fun a : Fin N => decide (a = u)))).getD (ps w) false = true ↔ u ∈ SX w := by
    intro w hw u
    rw [hSX]
    constructor
    · intro h
      refine ⟨?_, h⟩
      by_contra hp
      exact Bool.false_ne_true ((hoff w hw u hp).symm.trans h)
    · exact fun h => h.2
  have hsd : ∀ w ∈ W, ∀ x : Fin N → Bool,
      (Finset.univ.filter (fun b : Fin N => x b = true)).card ≤ R → (∀ b ∈ UX w, x b = false) →
      (X.wires (List.ofFn x)).getD (ps w) false = false := by
    intro w hw x hc hz
    have h := hsound w hw (S.filter (fun b => x b = true)) (Finset.filter_subset _ _)
      (fun p hp hI => by
        have h1 := (Finset.mem_filter.mp hp).2
        rw [hz p ((hUX w p).2 hI)] at h1
        exact Bool.false_ne_true h1)
      ((Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans hc)
    refine (hdep w x (fun a : Fin N => decide (a ∈ S.filter (fun b => x b = true))) (fun p hp => ?_)).trans h
    cases hx : x p <;> simp [hp, hx]
  have key : ∑ w ∈ W, min ((SX w).card - 1) R ≤ X.size := by
    obtain ⟨T, hT⟩ : ∃ T : Finset (Fin N), ∀ i, i ∈ T ↔ i ∈ W ∧ 2 ≤ (SX i).card :=
      ⟨W.filter (fun i => 2 ≤ (SX i).card), fun i => by rw [Finset.mem_filter]⟩
    obtain ⟨e⟩ : Nonempty (Fin T.card ≃ T) := ⟨T.equivFin.symm⟩
    have h := H1 N T.card R (fun j => UX (e j)) (fun j => SX (e j)) X (fun j => ps (e j))
      (fun j => min ((SX (e j)).card - 1) R)
      (fun i j hij => hUXint _ _ (fun h => hij (e.injective (Subtype.ext h))))
      (fun i => hSUX _ ((hT _).1 (e i).2).1)
      (fun i => ((hT _).1 (e i).2).2)
      hXg hXr (fun i u => hex _ ((hT _).1 (e i).2).1 u)
      (fun i x hx hz => hsd _ ((hT _).1 (e i).2).1 x hx hz)
      (fun i => min_le_right _ _)
      (fun i => by
        have h2 := ((hT _).1 (e i).2).2
        have h3 := min_le_left ((SX (e i)).card - 1) R
        omega)
    calc ∑ w ∈ W, min ((SX w).card - 1) R = ∑ i ∈ T, min ((SX i).card - 1) R := by
          symm
          apply Finset.sum_subset (fun i hi => ((hT i).1 hi).1)
          intro i hiW hi
          have h2 : ¬ 2 ≤ (SX i).card := fun h => hi ((hT i).2 ⟨hiW, h⟩)
          have h3 : (SX i).card - 1 = 0 := by omega
          rw [h3]
          simp
      _ = ∑ i : T, min ((SX i).card - 1) R :=
          (Finset.sum_coe_sort T (fun i => min ((SX i).card - 1) R)).symm
      _ = ∑ j : Fin T.card, min ((SX (e j)).card - 1) R :=
          (Equiv.sum_comp e (fun i : T => min ((SX i).card - 1) R)).symm
      _ ≤ X.size := h
  have hSXc : ∀ w ∈ W, (SX w).card ≤ q + 1 := fun w hw =>
    (Finset.card_le_card (hSUX w hw)).trans_eq (hUXc w)
  have sX : (∑ w ∈ W, (SX w).card) * R ≤ q * X.size + W.card * R := by
    calc (∑ w ∈ W, (SX w).card) * R = ∑ w ∈ W, (SX w).card * R := Finset.sum_mul _ _ _
      _ ≤ ∑ w ∈ W, (q * min ((SX w).card - 1) R + R) :=
          Finset.sum_le_sum (fun w hw =>
            PEqualNP.Outside.L_meta_1840.arith1 _ q R R (hSXc w hw) hRq le_rfl)
      _ = q * ∑ w ∈ W, min ((SX w).card - 1) R + W.card * R := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul]
      _ ≤ q * X.size + W.card * R := Nat.add_le_add_right (Nat.mul_le_mul_left _ key) _
  have e2 : ∑ w ∈ W, (S.filter (fun u : Fin N => (X.wires (List.ofFn (fun a : Fin N => decide (a = u)))).getD (ps w) false = true)).card = ∑ w ∈ W, (SX w).card :=
    Finset.sum_congr rfl (fun w _ => by rw [hSXe])
  rw [e2]
  calc R * ∑ w ∈ W, (SX w).card = (∑ w ∈ W, (SX w).card) * R := Nat.mul_comm _ _
    _ ≤ q * X.size + W.card * R := sX
    _ = R * W.card + q * X.size := by ring
