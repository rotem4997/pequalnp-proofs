import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowerPart
import PEqualNP.MetaComplexity.Helpers.LowerPart2

namespace PEqualNP.Outside.L_meta_4743

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm
open PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)

variable {n : ℕ}

-- The wire is true at two unit inputs of different sides.
def TS (C : Circuit) (s : Fin n → Bool) (w : ℕ) : Prop :=
  ∃ y y' : Fin n, wireVal n C w (unitInput y) = true ∧ wireVal n C w (unitInput y') = true ∧ s y ≠ s y'

theorem ts_input (C : Circuit) (s : Fin n → Bool) (w : ℕ) (hw : w < n) : ¬ TS C s w := by
  rintro ⟨y, y', h, h', hs⟩
  rw [wireVal_lt C w hw] at h h'
  simp only [unitInput, decide_eq_true_eq] at h h'
  exact hs (by rw [← h, ← h'])

theorem unit_pair (y : Fin n) (x : Fin n → Bool) (hy : x y = true) (C : Circuit) (hC : IsAO2 n C) (w : ℕ)
    (hw : w < n + C.gates.length) (h : wireVal n C w (unitInput y) = true) : wireVal n C w x = true :=
  mono C hC _ _ (unit_le y x hy) w hw h

theorem main (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool) (g : ℕ)
    (hs : ∀ u v : Fin n, G.Adj u v → s u ≠ s v) (H : OneDirty G C g)
    (hunit : ∀ w : Fin n, gateVal n C g (unitInput w) = false) (c : Fin 2)
    (h2 : TS C s (opnd C g c))
    (h1 : ∀ y y' : Fin n, wireVal n C (opnd C g (1 - c)) (unitInput y) = true →
      wireVal n C (opnd C g (1 - c)) (unitInput y') = true → s y = s y') :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  have hAO := H.ao
  have hgl := H.hg
  have hAlt := opnd_lt C hAO g hgl c
  have hBlt := opnd_lt C hAO g hgl (1 - c)
  -- a variable of the one-sided operand
  obtain ⟨b0, hb0⟩ : ∃ b, wireVal n C (opnd C g (1 - c)) (unitInput b) = true := by
    obtain ⟨y, _, h⟩ := (opnd_val H (1 - c) (fun _ => true)).1 (ones_val C hAO _ (by omega))
    exact ⟨y, h⟩
  have hB : ∀ y, wireVal n C (opnd C g (1 - c)) (unitInput y) = true → s y = s b0 :=
    fun y h => h1 y b0 h hb0
  -- the lowest two-sided gate in the tree of the two-sided operand
  have hex : ∃ t, t < C.gates.length ∧ OrReaches n C (opnd C g c) t ∧ TS C s (n + t) := by
    have hge : ¬ opnd C g c < n := fun h => ts_input C s _ h h2
    have e : n + (opnd C g c - n) = opnd C g c := by omega
    refine ⟨opnd C g c - n, by omega, ?_, by rw [e]; exact h2⟩
    have := reach_self C hAO (opnd C g c - n) (by omega)
    rwa [e] at this
  obtain ⟨t, ⟨htl, htr, htt⟩, hmin⟩ : ∃ t, (t < C.gates.length ∧ OrReaches n C (opnd C g c) t ∧ TS C s (n + t)) ∧
      ∀ m, m < t → ¬ (m < C.gates.length ∧ OrReaches n C (opnd C g c) m ∧ TS C s (n + m)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have htlow : Low G C (n + t) := by
    intro h
    obtain ⟨y, _, hy, _⟩ := htt
    have := h _ hy
    rw [unit_false] at this
    exact Bool.false_ne_true this
  have htg : ¬ OrReaches n C (n + t) g := fun h =>
    not_reach_opnd C hAO g hgl c (reach_trans C hAO t g htl h _ (by omega) htr)
  have hto : (gateAt C t).op = GateOp.or := by
    rcases LeafBound.ao_op hAO htl with ho | ho
    · have := low_and H t htl ho htlow
      subst this
      exact absurd htr (not_reach_opnd C hAO t htl c)
    · exact ho
  have htop : ∀ d, ¬ TS C s (opnd C t d) := by
    intro d hd
    by_cases hlt : opnd C t d < n
    · exact ts_input C s _ hlt hd
    · have hdl := opnd_lt C hAO t htl d
      have e : n + (opnd C t d - n) = opnd C t d := by omega
      refine hmin (opnd C t d - n) (by omega) ⟨by omega, ?_, by rw [e]; exact hd⟩
      refine reach_trans C hAO t _ htl ?_ _ (by omega) htr
      refine (reach_gate C hAO t _ htl).2 (Or.inr ⟨hto, d, ?_⟩)
      have := reach_self C hAO (opnd C t d - n) (by omega)
      rwa [e] at this
  have htv : ∀ x, gateVal n C t x = true ↔ ∃ d, wireVal n C (opnd C t d) x = true :=
    val_or' C hAO t htl hto
  have htA : ∀ y, gateVal n C t (unitInput y) = true → wireVal n C (opnd C g c) (unitInput y) = true :=
    fun y h => (reach_le C hAO t _ (by omega) htr).2 _ h
  -- its variables on both sides
  obtain ⟨p0, q0, hp0, hq0, hsp, hsq⟩ : ∃ p0 q0 : Fin n, gateVal n C t (unitInput p0) = true ∧
      gateVal n C t (unitInput q0) = true ∧ s p0 ≠ s b0 ∧ s q0 = s b0 := by
    obtain ⟨y, y', hy, hy', hne⟩ := htt
    by_cases h : s y = s b0
    · exact ⟨y', y, hy', hy, fun h' => hne (h.trans h'.symm), h⟩
    · refine ⟨y, y', hy, hy', h, ?_⟩
      revert hne h
      cases s y <;> cases s y' <;> cases s b0 <;> simp
  obtain ⟨e, he⟩ := (htv _).1 hp0
  have hel := opnd_lt C hAO t htl e
  have hside : ∀ y, gateVal n C t (unitInput y) = true → s y ≠ s b0 →
      wireVal n C (opnd C t e) (unitInput y) = true := by
    intro y hy hsy
    obtain ⟨d, hd⟩ := (htv _).1 hy
    rcases fin2_or e d with rfl | rfl
    · exact hd
    · exfalso
      obtain ⟨d', hd'⟩ := (htv _).1 hq0
      rcases fin2_or e d' with rfl | rfl
      · exact htop _ ⟨p0, q0, he, hd', fun h => hsp (h.trans hsq)⟩
      · exact htop _ ⟨y, q0, hd, hd', fun h => hsy (h.trans hsq)⟩
  -- a q in the tree on the side of b0 is not adjacent to a variable of B
  have hdisj : ∀ z, gateVal n C t (unitInput z) = true →
      ¬ wireVal n C (opnd C g (1 - c)) (unitInput z) = true := by
    intro z hz hz'
    have := (val_and' C hAO g hgl H.gand (unitInput z) c).2 ⟨htA z hz, hz'⟩
    rw [hunit z] at this
    exact Bool.false_ne_true this
  -- no other AND reads a wire above t
  have noAnd : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → j ≠ g → ∀ d,
      ¬ OrReaches n C (opnd C j d) t := by
    intro j hj ho hjg d hr
    have hjl := opnd_lt C hAO j hj d
    have hjl' := opnd_lt C hAO j hj (1 - d)
    have up : ∀ y, gateVal n C t (unitInput y) = true → wireVal n C (opnd C j d) (unitInput y) = true :=
      fun y h => (reach_le C hAO t _ (by omega) hr).2 _ h
    by_cases hvar : ∃ z, wireVal n C (opnd C j (1 - d)) (unitInput z) = true
    · obtain ⟨z, hz⟩ := hvar
      have a1 := hs _ _ (and_pair' H j hj ho hjg d p0 z (up p0 hp0) hz)
      have a2 := hs _ _ (and_pair' H j hj ho hjg d q0 z (up q0 hq0) hz)
      rw [hsq] at a2
      revert a1 a2 hsp
      cases s p0 <;> cases s z <;> cases s b0 <;> simp
    · have hlow := low_opnd H j hj (1 - d) (Or.inr ho)
      have hone := (val_low H _ (by omega) hlow (fun _ => true)).1 (ones_val C hAO _ (by omega))
      rcases hone with ⟨z, _, hz⟩ | ⟨hrg, _⟩
      · exact hvar ⟨z, hz⟩
      · have hadj : G.Adj q0 b0 := by
          apply pair_adj
          refine H.others j hj ho hjg _ ((val_and' C hAO j hj ho _ d).2 ⟨?_, ?_⟩)
          · exact unit_pair q0 _ (by simp [pairInput]) C hAO _ (by omega) (up q0 hq0)
          · refine (reach_le C hAO g _ (by omega) hrg).2 _ ((val_and' C hAO g hgl H.gand _ c).2 ⟨?_, ?_⟩)
            · exact unit_pair q0 _ (by simp [pairInput]) C hAO _ (by omega) (htA q0 hq0)
            · exact unit_pair b0 _ (by simp [pairInput]) C hAO _ (by omega) hb0
        exact hs _ _ hadj hsq
  -- redirect t to its operand e
  obtain ⟨o, hol, hoo, hob⟩ := out_gate H
  have hot : ¬ OrReaches n C (n + o) t := by
    intro h
    refine htlow fun x hx => hob x ?_
    exact (reach_le C hAO t _ (by omega) h).2 x hx
  have hone : n + o ≠ n + t := by
    intro h
    exact hot (by rw [h]; exact reach_self C hAO t htl)
  let r : ℕ → ℕ := fun u => if u = n + t then opnd C t e else u
  have hrne : ∀ u, u ≠ n + t → r u = u := fun u h => by simp [r, h]
  have hrt : r (n + t) = opnd C t e := by simp [r]
  have hrk : ∀ u, r u ≠ n + t ∧ r u ≤ u := by
    intro u
    by_cases h : u = n + t
    · rw [h, hrt]; omega
    · rw [hrne u h]; exact ⟨h, le_refl _⟩
  have hro : r C.output = n + o := by rw [hoo]; exact hrne _ hone
  have hFo : ∀ x, gateVal n C o x = graphFun G ∅ x := by
    intro x
    rw [← H.comp]
    show wireVal n C (n + o) x = wireVal n C C.output x
    rw [hoo]
  refine redirect_lt G C ((Finset.range C.gates.length).erase t) ?_ (fun j b => srcOf n (r (opnd C j b))) ?_
    (srcOf n (r C.output)) ?_ (adj_of_AO G C hAO H.comp (by omega)) ?_ ?_ ⟨t, htl, Or.inl (by simp)⟩
  · intro j hj
    exact Finset.mem_range.1 (Finset.mem_erase.1 hj).2
  · intro j hj b i hi
    have hjl := Finset.mem_range.1 (Finset.mem_erase.1 hj).2
    have hlt := opnd_lt C hAO j hjl b
    have hi' := srcOf_inr _ _ hi
    have := hrk (opnd C j b)
    exact ⟨Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 (by omega)⟩, by omega⟩
  · intro i hi
    have hi' := srcOf_inr _ _ hi
    rw [hro] at hi'
    exact Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 (by omega)⟩
  · intro x hx
    refine ⟨fun j => gateVal n C j x, super_of_le C hAO _ ?_ _ x ?_, ?_⟩
    · intro j hj
      exact Finset.mem_range.1 (Finset.mem_erase.1 hj).2
    · intro j _ b h
      rw [srcAt_srcOf] at h
      by_cases hu : opnd C j b = n + t
      · rw [hu, hrt] at h
        rw [hu]
        exact (htv x).2 ⟨e, h⟩
      · rwa [hrne _ hu] at h
    · rw [srcAt_srcOf, hro]
      exact (hFo x).trans hx
  · intro p q hpq
    have hFpq : graphFun G ∅ (pairInput p q) = true :=
      (graphFun_empty G _).2 ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
    by_cases hL : gateVal n C t (pairInput p q) = true ∧ ¬ wireVal n C (opnd C t e) (pairInput p q) = true
    · obtain ⟨hLt, hLe⟩ := hL
      -- t is on through a vertex z on the side of b0 only, so g is off
      have hgoff : ¬ gateVal n C g (pairInput p q) = true := by
        intro hg1
        have hBx := ((val_and' C hAO g hgl H.gand _ c).1 hg1).2
        obtain ⟨y, hy, hyB⟩ := (opnd_val H (1 - c) _).1 hBx
        obtain ⟨z, hz, hzt⟩ : ∃ z, pairInput p q z = true ∧ gateVal n C t (unitInput z) = true := by
          rcases (val_low H (n + t) (by omega) htlow _).1 hLt with h | ⟨h, _⟩
          · exact h
          · exact absurd h htg
        have hzs : s z = s b0 := by
          by_contra hne
          exact hLe (unit_pair z _ hz C hAO _ (by omega) (hside z hzt hne))
        have hys := hB y hyB
        have hyz : y ≠ z := by
          rintro rfl
          exact hdisj y hzt hyB
        have hpqs := hs _ _ hpq
        simp only [pairInput, decide_eq_true_eq] at hy hz
        rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
        · exact hyz rfl
        · exact hpqs (hys.trans hzs.symm)
        · exact hpqs (hzs.trans hys.symm)
        · exact hyz rfl
      refine ⟨fun j => gateVal n C j (pairInput p q) && decide (¬ OrReaches n C (n + j) t), ?_, ?_⟩
      · have wire : ∀ w, wireVal n C w (pairInput p q) = true → ¬ OrReaches n C w t →
            srcAt (pairInput p q) (fun j => gateVal n C j (pairInput p q) && decide (¬ OrReaches n C (n + j) t))
              (srcOf n (r w)) = true := by
          intro w hw hnr
          have hwt : w ≠ n + t := by
            rintro rfl
            exact hnr (reach_self C hAO t htl)
          rw [hrne w hwt]
          rcases srcOf_cases (n := n) w with ⟨v, rfl⟩ | ⟨j, rfl⟩
          · rw [srcOf_input]
            rw [wireVal_lt C _ v.2] at hw
            exact hw
          · rw [srcOf_gate]
            show (gateVal n C j (pairInput p q) && decide (¬ OrReaches n C (n + j) t)) = true
            rw [Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨hw, hnr⟩
        intro j hj hu
        have hjl := Finset.mem_range.1 (Finset.mem_erase.1 hj).2
        rw [Bool.and_eq_true, decide_eq_true_eq] at hu
        obtain ⟨hv, hnr⟩ := hu
        rcases LeafBound.ao_op hAO hjl with ho | ho
        · have hjg : j ≠ g := by
            rintro rfl
            exact hgoff hv
          obtain ⟨a0, a1⟩ := (val_and C hAO j hjl ho _).1 hv
          have : (progOf (n := n) C (fun j b => srcOf n (r (opnd C j b)))).isAnd j = true := by
            show isA (gateAt C j).op = true
            rw [ho]; rfl
          rw [this]
          exact (opv_and _ _).2 ⟨wire _ a0 (noAnd j hjl ho hjg 0), wire _ a1 (noAnd j hjl ho hjg 1)⟩
        · have hnd : ∀ d, ¬ OrReaches n C (opnd C j d) t := fun d hd =>
            hnr ((reach_gate C hAO j t hjl).2 (Or.inr ⟨ho, d, hd⟩))
          have : (progOf (n := n) C (fun j b => srcOf n (r (opnd C j b)))).isAnd j = false := by
            show isA (gateAt C j).op = false
            rw [ho]; rfl
          rw [this]
          refine (opv_or _ _).2 ?_
          rcases (val_or C hAO j hjl ho _).1 hv with h | h
          · exact Or.inl (wire _ h (hnd 0))
          · exact Or.inr (wire _ h (hnd 1))
      · rw [hro, srcOf_gate]
        show (gateVal n C o (pairInput p q) && decide (¬ OrReaches n C (n + o) t)) = true
        rw [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨(hFo _).trans hFpq, hot⟩
    · refine ⟨fun j => gateVal n C j (pairInput p q), ?_, ?_⟩
      · intro j hj h
        have hjl := Finset.mem_range.1 (Finset.mem_erase.1 hj).2
        simp only at h
        rw [gate_eq C hAO j hjl] at h
        have key : ∀ b, wireVal n C (opnd C j b) (pairInput p q) = true →
            srcAt (pairInput p q) (fun j => gateVal n C j (pairInput p q)) (srcOf n (r (opnd C j b))) = true := by
          intro b hb
          rw [srcAt_srcOf]
          by_cases hu : opnd C j b = n + t
          · rw [hu, hrt]
            by_contra hne
            rw [hu] at hb
            exact hL ⟨hb, hne⟩
          · rwa [hrne _ hu]
        exact opv_mono _ _ _ _ _ (key 0) (key 1) h
      · rw [srcAt_srcOf, hro]
        exact (hFo _).trans hFpq

end PEqualNP.Outside.L_meta_4743

theorem PEqualNP.Outside.L_meta_4743 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → (∀ w : Fin n, PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput w) = false) → (((∃ y y' : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y) = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y') = true ∧ s y ≠ s y') ∧ (∀ y y' : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y) = true → PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y') = true → s y = s y')) ∨ ((∃ y y' : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y) = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y') = true ∧ s y ≠ s y') ∧ (∀ y y' : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y) = true → PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y') = true → s y = s y'))) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C s g hs _ hAO hcomp hlift hlow hcone hg hand hdirty hothers hunit h
  have H : PEqualNP.MetaComplexity.LowerPart.OneDirty G C g :=
    ⟨hAO, hcomp, hlift, hlow, hcone, hg, hand, hdirty, hothers⟩
  rcases h with ⟨h2, h1⟩ | ⟨h2, h1⟩
  · exact PEqualNP.Outside.L_meta_4743.main G C s g hs H hunit 0 h2 h1
  · exact PEqualNP.Outside.L_meta_4743.main G C s g hs H hunit 1 h2 h1
