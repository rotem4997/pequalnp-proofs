import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowerPart

namespace PEqualNP.Outside.L_meta_4746

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm
open PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount
open PEqualNP.EdgeOwnership

theorem bool_eq_true (b : Bool) (h : b ≠ false) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

theorem bool_and_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem bool_or_iff (a b : Bool) : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem opv_true_iff (p q : Bool) : opv true p q = true ↔ p = true ∧ q = true := by
  cases p <;> cases q <;> decide

theorem opv_false_iff (p q : Bool) : opv false p q = true ↔ p = true ∨ q = true := by
  cases p <;> cases q <;> decide

theorem bool_ne_tri {a b c : Bool} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : False := by
  cases a <;> cases b <;> cases c <;>
    first | exact hab rfl | exact hbc rfl | exact hac rfl

theorem pair_third {α : Type} {p q z y1 y2 : α}
    (hz : z = p ∨ z = q) (h1 : y1 = p ∨ y1 = q) (h2 : y2 = p ∨ y2 = q)
    (h12 : y1 ≠ y2) (hz1 : z ≠ y1) : z = y2 := by
  rcases hz with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    first | rfl | exact absurd rfl h12 | exact absurd rfl hz1

theorem gateOp_and_ne_or (h : GateOp.and = GateOp.or) : False :=
  GateOp.noConfusion h

theorem gateOp_or_ne_and (h : GateOp.or = GateOp.and) : False :=
  GateOp.noConfusion h

def other (d : Fin 2) : Fin 2 := if d = 0 then 1 else 0

theorem other_ne (d : Fin 2) : other d ≠ d := by
  fin_cases d <;> decide

theorem other_other (d : Fin 2) : other (other d) = d := by
  fin_cases d <;> decide

theorem pairInput_true {n : ℕ} (p q z : Fin n) :
    pairInput p q z = true ↔ z = p ∨ z = q := by
  simp [pairInput]

theorem and_of_fin2 {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (x : Fin n → Bool) (d : Fin 2) :
    gateVal n C k x = true ↔
      wireVal n C (opnd C k d) x = true ∧ wireVal n C (opnd C k (other d)) x = true := by
  rw [val_and C hC k hk ho x]
  fin_cases d <;> simp [other, and_comm]

theorem or_of_fin2 {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.or) (x : Fin n → Bool) (d : Fin 2) :
    gateVal n C k x = true ↔
      wireVal n C (opnd C k d) x = true ∨ wireVal n C (opnd C k (other d)) x = true := by
  rw [val_or C hC k hk ho x]
  fin_cases d <;> simp [other, or_comm]

theorem and_pair_fin2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}
    (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (hkg : k ≠ g) (d : Fin 2) (y z : Fin n)
    (hy : wireVal n C (opnd C k d) (unitInput y) = true)
    (hz : wireVal n C (opnd C k (other d)) (unitInput z) = true) : G.Adj y z := by
  fin_cases d
  · exact and_pair H k hk ho hkg y z hy hz
  · exact (and_pair H k hk ho hkg z y hz hy).symm

theorem not_both_fin2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}
    (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (d : Fin 2) (hd : OrReaches n C (opnd C k d) g) :
    ¬ OrReaches n C (opnd C k (other d)) g := by
  intro hd'
  apply not_both H k hk ho
  fin_cases d
  · exact ⟨hd, hd'⟩
  · exact ⟨hd', hd⟩

theorem no_four_cycle_eq {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hC4 : NoFourCycle G) {a b c d : Fin n} (hab : a ≠ b)
    (hac : G.Adj a c) (had : G.Adj a d) (hbc : G.Adj b c) (hbd : G.Adj b d) : c = d := by
  classical
  by_contra hcd
  let S : Finset (Fin n) := Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w)
  have hsub : ({c, d} : Finset (Fin n)) ⊆ S := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rcases hw with rfl | rfl
    · exact ⟨hac, hbc⟩
    · exact ⟨had, hbd⟩
  have hcard : ({c, d} : Finset (Fin n)).card = 2 := Finset.card_pair hcd
  have hle := (Finset.card_le_card hsub).trans (hC4 a b hab)
  omega

theorem adj_of_pair {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {y z : Fin n}
    (h : graphFun G ∅ (pairInput y z) = true) : G.Adj y z := by
  obtain ⟨u, w, huw, hu, hw⟩ := (graphFun_empty G _).1 h
  simp only [pairInput, decide_eq_true_eq] at hu hw
  rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
  · exact absurd huw (G.loopless.irrefl _)
  · exact huw
  · exact huw.symm
  · exact absurd huw (G.loopless.irrefl _)

theorem pair_of_adj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {y z : Fin n}
    (h : G.Adj y z) : graphFun G ∅ (pairInput y z) = true := by
  refine (graphFun_empty G _).2 ⟨y, z, h, ?_, ?_⟩
  · simp [pairInput]
  · simp [pairInput]

theorem mono_unit {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (w : ℕ) (hw : w < n + C.gates.length)
    (x : Fin n → Bool) (y : Fin n) (hy : x y = true)
    (hwy : wireVal n C w (unitInput y) = true) : wireVal n C w x = true := by
  refine mono C hC (unitInput y) x ?_ w hw hwy
  intro a ha
  simp only [unitInput, decide_eq_true_eq] at ha
  rw [ha]
  exact hy

theorem reach_self {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (reach_gate C hC j j hj).2 (Or.inl rfl)

theorem reach_step_or {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (k j : ℕ)
    (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.or) (d : Fin 2)
    (hd : opnd C k d = n + j) (hj : j < C.gates.length) : OrReaches n C (n + k) j := by
  refine (reach_gate C hC k j hk).2 (Or.inr ⟨ho, d, ?_⟩)
  rw [hd]
  exact reach_self C hC j hj

theorem reach_trans {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j i : ℕ) :
    ∀ w < n + C.gates.length, OrReaches n C w j → OrReaches n C (n + j) i →
      OrReaches n C w i := by
  refine wire_induction C hC _ (fun w hw h => absurd h (reach_input C w j hw)) ?_
  intro k hk ih hkj hji
  rcases (reach_gate C hC k j hk).1 hkj with rfl | ⟨ho, b, hb⟩
  · exact hji
  · refine (reach_gate C hC k i hk).2 (Or.inr ⟨ho, b, ih b hb hji⟩)

theorem low_of_reach_g {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {g : ℕ} (H : OneDirty G C g) (j : ℕ) (hj : j < C.gates.length)
    (hr : OrReaches n C (n + j) g) : Low G C (n + j) := by
  intro hbel
  refine H.dirty fun x hx => hbel x ((reach_le C H.ao g (n + j) (by omega) hr).2 x hx)

theorem srcAt_srcOf_of_agree {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ → Bool)
    (w : ℕ) (h : ∀ j, w = n + j → u j = gateVal n C j x) :
    srcAt x u (srcOf n w) = wireVal n C w x := by
  unfold srcOf
  split_ifs with hw
  · exact (wireVal_lt C w hw x).symm
  · have e : n + (w - n) = w := by omega
    rw [show srcAt x u (some (Sum.inr (w - n))) = u (w - n) from rfl]
    rw [h (w - n) e.symm]
    change wireVal n C (n + (w - n)) x = wireVal n C w x
    rw [e]

theorem redirect_wire_lt {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {g : ℕ} (H : OneDirty G C g) (hne : ∃ u w, G.Adj u w)
    (j : ℕ) (hj : j < C.gates.length) (w : ℕ) (hw : w < n + j)
    (heq : ∀ x, wireVal n C w x = gateVal n C j x) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  let K : Finset ℕ := (Finset.range C.gates.length).erase j
  let ρ : ℕ → Fin 2 → Src n ℕ := fun k d =>
    if opnd C k d = n + j then srcOf n w else srcOf n (opnd C k d)
  let o : Src n ℕ := if C.output = n + j then srcOf n w else srcOf n C.output
  have hK : ∀ k ∈ K, k < C.gates.length := fun k hk =>
    Finset.mem_range.1 (Finset.mem_of_mem_erase hk)
  have hcl : ∀ k ∈ K, ∀ d : Fin 2, ∀ i : ℕ, ρ k d = some (Sum.inr i) → i ∈ K ∧ i < k := by
    intro k hk d i hi
    have hkl := hK k hk
    have hkj : k ≠ j := (Finset.mem_erase.1 hk).1
    have hlt := opnd_lt C H.ao k hkl d
    dsimp only [ρ] at hi
    split_ifs at hi with hop
    · have hwi := srcOf_inr w i hi
      have hij : i ≠ j := by omega
      refine ⟨Finset.mem_erase.2 ⟨hij, Finset.mem_range.2 (by omega)⟩, by omega⟩
    · have hwi := srcOf_inr (opnd C k d) i hi
      have hij : i ≠ j := by omega
      refine ⟨Finset.mem_erase.2 ⟨hij, Finset.mem_range.2 (by omega)⟩, by omega⟩
  have ho : ∀ i, o = some (Sum.inr i) → i ∈ K := by
    intro i hi
    obtain ⟨o0, ho0, hco, _⟩ := out_gate H
    dsimp only [o] at hi
    split_ifs at hi with hcj
    · have hwi := srcOf_inr w i hi
      have hij : i ≠ j := by omega
      exact Finset.mem_erase.2 ⟨hij, Finset.mem_range.2 (by omega)⟩
    · have hci := srcOf_inr C.output i hi
      have hio : i = o0 := by omega
      subst hio
      have hoj : i ≠ j := by omega
      exact Finset.mem_erase.2 ⟨hoj, Finset.mem_range.2 ho0⟩
  have hsrc : ∀ (x : Fin n → Bool) (k : ℕ) (d : Fin 2),
      srcAt x (fun i => gateVal n C i x) (ρ k d) = wireVal n C (opnd C k d) x := by
    intro x k d
    dsimp only [ρ]
    split_ifs with hop
    · rw [srcAt_srcOf, heq x]
      change wireVal n C (n + j) x = wireVal n C (opnd C k d) x
      rw [← hop]
    · exact srcAt_srcOf C (opnd C k d) x
  have hout : ∀ x : Fin n → Bool,
      srcAt x (fun i => gateVal n C i x) o = circuitFun n C x := by
    intro x
    dsimp only [o]
    split_ifs with hcj
    · rw [srcAt_srcOf, heq x]
      change wireVal n C (n + j) x = wireVal n C C.output x
      rw [← hcj]
    · exact srcAt_srcOf C C.output x
  refine redirect_lt G C K hK ρ hcl o ho hne ?_ ?_ ⟨j, hj, Or.inl (Finset.notMem_erase j _)⟩
  · intro x hFx
    refine ⟨fun i => gateVal n C i x, ?_, ?_⟩
    · refine super_of_le C H.ao K hK ρ x fun k _ d h => ?_
      rwa [hsrc] at h
    · rw [hout, H.comp, hFx]
  · intro p q hpq
    refine ⟨fun i => gateVal n C i (pairInput p q), ?_, ?_⟩
    · intro k hk hu
      dsimp only at hu
      rw [gate_eq C H.ao k (hK k hk) (pairInput p q)] at hu
      rw [hsrc, hsrc]
      exact hu
    · rw [hout, H.comp]
      exact pair_of_adj hpq

theorem partner_adj_v {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {g : ℕ} (H : OneDirty G C g) (v u : Fin n)
    (hgv : gateVal n C g (unitInput v) = true) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (d : Fin 2)
    (hr : OrReaches n C (opnd C k d) g)
    (hu : wireVal n C (opnd C k (other d)) (unitInput u) = true) : G.Adj v u := by
  have hg := H.hg
  have hkg : k ≠ g := by
    rintro rfl
    exact not_reach_opnd C H.ao k hk d hr
  have hlt1 := opnd_lt C H.ao k hk d
  have hlt2 := opnd_lt C H.ao k hk (other d)
  have hgx : gateVal n C g (pairInput v u) = true := by
    refine mono_unit C H.ao (n + g) (by omega) (pairInput v u) v ?_ hgv
    simp [pairInput]
  have hd : wireVal n C (opnd C k d) (pairInput v u) = true :=
    (reach_le C H.ao g _ (by omega) hr).2 _ hgx
  have hd' : wireVal n C (opnd C k (other d)) (pairInput v u) = true := by
    refine mono_unit C H.ao _ (by omega) (pairInput v u) u ?_ hu
    simp [pairInput]
  have hkx : gateVal n C k (pairInput v u) = true :=
    (and_of_fin2 C H.ao k hk ho (pairInput v u) d).2 ⟨hd, hd'⟩
  exact adj_of_pair (H.others k hk ho hkg (pairInput v u) hkx)

theorem partner_in_b_adj_a {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {g : ℕ} (H : OneDirty G C g) (ib : Fin 2) (u x : Fin n)
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and) (d : Fin 2)
    (hr : OrReaches n C (opnd C k d) g)
    (hu : wireVal n C (opnd C k (other d)) (unitInput u) = true)
    (hub : wireVal n C (opnd C g ib) (unitInput u) = true)
    (hxa : wireVal n C (opnd C g (other ib)) (unitInput x) = true) : G.Adj x u := by
  have hg := H.hg
  have hkg : k ≠ g := by
    rintro rfl
    exact not_reach_opnd C H.ao k hk d hr
  have hlta := opnd_lt C H.ao g hg (other ib)
  have hltb := opnd_lt C H.ao g hg ib
  have hlt1 := opnd_lt C H.ao k hk d
  have hlt2 := opnd_lt C H.ao k hk (other d)
  have ha : wireVal n C (opnd C g (other ib)) (pairInput x u) = true :=
    mono_unit C H.ao _ (by omega) (pairInput x u) x (by simp [pairInput]) hxa
  have hb : wireVal n C (opnd C g ib) (pairInput x u) = true :=
    mono_unit C H.ao _ (by omega) (pairInput x u) u (by simp [pairInput]) hub
  have hgx : gateVal n C g (pairInput x u) = true :=
    (and_of_fin2 C H.ao g hg H.gand (pairInput x u) (other ib)).2
      ⟨ha, by simpa [other_other] using hb⟩
  have hd : wireVal n C (opnd C k d) (pairInput x u) = true :=
    (reach_le C H.ao g _ (by omega) hr).2 _ hgx
  have hd' : wireVal n C (opnd C k (other d)) (pairInput x u) = true :=
    mono_unit C H.ao _ (by omega) (pairInput x u) u (by simp [pairInput]) hu
  have hkx : gateVal n C k (pairInput x u) = true :=
    (and_of_fin2 C H.ao k hk ho (pairInput x u) d).2 ⟨hd, hd'⟩
  exact adj_of_pair (H.others k hk ho hkg (pairInput x u) hkx)

def FeedsC1 {n : ℕ} (C : Circuit) (m : Fin n) (j : ℕ) : Prop :=
  ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ ∃ d : Fin 2,
    OrReaches n C (opnd C k d) j ∧ wireVal n C (opnd C k (other d)) (unitInput m) = true

def FeedsC2 {n : ℕ} (C : Circuit) (m : Fin n) (j : ℕ) : Prop :=
  ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ ∃ d : Fin 2,
    OrReaches n C (opnd C k d) j ∧ ∃ u : Fin n, u ≠ m ∧
      wireVal n C (opnd C k (other d)) (unitInput u) = true

theorem feedsC1_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (m : Fin n) (j i : ℕ)
    (hji : OrReaches n C (n + j) i) (hf : FeedsC1 C m j) : FeedsC1 C m i := by
  obtain ⟨k, hk, ho, d, hkj, hm⟩ := hf
  have hlt := opnd_lt C hC k hk d
  exact ⟨k, hk, ho, d, reach_trans C hC j i _ (by omega) hkj hji, hm⟩

theorem feedsC2_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (m : Fin n) (j i : ℕ)
    (hji : OrReaches n C (n + j) i) (hf : FeedsC2 C m j) : FeedsC2 C m i := by
  obtain ⟨k, hk, ho, d, hkj, u, hum, hu⟩ := hf
  have hlt := opnd_lt C hC k hk d
  exact ⟨k, hk, ho, d, reach_trans C hC j i _ (by omega) hkj hji, u, hum, hu⟩

theorem feeds_disjoint {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {g : ℕ} (H : OneDirty G C g) (hC4 : NoFourCycle G) (v m : Fin n)
    (hv_only : ∀ w : Fin n, gateVal n C g (unitInput w) = true ↔ w = v)
    (hvm : G.Adj v m) (r : ℕ) (hrl : r < C.gates.length) (_hrg : r ≠ g)
    (hrr : OrReaches n C (n + r) g) (hdiff : ∃ x, gateVal n C r x ≠ gateVal n C g x) :
    ¬ (FeedsC1 C m r ∧ FeedsC2 C m r) := by
  have hg := H.hg
  rintro ⟨⟨k1, hk1, ho1, d1, hr1, hm1⟩, ⟨k2, hk2, ho2, d2, hr2, u, hum, hu2⟩⟩
  obtain ⟨x, hx⟩ := hdiff
  have hrx : gateVal n C r x = true := by
    by_contra hrf
    have hrf' : gateVal n C r x = false := Bool.eq_false_iff.2 hrf
    have hgf : gateVal n C g x = false := by
      by_contra hgt
      have hgt' : gateVal n C g x = true := bool_eq_true _ hgt
      have hrt : gateVal n C r x = true := (reach_le C H.ao g (n + r) (by omega) hrr).2 x hgt'
      rw [hrf'] at hrt
      exact Bool.false_ne_true hrt
    exact hx (by rw [hrf', hgf])
  have hgf : gateVal n C g x = false := by
    by_contra hgt
    have hgt' : gateVal n C g x = true := bool_eq_true _ hgt
    exact hx (by rw [hrx, hgt'])
  have hlow := low_of_reach_g H r hrl hrr
  rcases (val_low H (n + r) (by omega) hlow x).1 hrx with ⟨w, hxw, hrw⟩ | ⟨_, hgt⟩
  · have hwv : w ≠ v := by
      intro heqv
      have hgt : gateVal n C g x = true := by
        have hgv := (hv_only v).2 rfl
        rw [← heqv] at hgv
        exact mono_unit C H.ao (n + g) (by omega) x w hxw hgv
      rw [hgt] at hgf
      exact Bool.false_ne_true hgf.symm
    have hlt1 := opnd_lt C H.ao k1 hk1 d1
    have hlt2 := opnd_lt C H.ao k2 hk2 d2
    have hk1g : k1 ≠ g := by
      intro heq
      rw [heq] at hr1
      exact not_reach_opnd C H.ao g hg d1 (reach_trans C H.ao r g _ (by have := opnd_lt C H.ao g hg d1; omega) hr1 hrr)
    have hk2g : k2 ≠ g := by
      intro heq
      rw [heq] at hr2
      exact not_reach_opnd C H.ao g hg d2 (reach_trans C H.ao r g _ (by have := opnd_lt C H.ao g hg d2; omega) hr2 hrr)
    have hw1 : wireVal n C (opnd C k1 d1) (unitInput w) = true :=
      (reach_le C H.ao r _ (by omega) hr1).2 (unitInput w) hrw
    have hw2 : wireVal n C (opnd C k2 d2) (unitInput w) = true :=
      (reach_le C H.ao r _ (by omega) hr2).2 (unitInput w) hrw
    have hawm : G.Adj w m := and_pair_fin2 H k1 hk1 ho1 hk1g d1 w m hw1 hm1
    have hawu : G.Adj w u := and_pair_fin2 H k2 hk2 ho2 hk2g d2 w u hw2 hu2
    have havu : G.Adj v u :=
      partner_adj_v H v u ((hv_only v).2 rfl) k2 hk2 ho2 d2
        (reach_trans C H.ao r g _ (by omega) hr2 hrr) hu2
    exact hum (no_four_cycle_eq hC4 hwv.symm havu hvm hawu hawm)
  · rw [hgt] at hgf
    exact Bool.false_ne_true hgf.symm

theorem feeds_total {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {g : ℕ} (H : OneDirty G C g) (m : Fin n) :
    ∀ j < C.gates.length, Low G C (n + j) → OrReaches n C (n + j) g →
      FeedsC1 C m j ∨ FeedsC2 C m j := by
  have key : ∀ t : ℕ, ∀ j < C.gates.length, C.gates.length - j = t → Low G C (n + j) →
      OrReaches n C (n + j) g → FeedsC1 C m j ∨ FeedsC2 C m j := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro j hj ht hlow hrg
      have hne : C.output ≠ n + j := by
        intro hco
        obtain ⟨o, _, hco', hob⟩ := out_gate H
        have hjo : j = o := by omega
        subst hjo
        exact hlow hob
      obtain ⟨_, h | ⟨_, hin⟩⟩ := H.cone j hj
      · exact absurd h hne
      · rw [LiveSize.cone_iff] at hin
        obtain ⟨k, hk, _⟩ := Relation.TransGen.head'_iff.1 hin
        obtain ⟨hkl, hjk, hmem⟩ := hk
        obtain ⟨d, hkd⟩ := mem_opnd C H.ao k hkl _ hmem
        have hlt := opnd_lt C H.ao k hkl d
        rcases LeafBound.ao_op H.ao hkl with ho | ho
        · have hrk : OrReaches n C (opnd C k d) j := by
            rw [hkd]
            exact reach_self C H.ao j hj
          have hrkg : OrReaches n C (opnd C k d) g :=
            reach_trans C H.ao j g _ (by omega) hrk hrg
          have hnrg : ¬ OrReaches n C (opnd C k (other d)) g :=
            not_both_fin2 H k hkl ho d hrkg
          have hlt' := opnd_lt C H.ao k hkl (other d)
          have hones := ones_val C H.ao (opnd C k (other d)) (by omega)
          obtain ⟨u, _, hu⟩ := (pure_val H k hkl ho (other d) hnrg (fun _ => true)).1 hones
          by_cases hum : u = m
          · subst hum
            exact Or.inl ⟨k, hkl, ho, d, hrk, hu⟩
          · exact Or.inr ⟨k, hkl, ho, d, hrk, u, hum, hu⟩
        · have hlowk : Low G C (n + k) := by
            intro hbel
            exact hlow fun x hx =>
              below_or H.ao k hkl ho hbel d x (by rw [hkd]; exact hx)
          have hrkj : OrReaches n C (n + k) j :=
            reach_step_or C H.ao k j hkl ho d hkd hj
          have hrkg : OrReaches n C (n + k) g :=
            reach_trans C H.ao j g (n + k) (by omega) hrkj hrg
          rcases ih (C.gates.length - k) (by omega) k hkl rfl hlowk hrkg with hf1 | hf2
          · exact Or.inl (feedsC1_mono C H.ao m k j hrkj hf1)
          · exact Or.inr (feedsC2_mono C H.ao m k j hrkj hf2)
  exact fun j hj => key _ j hj rfl

theorem wire_val_unit_of_lt {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) (y : Fin n) :
    wireVal n C w (unitInput y) = true ↔ w = y.1 := by
  rw [wireVal_lt C w hw]
  simp only [unitInput, decide_eq_true_eq, Fin.ext_iff]

theorem main_wlog {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (g : ℕ) (v m : Fin n)
    (hbip : ∀ u w : Fin n, G.Adj u w → s u ≠ s w)
    (hC4 : NoFourCycle G) (H : OneDirty G C g)
    (hv_only : ∀ w : Fin n, gateVal n C g (unitInput w) = true ↔ w = v)
    (ib : Fin 2)
    (hm_b : wireVal n C (opnd C g ib) (unitInput m) = true)
    (hk_ex : ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧
      ((OrReaches n C (opnd C k 0) g ∧ wireVal n C (opnd C k 1) (unitInput m) = true) ∨
       (OrReaches n C (opnd C k 1) g ∧ wireVal n C (opnd C k 0) (unitInput m) = true)))
    (hm_only_partner : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ z : Fin n,
      (OrReaches n C (opnd C k 0) g ∧ wireVal n C (opnd C k 1) (unitInput m) = true ∧
        wireVal n C (opnd C k 1) (unitInput z) = true) ∨
      (OrReaches n C (opnd C k 1) g ∧ wireVal n C (opnd C k 0) (unitInput m) = true ∧
        wireVal n C (opnd C k 0) (unitInput z) = true) → z = m) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  have hg := H.hg
  let ia : Fin 2 := other ib
  let a : ℕ := opnd C g ia
  let b : ℕ := opnd C g ib
  have hgv : gateVal n C g (unitInput v) = true := (hv_only v).2 rfl
  have hgab : gateVal n C g (unitInput v) = true ↔
      wireVal n C a (unitInput v) = true ∧ wireVal n C b (unitInput v) = true :=
    and_of_fin2 C H.ao g hg H.gand (unitInput v) ia |>.trans
      (by simp [ia, a, b, other_other])
  have ha_v : wireVal n C a (unitInput v) = true := (hgab.1 hgv).1
  have hb_v : wireVal n C b (unitInput v) = true := (hgab.1 hgv).2
  have hk_ex' : ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ ∃ d : Fin 2,
      OrReaches n C (opnd C k d) g ∧ wireVal n C (opnd C k (other d)) (unitInput m) = true := by
    obtain ⟨k, hk, ho, h0 | h1⟩ := hk_ex
    · exact ⟨k, hk, ho, 0, h0.1, h0.2⟩
    · exact ⟨k, hk, ho, 1, h1.1, h1.2⟩
  have hAm : ∀ x : Fin n, wireVal n C a (unitInput x) = true → G.Adj x m := by
    intro x hxa
    obtain ⟨k, hk, ho, d, hr, hm⟩ := hk_ex'
    exact partner_in_b_adj_a H ib m x k hk ho d hr hm hm_b hxa
  have hvm : G.Adj v m := hAm v ha_v
  have hne : ∃ u w, G.Adj u w := ⟨v, m, hvm⟩
  have hm_only' : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ d : Fin 2,
      OrReaches n C (opnd C k d) g →
      wireVal n C (opnd C k (other d)) (unitInput m) = true →
      ∀ z : Fin n, wireVal n C (opnd C k (other d)) (unitInput z) = true → z = m := by
    intro k hk ho d hr hm z hz
    fin_cases d
    · exact hm_only_partner k hk ho z (Or.inl ⟨hr, hm, hz⟩)
    · exact hm_only_partner k hk ho z (Or.inr ⟨hr, hm, hz⟩)
  by_cases hA_sing : ∀ x : Fin n, wireVal n C a (unitInput x) = true → x = v
  · refine redirect_wire_lt H hne g hg a (opnd_lt C H.ao g hg ia) fun x => ?_
    apply Bool.eq_iff_iff.2
    rw [opnd_val H ia x, and_of_fin2 C H.ao g hg H.gand x ia]
    simp only [ia, other_other]
    change (∃ y, x y = true ∧ wireVal n C a (unitInput y) = true) ↔
      wireVal n C a x = true ∧ wireVal n C b x = true
    constructor
    · rintro ⟨y, hxy, hya⟩
      obtain rfl := hA_sing y hya
      have hltb := opnd_lt C H.ao g hg ib
      refine ⟨(opnd_val H ia x).2 ⟨y, hxy, hya⟩, mono_unit C H.ao b (by omega) x y hxy hb_v⟩
    · rintro ⟨hax, _⟩
      exact (opnd_val H ia x).1 hax
  · by_cases hdup : ∃ r < C.gates.length, r ≠ g ∧ ∀ x, gateVal n C r x = gateVal n C g x
    · obtain ⟨r, hrl, hrg, heqr⟩ := hdup
      rcases lt_or_gt_of_ne hrg with hlt | hgt
      · refine redirect_wire_lt H hne g hg (n + r) (by omega) fun x => ?_
        exact heqr x
      · refine redirect_wire_lt H hne r hrl (n + g) (by omega) fun x => ?_
        exact (heqr x).symm
    · have hA_extra : ∃ a' : Fin n, a' ≠ v ∧ wireVal n C a (unitInput a') = true := by
        by_contra h
        apply hA_sing
        intro x hx
        by_contra hxv
        exact h ⟨x, hxv, hx⟩
      obtain ⟨a', ha'v, ha'⟩ := hA_extra
      have hdiff : ∀ r < C.gates.length, r ≠ g → ∃ x, gateVal n C r x ≠ gateVal n C g x := by
        intro r hrl hrg
        by_contra h
        apply hdup
        refine ⟨r, hrl, hrg, fun x => ?_⟩
        by_contra hne'
        exact h ⟨x, hne'⟩
      have ha'm : G.Adj a' m := hAm a' ha'
      have hb_partner_eq_m : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ d : Fin 2,
          OrReaches n C (opnd C k d) g → ∀ u : Fin n,
          wireVal n C (opnd C k (other d)) (unitInput u) = true →
          wireVal n C b (unitInput u) = true → u = m := by
        intro k hk ho d hr u hu hub
        have hvu : G.Adj v u := partner_in_b_adj_a H ib u v k hk ho d hr hu hub ha_v
        have ha'u : G.Adj a' u := partner_in_b_adj_a H ib u a' k hk ho d hr hu hub ha'
        exact no_four_cycle_eq hC4 ha'v.symm hvu hvm ha'u ha'm
      let K : Finset ℕ := (Finset.range C.gates.length).erase g
      let useA : ℕ → Fin 2 → Prop := fun k d =>
        ((gateAt C k).op = GateOp.or ∧ FeedsC1 C m k) ∨
        ((gateAt C k).op = GateOp.and ∧ wireVal n C (opnd C k (other d)) (unitInput m) = true)
      let ρ : ℕ → Fin 2 → Src n ℕ := fun k d =>
        if opnd C k d = n + g then
          (if useA k d then srcOf n a else some (Sum.inl v))
        else srcOf n (opnd C k d)
      let o : Src n ℕ := srcOf n C.output
      have hK : ∀ k ∈ K, k < C.gates.length := fun k hk =>
        Finset.mem_range.1 (Finset.mem_of_mem_erase hk)
      have hcl : ∀ k ∈ K, ∀ d : Fin 2, ∀ j : ℕ, ρ k d = some (Sum.inr j) → j ∈ K ∧ j < k := by
        intro k hk d j hj
        have hkl := hK k hk
        have hkg : k ≠ g := (Finset.mem_erase.1 hk).1
        have hlt := opnd_lt C H.ao k hkl d
        dsimp only [ρ] at hj
        split_ifs at hj with hop huse
        · have hal := opnd_lt C H.ao g hg ia
          have hja := srcOf_inr a j hj
          have hltg : n + g < n + k := by omega
          have hjg : j ≠ g := by omega
          exact ⟨Finset.mem_erase.2 ⟨hjg, Finset.mem_range.2 (by omega)⟩, by omega⟩
        · simp at hj
        · have hjo := srcOf_inr (opnd C k d) j hj
          have hjg : j ≠ g := by omega
          exact ⟨Finset.mem_erase.2 ⟨hjg, Finset.mem_range.2 (by omega)⟩, by omega⟩
      have hoK : ∀ j, o = some (Sum.inr j) → j ∈ K := by
        intro j hj
        obtain ⟨o0, ho0, hco, hob⟩ := out_gate H
        have hjo : j = o0 := by
          have := srcOf_inr C.output j hj
          omega
        subst hjo
        have hog : j ≠ g := by
          rintro rfl
          exact H.dirty hob
        exact Finset.mem_erase.2 ⟨hog, Finset.mem_range.2 ho0⟩
      have ha_nr : ¬ OrReaches n C a g := not_reach_opnd C H.ao g hg ia
      have hsrcA : ∀ (x : Fin n → Bool) (u : ℕ → Bool),
          (∀ j, a = n + j → u j = gateVal n C j x) →
          srcAt x u (srcOf n a) = wireVal n C a x :=
        fun x u h => srcAt_srcOf_of_agree C x u a h
      have ho_agree : ∀ (x : Fin n → Bool) (u : ℕ → Bool),
          (∀ j, C.output = n + j → u j = gateVal n C j x) →
          srcAt x u o = circuitFun n C x :=
        fun x u h => srcAt_srcOf_of_agree C x u C.output h
      refine redirect_lt G C K hK ρ hcl o hoK hne ?_ ?_
        ⟨g, hg, Or.inl (Finset.notMem_erase g _)⟩
      · intro x hFx
        let u : ℕ → Bool := fun j =>
          if Low G C (n + j) ∧ OrReaches n C (n + j) g ∧ FeedsC1 C m j then
            gateVal n C j x || wireVal n C a x
          else gateVal n C j x
        have hu_nr : ∀ j, ¬ OrReaches n C (n + j) g → u j = gateVal n C j x := by
          intro j hnr
          dsimp only [u]
          simp [hnr]
        have hu_a : srcAt x u (srcOf n a) = wireVal n C a x :=
          hsrcA x u fun j hj => hu_nr j (by rw [← hj]; exact ha_nr)
        have hu_low : ∀ j, ¬ Low G C (n + j) → u j = gateVal n C j x := by
          intro j hnl
          dsimp only [u]
          simp [hnl]
        have hu_out : srcAt x u o = false := by
          obtain ⟨o0, _, hco, hob⟩ := out_gate H
          rw [ho_agree x u fun j hj => hu_low j (by rw [show j = o0 by omega]; exact fun h => h hob)]
          rw [H.comp, hFx]
        refine ⟨u, ?_, hu_out⟩
        intro k hk hv
        have hkl := hK k hk
        have hkg : k ≠ g := (Finset.mem_erase.1 hk).1
        rcases LeafBound.ao_op H.ao hkl with ho | ho
        · have huk : u k = gateVal n C k x := hu_low k fun h => h (H.others k hkl ho hkg)
          rw [huk]
          by_contra hkf
          have hkf' : gateVal n C k x = false := Bool.eq_false_iff.2 hkf
          have hv0 : srcAt x u (ρ k 0) = true := by
            have : (progOf C ρ).isAnd k = true := by simp [progOf, isA, ho]
            rw [this] at hv
            exact (bool_and_iff _ _).1 (by simpa [opv] using hv) |>.1
          have hv1 : srcAt x u (ρ k 1) = true := by
            have : (progOf C ρ).isAnd k = true := by simp [progOf, isA, ho]
            rw [this] at hv
            exact (bool_and_iff _ _).1 (by simpa [opv] using hv) |>.2
          have hnd : ∃ d : Fin 2, wireVal n C (opnd C k d) x = false := by
            by_contra h
            have h0 : wireVal n C (opnd C k 0) x = true :=
              bool_eq_true _ fun hf => h ⟨0, hf⟩
            have h1 : wireVal n C (opnd C k 1) x = true :=
              bool_eq_true _ fun hf => h ⟨1, hf⟩
            have hkt : gateVal n C k x = true := (val_and C H.ao k hkl ho x).2 ⟨h0, h1⟩
            rw [hkt] at hkf'
            exact Bool.false_ne_true hkf'.symm
          obtain ⟨d, hwf⟩ := hnd
          have hvd : srcAt x u (ρ k d) = true := by
            fin_cases d <;> assumption
          have hvd' : srcAt x u (ρ k (other d)) = true := by
            fin_cases d
            · exact hv1
            · exact hv0
          have hlt := opnd_lt C H.ao k hkl d
          have hlt' := opnd_lt C H.ao k hkl (other d)
          have hr_and : OrReaches n C (opnd C k d) g ∧ wireVal n C a x = true ∧
              ((opnd C k d = n + g ∧ wireVal n C (opnd C k (other d)) (unitInput m) = true) ∨
               (∃ j, opnd C k d = n + j ∧ j ≠ g ∧ j < C.gates.length ∧
                 OrReaches n C (n + j) g ∧ FeedsC1 C m j)) := by
            dsimp only [ρ] at hvd
            split_ifs at hvd with hop huse
            · rcases huse with ⟨hor, _⟩ | ⟨_, hm⟩
              · rw [ho] at hor; exact absurd hor gateOp_and_ne_or
              · rw [hu_a] at hvd
                refine ⟨by rw [hop]; exact reach_self C H.ao g hg, hvd, Or.inl ⟨hop, hm⟩⟩
            · have hxv : x v = true := by simpa [srcAt] using hvd
              have hgt : wireVal n C (opnd C k d) x = true := by
                rw [hop]
                exact mono_unit C H.ao (n + g) (by omega) x v hxv hgv
              rw [hgt] at hwf
              exact Bool.false_ne_true hwf.symm |>.elim
            · have hnlt : ¬ opnd C k d < n := by
                intro hltw
                unfold srcOf at hvd
                rw [dif_pos hltw] at hvd
                have hwtrue : wireVal n C (opnd C k d) x = true := by
                  rw [wireVal_lt C _ hltw]
                  exact hvd
                rw [hwtrue] at hwf
                exact Bool.false_ne_true hwf.symm
              set j := opnd C k d - n
              have hej : opnd C k d = n + j := by omega
              have hjl : j < C.gates.length := by omega
              have hjg : j ≠ g := by omega
              have huj : u j = true := by
                unfold srcOf at hvd
                rw [dif_neg hnlt] at hvd
                exact hvd
              dsimp only [u] at huj
              split_ifs at huj with hcond
              · rcases (bool_or_iff _ _).1 huj with hjx | hax
                · have hwtrue : wireVal n C (opnd C k d) x = true := by
                    rw [hej]; exact hjx
                  rw [hwtrue] at hwf
                  exact Bool.false_ne_true hwf.symm |>.elim
                · exact ⟨by rw [hej]; exact hcond.2.1, hax, Or.inr ⟨j, hej, hjg, hjl, hcond.2.1, hcond.2.2⟩⟩
              · have hwtrue : wireVal n C (opnd C k d) x = true := by
                  rw [hej]; exact huj
                rw [hwtrue] at hwf
                exact Bool.false_ne_true hwf.symm |>.elim
          obtain ⟨hrkd, hax, hsub⟩ := hr_and
          have hnrd' : ¬ OrReaches n C (opnd C k (other d)) g :=
            not_both_fin2 H k hkl ho d hrkd
          have hwd' : wireVal n C (opnd C k (other d)) x = true := by
            have hng : opnd C k (other d) ≠ n + g := by
              intro h
              apply hnrd'
              rw [h]
              exact reach_self C H.ao g hg
            have hsrc_d' : srcAt x u (ρ k (other d)) = wireVal n C (opnd C k (other d)) x := by
              dsimp only [ρ]
              rw [ite_eq_right hng]
              refine srcAt_srcOf_of_agree C x u (opnd C k (other d)) fun j hj => ?_
              refine hu_nr j ?_
              rw [← hj]
              exact hnrd'
            rw [← hsrc_d']
            exact hvd'
          obtain ⟨z, hxz, hzd'⟩ := (pure_val H k hkl ho (other d) hnrd' x).1 hwd'
          have hzm : z = m := by
            rcases hsub with ⟨_, hm⟩ | ⟨j, hej, hjg, hjl, hrr, hf1⟩
            · exact hm_only' k hkl ho d hrkd hm z hzd'
            · by_contra hznm
              have hf2 : FeedsC2 C m j :=
                ⟨k, hkl, ho, d, by rw [hej]; exact reach_self C H.ao j hjl, z, hznm, hzd'⟩
              exact feeds_disjoint H hC4 v m hv_only hvm j hjl hjg hrr (hdiff j hjl hjg) ⟨hf1, hf2⟩
          rw [hzm] at hxz
          obtain ⟨y, hxy, hya⟩ := (opnd_val H ia x).1 hax
          have hbad : graphFun G ∅ x = true :=
            (graphFun_empty G x).2 ⟨y, m, hAm y hya, hxy, hxz⟩
          rw [hbad] at hFx
          exact Bool.false_ne_true hFx.symm
        · have hsrc_d : ∀ d : Fin 2, srcAt x u (ρ k d) = true → u k = true := by
            intro d hvd
            by_cases hcond : Low G C (n + k) ∧ OrReaches n C (n + k) g ∧ FeedsC1 C m k
            · have huk : u k = (gateVal n C k x || wireVal n C a x) := by
                dsimp only [u]; rw [ite_eq_left hcond]
              rw [huk]
              dsimp only [ρ] at hvd
              split_ifs at hvd with hop huse
              · rw [hu_a] at hvd
                exact (bool_or_iff _ _).2 (Or.inr hvd)
              · exact absurd (Or.inl ⟨ho, hcond.2.2⟩) huse
              · have hlt := opnd_lt C H.ao k hkl d
                by_cases hwn : opnd C k d < n
                · unfold srcOf at hvd
                  rw [dif_pos hwn] at hvd
                  have hwtrue : wireVal n C (opnd C k d) x = true := by
                    rw [wireVal_lt C _ hwn]
                    exact hvd
                  have hgk : gateVal n C k x = true :=
                    (or_of_fin2 C H.ao k hkl ho x d).2 (Or.inl hwtrue)
                  exact (bool_or_iff _ _).2 (Or.inl hgk)
                · set j := opnd C k d - n
                  have hej : opnd C k d = n + j := by omega
                  have huj : u j = true := by
                    unfold srcOf at hvd
                    rw [dif_neg hwn] at hvd
                    exact hvd
                  dsimp only [u] at huj
                  split_ifs at huj with hcj
                  · rcases (bool_or_iff _ _).1 huj with hjx | hax
                    · have hgk : gateVal n C k x = true :=
                        (or_of_fin2 C H.ao k hkl ho x d).2 (Or.inl (by rw [hej]; exact hjx))
                      exact (bool_or_iff _ _).2 (Or.inl hgk)
                    · exact (bool_or_iff _ _).2 (Or.inr hax)
                  · have hgk : gateVal n C k x = true :=
                      (or_of_fin2 C H.ao k hkl ho x d).2 (Or.inl (by rw [hej]; exact huj))
                    exact (bool_or_iff _ _).2 (Or.inl hgk)
            · have hwtrue : wireVal n C (opnd C k d) x = true := by
                by_cases hlowk : Low G C (n + k)
                · dsimp only [ρ] at hvd
                  split_ifs at hvd with hop huse
                  · have hrkg : OrReaches n C (n + k) g :=
                      reach_step_or C H.ao k g hkl ho d hop hg
                    have hnf1 : ¬ FeedsC1 C m k := fun hf1 => hcond ⟨hlowk, hrkg, hf1⟩
                    rcases huse with ⟨_, hf1⟩ | ⟨hand, _⟩
                    · exact absurd hf1 hnf1
                    · rw [ho] at hand; exact absurd hand gateOp_or_ne_and
                  · have hxv : x v = true := by simpa [srcAt] using hvd
                    rw [hop]
                    exact mono_unit C H.ao (n + g) (by omega) x v hxv hgv
                  · have hlt := opnd_lt C H.ao k hkl d
                    refine (srcAt_srcOf_of_agree C x u (opnd C k d) ?_).symm.trans hvd
                    intro j hej
                    by_cases hrjg : OrReaches n C (n + j) g
                    · have hjg : j ≠ g := by omega
                      have hjl : j < C.gates.length := by omega
                      have hrkj : OrReaches n C (n + k) j :=
                        reach_step_or C H.ao k j hkl ho d hej hjl
                      have hrkg : OrReaches n C (n + k) g :=
                        reach_trans C H.ao j g (n + k) (by omega) hrkj hrjg
                      have hnf1k : ¬ FeedsC1 C m k := fun hf1 => hcond ⟨hlowk, hrkg, hf1⟩
                      have hf2k : FeedsC2 C m k :=
                        (feeds_total H m k hkl hlowk hrkg).resolve_left hnf1k
                      have hf2j : FeedsC2 C m j := feedsC2_mono C H.ao m k j hrkj hf2k
                      have hnf1j : ¬ FeedsC1 C m j := fun hf1j =>
                        feeds_disjoint H hC4 v m hv_only hvm j hjl hjg hrjg (hdiff j hjl hjg) ⟨hf1j, hf2j⟩
                      dsimp only [u]
                      simp [hnf1j]
                    · exact hu_nr j hrjg
                · have hbelk : BelowF G C k := by
                    by_contra h
                    exact hlowk h
                  have hbeld : ¬ Low G C (opnd C k d) := fun hl =>
                    hl fun z hz => below_or H.ao k hkl ho hbelk d z hz
                  have hng : opnd C k d ≠ n + g := by
                    intro h
                    apply hbeld
                    rw [h]
                    exact H.dirty
                  dsimp only [ρ] at hvd
                  rw [ite_eq_right hng] at hvd
                  refine (srcAt_srcOf_of_agree C x u (opnd C k d) ?_).symm.trans hvd
                  intro j hj
                  refine hu_low j ?_
                  rw [← hj]
                  exact hbeld
              have huk : u k = gateVal n C k x := by
                dsimp only [u]; rw [ite_eq_right hcond]
              rw [huk]
              exact (or_of_fin2 C H.ao k hkl ho x d).2 (Or.inl hwtrue)
          have hvis : (progOf C ρ).isAnd k = false := by simp [progOf, isA, ho]
          rw [hvis] at hv
          rcases (bool_or_iff _ _).1 (by simpa [opv] using hv) with hv0 | hv1
          · exact hsrc_d 0 hv0
          · exact hsrc_d 1 hv1
      · intro p q hpq
        let x : Fin n → Bool := pairInput p q
        by_cases hsimple : gateVal n C g x = false ∨ x v = true
        · let u : ℕ → Bool := fun j => gateVal n C j x
          have hwire : ∀ k ∈ K, ∀ d : Fin 2,
              wireVal n C (opnd C k d) x = true → srcAt x u (ρ k d) = true := by
            intro k hk d hwd
            dsimp only [ρ]
            split_ifs with hop huse
            · rw [hsrcA x u fun _ _ => rfl]
              have hgd : gateVal n C g x = true := by
                change wireVal n C (n + g) x = true
                rw [← hop]
                exact hwd
              have haxb := (and_of_fin2 C H.ao g hg H.gand x ia).1 hgd
              simpa [ia, a] using haxb.1
            · rcases hsimple with hgf | hxv
              · have hgd : gateVal n C g x = true := by
                  change wireVal n C (n + g) x = true
                  rw [← hop]
                  exact hwd
                rw [hgd] at hgf
                exact Bool.false_ne_true hgf.symm |>.elim
              · exact hxv
            · rw [srcAt_srcOf]
              exact hwd
          refine ⟨u, ?_, ?_⟩
          · intro k hk huk
            have hkl := hK k hk
            dsimp only [u] at huk
            rw [gate_eq C H.ao k hkl x] at huk
            rcases LeafBound.ao_op H.ao hkl with ho | ho
            · have h01 : wireVal n C (opnd C k 0) x = true ∧ wireVal n C (opnd C k 1) x = true := by
                have : isA (gateAt C k).op = true := by simp [isA, ho]
                rw [this] at huk
                exact (bool_and_iff _ _).1 (by simpa [opv] using huk)
              have hs : isA (gateAt C k).op = true := by simp [isA, ho]
              change opv ((progOf C ρ).isAnd k) _ _ = true
              dsimp only [progOf]
              rw [hs, opv_true_iff]
              exact ⟨hwire k hk 0 h01.1, hwire k hk 1 h01.2⟩
            · have h01 : wireVal n C (opnd C k 0) x = true ∨ wireVal n C (opnd C k 1) x = true := by
                have : isA (gateAt C k).op = false := by simp [isA, ho]
                rw [this] at huk
                exact (bool_or_iff _ _).1 (by simpa [opv] using huk)
              have hs : isA (gateAt C k).op = false := by simp [isA, ho]
              change opv ((progOf C ρ).isAnd k) _ _ = true
              dsimp only [progOf]
              rw [hs, opv_false_iff]
              rcases h01 with h0 | h1
              · exact Or.inl (hwire k hk 0 h0)
              · exact Or.inr (hwire k hk 1 h1)
          · rw [ho_agree x u fun _ _ => rfl, H.comp]
            exact pair_of_adj hpq
        · have hgx : gateVal n C g x = true :=
            bool_eq_true _ fun hgf => hsimple (Or.inl hgf)
          have hxv : x v = false :=
            Bool.eq_false_iff.2 fun hxt => hsimple (Or.inr hxt)
          have hax : wireVal n C a x = true :=
            ((and_of_fin2 C H.ao g hg H.gand x ia).1 hgx).1
          have hbx : wireVal n C b x = true := by
            have := ((and_of_fin2 C H.ao g hg H.gand x ia).1 hgx).2
            simpa [ia, b, other_other] using this
          let u : ℕ → Bool := fun j =>
            if Low G C (n + j) ∧ OrReaches n C (n + j) g ∧ ¬ FeedsC1 C m j then
              decide (∃ y : Fin n, x y = true ∧ gateVal n C j (unitInput y) = true)
            else gateVal n C j x
          have hu_nr : ∀ j, ¬ OrReaches n C (n + j) g → u j = gateVal n C j x := by
            intro j hnr
            dsimp only [u]
            simp [hnr]
          have hu_low : ∀ j, ¬ Low G C (n + j) → u j = gateVal n C j x := by
            intro j hnl
            dsimp only [u]
            simp [hnl]
          have hu_a : srcAt x u (srcOf n a) = wireVal n C a x :=
            hsrcA x u fun j hj => hu_nr j (by rw [← hj]; exact ha_nr)
          have hu_out : srcAt x u o = true := by
            obtain ⟨o0, _, _, hob⟩ := out_gate H
            rw [ho_agree x u fun j hj => hu_low j (by rw [show j = o0 by omega]; exact fun h => h hob)]
            rw [H.comp]
            exact pair_of_adj hpq
          refine ⟨u, ?_, hu_out⟩
          intro k hk huk
          have hkl := hK k hk
          have hkg : k ≠ g := (Finset.mem_erase.1 hk).1
          rcases LeafBound.ao_op H.ao hkl with ho | ho
          · have hnlk : ¬ Low G C (n + k) := fun h => h (H.others k hkl ho hkg)
            have hkx : gateVal n C k x = true := by
              rw [hu_low k hnlk] at huk
              exact huk
            have hhs : (progOf C ρ).isAnd k = true := by simp [progOf, isA, ho]
            rw [hhs, opv_true_iff]
            have h_op : ∀ d : Fin 2, srcAt x u (ρ k d) = true := by
              intro d
              have hwd : wireVal n C (opnd C k d) x = true :=
                ((and_of_fin2 C H.ao k hkl ho x d).1 hkx).1
              by_cases hrd : OrReaches n C (opnd C k d) g
              · let d' := other d
                have hnrd' : ¬ OrReaches n C (opnd C k d') g := not_both_fin2 H k hkl ho d hrd
                have hwd' : wireVal n C (opnd C k d') x = true :=
                  ((and_of_fin2 C H.ao k hkl ho x d).1 hkx).2
                obtain ⟨z, hxz, hzd'⟩ := (pure_val H k hkl ho d' hnrd' x).1 hwd'
                have hzm : z = m := by
                  obtain ⟨y1, hxy1, hy1a⟩ := (opnd_val H ia x).1 hax
                  obtain ⟨y2, hxy2, hy2b⟩ := (opnd_val H ib x).1 hbx
                  have hy12 : y1 ≠ y2 := by
                    intro h12
                    have hy1b : wireVal n C b (unitInput y1) = true := by
                      rw [h12]; exact hy2b
                    have hgy1 : gateVal n C g (unitInput y1) = true :=
                      (and_of_fin2 C H.ao g hg H.gand (unitInput y1) ia).2
                        ⟨hy1a, by simpa [ia, b, other_other] using hy1b⟩
                    have hy1v : y1 = v := (hv_only y1).1 hgy1
                    rw [hy1v] at hxy1
                    rw [hxy1] at hxv
                    exact Bool.false_ne_true hxv.symm
                  have hzy1 : z ≠ y1 := by
                    intro hzy
                    have hvz : G.Adj v z := partner_adj_v H v z hgv k hkl ho d hrd hzd'
                    have hzm_a : G.Adj z m := by rw [hzy]; exact hAm y1 hy1a
                    exact bool_ne_tri (hbip v z hvz) (hbip z m hzm_a) (hbip v m hvm)
                  have hzpq : z = p ∨ z = q := (pairInput_true p q z).1 hxz
                  have hy1pq : y1 = p ∨ y1 = q := (pairInput_true p q y1).1 hxy1
                  have hy2pq : y2 = p ∨ y2 = q := (pairInput_true p q y2).1 hxy2
                  have hzy2 : z = y2 := pair_third hzpq hy1pq hy2pq hy12 hzy1
                  have hzb : wireVal n C b (unitInput z) = true := by
                    rw [hzy2]; exact hy2b
                  exact hb_partner_eq_m k hkl ho d hrd z hzd' hzb
                have hmd' : wireVal n C (opnd C k (other d)) (unitInput m) = true := by
                  rw [← hzm]; exact hzd'
                dsimp only [ρ]
                split_ifs with hop huse
                · rw [hu_a]
                  exact hax
                · exact absurd (Or.inr ⟨ho, hmd'⟩) huse
                · have hnlt : ¬ opnd C k d < n := fun hw => reach_input C (opnd C k d) g hw hrd
                  have hlt := opnd_lt C H.ao k hkl d
                  set j := opnd C k d - n
                  have hej : opnd C k d = n + j := by omega
                  have hjl : j < C.gates.length := by omega
                  have hf1j : FeedsC1 C m j :=
                    ⟨k, hkl, ho, d, by rw [hej]; exact reach_self C H.ao j hjl, hmd'⟩
                  refine (srcAt_srcOf_of_agree C x u (opnd C k d) ?_).trans hwd
                  intro j' hj'
                  have hj_eq : j' = j := by omega
                  rw [hj_eq]
                  dsimp only [u]
                  simp [hf1j]
              · have hng : opnd C k d ≠ n + g := by
                  intro h
                  apply hrd
                  rw [h]
                  exact reach_self C H.ao g hg
                dsimp only [ρ]
                rw [ite_eq_right hng]
                refine (srcAt_srcOf_of_agree C x u (opnd C k d) ?_).trans hwd
                intro j hj
                refine hu_nr j ?_
                rw [← hj]
                exact hrd
            exact ⟨h_op 0, h_op 1⟩
          · have hhs : (progOf C ρ).isAnd k = false := by simp [progOf, isA, ho]
            rw [hhs, opv_false_iff]
            by_cases hcond : Low G C (n + k) ∧ OrReaches n C (n + k) g ∧ ¬ FeedsC1 C m k
            · have huk' : decide (∃ y : Fin n, x y = true ∧ gateVal n C k (unitInput y) = true) = true := by
                dsimp only [u] at huk
                rwa [ite_eq_left hcond] at huk
              obtain ⟨y, hxy, hky⟩ := of_decide_eq_true huk'
              have hyne : y ≠ v := by
                intro hyv
                rw [hyv] at hxy
                rw [hxy] at hxv
                exact Bool.false_ne_true hxv.symm
              obtain ⟨d, hdy⟩ : ∃ d : Fin 2, wireVal n C (opnd C k d) (unitInput y) = true := by
                rcases (val_or C H.ao k hkl ho (unitInput y)).1 hky with h0 | h1
                · exact ⟨0, h0⟩
                · exact ⟨1, h1⟩
              have hng : opnd C k d ≠ n + g := by
                intro h
                have hgy : gateVal n C g (unitInput y) = true := by
                  change wireVal n C (n + g) (unitInput y) = true
                  rw [← h]; exact hdy
                exact hyne ((hv_only y).1 hgy)
              have hlt := opnd_lt C H.ao k hkl d
              have hsrc_d : srcAt x u (ρ k d) = true := by
                dsimp only [ρ]
                rw [ite_eq_right hng]
                by_cases hwn : opnd C k d < n
                · unfold srcOf
                  rw [dif_pos hwn]
                  have := mono_unit C H.ao (opnd C k d) (by omega) x y hxy hdy
                  rw [wireVal_lt C _ hwn] at this
                  exact this
                · set j := opnd C k d - n
                  have hej : opnd C k d = n + j := by omega
                  have hjl : j < C.gates.length := by omega
                  unfold srcOf
                  rw [dif_neg hwn]
                  show u j = true
                  dsimp only [u]
                  split_ifs with hcj
                  · refine decide_eq_true ⟨y, hxy, ?_⟩
                    change wireVal n C (n + j) (unitInput y) = true
                    rw [← hej]; exact hdy
                  · exact mono_unit C H.ao (n + j) (by omega) x y hxy (by rw [← hej]; exact hdy)
              fin_cases d
              · exact Or.inl hsrc_d
              · exact Or.inr hsrc_d
            · have hkx : gateVal n C k x = true := by
                dsimp only [u] at huk
                rwa [ite_eq_right hcond] at huk
              obtain ⟨d, hwd⟩ : ∃ d : Fin 2, wireVal n C (opnd C k d) x = true := by
                rcases (val_or C H.ao k hkl ho x).1 hkx with h0 | h1
                · exact ⟨0, h0⟩
                · exact ⟨1, h1⟩
              have hlt := opnd_lt C H.ao k hkl d
              have hsrc_d : srcAt x u (ρ k d) = true := by
                by_cases hlowk : Low G C (n + k)
                · by_cases hrkg : OrReaches n C (n + k) g
                  · have hf1k : FeedsC1 C m k := by
                      by_contra hnf1
                      exact hcond ⟨hlowk, hrkg, hnf1⟩
                    dsimp only [ρ]
                    split_ifs with hop huse
                    · rw [hu_a]
                      exact hax
                    · exact absurd (Or.inl ⟨ho, hf1k⟩) huse
                    · by_cases hwn : opnd C k d < n
                      · rw [srcAt_srcOf_of_agree C x u (opnd C k d) (fun _ hj => by omega)]
                        exact hwd
                      · set j := opnd C k d - n
                        have hej : opnd C k d = n + j := by omega
                        have hjl : j < C.gates.length := by omega
                        have hrkj : OrReaches n C (n + k) j :=
                          reach_step_or C H.ao k j hkl ho d hej hjl
                        have hf1j : FeedsC1 C m j := feedsC1_mono C H.ao m k j hrkj hf1k
                        refine (srcAt_srcOf_of_agree C x u (opnd C k d) ?_).trans hwd
                        intro j' hj'
                        have hj_eq : j' = j := by omega
                        rw [hj_eq]
                        dsimp only [u]
                        simp [hf1j]
                  · have hnrd : ¬ OrReaches n C (opnd C k d) g := by
                      intro hrd
                      apply hrkg
                      exact (reach_gate C H.ao k g hkl).2 (Or.inr ⟨ho, d, hrd⟩)
                    have hng : opnd C k d ≠ n + g := by
                      intro h
                      apply hnrd
                      rw [h]
                      exact reach_self C H.ao g hg
                    dsimp only [ρ]
                    rw [ite_eq_right hng]
                    refine (srcAt_srcOf_of_agree C x u (opnd C k d) ?_).trans hwd
                    intro j hj
                    refine hu_nr j ?_
                    rw [← hj]
                    exact hnrd
                · have hbelk : BelowF G C k := by
                    by_contra h
                    exact hlowk h
                  have hbeld : ¬ Low G C (opnd C k d) := fun hl =>
                    hl fun z hz => below_or H.ao k hkl ho hbelk d z hz
                  have hng : opnd C k d ≠ n + g := by
                    intro h
                    apply hbeld
                    rw [h]
                    exact H.dirty
                  dsimp only [ρ]
                  rw [ite_eq_right hng]
                  refine (srcAt_srcOf_of_agree C x u (opnd C k d) ?_).trans hwd
                  intro j hj
                  refine hu_low j ?_
                  rw [← hj]
                  exact hbeld
              fin_cases d
              · exact Or.inl hsrc_d
              · exact Or.inr hsrc_d

end PEqualNP.Outside.L_meta_4746

theorem PEqualNP.Outside.L_meta_4746 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ) (v m : Fin n), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → (∀ w : Fin n, PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput w) = true ↔ w = v) → (PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput m) = true ∨ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput m) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput m) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput m) = true))) → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin n, (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput m) = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput m) = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → z = m) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C s g v m hbip hC4 hAO hcomp hlift handLow hcone hg hgand hdirty hothers hv_only hm_opnd hk_ex hm_only_partner
  let H : PEqualNP.MetaComplexity.LowerPart.OneDirty G C g :=
    ⟨hAO, hcomp, hlift, handLow, hcone, hg, hgand, hdirty, hothers⟩
  rcases hm_opnd with hm0 | hm1
  · exact PEqualNP.Outside.L_meta_4746.main_wlog G C s g v m hbip hC4 H hv_only 0 hm0 hk_ex hm_only_partner
  · exact PEqualNP.Outside.L_meta_4746.main_wlog G C s g v m hbip hC4 H hv_only 1 hm1 hk_ex hm_only_partner
