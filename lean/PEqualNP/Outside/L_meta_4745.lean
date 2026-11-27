import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowerPart

namespace PEqualNP.Outside.L_meta_4745

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

theorem srcOf_gate (j : ℕ) : srcOf n (n + j) = (some (Sum.inr j) : Src n ℕ) := by
  simp [srcOf]

theorem srcOf_input (v : Fin n) : srcOf n (v : ℕ) = (some (Sum.inl v) : Src n ℕ) := by
  simp [srcOf, v.2]

theorem srcOf_cases (w : ℕ) : (∃ v : Fin n, w = v) ∨ ∃ j, w = n + j := by
  by_cases h : w < n
  · exact Or.inl ⟨⟨w, h⟩, rfl⟩
  · exact Or.inr ⟨w - n, by omega⟩

theorem fin2_inv (c : Fin 2) : 1 - (1 - c) = c := by
  revert c; decide

theorem fin2_or (c d : Fin 2) : d = c ∨ d = 1 - c := by
  revert c d; decide

theorem val_and' (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (x : Fin n → Bool) (c : Fin 2) :
    gateVal n C k x = true ↔ wireVal n C (opnd C k c) x = true ∧ wireVal n C (opnd C k (1 - c)) x = true := by
  rw [val_and C hC k hk ho x]
  fin_cases c
  · exact Iff.rfl
  · exact and_comm

theorem val_or' (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.or) (x : Fin n → Bool) :
    gateVal n C k x = true ↔ ∃ c, wireVal n C (opnd C k c) x = true := by
  rw [val_or C hC k hk ho x]
  constructor
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · rintro ⟨c, h⟩
    fin_cases c
    · exact Or.inl h
    · exact Or.inr h

theorem reach_self (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) : OrReaches n C (n + k) k :=
  (reach_gate C hC k k hk).2 (Or.inl rfl)

theorem reach_trans (C : Circuit) (hC : IsAO2 n C) (k g : ℕ) (_hk : k < C.gates.length)
    (hkg : OrReaches n C (n + k) g) : ∀ w < n + C.gates.length, OrReaches n C w k → OrReaches n C w g := by
  refine wire_induction C hC _ (fun w hw h => absurd h (reach_input C w k hw)) ?_
  intro j hj ih h
  rcases (reach_gate C hC j k hj).1 h with rfl | ⟨ho, c, hc⟩
  · exact hkg
  · exact (reach_gate C hC j g hj).2 (Or.inr ⟨ho, c, ih c hc⟩)

def PZ (C : Circuit) (g k : ℕ) (z : Fin n) : Prop :=
  (OrReaches n C (opnd C k 0) g ∧ wireVal n C (opnd C k 1) (unitInput z) = true) ∨
  (OrReaches n C (opnd C k 1) g ∧ wireVal n C (opnd C k 0) (unitInput z) = true)

theorem pz_iff (C : Circuit) (g k : ℕ) (z : Fin n) : PZ C g k z ↔
    ∃ c, OrReaches n C (opnd C k c) g ∧ wireVal n C (opnd C k (1 - c)) (unitInput z) = true := by
  constructor
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · rintro ⟨c, h⟩
    fin_cases c
    · exact Or.inl h
    · exact Or.inr h

theorem pair_adj (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (y z : Fin n)
    (h : graphFun G ∅ (pairInput y z) = true) : G.Adj y z := by
  obtain ⟨u, w, huw, hu, hw⟩ := (graphFun_empty G _).1 h
  simp only [pairInput, decide_eq_true_eq] at hu hw
  rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
  · exact absurd huw (G.loopless.irrefl _)
  · exact huw
  · exact huw.symm
  · exact absurd huw (G.loopless.irrefl _)

theorem unit_le (y : Fin n) (x : Fin n → Bool) (hy : x y = true) (a : Fin n) (ha : unitInput y a = true) :
    x a = true := by
  simp only [unitInput, decide_eq_true_eq] at ha
  rw [ha]; exact hy

section

variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}

theorem and_pair' (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (hkg : k ≠ g) (c : Fin 2) (y z : Fin n) (hy : wireVal n C (opnd C k c) (unitInput y) = true)
    (hz : wireVal n C (opnd C k (1 - c)) (unitInput z) = true) : G.Adj y z := by
  fin_cases c
  · exact and_pair H k hk ho hkg y z hy hz
  · exact (and_pair H k hk ho hkg z y hz hy).symm

theorem not_both' (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (c : Fin 2) (h : OrReaches n C (opnd C k c) g) : ¬ OrReaches n C (opnd C k (1 - c)) g := by
  intro h'
  fin_cases c
  · exact not_both H k hk ho ⟨h, h'⟩
  · exact not_both H k hk ho ⟨h', h⟩

theorem pz_ne (H : OneDirty G C g) (k : ℕ) (z : Fin n) (h : PZ C g k z) : k ≠ g := by
  rintro rfl
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  · exact not_reach_opnd C H.ao k H.hg 0 h
  · exact not_reach_opnd C H.ao k H.hg 1 h

theorem pz_F (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (z : Fin n) (h : PZ C g k z) (x : Fin n → Bool) (hx : gateVal n C g x = true) (hz : x z = true) :
    graphFun G ∅ x = true := by
  obtain ⟨c, hr, hw⟩ := (pz_iff C g k z).1 h
  have hl0 := opnd_lt C H.ao k hk c
  have hl1 := opnd_lt C H.ao k hk (1 - c)
  refine H.others k hk ho (pz_ne H k z h) x ((val_and' C H.ao k hk ho x c).2 ⟨?_, ?_⟩)
  · exact (reach_le C H.ao g _ (by omega) hr).2 x hx
  · exact mono C H.ao _ _ (unit_le z x hz) _ (by omega) hw

theorem pz_opnd (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (z : Fin n) (h : PZ C g k z) (y : Fin n) (c : Fin 2)
    (hzc : wireVal n C (opnd C g c) (unitInput z) = true)
    (hy : wireVal n C (opnd C g (1 - c)) (unitInput y) = true) : G.Adj z y := by
  apply pair_adj
  have hg := H.hg
  have hl0 := opnd_lt C H.ao g hg c
  have hl1 := opnd_lt C H.ao g hg (1 - c)
  refine pz_F H k hk ho z h _ ((val_and' C H.ao g hg H.gand _ c).2 ⟨?_, ?_⟩) (by simp [pairInput])
  · exact mono C H.ao _ _ (unit_le z _ (by simp [pairInput])) _ (by omega) hzc
  · exact mono C H.ao _ _ (unit_le y _ (by simp [pairInput])) _ (by omega) hy

theorem above_and (H : OneDirty G C g) : ∀ k < C.gates.length, Low G C (n + k) →
    ∃ T < C.gates.length, (gateAt C T).op = GateOp.and ∧ ∃ c, OrReaches n C (opnd C T c) k := by
  have key : ∀ m, ∀ k < C.gates.length, C.gates.length - k = m → Low G C (n + k) →
      ∃ T < C.gates.length, (gateAt C T).op = GateOp.and ∧ ∃ c, OrReaches n C (opnd C T c) k := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hk hm hl
      obtain ⟨o, hol, hoo, hob⟩ := out_gate H
      obtain ⟨_, h | ⟨_, hin⟩⟩ := H.cone k hk
      · have : o = k := by omega
        subst this
        exact absurd hob hl
      · rw [LiveSize.cone_iff] at hin
        obtain ⟨j, ⟨hjl, hkj, hmem⟩, _⟩ := Relation.TransGen.head'_iff.1 hin
        obtain ⟨c, hc⟩ := mem_opnd C H.ao j hjl _ hmem
        rcases LeafBound.ao_op H.ao hjl with ho | ho
        · exact ⟨j, hjl, ho, c, by rw [hc]; exact reach_self C H.ao k hk⟩
        · have hjlow : Low G C (n + j) := fun hb => hl fun x hx =>
            below_or H.ao j hjl ho hb c x (by rw [hc]; exact hx)
          obtain ⟨T, hT, hTo, d, hd⟩ := ih (C.gates.length - j) (by omega) j hjl rfl hjlow
          have hlt := opnd_lt C H.ao T hT d
          refine ⟨T, hT, hTo, d, reach_trans C H.ao j k hjl ?_ _ (by omega) hd⟩
          exact (reach_gate C H.ao j k hjl).2 (Or.inr ⟨ho, c, by rw [hc]; exact reach_self C H.ao k hk⟩)
  exact fun k hk => key _ k hk rfl

theorem dup_lt (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (w : ℕ) (hw : w < n + k)
    (hsame : ∀ x, gateVal n C k x = wireVal n C w x) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  have hAO := H.ao
  obtain ⟨o, hol, hoo, _⟩ := out_gate H
  let r : ℕ → ℕ := fun u => if u = n + k then w else u
  have hrv : ∀ u x, wireVal n C (r u) x = wireVal n C u x := by
    intro u x
    simp only [r]
    split_ifs with h
    · rw [h, ← hsame x]; rfl
    · rfl
  have hrk : ∀ u, r u ≠ n + k ∧ r u ≤ u := by
    intro u
    simp only [r]
    split_ifs with h <;> omega
  have hsv : ∀ x, srcAt x (fun j => gateVal n C j x) (srcOf n (r C.output)) = graphFun G ∅ x := by
    intro x
    rw [srcAt_srcOf, hrv, ← H.comp]
    rfl
  refine redirect_lt G C ((Finset.range C.gates.length).erase k) ?_ (fun j b => srcOf n (r (opnd C j b))) ?_
    (srcOf n (r C.output)) ?_ (adj_of_AO G C hAO H.comp (by omega)) ?_ ?_ ⟨k, hk, Or.inl (by simp)⟩
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
    have := hrk C.output
    exact Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 (by omega)⟩
  · intro x hx
    refine ⟨fun j => gateVal n C j x, super_of_le C hAO _ ?_ _ x ?_, ?_⟩
    · intro j hj
      exact Finset.mem_range.1 (Finset.mem_erase.1 hj).2
    · intro j _ b h
      rw [srcAt_srcOf, hrv] at h
      exact h
    · rw [hsv x]; exact hx
  · intro p q hpq
    refine ⟨fun j => gateVal n C j (pairInput p q), ?_, ?_⟩
    · intro j hj h
      have hjl := Finset.mem_range.1 (Finset.mem_erase.1 hj).2
      simp only at h
      rw [gate_eq C hAO j hjl] at h
      rw [srcAt_srcOf, srcAt_srcOf, hrv, hrv]
      exact h
    · rw [hsv]
      exact (graphFun_empty G _).2 ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩

end

theorem c4 {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (a b u w : Fin n) (hab : a ≠ b) (h1 : G.Adj a u) (h2 : G.Adj b u)
    (h3 : G.Adj a w) (h4' : G.Adj b w) : u = w :=
  Finset.card_le_one.1 (h4 a b hab) u (by simp [h1, h2]) w (by simp [h3, h4'])

theorem unit_pair (y : Fin n) (x : Fin n → Bool) (hy : x y = true) (C : Circuit) (hC : IsAO2 n C) (w : ℕ)
    (hw : w < n + C.gates.length) (h : wireVal n C w (unitInput y) = true) : wireVal n C w x = true :=
  mono C hC _ _ (unit_le y x hy) w hw h

def FeedsC1 (C : Circuit) (m : Fin n) (j : ℕ) : Prop :=
  ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ ∃ d : Fin 2,
    OrReaches n C (opnd C k d) j ∧ wireVal n C (opnd C k (1 - d)) (unitInput m) = true

def FeedsC2 (C : Circuit) (m : Fin n) (j : ℕ) : Prop :=
  ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ ∃ d : Fin 2,
    OrReaches n C (opnd C k d) j ∧ ∃ u : Fin n, u ≠ m ∧
      wireVal n C (opnd C k (1 - d)) (unitInput u) = true

theorem feedsC1_mono (C : Circuit) (hC : IsAO2 n C) (m : Fin n) (j i : ℕ)
    (hji : OrReaches n C (n + j) i) (hf : FeedsC1 C m j) : FeedsC1 C m i := by
  obtain ⟨k, hk, ho, d, hkj, hm⟩ := hf
  have hlt := opnd_lt C hC k hk d
  have hjlt : j < C.gates.length := by
    have := (reach_le C hC j _ (by omega) hkj).1
    omega
  exact ⟨k, hk, ho, d, reach_trans C hC j i hjlt hji _ (by omega) hkj, hm⟩

theorem feedsC2_mono (C : Circuit) (hC : IsAO2 n C) (m : Fin n) (j i : ℕ)
    (hji : OrReaches n C (n + j) i) (hf : FeedsC2 C m j) : FeedsC2 C m i := by
  obtain ⟨k, hk, ho, d, hkj, u, hum, hu⟩ := hf
  have hlt := opnd_lt C hC k hk d
  have hjlt : j < C.gates.length := by
    have := (reach_le C hC j _ (by omega) hkj).1
    omega
  exact ⟨k, hk, ho, d, reach_trans C hC j i hjlt hji _ (by omega) hkj, u, hum, hu⟩

theorem main (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool) (g : ℕ)
    (v m z : Fin n) (hs : ∀ u v : Fin n, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G) (H : OneDirty G C g)
    (hgv : ∀ w : Fin n, gateVal n C g (unitInput w) = true ↔ w = v) (cb : Fin 2)
    (hmB : wireVal n C (opnd C g cb) (unitInput m) = true) (hzm : z ≠ m)
    (k0 : ℕ) (hk0 : k0 < C.gates.length) (hk0o : (gateAt C k0).op = GateOp.and) (c0 : Fin 2)
    (hr0 : OrReaches n C (opnd C k0 c0) g)
    (hm0 : wireVal n C (opnd C k0 (1 - c0)) (unitInput m) = true)
    (hz0 : wireVal n C (opnd C k0 (1 - c0)) (unitInput z) = true) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  have hAO := H.ao
  have hgl := H.hg
  set ca : Fin 2 := 1 - cb with hca_def
  have hcb_eq : 1 - ca = cb := by rw [hca_def, fin2_inv]
  have hAlt := opnd_lt C hAO g hgl ca
  have hBlt := opnd_lt C hAO g hgl cb
  have hgv_true : gateVal n C g (unitInput v) = true := (hgv v).2 rfl
  have hvB : wireVal n C (opnd C g cb) (unitInput v) = true :=
    ((val_and' C hAO g hgl H.gand (unitInput v) cb).1 hgv_true).1
  have hvA : wireVal n C (opnd C g ca) (unitInput v) = true :=
    ((val_and' C hAO g hgl H.gand (unitInput v) cb).1 hgv_true).2
  have hpz_m : PZ C g k0 m := (pz_iff C g k0 m).2 ⟨c0, hr0, hm0⟩
  have hpz_z : PZ C g k0 z := (pz_iff C g k0 z).2 ⟨c0, hr0, hz0⟩
  have hadj_mA : ∀ y, wireVal n C (opnd C g ca) (unitInput y) = true → G.Adj m y :=
    fun y hy => pz_opnd H k0 hk0 hk0o m hpz_m y cb hmB hy
  have hadj_mv : G.Adj m v := hadj_mA v hvA
  have hvm : v ≠ m := fun h => G.loopless.irrefl m (h ▸ hadj_mv)
  have hsvm : s m ≠ s v := hs m v hadj_mv
  have hsideA : ∀ y, wireVal n C (opnd C g ca) (unitInput y) = true → s y = s v := by
    intro y hy
    have h1 := hs m y (hadj_mA y hy)
    revert h1 hsvm
    cases s m <;> cases s y <;> cases s v <;> simp
  have hadj_vpz : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ q, PZ C g k q → G.Adj v q := by
    intro k hk ho q hpz
    obtain ⟨c, hr, hq⟩ := (pz_iff C g k q).1 hpz
    have hlt := opnd_lt C hAO k hk c
    exact and_pair' H k hk ho (pz_ne H k q hpz) c v q ((reach_le C hAO g _ (by omega) hr).2 _ hgv_true) hq
  by_cases hA1 : ∀ y, wireVal n C (opnd C g ca) (unitInput y) = true → y = v
  · refine dup_lt H g hgl v (by have := v.2; omega) fun x => ?_
    rw [wireVal_lt C v v.2 x]
    apply Bool.eq_iff_iff.2
    constructor
    · intro hgx
      have hAx := ((val_and' C hAO g hgl H.gand x ca).1 hgx).1
      obtain ⟨y, hxy, hyA⟩ := (opnd_val H ca x).1 hAx
      rwa [hA1 y hyA] at hxy
    · intro hxv
      exact unit_pair v x hxv C hAO (n + g) (by omega) hgv_true
  · by_cases hdup : ∃ r < C.gates.length, r ≠ g ∧ ∀ x, gateVal n C r x = gateVal n C g x
    · obtain ⟨r, hrl, hrg, heqr⟩ := hdup
      rcases lt_or_gt_of_ne hrg with hlt | hgt
      · exact dup_lt H g hgl (n + r) (by omega) fun x => (heqr x).symm
      · exact dup_lt H r hrl (n + g) (by omega) heqr
    · push Not at hA1
      obtain ⟨v', hv'A, hv'v⟩ := hA1
      have hdiff : ∀ r < C.gates.length, r ≠ g → ∃ x, gateVal n C r x ≠ gateVal n C g x := by
        intro r hrl hrg
        by_contra h
        exact hdup ⟨r, hrl, hrg, fun x => Classical.not_not.1 fun hne => h ⟨x, hne⟩⟩
      have hadj_mv' : G.Adj m v' := hadj_mA v' hv'A
      have huniqB : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ q, PZ C g k q →
          wireVal n C (opnd C g cb) (unitInput q) = true → q = m := by
        intro k hk ho q hpz hqB
        have hqv : G.Adj q v := pz_opnd H k hk ho q hpz v cb hqB hvA
        have hqv' : G.Adj q v' := pz_opnd H k hk ho q hpz v' cb hqB hv'A
        exact c4 h4 v v' q m hv'v.symm hqv.symm hqv'.symm hadj_mv.symm hadj_mv'.symm
      have hdisjAB : ∀ y, wireVal n C (opnd C g ca) (unitInput y) = true →
          wireVal n C (opnd C g cb) (unitInput y) = true → y = v := by
        intro y hyA hyB
        exact (hgv y).1 ((val_and' C hAO g hgl H.gand (unitInput y) ca).2 ⟨hyA, by rw [hcb_eq]; exact hyB⟩)
      obtain ⟨ib, hib⟩ : ∃ ib, opnd C g cb = n + ib := by
        rcases srcOf_cases (n := n) (opnd C g cb) with ⟨u, hu⟩ | h
        · exfalso
          have key : ∀ y, wireVal n C (opnd C g cb) (unitInput y) = true → u = y := by
            intro y hy
            rw [hu, wireVal_lt C _ u.2] at hy
            simpa [unitInput] using hy
          exact hvm ((key v hvB).symm.trans (key m hmB))
        · exact h
      have hibg : ib < g := by omega
      have hibl : ib < C.gates.length := by omega
      have hunitB : ∀ y, wireVal n C (opnd C g cb) (unitInput y) = true →
          wireVal n C (n + ib) (unitInput y) = true := by
        intro y hy; rw [← hib]; exact hy
      have hnoT : ∀ T < C.gates.length, (gateAt C T).op = GateOp.and → T ≠ g → ∀ d,
          (∀ y, wireVal n C (opnd C g cb) (unitInput y) = true →
            wireVal n C (opnd C T d) (unitInput y) = true) → False := by
        intro T hT hTo hTg d hsub
        have hlt := opnd_lt C hAO T hT (1 - d)
        by_cases hr : OrReaches n C (opnd C T (1 - d)) g
        · have hpv : PZ C g T v := (pz_iff C g T v).2 ⟨1 - d, hr, by rw [fin2_inv]; exact hsub v hvB⟩
          exact hvm (huniqB T hT hTo v hpv hvB)
        · obtain ⟨q, _, hq⟩ := (pure_val H T hT hTo (1 - d) hr (fun _ => true)).1 (ones_val C hAO _ (by omega))
          have a1 := hs _ _ (and_pair' H T hT hTo hTg d v q (hsub v hvB) hq)
          have a2 := hs _ _ (and_pair' H T hT hTo hTg d m q (hsub m hmB) hq)
          revert a1 a2 hsvm
          cases s m <;> cases s v <;> cases s q <;> simp
      have honly : ∀ k < C.gates.length, k ≠ g → ∀ c, opnd C k c ≠ n + ib := by
        intro k hk hkg c hc
        rcases LeafBound.ao_op hAO hk with ho | ho
        · exact hnoT k hk ho hkg c fun y hy => by rw [hc]; exact hunitB y hy
        · have hsub : ∀ y, wireVal n C (opnd C g cb) (unitInput y) = true →
              gateVal n C k (unitInput y) = true := fun y hy =>
            (val_or' C hAO k hk ho _).2 ⟨c, by rw [hc]; exact hunitB y hy⟩
          have hlow : Low G C (n + k) := by
            intro hb
            have h2 := hb (unitInput v) (hsub v hvB)
            rw [unit_false] at h2
            exact absurd h2 (by decide)
          obtain ⟨T, hT, hTo, d, hd⟩ := above_and H k hk hlow
          have hltT := opnd_lt C hAO T hT d
          have hle := reach_le C hAO k _ (by omega) hd
          have hsub' : ∀ y, wireVal n C (opnd C g cb) (unitInput y) = true →
              wireVal n C (opnd C T d) (unitInput y) = true := fun y hy =>
            hle.2 _ (hsub y hy)
          by_cases hTg : T = g
          · subst hTg
            rcases fin2_or ca d with rfl | rfl
            · exact hvm (hdisjAB m (hsub' m hmB) hmB).symm
            · rw [hcb_eq, hib] at hle
              have h1 := opnd_lt C hAO k hk c
              omega
          · exact hnoT T hT hTo hTg d hsub'
      have hlow_ib : Low G C (n + ib) := by
        rw [← hib]
        exact low_opnd H g hgl cb (Or.inr H.gand)
      have hib_or : (gateAt C ib).op = GateOp.or := by
        rcases LeafBound.ao_op hAO hibl with ho | ho
        · have := low_and H ib hibl ho hlow_ib
          omega
        · exact ho
      have hib_nr : ¬ OrReaches n C (n + ib) g := by
        rw [← hib]
        exact not_reach_opnd C hAO g hgl cb
      have hne_ab : opnd C g ca ≠ n + ib := by
        intro h
        rw [← hib] at h
        exact hvm (hdisjAB m (by rw [h]; exact hmB) hmB).symm
      have hA_low : Low G C (opnd C g ca) := low_opnd H g hgl ca (Or.inr H.gand)
      have hA_nr : ¬ OrReaches n C (opnd C g ca) g := not_reach_opnd C hAO g hgl ca
      obtain ⟨o, hol, hoo, hob⟩ := out_gate H
      have hog : o ≠ g := fun h => H.dirty (h ▸ hob)
      have hoib : o ≠ ib := fun h => hlow_ib (h ▸ hob)
      have hk0g : k0 ≠ g := pz_ne H k0 m hpz_m
      have hnr0 : ¬ OrReaches n C (opnd C k0 (1 - c0)) g := not_both' H k0 hk0 hk0o c0 hr0
      have hboth_v : ∀ r < C.gates.length, r ≠ g → OrReaches n C (n + r) g →
          FeedsC1 C m r → FeedsC2 C m r → ∀ w, wireVal n C (n + r) (unitInput w) = true → w = v := by
        intro r hrl hrg hrr ⟨k1, hk1, ho1, d1, hr1, hm1⟩ ⟨k2, hk2, ho2, d2, hr2, u, hum, hu2⟩ w hrw
        have hlt1 := opnd_lt C hAO k1 hk1 d1
        have hlt2 := opnd_lt C hAO k2 hk2 d2
        have hk1g : k1 ≠ g := fun heq =>
          not_reach_opnd C hAO g hgl d1 (reach_trans C hAO r g hrl hrr _ (by rw [← heq]; omega) (heq ▸ hr1))
        have hk2g : k2 ≠ g := fun heq =>
          not_reach_opnd C hAO g hgl d2 (reach_trans C hAO r g hrl hrr _ (by rw [← heq]; omega) (heq ▸ hr2))
        have hw1 : wireVal n C (opnd C k1 d1) (unitInput w) = true :=
          (reach_le C hAO r _ (by omega) hr1).2 (unitInput w) hrw
        have hw2 : wireVal n C (opnd C k2 d2) (unitInput w) = true :=
          (reach_le C hAO r _ (by omega) hr2).2 (unitInput w) hrw
        have hawm : G.Adj w m := and_pair' H k1 hk1 ho1 hk1g d1 w m hw1 hm1
        have hawu : G.Adj w u := and_pair' H k2 hk2 ho2 hk2g d2 w u hw2 hu2
        have hpz_u : PZ C g k2 u := (pz_iff C g k2 u).2 ⟨d2, reach_trans C hAO r g hrl hrr _ (by omega) hr2, hu2⟩
        have havu : G.Adj v u := hadj_vpz k2 hk2 ho2 u hpz_u
        exact c4 h4 u m w v hum hawu.symm hawm.symm havu.symm hadj_mv
      have hfeeds_disj : ∀ r < C.gates.length, r ≠ g → Low G C (n + r) → OrReaches n C (n + r) g →
          ¬ (FeedsC1 C m r ∧ FeedsC2 C m r) := by
        intro r hrl hrg hlow hrr ⟨hf1, hf2⟩
        obtain ⟨x, hx⟩ := hdiff r hrl hrg
        have hrx : gateVal n C r x = true := by
          by_contra hrf
          have hrf' : gateVal n C r x = false := Bool.eq_false_iff.2 hrf
          have hgf : gateVal n C g x = false := by
            by_contra hgt
            have hgt' : gateVal n C g x = true := Bool.eq_true_of_ne_false hgt
            have hrt : gateVal n C r x = true := (reach_le C hAO g (n + r) (by omega) hrr).2 x hgt'
            rw [hrf'] at hrt
            exact Bool.false_ne_true hrt
          exact hx (by rw [hrf', hgf])
        have hgf : gateVal n C g x = false := by
          by_contra hgt
          have hgt' : gateVal n C g x = true := Bool.eq_true_of_ne_false hgt
          exact hx (by rw [hrx, hgt'])
        rcases (val_low H (n + r) (by omega) hlow x).1 hrx with ⟨w, hxw, hrw⟩ | ⟨_, hgt⟩
        · have hwv : w = v := hboth_v r hrl hrg hrr hf1 hf2 w hrw
          subst hwv
          have hgt : gateVal n C g x = true := unit_pair w x hxw C hAO (n + g) (by omega) hgv_true
          rw [hgt] at hgf
          exact Bool.false_ne_true hgf.symm
        · rw [hgt] at hgf
          exact Bool.false_ne_true hgf.symm
      have h0g : opnd C k0 c0 = n + g := by
        by_contra hne0
        have hl0 := opnd_lt C hAO k0 hk0 c0
        rcases srcOf_cases (n := n) (opnd C k0 c0) with ⟨a, ha⟩ | ⟨r, hr⟩
        · rw [ha] at hr0
          exact reach_input C _ g a.2 hr0
        · have hrl : r < C.gates.length := by omega
          have hrg : r ≠ g := fun h => hne0 (hr.trans (h ▸ rfl))
          have hlowr : Low G C (n + r) := by
            rw [← hr]
            exact low_opnd H k0 hk0 c0 (Or.inr hk0o)
          have hrr : OrReaches n C (n + r) g := by rw [← hr]; exact hr0
          have hr_self : OrReaches n C (opnd C k0 c0) r := by rw [hr]; exact reach_self C hAO r hrl
          have hf1 : FeedsC1 C m r := ⟨k0, hk0, hk0o, c0, hr_self, hm0⟩
          have hf2 : FeedsC2 C m r := ⟨k0, hk0, hk0o, c0, hr_self, z, hzm, hz0⟩
          exact hfeeds_disj r hrl hrg hlowr hrr ⟨hf1, hf2⟩
      have hl0 := opnd_lt C hAO k0 hk0 c0
      have hgk0 : g < k0 := by omega
      have hk0ib : k0 ≠ ib := by omega
      have hl0' := opnd_lt C hAO k0 hk0 (1 - c0)
      obtain ⟨ip, hip⟩ : ∃ ip, opnd C k0 (1 - c0) = n + ip := by
        rcases srcOf_cases (n := n) (opnd C k0 (1 - c0)) with ⟨u, hu⟩ | h
        · exfalso
          have key : ∀ y, wireVal n C (opnd C k0 (1 - c0)) (unitInput y) = true → u = y := by
            intro y hy
            rw [hu, wireVal_lt C _ u.2] at hy
            simpa [unitInput] using hy
          exact hzm ((key z hz0).symm.trans (key m hm0))
        · exact h
      have hip_lt : ip < k0 := by omega
      have hipl : ip < C.gates.length := by omega
      have hip_low : Low G C (n + ip) := by
        rw [← hip]
        exact low_opnd H k0 hk0 (1 - c0) (Or.inr hk0o)
      have hip_or : (gateAt C ip).op = GateOp.or := by
        rcases LeafBound.ao_op hAO hipl with ho | ho
        · have := low_and H ip hipl ho hip_low
          subst this
          exact absurd (by rw [hip]; exact reach_self C hAO ip hipl) hnr0
        · exact ho
      have hip_nr : ¬ OrReaches n C (n + ip) g := by rw [← hip]; exact hnr0
      have hip_g : ip ≠ g := fun h => hip_nr (h ▸ reach_self C hAO g hgl)
      have hip_ib : ip ≠ ib := fun h => honly k0 hk0 hk0g (1 - c0) (hip.trans (h ▸ rfl))
      have hm_ip : wireVal n C (n + ip) (unitInput m) = true := by rw [← hip]; exact hm0
      have hz_ip : wireVal n C (n + ip) (unitInput z) = true := by rw [← hip]; exact hz0
      have hvar_ip : ∀ y, wireVal n C (n + ip) (unitInput y) = true → G.Adj v y := by
        intro y hy
        rw [← hip] at hy
        exact and_pair' H k0 hk0 hk0o hk0g c0 v y (by rw [h0g]; exact hgv_true) hy
      have hex_t : ∃ t < C.gates.length, OrReaches n C (n + ip) t ∧
          wireVal n C (n + t) (unitInput m) = true ∧
          (∃ u, u ≠ m ∧ wireVal n C (n + t) (unitInput u) = true) ∧
          ∃ dm : Fin 2, wireVal n C (opnd C t dm) (unitInput m) = true ∧
            ∀ y, wireVal n C (opnd C t dm) (unitInput y) = true → y = m := by
        have key : ∀ t < C.gates.length, OrReaches n C (n + ip) t →
            wireVal n C (n + t) (unitInput m) = true →
            (∃ u, u ≠ m ∧ wireVal n C (n + t) (unitInput u) = true) →
            ∃ t' < C.gates.length, OrReaches n C (n + ip) t' ∧
              wireVal n C (n + t') (unitInput m) = true ∧
              (∃ u, u ≠ m ∧ wireVal n C (n + t') (unitInput u) = true) ∧
              ∃ dm : Fin 2, wireVal n C (opnd C t' dm) (unitInput m) = true ∧
                ∀ y, wireVal n C (opnd C t' dm) (unitInput y) = true → y = m := by
          intro t
          induction t using Nat.strong_induction_on with
          | _ t ih =>
            intro htl hrt hmt ⟨u, hum, hut⟩
            have htnr : ¬ OrReaches n C (n + t) g := fun h =>
              hip_nr (reach_trans C hAO t g htl h _ (by omega) hrt)
            have htg : t ≠ g := fun h => htnr (h ▸ reach_self C hAO g hgl)
            have htlow : Low G C (n + t) := by
              intro hb
              have h1 := hb (unitInput m) hmt
              rw [unit_false] at h1
              exact absurd h1 (by decide)
            have htor : (gateAt C t).op = GateOp.or := by
              rcases LeafBound.ao_op hAO htl with ho | ho
              · exact absurd (low_and H t htl ho htlow) htg
              · exact ho
            obtain ⟨dm, hdm⟩ := (val_or' C hAO t htl htor (unitInput m)).1 hmt
            by_cases hex : ∃ u', u' ≠ m ∧ wireVal n C (opnd C t dm) (unitInput u') = true
            · obtain ⟨u', hu'm, hu'⟩ := hex
              have hlt := opnd_lt C hAO t htl dm
              rcases srcOf_cases (n := n) (opnd C t dm) with ⟨a, ha⟩ | ⟨j, hj⟩
              · exfalso
                have h1 : a = m := by rw [ha, wireVal_lt C _ a.2] at hdm; simpa [unitInput] using hdm
                have h2 : a = u' := by rw [ha, wireVal_lt C _ a.2] at hu'; simpa [unitInput] using hu'
                exact hu'm (h2.symm.trans h1)
              · have hjl : j < C.gates.length := by omega
                have hrtj : OrReaches n C (n + t) j :=
                  (reach_gate C hAO t j htl).2 (Or.inr ⟨htor, dm, by rw [hj]; exact reach_self C hAO j hjl⟩)
                have hripj : OrReaches n C (n + ip) j :=
                  reach_trans C hAO t j htl hrtj _ (by omega) hrt
                rw [hj] at hdm hu'
                exact ih j (by omega) hjl hripj hdm ⟨u', hu'm, hu'⟩
            · refine ⟨t, htl, hrt, hmt, ⟨u, hum, hut⟩, dm, hdm, fun y hy => ?_⟩
              by_contra hym
              exact hex ⟨y, hym, hy⟩
        exact key ip hipl (reach_self C hAO ip hipl) hm_ip ⟨z, hzm, hz_ip⟩
      obtain ⟨t, htl, hrip_t, hmt, ⟨ut, hutm, hut⟩, dm, hdm_m, hdm_only⟩ := hex_t
      have htle_ip : t ≤ ip := by
        have := (reach_le C hAO t _ (by omega) hrip_t).1
        omega
      have ht_lt_k0 : t < k0 := by omega
      have ht_k0 : t ≠ k0 := by omega
      have ht_nr : ¬ OrReaches n C (n + t) g := fun h =>
        hip_nr (reach_trans C hAO t g htl h _ (by omega) hrip_t)
      have htg : t ≠ g := fun h => ht_nr (h ▸ reach_self C hAO g hgl)
      have htlow : Low G C (n + t) := by
        intro hb
        have h1 := hb (unitInput m) hmt
        rw [unit_false] at h1
        exact absurd h1 (by decide)
      have htor : (gateAt C t).op = GateOp.or := by
        rcases LeafBound.ao_op hAO htl with ho | ho
        · exact absurd (low_and H t htl ho htlow) htg
        · exact ho
      have hut_ip : wireVal n C (n + ip) (unitInput ut) = true :=
        (reach_le C hAO t _ (by omega) hrip_t).2 _ hut
      have hpz_ut : PZ C g k0 ut := (pz_iff C g k0 ut).2 ⟨c0, hr0, by rw [hip]; exact hut_ip⟩
      have hadj_vut : G.Adj v ut := hadj_vpz k0 hk0 hk0o ut hpz_ut
      have hut_not_A : ¬ wireVal n C (opnd C g ca) (unitInput ut) = true :=
        fun h => hs v ut hadj_vut (hsideA ut h).symm
      have hut_not_B : ¬ wireVal n C (opnd C g cb) (unitInput ut) = true :=
        fun h => hutm (huniqB k0 hk0 hk0o ut hpz_ut h)
      have ht_not_g : ∀ c, ¬ OrReaches n C (opnd C g c) t := by
        intro c hr
        have hlt := opnd_lt C hAO g hgl c
        have hut_c : wireVal n C (opnd C g c) (unitInput ut) = true :=
          (reach_le C hAO t _ (by omega) hr).2 _ hut
        rcases fin2_or ca c with rfl | rfl
        · exact hut_not_A hut_c
        · rw [hcb_eq] at hut_c
          exact hut_not_B hut_c
      have ht_ib : t ≠ ib := by
        rintro rfl
        exact ht_not_g cb (by rw [hib]; exact reach_self C hAO t htl)
      have hT_above_t : ∀ T < C.gates.length, (gateAt C T).op = GateOp.and → ∀ d,
          OrReaches n C (opnd C T d) t →
          T ≠ g ∧ wireVal n C (opnd C T (1 - d)) (unitInput v) = true ∧
          ∀ w, wireVal n C (opnd C T (1 - d)) (unitInput w) = true → w = v := by
        intro T hT hTo d hrd
        have hTg : T ≠ g := fun h => ht_not_g d (h ▸ hrd)
        have hlt_d := opnd_lt C hAO T hT d
        have hlt_d' := opnd_lt C hAO T hT (1 - d)
        have hm_d : wireVal n C (opnd C T d) (unitInput m) = true :=
          (reach_le C hAO t _ (by omega) hrd).2 _ hmt
        have hut_d : wireVal n C (opnd C T d) (unitInput ut) = true :=
          (reach_le C hAO t _ (by omega) hrd).2 _ hut
        have hwv : ∀ w, wireVal n C (opnd C T (1 - d)) (unitInput w) = true → w = v := by
          intro w hw
          have hwm : G.Adj m w := and_pair' H T hT hTo hTg d m w hm_d hw
          have hwut : G.Adj ut w := and_pair' H T hT hTo hTg d ut w hut_d hw
          exact c4 h4 ut m w v hutm hwut hwm hadj_vut.symm hadj_mv
        have hlow' := low_opnd H T hT (1 - d) (Or.inr hTo)
        refine ⟨hTg, ?_, hwv⟩
        rcases (val_low H _ (by omega) hlow' (fun _ => true)).1 (ones_val C hAO _ (by omega)) with ⟨w, _, hw⟩ | ⟨hr, _⟩
        · rwa [hwv w hw] at hw
        · exact (reach_le C hAO g _ (by omega) hr).2 _ hgv_true
      let P : Prog n ℕ :=
        { isAnd := fun k => if k = ib then true else if k = g then true else if k = k0 then false else isA (gateAt C k).op
          src := fun k c =>
            if k = ib then (if c = 0 then srcOf n (opnd C g ca) else some (Sum.inl m))
            else if k = g then (if c = 0 then some (Sum.inl v) else some (Sum.inr ip))
            else if k = k0 then (if c = 0 then some (Sum.inr ib) else some (Sum.inr g))
            else if k = t ∧ c = dm then (none : Src n ℕ)
            else if opnd C k c = n + g then some (Sum.inl v)
            else srcOf n (opnd C k c) }
      let rank : ℕ → ℕ := fun k =>
        if k = ib then 2 * g
        else if k = g then 2 * ip + 1
        else 2 * k
      let K := Finset.range C.gates.length
      have hK : ∀ k, k ∈ K ↔ k < C.gates.length := fun k => Finset.mem_range
      have hrank_ib : rank ib = 2 * g := by simp [rank]
      have hrank_g : rank g = 2 * ip + 1 := by
        have : g ≠ ib := by omega
        simp [rank, this]
      have hrank_other : ∀ j, j ≠ ib → j ≠ g → rank j = 2 * j := by
        intro j hjib hjg
        simp [rank, hjib, hjg]
      have hcl : Closed P rank K := by
        intro k hk c j hj
        have hkl := (hK k).1 hk
        by_cases hkib : k = ib
        · have hj' : (if c = 0 then srcOf n (opnd C g ca) else some (Sum.inl m)) = some (Sum.inr j) := by
            simpa only [P, ite_eq_left hkib] using hj
          split_ifs at hj' with hc0
          · have hw := srcOf_inr _ _ hj'
            have hjlt : j < g := by omega
            have hjib : j ≠ ib := fun h => hne_ab (hw.trans (h ▸ rfl))
            have hjg : j ≠ g := by omega
            subst hkib
            refine ⟨(hK j).2 (by omega), ?_⟩
            rw [hrank_other j hjib hjg, hrank_ib]
            omega
          · simp at hj'
        · by_cases hkg : k = g
          · have hj' : (if c = 0 then some (Sum.inl v) else some (Sum.inr ip)) = some (Sum.inr j) := by
              simpa only [P, ite_eq_right hkib, ite_eq_left hkg] using hj
            split_ifs at hj' with hc0
            · simp at hj'
            · have hjip : ip = j := by simpa using hj'
              subst hjip
              subst hkg
              refine ⟨(hK ip).2 hipl, ?_⟩
              rw [hrank_other ip hip_ib hip_g, hrank_g]
              omega
          · by_cases hkk0 : k = k0
            · have hj' : (if c = 0 then (some (Sum.inr ib) : Src n ℕ) else some (Sum.inr g)) = some (Sum.inr j) := by
                simpa only [P, ite_eq_right hkib, ite_eq_right hkg, ite_eq_left hkk0] using hj
              subst hkk0
              rw [hrank_other k hk0ib hk0g]
              split_ifs at hj' with hc0
              · have hjib : ib = j := by simpa using hj'
                subst hjib
                refine ⟨(hK ib).2 hibl, ?_⟩
                rw [hrank_ib]
                omega
              · have hjg : g = j := by simpa using hj'
                subst hjg
                refine ⟨(hK g).2 hgl, ?_⟩
                rw [hrank_g]
                omega
            · by_cases hkt : k = t ∧ c = dm
              · have hj' : (none : Src n ℕ) = some (Sum.inr j) := by
                  simpa only [P, ite_eq_right hkib, ite_eq_right hkg, ite_eq_right hkk0, ite_eq_left hkt] using hj
                simp at hj'
              · by_cases hcg : opnd C k c = n + g
                · have hj' : (some (Sum.inl v) : Src n ℕ) = some (Sum.inr j) := by
                    simpa only [P, ite_eq_right hkib, ite_eq_right hkg, ite_eq_right hkk0,
                      ite_eq_right hkt, ite_eq_left hcg] using hj
                  simp at hj'
                · have hj' : srcOf n (opnd C k c) = some (Sum.inr j) := by
                    simpa only [P, ite_eq_right hkib, ite_eq_right hkg, ite_eq_right hkk0,
                      ite_eq_right hkt, ite_eq_right hcg] using hj
                  have hw := srcOf_inr _ _ hj'
                  have hlt := opnd_lt C hAO k hkl c
                  have hjng : j ≠ g := fun h => hcg (hw.trans (h ▸ rfl))
                  have hjib : j ≠ ib := fun h => honly k hkl hkg c (hw.trans (h ▸ rfl))
                  refine ⟨(hK j).2 (by omega), ?_⟩
                  rw [hrank_other j hjib hjng, hrank_other k hkib hkg]
                  omega
      obtain ⟨val, hval⟩ := sol_exists P rank K hcl
      have hplain : ∀ k, k ≠ ib → k ≠ g → k ≠ k0 → P.isAnd k = isA (gateAt C k).op := by
        intro k hkib hkg hkk0
        simp only [P, ite_eq_right hkib, ite_eq_right hkg, ite_eq_right hkk0]
      have hsrcp : ∀ k c, k ≠ ib → k ≠ g → k ≠ k0 → ¬ (k = t ∧ c = dm) → opnd C k c ≠ n + g →
          P.src k c = srcOf n (opnd C k c) := by
        intro k c hkib hkg hkk0 hkt hcg
        simp only [P, ite_eq_right hkib, ite_eq_right hkg, ite_eq_right hkk0, ite_eq_right hkt, ite_eq_right hcg]
      have hpure_no_t : ∀ k < C.gates.length, k ≠ g → k ≠ ib → Low G C (n + k) →
          ¬ OrReaches n C (n + k) g → ¬ OrReaches n C (n + k) t → ∀ x, val k x = gateVal n C k x := by
        intro k
        induction k using Nat.strong_induction_on with
        | _ k ih =>
          intro hkl hkng hkib hl hr hrt x
          have hor : (gateAt C k).op = GateOp.or := by
            rcases LeafBound.ao_op hAO hkl with ho | ho
            · exact absurd (low_and H k hkl ho hl) hkng
            · exact ho
          have hkk0 : k ≠ k0 := by rintro rfl; rw [hk0o] at hor; cases hor
          have hkt : k ≠ t := fun h => hrt (h ▸ reach_self C hAO k hkl)
          have hcr : ∀ c, ¬ OrReaches n C (opnd C k c) g := fun c h =>
            hr ((reach_gate C hAO k g hkl).2 (Or.inr ⟨hor, c, h⟩))
          have hcrt : ∀ c, ¬ OrReaches n C (opnd C k c) t := fun c h =>
            hrt ((reach_gate C hAO k t hkl).2 (Or.inr ⟨hor, c, h⟩))
          have hc : ∀ c, opnd C k c ≠ n + g := fun c h => hcr c (by rw [h]; exact reach_self C hAO g hgl)
          have hs : ∀ c, srcAt x (fun j => val j x) (P.src k c) = wireVal n C (opnd C k c) x := by
            intro c
            rw [hsrcp k c hkib hkng hkk0 (fun h => hkt h.1) (hc c)]
            have hlt := opnd_lt C hAO k hkl c
            rcases srcOf_cases (n := n) (opnd C k c) with ⟨a, ha⟩ | ⟨j, hj⟩
            · rw [ha, srcOf_input, wireVal_lt C _ a.2]
              rfl
            · have hlow := low_opnd H k hkl c (Or.inl hl)
              have hrj := hcr c
              have hrtj := hcrt c
              have hcj := hc c
              have hjib : j ≠ ib := fun h => honly k hkl hkng c (hj.trans (h ▸ rfl))
              rw [hj] at hlow hrj hrtj hcj ⊢
              rw [srcOf_gate]
              exact ih j (by omega) (by omega) (by omega) hjib hlow hrj hrtj x
          have e := hval x k ((hK k).2 hkl)
          simp only at e
          rw [e, hs, hs, hplain k hkib hkng hkk0]
          exact (gate_eq C hAO k hkl x).symm
      have hpureW_no_t : ∀ w < n + C.gates.length, Low G C w → ¬ OrReaches n C w g → ¬ OrReaches n C w t →
          w ≠ n + g → w ≠ n + ib → ∀ x, srcAt x (fun j => val j x) (srcOf n w) = wireVal n C w x := by
        intro w hw hl hr hrt hwg hwib x
        rcases srcOf_cases (n := n) w with ⟨a, ha⟩ | ⟨j, hj⟩
        · rw [ha, srcOf_input, wireVal_lt C _ a.2]
          rfl
        · rw [hj] at hl hr hrt hwg hwib hw ⊢
          rw [srcOf_gate]
          exact hpure_no_t j (by omega) (by omega) (by omega) hl hr hrt x
      have hfacA : ∀ x, srcAt x (fun j => val j x) (srcOf n (opnd C g ca)) = wireVal n C (opnd C g ca) x :=
        fun x => hpureW_no_t _ (by omega) hA_low hA_nr (ht_not_g ca) (by omega) hne_ab x
      have hib_val : ∀ x, val ib x = (wireVal n C (opnd C g ca) x && x m) := by
        intro x
        have e := hval x ib ((hK ib).2 hibl)
        simp only at e
        have e1 : P.isAnd ib = true := by simp only [P, ite_true]
        have e2 : P.src ib 0 = srcOf n (opnd C g ca) := by simp only [P, ite_true]
        have e3 : P.src ib 1 = some (Sum.inl m) := by simp only [P, ite_true]; rfl
        rw [e, e1, e2, e3, hfacA x]
        rfl
      have hib_F : ∀ x, val ib x = true → graphFun G ∅ x = true := by
        intro x hx
        rw [hib_val x, Bool.and_eq_true] at hx
        obtain ⟨h1, h2⟩ := hx
        obtain ⟨y, hy, hw⟩ := (opnd_val H ca x).1 h1
        exact (graphFun_empty G x).2 ⟨m, y, hadj_mA y hw, h2, hy⟩
      have hg_val : ∀ x, val g x = (x v && val ip x) := by
        intro x
        have hgib : g ≠ ib := by omega
        have e := hval x g ((hK g).2 hgl)
        simp only at e
        have e1 : P.isAnd g = true := by simp only [P, ite_eq_right hgib, ite_true]
        have e2 : P.src g 0 = some (Sum.inl v) := by simp only [P, ite_eq_right hgib, ite_true]
        have e3 : P.src g 1 = some (Sum.inr ip) := by simp only [P, ite_eq_right hgib, ite_true]; rfl
        rw [e, e1, e2, e3]
        rfl
      have hk0_val : ∀ x, val k0 x = (val ib x || val g x) := by
        intro x
        have e := hval x k0 ((hK k0).2 hk0)
        simp only at e
        have e1 : P.isAnd k0 = false := by
          simp only [P, ite_eq_right hk0ib, ite_eq_right hk0g, ite_true]
        have e2 : P.src k0 0 = some (Sum.inr ib) := by
          simp only [P, ite_eq_right hk0ib, ite_eq_right hk0g, ite_true]
        have e3 : P.src k0 1 = some (Sum.inr g) := by
          simp only [P, ite_eq_right hk0ib, ite_eq_right hk0g, ite_true]; rfl
        rw [e, e1, e2, e3]
        rfl
      -- Now look at `val k x ≤ gateVal n C k x` for all `k ≠ ib, g, k0`!
      -- Even better: for ANY low gate `k < C.gates.length` (`k ≠ g`, `k ≠ ib`):
      --   `val k x = true → gateVal n C k x = true`!
      -- Why? Because every low gate `k ≠ g, ib` is an OR gate (so `k ≠ k0`), and its operands are either:
      --   - `none` (false ≤ anything)
      --   - `some (Sum.inl v)` (when `opnd C k c = n + g`, and `x v = true → gateVal n C g x = true`!)
      --   - `srcOf n (opnd C k c)` (where `opnd C k c` is low and not `n + g` or `n + ib`, so by IH `≤ wireVal`!)!
      have hlow_le : ∀ k < C.gates.length, k ≠ g → k ≠ ib → Low G C (n + k) → ∀ x,
          val k x = true → gateVal n C k x = true := by
        intro k
        induction k using Nat.strong_induction_on with
        | _ k ih =>
          intro hkl hkng hkib hl x hvk
          have hor : (gateAt C k).op = GateOp.or := by
            rcases LeafBound.ao_op hAO hkl with ho | ho
            · exact absurd (low_and H k hkl ho hl) hkng
            · exact ho
          have hkk0 : k ≠ k0 := by rintro rfl; rw [hk0o] at hor; cases hor
          have hop : ∀ c, srcAt x (fun j => val j x) (P.src k c) = true →
              wireVal n C (opnd C k c) x = true := by
            intro c hsc
            have hlt := opnd_lt C hAO k hkl c
            have hlow := low_opnd H k hkl c (Or.inl hl)
            by_cases hkt : k = t ∧ c = dm
            · have ep : P.src k c = none := by
                simp only [P, ite_eq_right hkib, ite_eq_right hkng, ite_eq_right hkk0, ite_eq_left hkt]
              rw [ep] at hsc
              exact Bool.false_ne_true hsc |>.elim
            · by_cases hcg : opnd C k c = n + g
              · have ep : P.src k c = some (Sum.inl v) := by
                  simp only [P, ite_eq_right hkib, ite_eq_right hkng, ite_eq_right hkk0,
                    ite_eq_right hkt, ite_eq_left hcg]
                rw [ep] at hsc
                rw [hcg]
                exact unit_pair v x hsc C hAO (n + g) (by omega) hgv_true
              · rw [hsrcp k c hkib hkng hkk0 hkt hcg] at hsc
                rcases srcOf_cases (n := n) (opnd C k c) with ⟨a, ha⟩ | ⟨j, hj⟩
                · rw [ha, srcOf_input] at hsc
                  rw [ha, wireVal_lt C _ a.2]
                  exact hsc
                · have hjib : j ≠ ib := fun h => honly k hkl hkng c (hj.trans (h ▸ rfl))
                  rw [hj] at hlow hcg hsc ⊢
                  rw [srcOf_gate] at hsc
                  exact ih j (by omega) (by omega) (by rintro rfl; exact hcg rfl) hjib hlow x hsc
          have e := hval x k ((hK k).2 hkl)
          simp only at e
          have hA : P.isAnd k = false := by rw [hplain k hkib hkng hkk0, hor]; rfl
          rw [e, hA, opv_or] at hvk
          refine (val_or C hAO k hkl hor x).2 ?_
          rcases hvk with h0 | h1
          · exact Or.inl (hop 0 h0)
          · exact Or.inr (hop 1 h1)
      have hlowW_le : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → k ≠ k0 → ∀ c x,
          srcAt x (fun j => val j x) (P.src k c) = true → wireVal n C (opnd C k c) x = true := by
        intro k hkl ho hkng hkk0 c x hsc
        have hkib : k ≠ ib := by rintro rfl; rw [hib_or] at ho; cases ho
        have hkt : ¬ (k = t ∧ c = dm) := by rintro ⟨rfl, _⟩; rw [htor] at ho; cases ho
        have hlt := opnd_lt C hAO k hkl c
        have hlow := low_opnd H k hkl c (Or.inr ho)
        by_cases hcg : opnd C k c = n + g
        · have ep : P.src k c = some (Sum.inl v) := by
            simp only [P, ite_eq_right hkib, ite_eq_right hkng, ite_eq_right hkk0,
              ite_eq_right hkt, ite_eq_left hcg]
          rw [ep] at hsc
          rw [hcg]
          exact unit_pair v x hsc C hAO (n + g) (by omega) hgv_true
        · rw [hsrcp k c hkib hkng hkk0 hkt hcg] at hsc
          rcases srcOf_cases (n := n) (opnd C k c) with ⟨a, ha⟩ | ⟨j, hj⟩
          · rw [ha, srcOf_input] at hsc
            rw [ha, wireVal_lt C _ a.2]
            exact hsc
          · have hjib : j ≠ ib := fun h => honly k hkl hkng c (hj.trans (h ▸ rfl))
            rw [hj] at hlow hcg hsc ⊢
            rw [srcOf_gate] at hsc
            exact hlow_le j (by omega) (by rintro rfl; exact hcg rfl) hjib hlow x hsc
      have hg_F : ∀ x, val g x = true → graphFun G ∅ x = true := by
        intro x hgx
        rw [hg_val x, Bool.and_eq_true] at hgx
        obtain ⟨hxv, hipx⟩ := hgx
        have hip_cw : gateVal n C ip x = true := hlow_le ip hipl hip_g hip_ib hip_low x hipx
        refine H.others k0 hk0 hk0o hk0g x ((val_and' C hAO k0 hk0 hk0o x c0).2 ⟨?_, ?_⟩)
        · rw [h0g]
          exact unit_pair v x hxv C hAO (n + g) (by omega) hgv_true
        · rw [hip]
          exact hip_cw
      have hk0_F : ∀ x, val k0 x = true → graphFun G ∅ x = true := by
        intro x hk0x
        rw [hk0_val x, Bool.or_eq_true] at hk0x
        rcases hk0x with hibx | hgx
        · exact hib_F x hibx
        · exact hg_F x hgx
      have hupper : ∀ x, graphFun G ∅ x = false → ∀ k < C.gates.length, BelowF G C k → val k x = false := by
        intro x hx k
        induction k using Nat.strong_induction_on with
        | _ k ih =>
          intro hkl hb
          have hkng : k ≠ g := fun h => H.dirty (h ▸ hb)
          have hkib : k ≠ ib := fun h => hlow_ib (h ▸ hb)
          by_contra hne
          have hvt : val k x = true := by simpa using hne
          have contra : graphFun G ∅ x = true → False := fun h => by
            rw [hx] at h
            exact absurd h (by decide)
          by_cases hkk0 : k = k0
          · subst hkk0
            exact contra (hk0_F x hvt)
          · rcases LeafBound.ao_op hAO hkl with ho | ho
            · have e := hval x k ((hK k).2 hkl)
              simp only at e
              have hA : P.isAnd k = true := by rw [hplain k hkib hkng hkk0, ho]; rfl
              rw [e, hA, opv_and] at hvt
              have hw0 := hlowW_le k hkl ho hkng hkk0 0 x hvt.1
              have hw1 := hlowW_le k hkl ho hkng hkk0 1 x hvt.2
              exact contra (hb x ((val_and C hAO k hkl ho x).2 ⟨hw0, hw1⟩))
            · have hkt : k ≠ t := fun h => htlow (h ▸ hb)
              have e := hval x k ((hK k).2 hkl)
              simp only at e
              have hA : P.isAnd k = false := by rw [hplain k hkib hkng hkk0, ho]; rfl
              rw [hvt, hA] at e
              have hop : ∀ c, srcAt x (fun j => val j x) (P.src k c) = false := by
                intro c
                have hlt := opnd_lt C hAO k hkl c
                have hbel : ∀ w, wireVal n C (opnd C k c) w = true → graphFun G ∅ w = true :=
                  fun w hw => below_or hAO k hkl ho hb c w hw
                have hc : opnd C k c ≠ n + g := by
                  intro h
                  refine H.dirty fun w hw => hbel w ?_
                  rw [h]; exact hw
                rw [hsrcp k c hkib hkng hkk0 (fun h => hkt h.1) hc]
                rcases srcOf_cases (n := n) (opnd C k c) with ⟨a, ha⟩ | ⟨j, hj⟩
                · rw [ha] at hbel
                  exact absurd hbel (input_low _ a.2)
                · rw [hj] at hbel ⊢
                  rw [srcOf_gate]
                  exact ih j (by omega) (by omega) hbel
              rw [hop 0, hop 1] at e
              exact absurd e (by decide)
      have hrise : ∀ x, ∀ p < C.gates.length, BelowF G C p → val p x = true → val o x = true := by
        intro x p hp hb hpv
        have hup : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → BelowF G C j → ∀ b i, opnd C j b = n + i →
            BelowF G C i → val i x = true → val j x = true := by
          intro j hj hop hbj c i hi hbi hvi
          have hjng : j ≠ g := fun h => H.dirty (h ▸ hbj)
          have hjib : j ≠ ib := fun h => hlow_ib (h ▸ hbj)
          have hjk0 : j ≠ k0 := by rintro rfl; rw [hk0o] at hop; cases hop
          have hjt : j ≠ t := fun h => htlow (h ▸ hbj)
          have hing : i ≠ g := fun h => H.dirty (h ▸ hbi)
          have e := hval x j ((hK j).2 hj)
          simp only at e
          have hA : P.isAnd j = false := by rw [hplain j hjib hjng hjk0, hop]; rfl
          have hsi : srcAt x (fun k => val k x) (P.src j c) = true := by
            rw [hsrcp j c hjib hjng hjk0 (fun h => hjt h.1) (by omega), hi, srcOf_gate]
            exact hvi
          rw [e, hA, opv_or]
          fin_cases c
          · exact Or.inl hsi
          · exact Or.inr hsi
        obtain ⟨o', ho', hvo⟩ := top_up H (fun k => val k x) hup p hp hb hpv
        have : o' = o := by omega
        rwa [this] at hvo
      -- Now for `hlower`: every low gate `k ≠ g, ib` is true at `(x, y)` whenever `x y = true`, `y` is a variable of `n + k`,
      -- AND `(OrReaches n C (n + k) t → y ≠ m)`!
      have hlow_vtx : ∀ k < C.gates.length, k ≠ g → k ≠ ib → Low G C (n + k) → ∀ x y,
          x y = true → (OrReaches n C (n + k) t → y ≠ m) →
          wireVal n C (n + k) (unitInput y) = true → val k x = true := by
        intro k
        induction k using Nat.strong_induction_on with
        | _ k ih =>
          intro hkl hkng hkib hl x y hxy hym hy
          have hor : (gateAt C k).op = GateOp.or := by
            rcases LeafBound.ao_op hAO hkl with ho | ho
            · exact absurd (low_and H k hkl ho hl) hkng
            · exact ho
          have hkk0 : k ≠ k0 := by rintro rfl; rw [hk0o] at hor; cases hor
          obtain ⟨c, hc⟩ := (val_or' C hAO k hkl hor (unitInput y)).1 hy
          have hlt := opnd_lt C hAO k hkl c
          have hlow := low_opnd H k hkl c (Or.inl hl)
          have hkt : ¬ (k = t ∧ c = dm) := by
            rintro ⟨rfl, rfl⟩
            exact hym (reach_self C hAO k hkl) (hdm_only y hc)
          have hsc : srcAt x (fun j => val j x) (P.src k c) = true := by
            by_cases hcg : opnd C k c = n + g
            · have ep : P.src k c = some (Sum.inl v) := by
                simp only [P, ite_eq_right hkib, ite_eq_right hkng, ite_eq_right hkk0,
                  ite_eq_right hkt, ite_eq_left hcg]
              rw [ep]
              rw [hcg] at hc
              rwa [(hgv y).1 hc] at hxy
            · rw [hsrcp k c hkib hkng hkk0 hkt hcg]
              rcases srcOf_cases (n := n) (opnd C k c) with ⟨a, ha⟩ | ⟨j, hj⟩
              · rw [ha, wireVal_lt C _ a.2] at hc
                have hay : a = y := by simpa [unitInput] using hc
                rw [ha, srcOf_input, hay]
                exact hxy
              · have hjl : j < C.gates.length := by omega
                have hjib : j ≠ ib := fun h => honly k hkl hkng c (hj.trans (h ▸ rfl))
                have hrkj : OrReaches n C (n + k) j :=
                  (reach_gate C hAO k j hkl).2 (Or.inr ⟨hor, c, by rw [hj]; exact reach_self C hAO j hjl⟩)
                rw [hj] at hlow hcg hc ⊢
                rw [srcOf_gate]
                exact ih j (by omega) hjl (by rintro rfl; exact hcg rfl) hjib hlow x y hxy
                  (fun hrjt => hym (reach_trans C hAO j t hjl hrjt _ (by omega) hrkj)) hc
          have e := hval x k ((hK k).2 hkl)
          simp only at e
          have hA : P.isAnd k = false := by rw [hplain k hkib hkng hkk0, hor]; rfl
          rw [e, hA, opv_or]
          fin_cases c
          · exact Or.inl hsc
          · exact Or.inr hsc
      have hopW_vtx : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → k ≠ k0 → ∀ c x y,
          x y = true → (OrReaches n C (opnd C k c) t → y ≠ m) →
          wireVal n C (opnd C k c) (unitInput y) = true →
          srcAt x (fun j => val j x) (P.src k c) = true := by
        intro k hkl ho hkng hkk0 c x y hxy hym hy
        have hkib : k ≠ ib := by rintro rfl; rw [hib_or] at ho; cases ho
        have hkt : ¬ (k = t ∧ c = dm) := by rintro ⟨rfl, _⟩; rw [htor] at ho; cases ho
        have hlt := opnd_lt C hAO k hkl c
        have hlow := low_opnd H k hkl c (Or.inr ho)
        by_cases hcg : opnd C k c = n + g
        · have ep : P.src k c = some (Sum.inl v) := by
            simp only [P, ite_eq_right hkib, ite_eq_right hkng, ite_eq_right hkk0,
              ite_eq_right hkt, ite_eq_left hcg]
          rw [ep]
          rw [hcg] at hy
          rwa [(hgv y).1 hy] at hxy
        · rw [hsrcp k c hkib hkng hkk0 hkt hcg]
          rcases srcOf_cases (n := n) (opnd C k c) with ⟨a, ha⟩ | ⟨j, hj⟩
          · rw [ha, wireVal_lt C _ a.2] at hy
            have hay : a = y := by simpa [unitInput] using hy
            rw [ha, srcOf_input, hay]
            exact hxy
          · have hjl : j < C.gates.length := by omega
            have hjib : j ≠ ib := fun h => honly k hkl hkng c (hj.trans (h ▸ rfl))
            rw [hj] at hlow hcg hy hym ⊢
            rw [srcOf_gate]
            exact hlow_vtx j hjl (by rintro rfl; exact hcg rfl) hjib hlow x y hxy hym hy
      have hlower : ∀ p q, G.Adj p q → val o (pairInput p q) = true := by
        intro p q hpq
        set e := pairInput p q with he
        have hFe : graphFun G ∅ e = true :=
          (graphFun_empty G e).2 ⟨p, q, hpq, by simp [he, pairInput], by simp [he, pairInput]⟩
        have hk0b : BelowF G C k0 := H.others k0 hk0 hk0o hk0g
        by_cases hibe : val ib e = true
        · refine hrise e k0 hk0 hk0b ?_
          rw [hk0_val e, Bool.or_eq_true]
          exact Or.inl hibe
        · have hnot_ib : ¬ (wireVal n C (opnd C g ca) e = true ∧ e m = true) := by
            intro ⟨h1, h2⟩
            refine hibe ?_
            rw [hib_val e, Bool.and_eq_true]
            exact ⟨h1, h2⟩
          have hem_no_v : e m = true → e v = false := by
            intro hem
            by_contra hev
            have hevt : e v = true := Bool.eq_true_of_ne_false hev
            exact hnot_ib ⟨unit_pair v e hevt C hAO _ (by omega) hvA, hem⟩
          obtain ⟨T, hT, hTo, hTb, hTe⟩ := top_down H e hFe
          have hTg : T ≠ g := fun h => H.dirty (h ▸ hTb)
          have hT_vars : ∀ c, ∃ y, e y = true ∧ (OrReaches n C (opnd C T c) t → y ≠ m) ∧
              wireVal n C (opnd C T c) (unitInput y) = true := by
            intro c
            have hlt_c := opnd_lt C hAO T hT c
            have hlow_c := low_opnd H T hT c (Or.inr hTo)
            have hwc : wireVal n C (opnd C T c) e = true := ((val_and' C hAO T hT hTo e c).1 hTe).1
            have hwc' : wireVal n C (opnd C T (1 - c)) e = true := ((val_and' C hAO T hT hTo e c).1 hTe).2
            rcases (val_low H _ (by omega) hlow_c e).1 hwc with ⟨y, hye, hyw⟩ | ⟨hrc, hge⟩
            · refine ⟨y, hye, fun hrt hym => ?_, hyw⟩
              subst hym
              have hev_f : e v = false := hem_no_v hye
              obtain ⟨_, _, hwv⟩ := hT_above_t T hT hTo c hrt
              have hlt_c' := opnd_lt C hAO T hT (1 - c)
              have hlow_c' := low_opnd H T hT (1 - c) (Or.inr hTo)
              rcases (val_low H _ (by omega) hlow_c' e).1 hwc' with ⟨w, hwe, hww⟩ | ⟨_, hge'⟩
              · rw [hwv w hww, hev_f] at hwe
                exact Bool.false_ne_true hwe
              · have hAx : wireVal n C (opnd C g ca) e = true :=
                  ((val_and' C hAO g hgl H.gand e ca).1 hge').1
                exact hnot_ib ⟨hAx, hye⟩
            · have hnr' : ¬ OrReaches n C (opnd C T (1 - c)) g := not_both' H T hT hTo c hrc
              obtain ⟨q', hq'e, hq'w⟩ := (pure_val H T hT hTo (1 - c) hnr' e).1 hwc'
              have hpz_q' : PZ C g T q' := (pz_iff C g T q').2 ⟨c, hrc, hq'w⟩
              have hAx : wireVal n C (opnd C g ca) e = true :=
                ((val_and' C hAO g hgl H.gand e ca).1 hge).1
              have hBx : wireVal n C (opnd C g cb) e = true :=
                ((val_and' C hAO g hgl H.gand e cb).1 hge).1
              obtain ⟨yA, hyAe, hyAw⟩ := (opnd_val H ca e).1 hAx
              obtain ⟨yB, hyBe, hyBw⟩ := (opnd_val H cb e).1 hBx
              by_cases hev : e v = true
              · refine ⟨v, hev, fun _ h => ?_, (reach_le C hAO g _ (by omega) hrc).2 _ hgv_true⟩
                subst h
                rw [hem_no_v hev] at hev
                exact Bool.false_ne_true hev
              · exfalso
                have hyAv : yA ≠ v := fun h => hev (h ▸ hyAe)
                have hyBv : yB ≠ v := fun h => hev (h ▸ hyBe)
                have hyAB : yA ≠ yB := fun h => hyAv (hdisjAB yA hyAw (h ▸ hyBw))
                have hsyA : s yA = s v := hsideA yA hyAw
                have hsq' : s q' ≠ s v := (hs v q' (hadj_vpz T hT hTo q' hpz_q')).symm
                have hq'yA : q' ≠ yA := fun h => hsq' (h ▸ hsyA)
                have hq'yB : q' = yB := by
                  rw [he] at hyAe hyBe hq'e
                  simp only [pairInput, decide_eq_true_eq] at hyAe hyBe hq'e
                  rcases hyAe with rfl | rfl <;> rcases hyBe with rfl | rfl
                  · exact absurd rfl hyAB
                  · rcases hq'e with rfl | rfl
                    · exact absurd rfl hq'yA
                    · rfl
                  · rcases hq'e with rfl | rfl
                    · rfl
                    · exact absurd rfl hq'yA
                  · exact absurd rfl hyAB
                subst hq'yB
                have hqm : q' = m := huniqB T hT hTo q' hpz_q' hyBw
                subst hqm
                exact hnot_ib ⟨hAx, hq'e⟩
          by_cases hTk0 : T = k0
          · subst hTk0
            obtain ⟨y0, hy0e, _, hy0w⟩ := hT_vars c0
            obtain ⟨y1, hy1e, hy1m, hy1w⟩ := hT_vars (1 - c0)
            rw [h0g] at hy0w
            have hy0v : y0 = v := (hgv y0).1 hy0w
            subst hy0v
            rw [hip] at hy1w hy1m
            have hvipe : val ip e = true :=
              hlow_vtx ip hipl hip_g hip_ib hip_low e y1 hy1e hy1m hy1w
            have hvge : val g e = true := by
              rw [hg_val e, Bool.and_eq_true]
              exact ⟨hy0e, hvipe⟩
            refine hrise e T hT hTb ?_
            rw [hk0_val e, Bool.or_eq_true]
            exact Or.inr hvge
          · refine hrise e T hT hTb ?_
            have hTib : T ≠ ib := by rintro rfl; rw [hib_or] at hTo; cases hTo
            have eT := hval e T ((hK T).2 hT)
            simp only at eT
            have hA : P.isAnd T = true := by rw [hplain T hTib hTg hTk0, hTo]; rfl
            rw [eT, hA, opv_and]
            obtain ⟨y0, hy0e, hy0m, hy0w⟩ := hT_vars 0
            obtain ⟨y1, hy1e, hy1m, hy1w⟩ := hT_vars 1
            exact ⟨hopW_vtx T hT hTo hTg hTk0 0 e y0 hy0e hy0m hy0w,
              hopW_vtx T hT hTo hTg hTk0 1 e y1 hy1e hy1m hy1w⟩
      obtain ⟨D, hD, hs_le, hf⟩ := fold_computes G P rank val K hcl hval (some (Sum.inr o))
        (fun j hj => by
          have : o = j := by simpa using hj
          rw [← this]
          exact (hK o).2 hol)
        (adj_of_AO G C hAO H.comp (by omega))
        (fun x hx => by
          by_contra hne
          have h := hupper x (by simpa using hne) o hol hob
          have hx' : val o x = true := hx
          rw [h] at hx'
          exact absurd hx' (by decide))
        (fun p q hpq => hlower p q hpq)
      refine ⟨D, hD, lt_of_le_of_lt hs_le ?_, hf⟩
      have hsub : kept P val K ⊆ (Finset.range C.gates.length).erase t := by
        intro i hi
        obtain ⟨hiK, h0, h1⟩ := Finset.mem_filter.1 hi
        refine Finset.mem_erase.2 ⟨?_, hiK⟩
        rintro rfl
        have hdm_true : srcAt (fun _ => true) (fun j => val j fun _ => true) (P.src i dm) = true := by
          fin_cases dm
          · exact h0
          · exact h1
        have ep : P.src i dm = none := by
          simp [P, ht_ib, htg, ht_k0]
        rw [ep] at hdm_true
        exact Bool.false_ne_true hdm_true
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_range.2 htl), Finset.card_range] at h2
      show _ < C.gates.length
      omega

end PEqualNP.Outside.L_meta_4745

theorem PEqualNP.Outside.L_meta_4745 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ) (v m z : Fin n), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → (∀ w : Fin n, PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput w) = true ↔ w = v) → (PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput m) = true ∨ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput m) = true) → z ≠ m → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput m) = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput m) = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true))) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C s g v m z hs h4 hAO hcomp hlift handLow hcone hg hgand hdirty hothers hgv hmB hzm ⟨k0, hk0, hk0o, h01⟩
  let H : PEqualNP.MetaComplexity.LowerPart.OneDirty G C g :=
    ⟨hAO, hcomp, hlift, handLow, hcone, hg, hgand, hdirty, hothers⟩
  rcases hmB with hmB0 | hmB1 <;> rcases h01 with ⟨hr0, hm0, hz0⟩ | ⟨hr0, hm0, hz0⟩
  · exact PEqualNP.Outside.L_meta_4745.main G C s g v m z hs h4 H hgv 0 hmB0 hzm k0 hk0 hk0o 0 hr0 hm0 hz0
  · exact PEqualNP.Outside.L_meta_4745.main G C s g v m z hs h4 H hgv 0 hmB0 hzm k0 hk0 hk0o 1 hr0 hm0 hz0
  · exact PEqualNP.Outside.L_meta_4745.main G C s g v m z hs h4 H hgv 1 hmB1 hzm k0 hk0 hk0o 0 hr0 hm0 hz0
  · exact PEqualNP.Outside.L_meta_4745.main G C s g v m z hs h4 H hgv 1 hmB1 hzm k0 hk0 hk0o 1 hr0 hm0 hz0
