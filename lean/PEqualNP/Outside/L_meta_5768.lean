import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5768

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma live_iff (n : ℕ) (C : Circuit) (j : ℕ) :
    j ∈ PEqualNP.FactorSubst.liveGates n C ↔ j < C.gates.length ∧ n ≤ C.output ∧
      (j = C.output - n ∨ InCone n C j (C.output - n)) := by
  simp [PEqualNP.FactorSubst.liveGates]

lemma cone_down (n : ℕ) (C : Circuit) : ∀ o j k, InCone n C j o → k < j →
    n + k ∈ (gateAt C j).inputs → InCone n C k o := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
    intro j k hj hk hin
    rw [inCone_iff] at hj
    obtain ⟨ho, m, hm, hmin, hjm⟩ := hj
    rw [inCone_iff]
    refine ⟨ho, m, hm, hmin, Or.inr ?_⟩
    rcases hjm with rfl | hjm
    · rw [inCone_iff]
      exact ⟨by omega, k, hk, hin, Or.inl rfl⟩
    · exact ih m hm j k hjm hk hin

lemma cone_reader (n : ℕ) (C : Circuit) : ∀ o j, InCone n C j o →
    ∃ m, m ≤ o ∧ (m = o ∨ InCone n C m o) ∧ n + j ∈ (gateAt C m).inputs := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
    intro j h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨ho, k, hk, hkin, hjk⟩ := h'
    rcases hjk with rfl | hjk
    · exact ⟨o, le_rfl, Or.inl rfl, hkin⟩
    · obtain ⟨m, hmk, hm, hmin⟩ := ih k hk j hjk
      refine ⟨m, by omega, Or.inr ?_, hmin⟩
      rw [inCone_iff]
      exact ⟨ho, k, hk, hkin, hm⟩

noncomputable def S (n : ℕ) (C : Circuit) : List ℕ :=
  C.output :: List.flatMap (fun m => (gateAt C m).inputs)
    (PEqualNP.FactorSubst.liveGates n C).toList

lemma live_down (n : ℕ) (C : Circuit) (R : ReadsBack n C) (j : ℕ)
    (hj : j ∈ PEqualNP.FactorSubst.liveGates n C) (k : ℕ) (hk : n + k ∈ (gateAt C j).inputs) :
    k ∈ PEqualNP.FactorSubst.liveGates n C := by
  rw [live_iff] at hj ⊢
  obtain ⟨hjl, hno, hor⟩ := hj
  have hlt := R j hjl (n + k) hk
  refine ⟨by omega, hno, Or.inr ?_⟩
  rcases hor with h | h
  · rw [inCone_iff]
    refine ⟨by omega, k, by omega, ?_, Or.inl rfl⟩
    rw [← h]; exact hk
  · exact cone_down n C _ j k h (by omega) hk

lemma live_mem (n : ℕ) (C : Circuit) (j : ℕ) (hj : j ∈ PEqualNP.FactorSubst.liveGates n C) :
    n + j ∈ S n C := by
  have hj' := hj
  rw [live_iff] at hj'
  obtain ⟨hjl, hno, hor⟩ := hj'
  rcases hor with h | h
  · exact List.mem_cons.2 (Or.inl (by omega))
  · obtain ⟨m, hmo, hm, hmin⟩ := cone_reader n C _ j h
    have hol := ((inCone_iff n C j _).1 h).1
    have hml : m ∈ PEqualNP.FactorSubst.liveGates n C := by
      rw [live_iff]; exact ⟨by omega, hno, hm⟩
    exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨m, Finset.mem_toList.2 hml, hmin⟩)

lemma agree (n : ℕ) (C : Circuit) (R : ReadsBack n C) (x y : List Bool) (hx : x.length = n)
    (hy : y.length = n) (hxy : ∀ i < n, i ∈ S n C → x.getD i false = y.getD i false) :
    ∀ j, j ∈ PEqualNP.FactorSubst.liveGates n C → val C x (n + j) = val C y (n + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hjl := ((live_iff n C j).1 hj).1
    rw [val_gate hx hjl, val_gate hy hjl]
    congr 1
    apply List.map_congr_left
    intro i hi
    by_cases h : i < n + j
    · rw [if_pos h, if_pos h]
      by_cases hin : i < n
      · rw [val_input hx hin, val_input hy hin]
        exact hxy i hin (List.mem_cons_of_mem _
          (List.mem_flatMap.2 ⟨j, Finset.mem_toList.2 hj, hi⟩))
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        exact ih k (by omega) (live_down n C R j hj k hi)
    · rw [if_neg h, if_neg h]

lemma out_agree (n : ℕ) (C : Circuit) (R : ReadsBack n C) (x y : List Bool) (hx : x.length = n)
    (hy : y.length = n) (hxy : ∀ i < n, i ∈ S n C → x.getD i false = y.getD i false) :
    val C x C.output = val C y C.output := by
  by_cases h1 : C.output < n
  · rw [val_input hx h1, val_input hy h1]
    exact hxy _ h1 (by simp [S])
  by_cases h2 : n + C.gates.length ≤ C.output
  · rw [val_ge hx h2, val_ge hy h2]
  have hl : C.output - n ∈ PEqualNP.FactorSubst.liveGates n C := by
    rw [live_iff]; exact ⟨by omega, by omega, Or.inl rfl⟩
  have := agree n C R x y hx hy hxy _ hl
  rwa [show n + (C.output - n) = C.output by omega] at this

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

lemma point_mem (x1 x2 : ℕ) (E : Finset (Fin x1 × Fin x2)) (C : Circuit)
    (R : ReadsBack (x1 + x2) C)
    (hf : ∀ (x6 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) C x6 =
      decide (∃ (x7 : Fin x1) (x8 : Fin x2), (x7, x8) ∈ E ∧ x6 (Fin.castAdd x2 x7) = true ∧
        x6 (Fin.natAdd x1 x8) = true))
    (p : Fin x1) (l : Fin x2) (hpl : (p, l) ∈ E) : (p : ℕ) ∈ S (x1 + x2) C := by
  by_contra hp
  have hX := hf (fun w => decide (w = Fin.castAdd x2 p ∨ w = Fin.natAdd x1 l))
  have hY := hf (fun w => decide (w = Fin.natAdd x1 l))
  have e1 : decide (∃ (x7 : Fin x1) (x8 : Fin x2), (x7, x8) ∈ E ∧
      decide (Fin.castAdd x2 x7 = Fin.castAdd x2 p ∨ Fin.castAdd x2 x7 = Fin.natAdd x1 l) = true ∧
      decide (Fin.natAdd x1 x8 = Fin.castAdd x2 p ∨ Fin.natAdd x1 x8 = Fin.natAdd x1 l) = true)
        = true := by
    apply decide_eq_true
    exact ⟨p, l, hpl, by simp, by simp⟩
  have e2 : decide (∃ (x7 : Fin x1) (x8 : Fin x2), (x7, x8) ∈ E ∧
      decide (Fin.castAdd x2 x7 = Fin.natAdd x1 l) = true ∧
      decide (Fin.natAdd x1 x8 = Fin.natAdd x1 l) = true) = false := by
    apply decide_eq_false
    rintro ⟨a, b, _, ha, _⟩
    rw [decide_eq_true_eq] at ha
    have := congrArg Fin.val ha
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
    have := a.isLt
    omega
  rw [e1] at hX
  rw [e2] at hY
  have hag := out_agree (x1 + x2) C R
    (List.ofFn (fun w => decide (w = Fin.castAdd x2 p ∨ w = Fin.natAdd x1 l)))
    (List.ofFn (fun w => decide (w = Fin.natAdd x1 l))) (by simp) (by simp) (by
      intro i hi hiS
      rw [ofFn_getD _ i hi, ofFn_getD _ i hi]
      have hne : (⟨i, hi⟩ : Fin (x1 + x2)) ≠ Fin.castAdd x2 p := by
        intro h
        apply hp
        have := congrArg Fin.val h
        simp only [Fin.coe_castAdd] at this
        rw [← this]
        exact hiS
      simp [hne])
  have c1 : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C
      (fun w => decide (w = Fin.castAdd x2 p ∨ w = Fin.natAdd x1 l)) =
      val C (List.ofFn (fun w => decide (w = Fin.castAdd x2 p ∨ w = Fin.natAdd x1 l))) C.output :=
    rfl
  have c2 : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C
      (fun w => decide (w = Fin.natAdd x1 l)) =
      val C (List.ofFn (fun w => decide (w = Fin.natAdd x1 l))) C.output := rfl
  rw [c1] at hX
  rw [c2] at hY
  rw [hX, hY] at hag
  cases hag

lemma line_mem (x1 x2 : ℕ) (E : Finset (Fin x1 × Fin x2)) (C : Circuit)
    (R : ReadsBack (x1 + x2) C)
    (hf : ∀ (x6 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) C x6 =
      decide (∃ (x7 : Fin x1) (x8 : Fin x2), (x7, x8) ∈ E ∧ x6 (Fin.castAdd x2 x7) = true ∧
        x6 (Fin.natAdd x1 x8) = true))
    (p : Fin x1) (l : Fin x2) (hpl : (p, l) ∈ E) : x1 + (l : ℕ) ∈ S (x1 + x2) C := by
  by_contra hp
  have hX := hf (fun w => decide (w = Fin.castAdd x2 p ∨ w = Fin.natAdd x1 l))
  have hY := hf (fun w => decide (w = Fin.castAdd x2 p))
  have e1 : decide (∃ (x7 : Fin x1) (x8 : Fin x2), (x7, x8) ∈ E ∧
      decide (Fin.castAdd x2 x7 = Fin.castAdd x2 p ∨ Fin.castAdd x2 x7 = Fin.natAdd x1 l) = true ∧
      decide (Fin.natAdd x1 x8 = Fin.castAdd x2 p ∨ Fin.natAdd x1 x8 = Fin.natAdd x1 l) = true)
        = true := by
    apply decide_eq_true
    exact ⟨p, l, hpl, by simp, by simp⟩
  have e2 : decide (∃ (x7 : Fin x1) (x8 : Fin x2), (x7, x8) ∈ E ∧
      decide (Fin.castAdd x2 x7 = Fin.castAdd x2 p) = true ∧
      decide (Fin.natAdd x1 x8 = Fin.castAdd x2 p) = true) = false := by
    apply decide_eq_false
    rintro ⟨a, b, _, _, hb⟩
    rw [decide_eq_true_eq] at hb
    have := congrArg Fin.val hb
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
    have := p.isLt
    omega
  rw [e1] at hX
  rw [e2] at hY
  have hag := out_agree (x1 + x2) C R
    (List.ofFn (fun w => decide (w = Fin.castAdd x2 p ∨ w = Fin.natAdd x1 l)))
    (List.ofFn (fun w => decide (w = Fin.castAdd x2 p))) (by simp) (by simp) (by
      intro i hi hiS
      rw [ofFn_getD _ i hi, ofFn_getD _ i hi]
      have hne : (⟨i, hi⟩ : Fin (x1 + x2)) ≠ Fin.natAdd x1 l := by
        intro h
        apply hp
        have := congrArg Fin.val h
        simp only [Fin.coe_natAdd] at this
        rw [← this]
        exact hiS
      simp [hne])
  have c1 : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C
      (fun w => decide (w = Fin.castAdd x2 p ∨ w = Fin.natAdd x1 l)) =
      val C (List.ofFn (fun w => decide (w = Fin.castAdd x2 p ∨ w = Fin.natAdd x1 l))) C.output :=
    rfl
  have c2 : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C
      (fun w => decide (w = Fin.castAdd x2 p)) =
      val C (List.ofFn (fun w => decide (w = Fin.castAdd x2 p))) C.output := rfl
  rw [c1] at hX
  rw [c2] at hY
  rw [hX, hY] at hag
  cases hag

theorem main (x1 x2 : ℕ) (E : Finset (Fin x1 × Fin x2)) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 (x1 + x2) C)
    (hf : ∀ (x6 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) C x6 =
      decide (∃ (x7 : Fin x1) (x8 : Fin x2), (x7, x8) ∈ E ∧ x6 (Fin.castAdd x2 x7) = true ∧
        x6 (Fin.natAdd x1 x8) = true)) :
    (E.image Prod.fst).card + (E.image Prod.snd).card +
      (PEqualNP.FactorSubst.liveGates (x1 + x2) C).card ≤ (S (x1 + x2) C).toFinset.card := by
  have R : ReadsBack (x1 + x2) C := hC.2.1
  set A := (E.image Prod.fst).image (fun p : Fin x1 => (p : ℕ)) with hA
  set B := (E.image Prod.snd).image (fun l : Fin x2 => x1 + (l : ℕ)) with hB
  set G := (PEqualNP.FactorSubst.liveGates (x1 + x2) C).image (fun j => x1 + x2 + j) with hG
  have cA : A.card = (E.image Prod.fst).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have cB : B.card = (E.image Prod.snd).card := by
    apply Finset.card_image_of_injective
    intro a b h
    apply Fin.ext
    simp only at h
    omega
  have cG : G.card = (PEqualNP.FactorSubst.liveGates (x1 + x2) C).card := by
    apply Finset.card_image_of_injective
    intro a b h
    simp only at h
    omega
  have dAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [hA, Finset.mem_image] at ha
    rw [hB, Finset.mem_image] at hb
    obtain ⟨p, _, rfl⟩ := ha
    obtain ⟨l, _, h⟩ := hb
    have := p.isLt
    omega
  have dABG : Disjoint (A ∪ B) G := by
    rw [Finset.disjoint_left]
    intro a ha hg
    rw [hG, Finset.mem_image] at hg
    obtain ⟨j, _, rfl⟩ := hg
    rcases Finset.mem_union.1 ha with ha | ha
    · rw [hA, Finset.mem_image] at ha
      obtain ⟨p, _, h⟩ := ha
      have := p.isLt
      omega
    · rw [hB, Finset.mem_image] at ha
      obtain ⟨l, _, h⟩ := ha
      have := l.isLt
      omega
  have hsub : A ∪ B ∪ G ⊆ (S (x1 + x2) C).toFinset := by
    intro a ha
    rw [List.mem_toFinset]
    rcases Finset.mem_union.1 ha with ha | ha
    · rcases Finset.mem_union.1 ha with ha | ha
      · rw [hA, Finset.mem_image] at ha
        obtain ⟨p, hp, rfl⟩ := ha
        rw [Finset.mem_image] at hp
        obtain ⟨⟨p', l⟩, hpl, rfl⟩ := hp
        exact point_mem x1 x2 E C R hf p' l hpl
      · rw [hB, Finset.mem_image] at ha
        obtain ⟨l, hl, rfl⟩ := ha
        rw [Finset.mem_image] at hl
        obtain ⟨⟨p, l'⟩, hpl, rfl⟩ := hl
        exact line_mem x1 x2 E C R hf p l' hpl
    · rw [hG, Finset.mem_image] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      exact live_mem _ C j hj
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint dABG, Finset.card_union_of_disjoint dAB] at hc
  omega

end PEqualNP.Outside.L_meta_5768

theorem PEqualNP.Outside.L_meta_5768 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →     (∀ (x6 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x6 = Decidable.decide (∃ (x7 : Fin x1) (x8 : Fin x2), (x7, x8) ∈ x3 ∧ x6 (Fin.castAdd x2 x7) = Bool.true ∧ x6 (Fin.natAdd x1 x8) = Bool.true)) →       have x7 : Finset ℕ := PEqualNP.FactorSubst.liveGates (x1 + x2) x4;       have x8 : List ℕ := x4.output :: List.flatMap (fun (x8 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x8).inputs) x7.toList;       (Finset.image Prod.fst x3).card + (Finset.image Prod.snd x3).card + x7.card ≤ x8.toFinset.card := by
  intro x1 x2 x3 x4 h1 h2
  exact PEqualNP.Outside.L_meta_5768.main x1 x2 x3 x4 h1 h2
