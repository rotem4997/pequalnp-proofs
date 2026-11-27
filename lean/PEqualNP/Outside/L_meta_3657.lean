import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

namespace PEqualNP.Outside.L_meta_3657

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (step x g) := rfl

lemma run_append (l1 l2 : List Gate) (x : List Bool) :
    run (l1 ++ l2) x = run l2 (run l1 x) := by
  simp [run, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih, step_length]; simp; omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

lemma step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma run_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih _ (by rw [step_length]; omega), step_getD _ _ _ hi]

lemma run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) x).getD i false) := by
  have hsplit : run gs x = run (gs.drop (j + 1)) (step (run (gs.take j) x) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
    rw [run_append, run_cons]
  have hl : (run (gs.take j) x).length = x.length + j := by
    rw [run_length, List.length_take]; omega
  rw [hsplit, run_getD _ _ _ (by rw [step_length]; omega), ← hl, step_getD_last]

lemma run_prefix_getD (gs : List Gate) (x : List Bool) (j i : ℕ) (hj : j ≤ gs.length)
    (hi : i < x.length + j) :
    (run (gs.take j) x).getD i false = (run gs x).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  exact (run_getD _ _ _ (by rw [run_length, List.length_take]; omega)).symm

lemma gate_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hr : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run gs x).getD i false) := by
  rw [run_gate gs x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact run_prefix_getD gs x j i hj.le (hr i hi)

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hj

lemma gateAt_out (C : Circuit) (j : ℕ) (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  exact List.getD_eq_default _ _ hj

lemma cval_gate (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (hRB : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (run C.gates x).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  rw [gateAt_eq C j hj]
  have := gate_val C.gates x j hj (by
    intro i hi
    have := hRB j hj i (by rw [gateAt_eq C j hj]; exact hi)
    omega)
  rw [hx] at this
  exact this

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

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩


lemma gv (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    gateVal n C j x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires (List.ofFn x)).getD i false) :=
  cval_gate n C (List.ofFn x) (by simp) hRB j hj

end PEqualNP.Outside.L_meta_3657

theorem PEqualNP.Outside.L_meta_3657 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.Core.IsLiftFixedPoint G C →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) →
  (∀ k < C.gates.length, ∃ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C k x = true) →
  ∀ h < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op = PEqualNP.CircuitLowerBounds.GateOp.and →
    (PEqualNP.TopForm.BelowF G C h ↔ ∀ k < C.gates.length, PEqualNP.EdgeOwnership.InCone n C h k → (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or) := by
  intro n G _ C hAO hfun hcone hlift hnoand hnz h hh hand
  obtain ⟨hAOonly, hRB, hTwo⟩ := hAO
  constructor
  · intro hbelow
    have key : ∀ k, InCone n C h k → (gateAt C k).op = GateOp.or ∧ PEqualNP.TopForm.BelowF G C k := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        have hk' := hk
        rw [PEqualNP.Outside.L_meta_3657.inCone_iff] at hk'
        obtain ⟨hkl, j, hjk, hjin, hj⟩ := hk'
        have hjb : PEqualNP.TopForm.BelowF G C j := by
          rcases hj with rfl | hj
          · exact hbelow
          · exact (ih j hjk hj).2
        have hjl : j < C.gates.length := by
          rcases hj with rfl | hj
          · exact hh
          · exact (PEqualNP.Outside.L_meta_3657.inCone_lt n C h j hj).2
        have hmem : gateAt C k ∈ C.gates := by
          rw [PEqualNP.Outside.L_meta_3657.gateAt_eq C k hkl]
          exact List.getElem_mem _
        have hor : (gateAt C k).op = GateOp.or := by
          rcases hAOonly (gateAt C k) hmem with h1 | h1
          · exfalso
            exact hnoand k hkl h1 (n + j) hjin (fun x hx => hjb x hx)
          · exact h1
        refine ⟨hor, ?_⟩
        by_contra hnb
        have hlen2 : (gateAt C k).inputs.length = 2 := hTwo _ hmem
        obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen2
        obtain ⟨b, hb⟩ : ∃ b : Fin 2, PEqualNP.TopForm.opnd C k b = n + j := by
          rw [hpq] at hjin
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjin
          rcases hjin with h1 | h1
          · exact ⟨0, by simp [PEqualNP.TopForm.opnd, hpq, h1]⟩
          · exact ⟨1, by simp [PEqualNP.TopForm.opnd, hpq, h1]⟩
        obtain ⟨x0, hx0⟩ := hnz j hjl
        exact hlift ⟨k, hkl, b, hcone k hkl, hor, hnb, by
          rw [hb]
          exact ⟨fun x hx => hjb x hx, x0, hx0⟩⟩
    intro k hk hin
    exact (key k hin).1
  · intro hall x hx
    have up : ∀ k, (k = h ∨ InCone n C h k) → PEqualNP.EdgeOwnership.gateVal n C k x = true := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        rintro (rfl | hk)
        · exact hx
        · have hk' := hk
          rw [PEqualNP.Outside.L_meta_3657.inCone_iff] at hk'
          obtain ⟨hkl, j, hjk, hjin, hj⟩ := hk'
          have hjv := ih j hjk (hj.imp_left Eq.symm)
          have hor := hall k hkl hk
          rw [PEqualNP.Outside.L_meta_3657.gv n C hRB k hkl x, hor]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          exact ⟨n + j, hjin, hjv⟩
    have hF := congrFun hfun x
    rw [← hF]
    change (C.wires (List.ofFn x)).getD C.output false = true
    obtain ⟨_, ho⟩ := hcone h hh
    rcases ho with ho | ⟨hno, ho⟩
    · rw [ho]
      exact hx
    · have := up (C.output - n) (Or.inr ho)
      rw [show C.output = n + (C.output - n) by omega]
      exact this
