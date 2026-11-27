import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6718

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.SplitCount PEqualNP.CleanedNonEdge PEqualNP.TopForm

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

theorem fold_ext (gs : List Gate) : ∀ w : List Bool, ∃ T : List Bool,
    gs.foldl stepW w = w ++ T := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨T, hT⟩ := ih (stepW w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ T, ?_⟩
    rw [List.foldl_cons, hT]
    simp [stepW]

theorem fold_len (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

theorem getD_app_left (w T : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ T).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hi]

theorem wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    wireVal n C i.val x = x i := by
  unfold wireVal
  rw [wires_eq]
  obtain ⟨T, hT⟩ := fold_ext C.gates (List.ofFn x)
  rw [hT, getD_app_left _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem gateVal_step (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    gateVal n C j x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wireVal n C i x) := by
  have hg : gateAt C j = C.gates[j] := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, hj]
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp
  have hW0 : ((C.gates.take j).foldl stepW (List.ofFn x)).length = n + j := by
    rw [fold_len]; simp; omega
  obtain ⟨T, hT⟩ := fold_ext (C.gates.drop (j + 1))
    (stepW ((C.gates.take j).foldl stepW (List.ofFn x)) C.gates[j])
  have hall : C.wires (List.ofFn x) =
      ((C.gates.take j).foldl stepW (List.ofFn x) ++
        [C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
          ((C.gates.take j).foldl stepW (List.ofFn x)).getD i false)]) ++ T := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons, hT]
    rfl
  have hread : ∀ i, i < n + j → wireVal n C i x =
      ((C.gates.take j).foldl stepW (List.ofFn x)).getD i false := by
    intro i hi
    unfold wireVal
    rw [hall, List.append_assoc, getD_app_left _ _ _ (by omega)]
  unfold gateVal
  rw [hg] at hb ⊢
  have hval : (C.wires (List.ofFn x)).getD (n + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
          ((C.gates.take j).foldl stepW (List.ofFn x)).getD i false) := by
    rw [hall]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by omega)]
    simp [hW0]
  rw [hval]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hread i (hb i hi)).symm

theorem gate_cases (n : ℕ) (C : Circuit) (h : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    opnd C j 0 ∈ (gateAt C j).inputs ∧ opnd C j 1 ∈ (gateAt C j).inputs ∧
    (((gateAt C j).op = GateOp.and ∧ ∀ x : Fin n → Bool, gateVal n C j x =
        (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x)) ∨
     ((gateAt C j).op = GateOp.or ∧ ∀ x : Fin n → Bool, gateVal n C j x =
        (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x))) := by
  obtain ⟨hAO, hRB, hTwo⟩ := h
  have hg : gateAt C j = C.gates[j] := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, hj]
  have hmem : gateAt C j ∈ C.gates := by rw [hg]; exact List.getElem_mem hj
  have h2 := hTwo _ hmem
  obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt C j).inputs = [a, b] := by
    match hI : (gateAt C j).inputs, h2 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have e0 : opnd C j 0 = a := by simp [opnd, hab]
  have e1 : opnd C j 1 = b := by simp [opnd, hab]
  refine ⟨by rw [e0, hab]; simp, by rw [e1, hab]; simp, ?_⟩
  rcases hAO _ hmem with ho | ho
  · left
    refine ⟨ho, fun x => ?_⟩
    rw [gateVal_step n C x j hj (hRB j hj), ho, hab, e0, e1]
    simp [GateOp.eval]
  · right
    refine ⟨ho, fun x => ?_⟩
    rw [gateVal_step n C x j hj (hRB j hj), ho, hab, e0, e1]
    simp [GateOp.eval]

-- The cone lemmas below (`cones_len`, `cones_char`, `inCone_iff`) are taken from the checked
-- file `L_meta_5332.lean` of this repository (Apache-2.0).
theorem cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

theorem cones_char (n : ℕ) (gs : List Gate) :
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

theorem inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
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

theorem pair_self (n : ℕ) (u : Fin n) (w : Fin n) : pairInput u u w = decide (w = u) := by
  simp [pairInput]

theorem wire_is_gate (n : ℕ) (C : Circuit) (u v : Fin n) (w : ℕ)
    (h1 : wireVal n C w (pairInput u v) = true)
    (h2 : wireVal n C w (pairInput u u) = false)
    (h3 : wireVal n C w (pairInput v v) = false) : n ≤ w := by
  by_contra hlt
  have hw : w < n := by omega
  have e1 := wireVal_input n C (pairInput u v) ⟨w, hw⟩
  have e2 := wireVal_input n C (pairInput u u) ⟨w, hw⟩
  have e3 := wireVal_input n C (pairInput v v) ⟨w, hw⟩
  simp only at e1 e2 e3
  rw [h1] at e1
  rw [h2] at e2
  rw [h3] at e3
  simp [pairInput] at e1 e2 e3
  rcases e1 with e | e
  · exact e2 e
  · exact e3 e

theorem trace_main (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (u v : Fin n) : ∀ j : ℕ,
    j < C.gates.length → gateVal n C j (pairInput u v) = true →
    gateVal n C j (pairInput u u) = false → gateVal n C j (pairInput v v) = false →
    ∃ k < C.gates.length, InConeOrSelf n C k j ∧ (gateAt C k).op = GateOp.and ∧
      ∃ b : Fin 2, wireVal n C (opnd C k b) (pairInput u u) = true ∧
        wireVal n C (opnd C k (1 - b)) (pairInput v v) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj h1 h2 h3
    -- descending into an operand
    have down : ∀ w ∈ (gateAt C j).inputs, wireVal n C w (pairInput u v) = true →
        wireVal n C w (pairInput u u) = false → wireVal n C w (pairInput v v) = false →
        ∃ k < C.gates.length, InConeOrSelf n C k j ∧ (gateAt C k).op = GateOp.and ∧
          ∃ b : Fin 2, wireVal n C (opnd C k b) (pairInput u u) = true ∧
            wireVal n C (opnd C k (1 - b)) (pairInput v v) = true := by
      intro w hw a1 a2 a3
      have hn := wire_is_gate n C u v w a1 a2 a3
      have hlt : w < n + j := hC.2.1 j hj w hw
      have hwe : n + (w - n) = w := by omega
      have hjl : w - n < C.gates.length := by omega
      rw [← hwe] at a1 a2 a3 hw
      obtain ⟨k, hk, hcone, hop, hb⟩ := ih (w - n) (by omega) hjl a1 a2 a3
      refine ⟨k, hk, Or.inr ?_, hop, hb⟩
      rw [inCone_iff]
      exact ⟨hj, w - n, by omega, hw, hcone⟩
    obtain ⟨m0, m1, hcase⟩ := gate_cases n C hC j hj
    rcases hcase with ⟨hop, hv⟩ | ⟨hop, hv⟩
    · rw [hv] at h1 h2 h3
      rw [Bool.and_eq_true] at h1
      obtain ⟨p1, q1⟩ := h1
      by_cases c0 : wireVal n C (opnd C j 0) (pairInput u u) = false ∧
          wireVal n C (opnd C j 0) (pairInput v v) = false
      · exact down _ m0 p1 c0.1 c0.2
      by_cases c1 : wireVal n C (opnd C j 1) (pairInput u u) = false ∧
          wireVal n C (opnd C j 1) (pairInput v v) = false
      · exact down _ m1 q1 c1.1 c1.2
      refine ⟨j, hj, Or.inl rfl, hop, ?_⟩
      have e10 : (1 : Fin 2) - 0 = 1 := by decide
      have e11 : (1 : Fin 2) - 1 = 0 := by decide
      cases a0 : wireVal n C (opnd C j 0) (pairInput u u) with
      | true =>
        have b0 : wireVal n C (opnd C j 1) (pairInput u u) = false := by
          rw [a0] at h2; simpa using h2
        have b1 : wireVal n C (opnd C j 1) (pairInput v v) = true := by
          cases hb1 : wireVal n C (opnd C j 1) (pairInput v v) with
          | true => rfl
          | false => exact absurd ⟨b0, hb1⟩ c1
        refine ⟨0, a0, ?_⟩
        rw [e10]
        exact b1
      | false =>
        have a1 : wireVal n C (opnd C j 0) (pairInput v v) = true := by
          cases ha1 : wireVal n C (opnd C j 0) (pairInput v v) with
          | true => rfl
          | false => exact absurd ⟨a0, ha1⟩ c0
        have b1 : wireVal n C (opnd C j 1) (pairInput v v) = false := by
          rw [a1] at h3; simpa using h3
        have b0 : wireVal n C (opnd C j 1) (pairInput u u) = true := by
          cases hb0 : wireVal n C (opnd C j 1) (pairInput u u) with
          | true => rfl
          | false => exact absurd ⟨hb0, b1⟩ c1
        refine ⟨1, b0, ?_⟩
        rw [e11]
        exact a1
    · rw [hv] at h1 h2 h3
      rw [Bool.or_eq_false_iff] at h2 h3
      rw [Bool.or_eq_true] at h1
      rcases h1 with p | p
      · exact down _ m0 p h2.1 h3.1
      · exact down _ m1 p h2.2 h3.2

theorem trace : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → ∀ (u v : Fin n) (j : ℕ),
      j < C.gates.length → gateVal n C j (pairInput u v) = true →
      gateVal n C j (pairInput u u) = false → gateVal n C j (pairInput v v) = false →
      ∃ k < C.gates.length, InConeOrSelf n C k j ∧ (gateAt C k).op = GateOp.and ∧
        ∃ b : Fin 2, wireVal n C (opnd C k b) (pairInput u u) = true ∧
          wireVal n C (opnd C k (1 - b)) (pairInput v v) = true :=
  fun n C hC u v j => trace_main n C hC u v j

end PEqualNP.Outside.L_meta_6718

theorem PEqualNP.Outside.L_meta_6718 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → ∀ (x4 x5 : Fin x1), ∀ x6 < x2.gates.length, PEqualNP.EdgeOwnership.gateVal x1 x2 x6 (PEqualNP.EdgeOwnership.pairInput x4 x5) = Bool.true → PEqualNP.EdgeOwnership.gateVal x1 x2 x6 (PEqualNP.EdgeOwnership.pairInput x4 x4) = Bool.false → PEqualNP.EdgeOwnership.gateVal x1 x2 x6 (PEqualNP.EdgeOwnership.pairInput x5 x5) = Bool.false → ∃ x11 < x2.gates.length, PEqualNP.SplitCount.InConeOrSelf x1 x2 x11 x6 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x12 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal x1 x2 (PEqualNP.TopForm.opnd x2 x11 x12) (PEqualNP.EdgeOwnership.pairInput x4 x4) = Bool.true ∧ PEqualNP.CleanedNonEdge.wireVal x1 x2 (PEqualNP.TopForm.opnd x2 x11 ((1 : Fin (2 : ℕ)) - x12)) (PEqualNP.EdgeOwnership.pairInput x5 x5) = Bool.true :=
  PEqualNP.Outside.L_meta_6718.trace
