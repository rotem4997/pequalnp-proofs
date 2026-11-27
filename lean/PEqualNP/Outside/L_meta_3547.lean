import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3547_aux

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

-- The three cone lemmas below are adapted from L_meta_1490.
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

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]

/-- Inside the prepended block, cones stay inside the block. -/
theorem cone_low (n L : ℕ) (D : Circuit) (hL : L ≤ D.gates.length)
    (hlow : ∀ j < L, ∀ w ∈ (gateAt D j).inputs, w < n + j) :
    ∀ j, j < L → ∀ i, InCone n D i j → i < L := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj i hi
    obtain ⟨-, k, hk, -, hik⟩ := (inCone_iff n D i j).mp hi
    rcases hik with rfl | hik
    · omega
    · exact ih k hk (by omega) i hik

end PEqualNP.Outside.L_meta_3547_aux

open PEqualNP.Outside.L_meta_3547_aux PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership in
theorem PEqualNP.Outside.L_meta_3547 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → ∀ g15 o15 : ℕ, C.output = n + o15 → g15 < C.gates.length → ¬ Relation.ReflTransGen (fun a13 b13 : ℕ => a13 < b13 ∧ b13 < C.gates.length ∧ ((n + a13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C b13).inputs ∧ ¬ ∃ k13 < m, a13 = u k13 ∧ NR k13 b13) ∨ ∃ k14 < m, NR k14 b13 ∧ rho b13 (n + u k14) = n + G0.length + a13)) g15 o15 → G0.length + g15 ∉ PEqualNP.FactorSubst.liveGates n D := by
  intro n H qH C m u T W z NR P G0 rho D _ _ _ _ _ _ _ _ hG0 hD hrho _ g15 o15 hout hg15 hnot
  classical
  set L := G0.length with hL
  set R := (fun a13 b13 : ℕ => a13 < b13 ∧ b13 < C.gates.length ∧
    ((n + a13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C b13).inputs ∧
      ¬ ∃ k13 < m, a13 = u k13 ∧ NR k13 b13) ∨
      ∃ k14 < m, NR k14 b13 ∧ rho b13 (n + u k14) = n + G0.length + a13)) with hR
  have hDlen : D.gates.length = L + C.gates.length := by rw [hD]; simp [L]
  have hDhigh : ∀ r (hr : r < C.gates.length), gateAt D (L + r) =
      { op := (C.gates[r]'hr).op, inputs := (C.gates[r]'hr).inputs.map (fun i7 => rho r i7) } := by
    intro r hr
    rw [gateAt_eq D _ (by omega)]
    simp only [hD]
    rw [List.getElem_append_right (by simp [L])]
    simp [L, List.getElem_mapIdx]
  have hDlow : ∀ j < L, ∀ w ∈ (gateAt D j).inputs, w < n + j := by
    intro j hj w hw
    rw [gateAt_eq D _ (by omega)] at hw
    simp only [hD] at hw
    rw [List.getElem_append_left (by simpa [L] using hj)] at hw
    have := hG0 j (by simpa [L] using hj) w (by
      rw [List.getD_eq_getElem _ _ (by simpa [L] using hj)]; exact hw)
    exact this
  -- every cone relation between high gates is a path of R
  have key : ∀ j, ∀ i, InCone n D i j → L ≤ i → Relation.ReflTransGen R (i - L) (j - L) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro i hi hiL
      obtain ⟨hjD, k, hk, hkin, hik⟩ := (inCone_iff n D i j).mp hi
      have hjL : L ≤ j := by
        by_contra hjL
        push_neg at hjL
        have := cone_low n L D (by omega) hDlow j hjL i hi
        omega
      have hkL : L ≤ k := by
        rcases hik with rfl | hik
        · exact hiL
        · by_contra hkL
          push_neg at hkL
          have := cone_low n L D (by omega) hDlow k hkL i hik
          omega
      set r := j - L with hr
      have hrC : r < C.gates.length := by omega
      have hjr : j = L + r := by omega
      rw [hjr, hDhigh r hrC] at hkin
      simp only [List.mem_map] at hkin
      obtain ⟨i8, hi8, hrho8⟩ := hkin
      have hstep : R (k - L) r := by
        refine ⟨by omega, hrC, ?_⟩
        by_cases hnar : ∃ k8 < m, NR k8 r ∧ i8 = n + u k8
        · obtain ⟨k8, hk8, hNR, rfl⟩ := hnar
          right
          exact ⟨k8, hk8, hNR, by rw [hrho8]; omega⟩
        · push_neg at hnar
          have hr8 := hrho r hrC i8 (by rw [gateAt_eq C r hrC]; exact hi8)
            (fun k8 hk8 h => hnar k8 hk8 h.1 h.2)
          rw [hrho8] at hr8
          split_ifs at hr8 with hlt
          · omega
          · left
            have hi8eq : i8 = n + (k - L) := by omega
            refine ⟨by rw [gateAt_eq C r hrC, ← hi8eq]; exact hi8, ?_⟩
            rintro ⟨k13, hk13, hku, hNR⟩
            exact hnar k13 hk13 hNR (by rw [hi8eq, hku])
      rcases hik with rfl | hik
      · exact Relation.ReflTransGen.single hstep
      · exact (ih k hk i hik hiL).tail hstep
  intro hlive
  simp only [PEqualNP.FactorSubst.liveGates, Finset.mem_filter, Finset.mem_range] at hlive
  obtain ⟨-, -, hcase⟩ := hlive
  have hDout : D.output - n = L + o15 := by
    rw [hD]; simp only [hout]; rw [if_neg (by omega)]; simp [L]; omega
  rw [hDout] at hcase
  rcases hcase with h | h
  · exact hnot (by rw [show g15 = o15 by omega])
  · have := key _ _ h (by omega)
    simp only [Nat.add_sub_cancel_left] at this
    exact hnot this

