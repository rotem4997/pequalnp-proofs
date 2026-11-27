import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- In the matching case, both ends of each edge are essential inputs.
-- The backward dependency argument follows L-meta-2074.

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_18397_271
    (leftBranching : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∃ e ∈ x3, ∃ e' ∈ x3, e ≠ e' ∧ e.1 = e'.1) → (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (∃ (x8 : Fin x4.gates.length), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ))
    (rightBranching : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ e ∈ x3, ∀ e' ∈ x3, e.1 = e'.1 → e = e') → (∃ e ∈ x3, ∃ e' ∈ x3, e ≠ e' ∧ e.2 = e'.2) → (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (∃ (x8 : Fin x4.gates.length), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (∃ (x8 : Fin x4.gates.length), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ) := by
  intro n m E C hFour hAO hCompute hAnd
  classical
  by_cases hL : ∀ e ∈ E, ∀ f ∈ E, e.1 = f.1 → e = f
  · by_cases hR : ∀ e ∈ E, ∀ f ∈ E, e.2 = f.2 → e = f
    ·
      let stepWire (w : List Bool) (g : Gate) : List Bool :=
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

      have wires_eq_foldl (C : Circuit) (x : List Bool) :
          C.wires x = C.gates.foldl stepWire x := rfl

      have foldl_length (gs : List Gate) (w : List Bool) :
          (gs.foldl stepWire w).length = w.length + gs.length := by
        induction gs generalizing w with
        | nil => simp
        | cons g gs ih =>
          rw [List.foldl_cons, ih]
          simp [stepWire]
          omega

      have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
          (gs.foldl stepWire w).getD i false = w.getD i false := by
        induction gs generalizing w with
        | nil => rfl
        | cons g gs ih =>
          simp only [List.foldl_cons]
          have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
          rw [ih (stepWire w g) hlt]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

      have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

      have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
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
            · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
              simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
            · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
          | succ j =>
            have hj' : j < gs.length := by simpa using hj
            have key := ih (stepWire w g) j hj'
            have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
            rw [hl] at key
            have e : w.length + (j + 1) = w.length + 1 + j := by omega
            simp only [List.getElem_cons_succ]
            rw [e]
            exact key

      let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

      have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
        change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
        simp [List.getD_eq_getElem?_getD, hj]

      have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
        rw [gateAt_eq hj]; exact List.getElem_mem hj

      have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
          val C x u = x.getD u false := by
        unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

      have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
          (hu : n + C.gates.length ≤ u) : val C x u = false := by
        unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

      have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
          (hj : j < C.gates.length) :
          val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
            if i < n + j then val C x i else false) := by
        subst hx
        rw [gateAt_eq hj]
        exact foldl_getD_gate C.gates x j hj

      have dep (n : ℕ) (C : Circuit) (hR : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2) :
          ∀ k, k ≤ C.gates.length → ∀ W : Finset ℕ, (∀ w ∈ W, w < n + k) →
            ∃ T : Finset (Fin n), T.card ≤ k + W.card ∧
              ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
                ∀ w ∈ W, val C (List.ofFn x) w = val C (List.ofFn y) w := by
        intro k
        induction k with
        | zero =>
          intro _ W hW
          refine ⟨Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ W), ?_, ?_⟩
          · rw [Nat.zero_add, ← Finset.card_image_of_injective _ Fin.val_injective]
            apply Finset.card_le_card
            intro a ha
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
            exact (Finset.mem_filter.1 hi).2
          · intro x y h w hw
            have hw' : w < n := by simpa using hW w hw
            have e : ∀ z : Fin n → Bool, (List.ofFn z).getD w false = z ⟨w, hw'⟩ := by
              intro z; simp [List.getD_eq_getElem?_getD, hw']
            rw [val_input (by simp) hw', val_input (by simp) hw', e, e]
            exact h ⟨w, hw'⟩ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)
        | succ k ih =>
          intro hk W hW
          by_cases hmem : n + k ∈ W
          · obtain ⟨W2, hW2⟩ : ∃ W2 : Finset ℕ, W2 = W.erase (n + k) ∪
                ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset := ⟨_, rfl⟩
            have hlt2 : ∀ w ∈ W2, w < n + k := by
              intro w hw
              rw [hW2] at hw
              rcases Finset.mem_union.1 hw with h | h
              · have h1 := hW w (Finset.mem_of_mem_erase h)
                have h2 := Finset.ne_of_mem_erase h
                omega
              · simp at h; exact h.2
            have hs1 : ∀ w ∈ W, w ≠ n + k → w ∈ W2 := by
              intro w hw hne
              rw [hW2]
              exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
            have hs2 : ∀ i ∈ (gateAt C k).inputs, i < n + k → i ∈ W2 := by
              intro i hi hlt
              rw [hW2]
              exact Finset.mem_union_right _ (by simp [hi, hlt])
            have hc : W2.card + 1 ≤ W.card + 2 := by
              rw [hW2]
              have h1 := Finset.card_union_le (W.erase (n + k))
                ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset
              have h2 : ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset.card ≤ 2 :=
                (List.toFinset_card_le _).trans
                  ((List.length_filter_le _ _).trans (hR k (by omega)).le)
              have h3 := Finset.card_erase_of_mem hmem
              have h4 : 0 < W.card := Finset.card_pos.2 ⟨_, hmem⟩
              omega
            obtain ⟨T, hT, hdep⟩ := ih (by omega) W2 hlt2
            refine ⟨T, by omega, ?_⟩
            intro x y h w hw
            by_cases hwk : w = n + k
            · rw [hwk, val_gate (by simp) (by omega), val_gate (by simp) (by omega)]
              congr 1
              apply List.map_congr_left
              intro i hi
              by_cases hlt : i < n + k
              · simp only [ite_eq_left hlt]
                exact hdep x y h i (hs2 i hi hlt)
              · simp only [ite_eq_right hlt]
            · exact hdep x y h w (hs1 w hw hwk)
          · obtain ⟨T, hT, hdep⟩ := ih (by omega) W (by
              intro w hw
              have h1 := hW w hw
              have h2 : w ≠ n + k := fun h => hmem (h ▸ hw)
              omega)
            exact ⟨T, by omega, hdep⟩

      obtain ⟨T, hT, hdep⟩ : ∃ T : Finset (Fin (n + m)), T.card ≤ C.size + 1 ∧
          ∀ x y : Fin (n + m) → Bool, (∀ i ∈ T, x i = y i) →
            circuitFun (n + m) C x = circuitFun (n + m) C y := by
        by_cases ho : C.output < n + m + C.gates.length
        · obtain ⟨T, hT, hsupport⟩ := dep (n + m) C
            (fun j hj => hAO.2.2 _ (gateAt_mem hj)) C.gates.length le_rfl
            {C.output} (by simpa using ho)
          exact ⟨T, hT, fun x y h => hsupport x y h _ (Finset.mem_singleton_self _)⟩
        · refine ⟨∅, by simp, fun x y _ => ?_⟩
          change val C (List.ofFn x) C.output = val C (List.ofFn y) C.output
          rw [val_ge (n := n + m) (by simp) (by omega),
            val_ge (n := n + m) (by simp) (by omega)]
      let leftWire (e : Fin n × Fin m) := Fin.castAdd m e.1
      let rightWire (e : Fin n × Fin m) := Fin.natAdd n e.2
      have separated (e f : Fin n × Fin m) : leftWire e ≠ rightWire f := by
        intro eq
        have hv := congrArg Fin.val eq
        change e.1.val = n + f.2.val at hv
        exact (Nat.not_lt_of_ge (by omega)) e.1.isLt
      have essential (e : Fin n × Fin m) (heE : e ∈ E) (i : Fin (n + m))
          (hi : i = leftWire e ∨ i = rightWire e) : i ∈ T := by
        by_contra he
        let x (w : Fin (n + m)) := decide (w = leftWire e ∨ w = rightWire e)
        let y (w : Fin (n + m)) := if w = i then false else x w
        have agree : ∀ w ∈ T, x w = y w := by
          intro w hw
          simp [y, show w ≠ i from fun eq => he (eq ▸ hw)]
        have hx : circuitFun (n + m) C x = true := by
          rw [hCompute, decide_eq_true_eq]
          exact ⟨e.1, e.2, heE, by simp [x, leftWire], by simp [x, rightWire]⟩
        have hy : circuitFun (n + m) C y = false := by
          rw [hCompute, decide_eq_false_iff_not]
          rintro ⟨a, b, _, hfL, hfR⟩
          change y (leftWire (a, b)) = true at hfL
          change y (rightWire (a, b)) = true at hfR
          rcases hi with rfl | rfl
          · by_cases eq : leftWire (a, b) = leftWire e
            · simp [y, eq] at hfL
            · simp [y, x, eq, separated (a, b) e] at hfL
          · by_cases eq : rightWire (a, b) = rightWire e
            · simp [y, eq] at hfR
            · simp [y, x, eq, (separated e (a, b)).symm] at hfR
        have eq := hdep x y agree
        rw [hx, hy] at eq
        cases eq
      have hLeft : Set.InjOn leftWire (E : Set (Fin n × Fin m)) := by
        intro e he f hf eq
        apply hL e he f hf
        exact Fin.castAdd_inj.mp eq
      have hRight : Set.InjOn rightWire (E : Set (Fin n × Fin m)) := by
        intro e he f hf eq
        apply hR e he f hf
        apply Fin.ext
        have hv := congrArg Fin.val eq
        change n + e.2.val = n + f.2.val at hv
        omega
      have hd : Disjoint (E.image leftWire) (E.image rightWire) := by
        refine Finset.disjoint_left.mpr ?_
        intro w hw hw'
        obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hw
        obtain ⟨f, _, eq⟩ := Finset.mem_image.mp hw'
        exact separated e f eq.symm
      have hs : E.image leftWire ∪ E.image rightWire ⊆ T := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hw
          exact essential e he _ (Or.inl rfl)
        · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hw
          exact essential e he _ (Or.inr rfl)
      have hc := Finset.card_le_card hs
      rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injOn hLeft,
        Finset.card_image_of_injOn hRight] at hc
      refine ⟨E.image Prod.fst, ∅, fun e he => Or.inl (Finset.mem_image_of_mem _ he), ?_⟩
      have hb : (E.image Prod.fst).card ≤ E.card := Finset.card_image_le
      rw [Finset.card_empty, add_zero]
      omega
    · push Not at hR
      obtain ⟨e, he, f, hf, heq, hne⟩ := hR
      exact rightBranching n m E C hL ⟨e, he, f, hf, hne, heq⟩ hFour hAO hCompute hAnd
  · push Not at hL
    obtain ⟨e, he, f, hf, heq, hne⟩ := hL
    exact leftBranching n m E C ⟨e, he, f, hf, hne, heq⟩ hFour hAO hCompute hAnd
