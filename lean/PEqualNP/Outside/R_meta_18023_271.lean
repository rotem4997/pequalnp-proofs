import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- When every edge has a degree-one endpoint, the active vertices partition into stars.
-- Their total rectangle cost is bounded by the number of essential circuit inputs.
-- The backward dependency argument follows L-meta-2074.

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_18023_271
    (withNesting : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∃ p p' : Fin x1, ∃ q q' : Fin x2, p ≠ p' ∧ q ≠ q' ∧ x3 p q ∧ x3 p q' ∧ x3 p' q) → (∃ i j : ℕ, (gateAt x5 i).op = GateOp.and ∧ (gateAt x5 j).op = GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (x1 + x2) x5 i j) → (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : ℕ) (x10 : Fin x9 → Finset (Fin x1)) (x11 : Fin x9 → Finset (Fin x2)), (∀ (x12 : Fin x9), (x10 x12).Nonempty ∧ (x11 x12).Nonempty) ∧ (∀ (x12 : Fin x9), ∀ x13 ∈ x10 x12, ∀ x15 ∈ x11 x12, x3 x13 x15) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 → ∃ (x15 : Fin x9), x12 ∈ x10 x15 ∧ x13 ∈ x11 x15) ∧ ∑ x12 : Fin x9, ((x10 x12).card + (x11 x12).card) ≤ x5.size + (1 : ℕ))
    (withoutNesting : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∃ p p' : Fin x1, ∃ q q' : Fin x2, p ≠ p' ∧ q ≠ q' ∧ x3 p q ∧ x3 p q' ∧ x3 p' q) → ¬ (∃ i j : ℕ, (gateAt x5 i).op = GateOp.and ∧ (gateAt x5 j).op = GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (x1 + x2) x5 i j) → (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : ℕ) (x10 : Fin x9 → Finset (Fin x1)) (x11 : Fin x9 → Finset (Fin x2)), (∀ (x12 : Fin x9), (x10 x12).Nonempty ∧ (x11 x12).Nonempty) ∧ (∀ (x12 : Fin x9), ∀ x13 ∈ x10 x12, ∀ x15 ∈ x11 x12, x3 x13 x15) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 → ∃ (x15 : Fin x9), x12 ∈ x10 x15 ∧ x13 ∈ x11 x15) ∧ ∑ x12 : Fin x9, ((x10 x12).card + (x11 x12).card) ≤ x5.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : ℕ) (x10 : Fin x9 → Finset (Fin x1)) (x11 : Fin x9 → Finset (Fin x2)), (∀ (x12 : Fin x9), (x10 x12).Nonempty ∧ (x11 x12).Nonempty) ∧ (∀ (x12 : Fin x9), ∀ x13 ∈ x10 x12, ∀ x15 ∈ x11 x12, x3 x13 x15) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 → ∃ (x15 : Fin x9), x12 ∈ x10 x15 ∧ x13 ∈ x11 x15) ∧ ∑ x12 : Fin x9, ((x10 x12).card + (x11 x12).card) ≤ x5.size + (1 : ℕ) := by
  intro n m R _ C hFour hAO hCompute
  classical
  by_cases nonstar : ∃ p p' : Fin n, ∃ q q' : Fin m,
      p ≠ p' ∧ q ≠ q' ∧ R p q ∧ R p q' ∧ R p' q
  · by_cases nested : ∃ i j : ℕ,
        (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
          PEqualNP.EdgeOwnership.InCone (n + m) C i j
    · exact withNesting n m R C nonstar nested hFour hAO hCompute
    · exact withoutNesting n m R C nonstar nested hFour hAO hCompute
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
    have separated (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
      intro eq
      have hv := congrArg Fin.val eq
      change a.val = n + b.val at hv
      exact (Nat.not_lt_of_ge (by omega)) a.isLt
    have essential (a : Fin n) (b : Fin m) (edge : R a b) (i : Fin (n + m))
        (hi : i = Fin.castAdd m a ∨ i = Fin.natAdd n b) : i ∈ T := by
      by_contra he
      let x (w : Fin (n + m)) := decide (w = Fin.castAdd m a ∨ w = Fin.natAdd n b)
      let y (w : Fin (n + m)) := if w = i then false else x w
      have agree : ∀ w ∈ T, x w = y w := by
        intro w hw
        simp [y, show w ≠ i from fun eq => he (eq ▸ hw)]
      have hx : circuitFun (n + m) C x = true := by
        rw [hCompute, decide_eq_true_eq]
        exact ⟨a, b, edge, by simp [x], by simp [x]⟩
      have hy : circuitFun (n + m) C y = false := by
        rw [hCompute, decide_eq_false_iff_not]
        rintro ⟨p, q, _, hp, hq⟩
        rcases hi with rfl | rfl
        · by_cases eq : Fin.castAdd m p = Fin.castAdd m a
          · simp [y, eq] at hp
          · simp [y, x, eq, separated p b] at hp
        · by_cases eq : Fin.natAdd n q = Fin.natAdd n b
          · simp [y, eq] at hq
          · simp [y, x, eq, (separated a q).symm] at hq
      have eq := hdep x y agree
      rw [hx, hy] at eq
      cases eq

    let High (a : Fin n) : Prop := ∃ b c : Fin m, b ≠ c ∧ R a b ∧ R a c
    let row (a : Fin n) : Finset (Fin m) := Finset.univ.filter (R a)
    let col (b : Fin m) : Finset (Fin n) := Finset.univ.filter (fun a => R a b ∧ ¬ High a)
    have rowMem (a : Fin n) (b : Fin m) : b ∈ row a ↔ R a b := by simp [row]
    have colMem (a : Fin n) (b : Fin m) : a ∈ col b ↔ R a b ∧ ¬ High a := by simp [col]
    have lowUnique {a : Fin n} {b c : Fin m} (h : ¬ High a)
        (hb : R a b) (hc : R a c) : b = c := by
      by_contra hn
      exact h ⟨b, c, hn, hb, hc⟩
    have highUnique {a a' : Fin n} {b : Fin m} (high : High a)
        (hab : R a b) (ha'b : R a' b) : a' = a := by
      by_contra hn
      obtain ⟨c, d, ne, hc, hd⟩ := high
      by_cases eq : b = c
      · exact nonstar ⟨a, a', b, d, (fun h => hn h.symm), eq.symm ▸ ne, hab, hd, ha'b⟩
      · exact nonstar ⟨a, a', b, c, (fun h => hn h.symm), eq, hab, hc, ha'b⟩

    let I := {a : Fin n // High a} ⊕ {b : Fin m // (col b).Nonempty}
    let A : I → Finset (Fin n) :=
      Sum.elim (fun a => {a.val}) (fun b => col b.val)
    let B : I → Finset (Fin m) :=
      Sum.elim (fun a => row a.val) (fun b => {b.val})
    have nonempty (i : I) : (A i).Nonempty ∧ (B i).Nonempty := by
      rcases i with a | b
      · obtain ⟨q, _, _, hq, _⟩ := a.property
        exact ⟨Finset.singleton_nonempty _, ⟨q, (rowMem _ _).2 hq⟩⟩
      · exact ⟨b.property, Finset.singleton_nonempty _⟩
    have rect (i : I) (a : Fin n) (ha : a ∈ A i) (b : Fin m) (hb : b ∈ B i) :
        R a b := by
      rcases i with p | q
      · have eq : a = p.val := Finset.mem_singleton.mp ha
        subst a
        exact (rowMem _ _).1 hb
      · have eq : b = q.val := Finset.mem_singleton.mp hb
        subst b
        exact ((colMem _ _).1 ha).1
    have cover (a : Fin n) (b : Fin m) (edge : R a b) : ∃ i : I, a ∈ A i ∧ b ∈ B i := by
      by_cases high : High a
      · exact ⟨Sum.inl ⟨a, high⟩, Finset.mem_singleton_self _, (rowMem _ _).2 edge⟩
      · have ha : a ∈ col b := (colMem _ _).2 ⟨edge, high⟩
        exact ⟨Sum.inr ⟨b, ⟨a, ha⟩⟩, ha, Finset.mem_singleton_self _⟩
    have rowLabel (i j : I) (a : Fin n) (hi : a ∈ A i) (hj : a ∈ A j) : i = j := by
      rcases i with p | q <;> rcases j with p' | q'
      · have he : p.val = p'.val :=
          (Finset.mem_singleton.mp hi).symm.trans (Finset.mem_singleton.mp hj)
        exact congrArg Sum.inl (Subtype.ext he)
      · have eq : a = p.val := Finset.mem_singleton.mp hi
        exact False.elim (((colMem _ _).1 hj).2 (eq.symm ▸ p.property))
      · have eq : a = p'.val := Finset.mem_singleton.mp hj
        exact False.elim (((colMem _ _).1 hi).2 (eq.symm ▸ p'.property))
      · have h1 := (colMem a q.val).1 hi
        have h2 := (colMem a q'.val).1 hj
        exact congrArg Sum.inr (Subtype.ext (lowUnique h1.2 h1.1 h2.1))
    have colLabel (i j : I) (b : Fin m) (hi : b ∈ B i) (hj : b ∈ B j) : i = j := by
      rcases i with p | q <;> rcases j with p' | q'
      · have eq := highUnique p.property ((rowMem _ _).1 hi) ((rowMem _ _).1 hj)
        exact congrArg Sum.inl (Subtype.ext eq.symm)
      · have eq : b = q'.val := Finset.mem_singleton.mp hj
        obtain ⟨a, ha⟩ := q'.property
        have ha' := (colMem a q'.val).1 ha
        have h := highUnique p.property ((rowMem _ _).1 hi) (eq.symm ▸ ha'.1)
        exact False.elim (ha'.2 (h.symm ▸ p.property))
      · have eq : b = q.val := Finset.mem_singleton.mp hi
        obtain ⟨a, ha⟩ := q.property
        have ha' := (colMem a q.val).1 ha
        have h := highUnique p'.property ((rowMem _ _).1 hj) (eq.symm ▸ ha'.1)
        exact False.elim (ha'.2 (h.symm ▸ p'.property))
      · have he : q.val = q'.val :=
          (Finset.mem_singleton.mp hi).symm.trans (Finset.mem_singleton.mp hj)
        exact congrArg Sum.inr (Subtype.ext he)

    let equiv : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    let X (i : Fin (Fintype.card I)) := A (equiv.symm i)
    let Y (i : Fin (Fintype.card I)) := B (equiv.symm i)
    refine ⟨Fintype.card I, X, Y, fun i => nonempty _, ?_, ?_, ?_⟩
    · intro i a ha b hb
      exact rect (equiv.symm i) a ha b hb
    · intro a b edge
      obtain ⟨i, hi, hj⟩ := cover a b edge
      exact ⟨equiv i, by simpa [X], by simpa [Y]⟩
    · let parts (i : I) : Finset (Fin (n + m)) :=
        (A i).image (Fin.castAdd m) ∪ (B i).image (Fin.natAdd n)
      have injectRight : Function.Injective (Fin.natAdd n : Fin m → Fin (n + m)) := by
        intro x y eq
        apply Fin.ext
        have hv := congrArg Fin.val eq
        change n + x.val = n + y.val at hv
        omega
      have partsCard (i : I) : (parts i).card = (A i).card + (B i).card := by
        have hd : Disjoint ((A i).image (Fin.castAdd m)) ((B i).image (Fin.natAdd n)) := by
          refine Finset.disjoint_left.mpr ?_
          intro w h1 h2
          obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h1
          obtain ⟨b, _, eq⟩ := Finset.mem_image.mp h2
          exact separated a b eq.symm
        change ((A i).image (Fin.castAdd m) ∪ (B i).image (Fin.natAdd n)).card = _
        rw [Finset.card_union_of_disjoint hd,
          Finset.card_image_of_injective _ (Fin.castAdd_injective n m),
          Finset.card_image_of_injective _ injectRight]
      have pairwise : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint parts := by
        intro i _ j _ ne
        refine Finset.disjoint_left.mpr ?_
        intro w hw hw'
        rcases Finset.mem_union.mp hw with h1 | h1 <;>
          rcases Finset.mem_union.mp hw' with h2 | h2
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h1
          obtain ⟨a', ha', he⟩ := Finset.mem_image.mp h2
          have eq := (Fin.castAdd_injective n m) he
          exact ne (rowLabel i j a ha (eq ▸ ha'))
        · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h1
          obtain ⟨b, _, eq⟩ := Finset.mem_image.mp h2
          exact separated a b eq.symm
        · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h1
          obtain ⟨a, _, eq⟩ := Finset.mem_image.mp h2
          exact separated a b eq
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h1
          obtain ⟨b', hb', he⟩ := Finset.mem_image.mp h2
          have eq := injectRight he
          exact ne (colLabel i j b hb (eq ▸ hb'))
      have sub : Finset.univ.biUnion parts ⊆ T := by
        intro w hw
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
        rcases Finset.mem_union.mp hi with hi | hi
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
          obtain ⟨b, hb⟩ := (nonempty i).2
          exact essential a b (rect i a ha b hb) _ (Or.inl rfl)
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hi
          obtain ⟨a, ha⟩ := (nonempty i).1
          exact essential a b (rect i a ha b hb) _ (Or.inr rfl)
      have budget := (Finset.card_le_card sub).trans hT
      rw [Finset.card_biUnion pairwise] at budget
      simp only [partsCard] at budget
      exact (equiv.symm.sum_comp (fun i => (A i).card + (B i).card)).trans_le budget
