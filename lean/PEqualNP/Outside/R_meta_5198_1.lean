import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_5198_1
    (h1 : let P : Fin 13 → Finset (Fin 13) := PEqualNP.HeptadCover.singerLines3
    let X := fun (T L : Finset (Fin 13)) =>
      (List.ofFn fun q : Fin 13 => decide (q ∈ T)) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ L))
    let W := fun (C : Circuit) (r : ℕ) (x : List Bool) => (C.wires x).getD r false
    let G := PEqualNP.MetaComplexity.NestedCover.gateAt
    let A := PEqualNP.CircuitLowerBounds.GateOp.and
    let aa := fun (C : Circuit) (j : ℕ) => (G C j).op = A ∧ ∃ i ∈ (G C j).inputs, 26 ≤ i ∧ (G C (i - 26)).op = A
    ∀ (C : Circuit) (o : ℕ), Monotone2 C → ReadsBack 26 C → o < 26 + C.size →
      (∀ p l : Fin 13, p ∈ P l → W C o (X {p} {l}) = true) →
      (∀ S : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle P S →
        W C o (X S (PEqualNP.HeptadCover.missLines P S)) = false) →
      (∀ j ∈ Finset.range C.size, ¬ aa C j) → 64 ≤ C.size)
    (h2 : let P : Fin 13 → Finset (Fin 13) := PEqualNP.HeptadCover.singerLines3
    let X := fun (T L : Finset (Fin 13)) =>
      (List.ofFn fun q : Fin 13 => decide (q ∈ T)) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ L))
    let W := fun (C : Circuit) (r : ℕ) (x : List Bool) => (C.wires x).getD r false
    let G := PEqualNP.MetaComplexity.NestedCover.gateAt
    let A := PEqualNP.CircuitLowerBounds.GateOp.and
    let aa := fun (C : Circuit) (j : ℕ) => (G C j).op = A ∧ ∃ i ∈ (G C j).inputs, 26 ≤ i ∧ (G C (i - 26)).op = A
    ∀ (C : Circuit) (o : ℕ), Monotone2 C → ReadsBack 26 C → o < 26 + C.size →
      (∀ p l : Fin 13, p ∈ P l → W C o (X {p} {l}) = true) →
      (∀ S : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle P S →
        W C o (X S (PEqualNP.HeptadCover.missLines P S)) = false) →
      (∃ j ∈ Finset.range C.size, aa C j ∧ ∀ k ∈ Finset.range C.size, aa C k → k = j) →
      64 ≤ C.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => (x4 x6 x7).op = x5 ∧ ∃ x8 ∈ (x4 x6 x7).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x6 (x8 - (26 : ℕ))).op = x5; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 x9 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 → x8 < (26 : ℕ) + x7.size → x9 < (26 : ℕ) + x7.size → (∀ (x14 x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 → x3 x7 x8 (x2 {x14} {x15}) = Bool.true ∨ x3 x7 x9 (x2 {x14} {x15}) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x15 → x3 x7 x8 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false ∧ x3 x7 x9 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 ∈ x1 x17 ∧ x3 x7 x8 (x2 {x16} {x17}) = Bool.true ∧ x3 x7 x9 (x2 {x16} {x17}) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 ∈ x1 x18 ∧ x3 x7 x9 (x2 {x17} {x18}) = Bool.true ∧ x3 x7 x8 (x2 {x17} {x18}) = Bool.false) → (∀ x18 ∈ Finset.range x7.size, ∀ x20 ∈ Finset.range x7.size, x6 x7 x18 → x6 x7 x20 → x18 = x20) → (63 : ℕ) ≤ x7.size := by
  intro x1 x2 x3 x4 x5 x6 C a b hm hr ha hb hpos hneg _ _ hat
  -- the merged circuit: one OR gate reading the two output wires
  let C' : Circuit := ⟨C.gates ++ [⟨GateOp.or, [a, b]⟩], 0⟩
  have hlen : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
        = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp; omega
  have hsize : C'.size = C.size + 1 := by
    show (C.gates ++ [(⟨GateOp.or, [a, b]⟩ : Gate)]).length = C.gates.length + 1
    rw [List.length_append, List.length_singleton]
  have hwires : ∀ x : List Bool, C'.wires x =
      C.wires x ++ [(C.wires x).getD a false || (C.wires x).getD b false] := by
    intro x
    have e : C'.wires x = C.wires x ++ [([a, b].map fun i => (C.wires x).getD i false).any id] := by
      show List.foldl _ x (C.gates ++ [(⟨GateOp.or, [a, b]⟩ : Gate)]) = _
      rw [List.foldl_append]
      rfl
    rw [e, List.map_cons, List.map_cons, List.map_nil, List.any_cons, List.any_cons, List.any_nil,
      id_eq, id_eq, Bool.or_false]
  have hXlen : ∀ T L : Finset (Fin 13),
      ((List.ofFn fun q : Fin 13 => decide (q ∈ T)) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ L))).length = 26 := by
    intro T L
    simp
  have hWlen : ∀ x : List Bool, x.length = 26 → (C.wires x).length = 26 + C.size := by
    intro x hx
    have h := hlen C.gates x
    rw [hx] at h
    exact h
  -- value of the new output wire
  have hout : ∀ x : List Bool, x.length = 26 →
      (C'.wires x).getD (26 + C.size) false = ((C.wires x).getD a false || (C.wires x).getD b false) := by
    intro x hx
    rw [hwires, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hWlen x hx])]
    simp [hWlen x hx]
  -- gates of C' below C.size are those of C
  have hgate : ∀ j, j < C.size → gateAt C' j = gateAt C j := by
    intro j hj
    have hj0 : j < C.gates.length := hj
    show (C.gates ++ [(⟨GateOp.or, [a, b]⟩ : Gate)]).getD j (⟨GateOp.or, []⟩ : Gate) = C.gates.getD j (⟨GateOp.or, []⟩ : Gate)
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hj0]
  have hgateN : gateAt C' C.size = ⟨GateOp.or, [a, b]⟩ := by
    show (C.gates ++ [(⟨GateOp.or, [a, b]⟩ : Gate)]).getD C.gates.length (⟨GateOp.or, []⟩ : Gate) = (⟨GateOp.or, [a, b]⟩ : Gate)
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
    rfl
  have hm' : Monotone2 C' := by
    intro g hg
    simp only [C', List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact hm g hg
    · subst hg; simp
  have hr' : ReadsBack 26 C' := by
    intro j hj i hi
    have hj' : j < C.gates.length + 1 := by
      have h : j < C'.size := hj
      rw [hsize] at h
      exact h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj2 | hj2
    · rw [hgate j hj2] at hi
      exact hr j hj2 i hi
    · subst hj2
      rw [show C.gates.length = C.size from rfl, hgateN] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi <;> subst hi <;> exact (by assumption : _ < 26 + C.size)
  -- aa transfers
  have haa : ∀ j, j < C.size →
      (((gateAt C' j).op = GateOp.and ∧ ∃ i ∈ (gateAt C' j).inputs, 26 ≤ i ∧ (gateAt C' (i - 26)).op = GateOp.and) ↔
       ((gateAt C j).op = GateOp.and ∧ ∃ i ∈ (gateAt C j).inputs, 26 ≤ i ∧ (gateAt C (i - 26)).op = GateOp.and)) := by
    intro j hj
    rw [hgate j hj]
    constructor
    · rintro ⟨h1, i, hi, h26, h3⟩
      have : i < 26 + j := hr j hj i hi
      refine ⟨h1, i, hi, h26, ?_⟩
      rw [← hgate (i - 26) (by omega)]
      exact h3
    · rintro ⟨h1, i, hi, h26, h3⟩
      have : i < 26 + j := hr j hj i hi
      refine ⟨h1, i, hi, h26, ?_⟩
      rw [hgate (i - 26) (by omega)]
      exact h3
  have haaN : ¬ ((gateAt C' C.size).op = GateOp.and ∧ ∃ i ∈ (gateAt C' C.size).inputs, 26 ≤ i ∧ (gateAt C' (i - 26)).op = GateOp.and) := by
    rw [hgateN]
    rintro ⟨h, _⟩
    cases h
  have hrange : ∀ j, j ∈ Finset.range C'.size → j < C.size ∨ j = C.size := by
    intro j hj
    rw [Finset.mem_range, hsize] at hj
    omega
  have ho : 26 + C.size < 26 + C'.size := by rw [hsize]; omega
  have hpos' : ∀ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l →
      (C'.wires ((List.ofFn fun q : Fin 13 => decide (q ∈ ({p} : Finset (Fin 13)))) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ ({l} : Finset (Fin 13)))))).getD (26 + C.size) false = true := by
    intro p l hp
    rw [hout _ (hXlen _ _)]
    rcases hpos p l hp with h | h
    · simp only [x3, x2] at h; rw [h, Bool.true_or]
    · simp only [x3, x2] at h; rw [h, Bool.or_true]
  have hneg' : ∀ S : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 S →
      (C'.wires ((List.ofFn fun q : Fin 13 => decide (q ∈ S)) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 S)))).getD (26 + C.size) false = false := by
    intro S hS
    rw [hout _ (hXlen _ _)]
    obtain ⟨h, h'⟩ := hneg S hS
    simp only [x3, x2, x1] at h h'
    rw [h, h']
    rfl
  by_cases hz : ∃ j ∈ Finset.range C.size, ((gateAt C j).op = GateOp.and ∧ ∃ i ∈ (gateAt C j).inputs, 26 ≤ i ∧ (gateAt C (i - 26)).op = GateOp.and)
  · obtain ⟨j, hj, hjaa⟩ := hz
    have := h2 C' (26 + C.size) hm' hr' ho hpos' hneg' ⟨j, by rw [Finset.mem_range, hsize]; rw [Finset.mem_range] at hj; omega, (haa j (Finset.mem_range.mp hj)).mpr hjaa, by
      intro k hk hkaa
      rcases hrange k hk with hk2 | hk2
      · exact hat k (Finset.mem_range.mpr hk2) j hj ((haa k hk2).mp hkaa) hjaa
      · subst hk2; exact absurd hkaa haaN⟩
    omega
  · have := h1 C' (26 + C.size) hm' hr' ho hpos' hneg' (by
      intro k hk hkaa
      rcases hrange k hk with hk2 | hk2
      · exact hz ⟨k, Finset.mem_range.mpr hk2, (haa k hk2).mp hkaa⟩
      · subst hk2; exact haaN hkaa)
    omega
