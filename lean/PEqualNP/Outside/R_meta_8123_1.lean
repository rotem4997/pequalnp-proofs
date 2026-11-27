import Mathlib
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_8123_1
    (relabel :
      let ds : List ℕ := [0, 5, 7, 17, 20]
      let computes : Circuit → Prop := fun C =>
        ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ds) ∧
            x u = true ∧ x v = true
      let ors : Circuit → ℕ := fun C => C.gates.countP
        (fun g => GateOp.casesOn g.op false true false (fun _ => false) false)
      let bad : Circuit → List (ℕ × ℕ) := fun C =>
        ReadK.doubleReread C 42 (fun w => decide (21 ≤ w))
          ((List.range 21).flatMap fun p => ds.map fun d => (p, 21 + (p+d)%21))
      ∀ P L : Fin 21 → Fin 21, Function.Injective P → Function.Injective L →
        (∀ i j, ((L j - P i : Fin 21).val ∈ ds ↔ (j - i).val ∈ ds)) →
        ∀ C, TopForm.IsAO2 42 C → computes C → ((P 0).val, 21 + (L 0).val) ∈ bad C →
          ∃ D, TopForm.IsAO2 42 D ∧ computes D ∧ ors D = ors C ∧
            (bad D).length = (bad C).length ∧ (0, 21) ∈ bad D)
    (repairAtOrigin :
      let ds : List ℕ := [0, 5, 7, 17, 20]
      let computes : Circuit → Prop := fun C =>
        ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ds) ∧
            x u = true ∧ x v = true
      let ors : Circuit → ℕ := fun C => C.gates.countP
        (fun g => GateOp.casesOn g.op false true false (fun _ => false) false)
      let bad : Circuit → List (ℕ × ℕ) := fun C =>
        ReadK.doubleReread C 42 (fun w => decide (21 ≤ w))
          ((List.range 21).flatMap fun p => ds.map fun d => (p, 21 + (p+d)%21))
      ∀ C, TopForm.IsAO2 42 C → computes C →
        (∀ D, TopForm.IsAO2 42 D → computes D → ors C ≤ ors D) →
        (0, 21) ∈ bad C → ∃ D, TopForm.IsAO2 42 D ∧ computes D ∧
          ors D ≤ ors C ∧ (bad D).length < (bad C).length) :
    (have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x3.op Bool.false Bool.true Bool.false (fun (x4 : ℕ) => Bool.false) Bool.false) x2.gates; have x3 : PEqualNP.CircuitLowerBounds.Circuit → List (ℕ × ℕ) := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.ReadK.doubleReread x3 (42 : ℕ) (fun (x4 : ℕ) => Decidable.decide ((21 : ℕ) ≤ x4)) (List.flatMap (fun (x4 : ℕ) => List.map (fun (x5 : ℕ) => (x4, (21 : ℕ) + (x4 + x5) % (21 : ℕ))) [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) (List.range (21 : ℕ))); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (42 : ℕ) x4 → x1 x4 → (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (42 : ℕ) x7 → x1 x7 → x2 x4 ≤ x2 x7) → x3 x4 ≠ [] → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (42 : ℕ) x9 ∧ x1 x9 ∧ x2 x9 ≤ x2 x4 ∧ (x3 x9).length < (x3 x4).length) := by
  let ds : List ℕ := [0, 5, 7, 17, 20]
  let edges := (List.range 21).flatMap fun p => ds.map fun d => (p, 21 + (p+d)%21)
  let bad (C : Circuit) := ReadK.doubleReread C 42 (fun w => decide (21 ≤ w)) edges
  let point : Fin 21 → Fin 21 := fun i =>
    ([0, 5, 10, 16, 6, 11, 8, 18, 12, 7, 20, 17, 13, 1, 9, 14, 19, 3, 15, 2, 4] : List (Fin 21)).getD i.val 0
  let line : Fin 21 → Fin 21 := fun i =>
    ([5, 10, 15, 2, 11, 7, 4, 17, 12, 6, 16, 13, 18, 8, 14, 19, 3, 20, 1, 9, 0] : List (Fin 21)).getD i.val 0
  let incident (i j : Fin 21) := (j - i).val ∈ ds
  have pointInj : Function.Injective point := by
    have h : ∀ i j : Fin 21, point i = point j → i = j := by
      dsimp only [point]
      decide
    exact fun {i j} => h i j
  have lineInj : Function.Injective line := by
    have h : ∀ i j : Fin 21, line i = line j → i = j := by
      dsimp only [line]
      decide
    exact fun {i j} => h i j
  have preserves : ∀ i j, incident (point i) (line j) ↔ incident i j := by
    dsimp only [incident, ds, point, line]
    decide
  have preservesPow (k : ℕ) (i j : Fin 21) :
      incident (point^[k] i) (line^[k] j) ↔ incident i j := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (preserves _ _).trans ih
  have pointZero (k : ℕ) : point^[k] 0 = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl
  have lineOrbit (d : ℕ) (hd : d ∈ ds) : ∃ k : ℕ, (line^[k] 0).val = d := by
    simp only [ds, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  intro computes ors defect C hC hF hmin hn
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil (bad C) hn
  have heE : e ∈ edges := (List.mem_filter.mp he).1
  obtain ⟨p, hp, hm⟩ := List.mem_flatMap.mp heE
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
  obtain ⟨k, hk⟩ := lineOrbit d hd
  let t : Fin 21 := ⟨p, List.mem_range.mp hp⟩
  let P (i : Fin 21) := t + point^[k] i
  let L (j : Fin 21) := t + line^[k] j
  have hP : Function.Injective P := fun _ _ h => (pointInj.iterate k) (add_left_cancel h)
  have hL : Function.Injective L := fun _ _ h => (lineInj.iterate k) (add_left_cancel h)
  have hI (i j : Fin 21) : incident (P i) (L j) ↔ incident i j := by
    have heq : L j - P i = line^[k] j - point^[k] i := by dsimp only [P, L]; abel
    change (L j - P i).val ∈ ds ↔ _
    rw [heq]
    exact preservesPow k i j
  have p0 : (P 0).val = p := by simp only [P, pointZero, add_zero]; rfl
  have l0 : (L 0).val = (p+d)%21 := by
    change (t + line^[k] 0).val = _
    rw [Fin.val_add, hk]
  have hedge : ((P 0).val, 21 + (L 0).val) ∈ bad C := by simpa only [p0, l0] using he
  obtain ⟨D, hD, hDF, hcost, hlen, hanchor⟩ := relabel P L hP hL hI C hC hF hedge
  obtain ⟨A, hA, hAF, hAO, hless⟩ := repairAtOrigin D hD hDF
    (fun T hT hTF => hcost.le.trans (hmin T hT hTF)) hanchor
  exact ⟨A, hA, hAF, hAO.trans hcost.le, hlen ▸ hless⟩
