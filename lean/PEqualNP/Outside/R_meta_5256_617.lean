import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 40000 in
set_option maxHeartbeats 7000000 in
theorem PEqualNP.Outside.R_meta_5256_617
    (pairSupport : ∀ C : Circuit, Monotone2 C → ReadsBack 26 C →
      (∀ j < C.size, ∃ x : List Bool, x.length = 26 ∧ (C.wires x).getD (26+j) false = true) →
      2 ≤ C.lineDeg 26 (Finset.Ico 13 26) → C.lineDeg 26 (Finset.range 26) ≤ 2 →
      ∃ a b : Fin 13, ∀ x : List Bool, x.length = 26 →
        x.getD (13+a.val) false = true → x.getD (13+b.val) false = true → C.eval x = true)
    (highDegree :
      let D : Finset (Fin 13) := {0,1,3,9}
      let test (b : Bool) (x : List Bool) : Prop :=
        if b = true then ∃ p l : Fin 13, p-l ∈ D ∧
          x = (List.ofFn fun i : Fin 13 => decide (i=p)) ++
            (List.ofFn fun i : Fin 13 => decide (i=l))
        else ∃ Q : Finset (Fin 13), Q.card = 4 ∧
          (∀ l : Fin 13, {p ∈ Q | p-l ∈ D}.card ≤ 2) ∧
          x = (List.ofFn fun p : Fin 13 => decide (p∈Q)) ++
            (List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ D))
      ∀ C : Circuit, Monotone2 C → ReadsBack 26 C →
        (∀ b x, test b x → C.eval x = b) →
        2 ≤ C.lineDeg 26 (Finset.Ico 13 26) →
        (∀ j < C.size, ∀ i ≤ 26+j, ∃ b x, test b x ∧
          (C.wires x).getD (26+j) false = b ∧
          (if i = 26+j then false else (C.wires x).getD i false) = !b) →
        (∃ g h : ℕ, (gateAt C g).op = .and ∧ (gateAt C h).op = .and ∧
          PEqualNP.EdgeOwnership.InCone 26 C g h) →
        3 ≤ C.lineDeg 26 (Finset.range 26) → 64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → (∀ (x6 : Bool) (x7 : List Bool), x2 x6 x7 → x3.eval x7 = x6) → (2 : ℕ) ≤ x3.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) → (∀ x8 < x3.size, ∀ x10 ≤ (26 : ℕ) + x8, ∃ (x12 : Bool) (x13 : List Bool), x2 x12 x13 ∧ (x3.wires x13).getD ((26 : ℕ) + x8) Bool.false = x12 ∧ (if x10 = (26 : ℕ) + x8 then Bool.false else (x3.wires x13).getD x10 Bool.false) = !x12) → (∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x9 x10) → (64 : ℕ) ≤ x3.size := by
  dsimp only
  intro C mono back tests marked separated nested
  apply highDegree C mono back tests marked separated nested
  by_contra! small
  have active (j : ℕ) (hj : j < C.size) :
      ∃ x : List Bool, x.length = 26 ∧ (C.wires x).getD (26+j) false = true := by
    obtain ⟨b,x,sample,atWire,opp⟩ := separated j hj (26+j) le_rfl
    have hb : b = true := by
      rw [ite_eq_left (rfl : 26+j = 26+j)] at opp
      cases b with
      | false => exact Bool.noConfusion opp
      | true => rfl
    refine ⟨x, ?_, atWire.trans hb⟩
    have positive : ∃ p l : Fin 13, p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ∧
        x = (List.ofFn fun i : Fin 13 => decide (i=p)) ++
          (List.ofFn fun i : Fin 13 => decide (i=l)) := by
      rw [hb] at sample
      exact sample
    obtain ⟨p,l,_,rfl⟩ := positive
    simp only [List.length_append, List.length_ofFn]
  obtain ⟨a,b,forces⟩ := pairSupport C mono back active marked (by omega)
  let D : Finset (Fin 13) := {0,1,3,9}
  have geometry : ∀ i j : Fin 13,
      let rows : Fin 13 → Finset (Fin 13) :=
        ![{2,4,5,6}, {5,6,7,11}, {4,6,7,8}, {2,5,7,8}, {2,6,8,10},
          {2,4,7,11}, {4,5,8,10}, {2,4,5,6}, {2,5,6,10},
          {2,4,6,8}, {2,4,5,8}, {2,4,5,6}, {4,5,6,10}]
      let Q := (rows (j-i)).image (fun p => p+i)
      let marks : Finset (Fin 13) := {0,1,3,9}
      Q.card = 4 ∧ (∀ l : Fin 13, {p ∈ Q | p-l ∈ marks}.card ≤ 2) ∧
        ∀ p ∈ Q, p-i ∉ marks ∧ p-j ∉ marks := by
    decide +kernel
  have existsQ : ∃ Q : Finset (Fin 13),
      Q.card = 4 ∧ (∀ l : Fin 13, {p ∈ Q | p-l ∈ D}.card ≤ 2) ∧
        ∀ p ∈ Q, p-a ∉ D ∧ p-b ∉ D := by
    exact ⟨_, geometry a b⟩
  obtain ⟨Q, cardQ, quad, miss⟩ := existsQ
  let points := List.ofFn fun p : Fin 13 => decide (p ∈ Q)
  let lines := List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ D)
  let row := points ++ lines
  have lengthRow : row.length = 26 := by simp [row, points, lines]
  have rejects : C.eval row = false := by
    exact tests false row ⟨Q, cardQ, quad, rfl⟩
  have lineOn (l : Fin 13) (away : ∀ p ∈ Q, p-l ∉ D) :
      row.getD (13+l.val) false = true := by
    have lenPoints : points.length = 13 := by simp [points]
    change (points ++ lines).getD (13+l.val) false = true
    rw [List.getD_append_right _ _ _ _ (by omega), lenPoints,
      show 13+l.val-13 = l.val by omega]
    have hlt : l.val < lines.length := by simpa only [lines, List.length_ofFn] using l.isLt
    rw [List.getD_eq_getElem _ _ hlt]
    unfold lines
    rw [List.getElem_ofFn]
    exact decide_eq_true away
  have fa := lineOn a (fun p hp => (miss p hp).1)
  have fb := lineOn b (fun p hp => (miss p hp).2)
  have accepts := forces row lengthRow fa fb
  rw [rejects] at accepts
  contradiction
