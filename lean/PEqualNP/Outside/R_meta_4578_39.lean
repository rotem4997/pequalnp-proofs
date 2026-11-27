import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.CircuitMoves

set_option maxHeartbeats 2200000 in
set_option maxRecDepth 5000 in
theorem PEqualNP.Outside.R_meta_4578_39
    (peel : ∀ C : Circuit, Monotone2 C → C.size < 64 →
      ¬ HasLineDegree 26 (Finset.range 13) C 1 →
      ¬ HasLineDegree 26 (Finset.Ico 13 26) C 1 →
      (∀ p l, p ∈ singerLines3 l → C.eval (incidenceInput {p} {l}) = true) →
      (∀ X Y, C.eval (incidenceInput X Y) = true → incidenceFun singerLines3 X Y = true) →
      ∃ (point : Bool) (v : Fin 13) (m : (i : Fin 5) → Fin (C.size - i.val)) (r : Fin 5 → ℕ),
        let D := (List.finRange 5).foldl (fun A i => eraseGate 26 A (m i).val (r i)) C
        ∀ X Y, (if point then v ∉ X else v ∉ Y) →
          D.eval (incidenceInput X Y) = C.eval (incidenceInput X Y))
    (punctured : ∀ (D : Circuit) (point : Bool) (v : Fin 13), Monotone2 D →
      (∀ p l, (if point then p ≠ v else l ≠ v) → p ∈ singerLines3 l →
        D.eval (incidenceInput {p} {l}) = true) →
      (∀ X Y, (if point then v ∉ X else v ∉ Y) →
        D.eval (incidenceInput X Y) = true → incidenceFun singerLines3 X Y = true) →
      59 ≤ D.size) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset (Fin (13 : ℕ))) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x5 : Fin (26 : ℕ)) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x4)) x5; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (x3 x4 : Finset (Fin (13 : ℕ))) => ∃ x5 ∈ x3, ∃ x6 ∈ x4, x1 x5 x6; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 x7 : Fin (13 : ℕ)), x1 x6 x7 → x2 x4 {x6} {x7} = Bool.true) → (∀ (x7 x8 : Finset (Fin (13 : ℕ))), x2 x4 x7 x8 = Bool.true → x3 x7 x8) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x4 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x4 (1 : ℕ) → (64 : ℕ) ≤ x4.size := by
  intro I value edge C mono hits sound hp hl
  by_contra! small
  have incidence : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ I p l := by decide +kernel
  have same (X Y : Finset (Fin 13)) : C.eval (incidenceInput X Y) = value C X Y := by
    let z : Fin 26 → Bool := fun i => Fin.addCases
      (fun p : Fin 13 => decide (p ∈ X)) (fun l : Fin 13 => decide (l ∈ Y)) i
    change C.eval _ = C.eval (List.ofFn z)
    congr 1
  have positive (p l : Fin 13) (inc : p ∈ singerLines3 l) : C.eval (incidenceInput {p} {l}) = true :=
    (same _ _).trans (hits _ _ ((incidence _ _).mp inc))
  have safe (X Y : Finset (Fin 13)) (h : C.eval (incidenceInput X Y) = true) :
      incidenceFun singerLines3 X Y = true := by
    obtain ⟨p,hp,l,hl,hi⟩ := sound _ _ ((same _ _).symm.trans h)
    exact decide_eq_true ⟨p,hp,l,hl,(incidence _ _).mpr hi⟩
  obtain ⟨point,v,m,r,agreement⟩ := peel C mono small hp hl positive safe
  let edit (A : Circuit) (i : Fin 5) := eraseGate 26 A (m i).val (r i)
  let D := (List.finRange 5).foldl edit C
  have erase {A : Circuit} (g t : ℕ) (hg : g < A.size) (hA : Monotone2 A) :
      (eraseGate 26 A g t).size + 1 = A.size ∧ Monotone2 (eraseGate 26 A g t) := by
    change g < A.gates.length at hg
    unfold eraseGate
    rw [if_pos hg]
    constructor
    · change (A.gates.take g ++ (A.gates.drop (g+1)).map _).length + 1 = A.gates.length
      rw [List.length_append,List.length_take,List.length_map,List.length_drop,Nat.min_eq_left (Nat.le_of_lt hg)]
      omega
    · intro z hz
      simp only [List.mem_append,List.mem_map] at hz
      rcases hz with before | ⟨a,ha,rfl⟩
      · exact hA _ (List.mem_of_mem_take before)
      · obtain ⟨ops,len⟩ := hA _ (List.mem_of_mem_drop ha)
        exact ⟨ops,by simpa using len⟩
  let A := edit C 0
  let B := edit A 1
  let E := edit B 2
  let G := edit E 3
  have valid (i : Fin 5) := (m i).isLt
  have z := erase (m 0) (r 0) (by simpa using valid 0) mono
  change A.size + 1 = C.size ∧ Monotone2 A at z
  have o := erase (m 1) (r 1) (by have h := valid 1; change (m 1).val < C.size - 1 at h; omega) z.2
  change B.size + 1 = A.size ∧ Monotone2 B at o
  have t := erase (m 2) (r 2) (by have h := valid 2; change (m 2).val < C.size - 2 at h; omega) o.2
  change E.size + 1 = B.size ∧ Monotone2 E at t
  have f := erase (m 3) (r 3) (by have h := valid 3; change (m 3).val < C.size - 3 at h; omega) t.2
  change G.size + 1 = E.size ∧ Monotone2 G at f
  have q := erase (m 4) (r 4) (by have h := valid 4; change (m 4).val < C.size - 4 at h; omega) f.2
  change D.size + 1 = G.size ∧ Monotone2 D at q
  have assn (X Y : Finset (Fin 13)) (h : if point then v ∉ X else v ∉ Y) :
      D.eval (incidenceInput X Y) = C.eval (incidenceInput X Y) := agreement X Y h
  have lower := punctured D point v q.2 (by
    intro p l away inc
    apply (assn {p} {l} ?_).trans (positive p l inc)
    cases point <;> simpa [ne_comm] using away) (by
    intro X Y h hit
    exact safe _ _ ((assn X Y h).symm.trans hit))
  omega
