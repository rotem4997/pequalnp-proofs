import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- A pair of raw input wires can accept one missing edge at cost two.
-- The search can therefore keep only pairs that use a computed wire and pay
-- for the edges still missing. The added pairs preserve every AND gate witness.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_6796_519
    (completeRows : ∀ (P Q : List ℕ) (v : ℕ → ℕ → Bool) (K : ℕ) (T : List (ℕ × ℕ)),
      let hit := fun r => T.any fun e => v r e.1 && v r e.2
      (∀ e ∈ P, ∃ a b : Fin K, ∀ r ∈ P ++ Q, (v r a.val && v r b.val) = decide (r = e)) →
      (∀ r ∈ Q, hit r = false) → ∃ R : List (ℕ × ℕ),
        R.length ≤ (P.filter fun r => !(hit r)).length ∧
        (∀ e ∈ R, e.1 < K ∧ e.2 < K) ∧
        ∀ r ∈ P ++ Q, ((T ++ R).any fun e => v r e.1 && v r e.2) = decide (r ∈ P))
    (core : ∃ (B : Circuit) (T : List (ℕ × ℕ)),
      let P : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
      let Q : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
      let v := fun (r w : ℕ) => BlindGate.wireValue B 11 (fun i => r.testBit i.val) w
      let hit := fun r => T.any fun e => v r e.1 && v r e.2
      IsAO2 11 B ∧ T ≠ [] ∧ B.size + 2 * (T.length + (P.filter fun r => !(hit r)).length) ≤ 22 ∧
      3 ≤ ReadTwo.nAnd B ∧
      (∀ e ∈ T, e.1 < 11 + B.size ∧ e.2 < 11 + B.size ∧ (11 ≤ e.1 ∨ 11 ≤ e.2)) ∧
      (∀ j < B.size, (P.any fun r => v r (11+j)) = true ∧ (Q.any fun r => v r (11+j)) = true) ∧
      (∀ j < B.size, ReadTwo.isAnd B j → ∃ e ∈ T, ∃ w ∈ [e.1,e.2],
        w = 11+j ∨ (11 ≤ w ∧ EdgeOwnership.InCone 11 B j (w-11))) ∧
      ∀ r ∈ Q, hit r = false) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (ℕ × ℕ)),   have x3 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)];   have x4 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)];   have x5 : ℕ → ℕ → Bool := fun (x5 x6 : ℕ) => PEqualNP.BlindGate.wireValue x1 (11 : ℕ) (fun (x7 : Fin (11 : ℕ)) => x5.testBit ↑x7) x6;   PEqualNP.TopForm.IsAO2 (11 : ℕ) x1 ∧ x2 ≠ [] ∧ x1.size + (2 : ℕ) * x2.length ≤ (22 : ℕ) ∧ (3 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x1 ∧ (∀ x6 ∈ x2, x6.1 < (11 : ℕ) + x1.size ∧ x6.2 < (11 : ℕ) + x1.size) ∧ (∀ x6 < x1.size, (x3.any fun (x8 : ℕ) => x5 x8 ((11 : ℕ) + x6)) = Bool.true ∧ (x4.any fun (x8 : ℕ) => x5 x8 ((11 : ℕ) + x6)) = Bool.true) ∧ (∀ x6 < x1.size, PEqualNP.ReadTwo.isAnd x1 x6 → ∃ x9 ∈ x2, ∃ x10 ∈ [x9.1, x9.2], x10 = (11 : ℕ) + x6 ∨ (11 : ℕ) ≤ x10 ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x1 x6 (x10 - (11 : ℕ))) ∧ ∀ x6 ∈ x3 ++ x4, (x2.any fun (x8 : ℕ × ℕ) => x5 x6 x8.1 && x5 x6 x8.2) = Decidable.decide (x6 ∈ x3) := by
  let P : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
  let Q : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
  obtain ⟨B,T,ao,nonempty,budget,ands,bounds,dirty,cones,sound⟩ := core
  let v := fun (r w : ℕ) => BlindGate.wireValue B 11 (fun i => r.testBit i.val) w
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  have extendWires (gs : List Gate) (x : List Bool) : ∃ t, gs.foldl step x = x ++ t := by
    induction gs generalizing x with
    | nil => exact ⟨[], by simp⟩
    | cons g gs ih =>
      obtain ⟨t, ht⟩ := ih (step x g)
      refine ⟨g.op.eval (g.inputs.map fun k => x.getD k false) :: t, ?_⟩
      simpa [step, List.append_assoc] using ht
  have raw (r : ℕ) (a : Fin 11) : v r a.val = r.testBit a.val := by
    let x := List.ofFn (fun i : Fin 11 => r.testBit i.val)
    obtain ⟨tail, ht⟩ := extendWires B.gates x
    change (B.gates.foldl step x).getD a.val false = _
    rw [ht, List.getD_append _ _ _ _ (by simpa only [x, List.length_ofFn] using a.isLt)]
    simp only [x,List.getD_eq_getElem?_getD,List.getElem?_ofFn,a.isLt,dite_true,Option.getD_some]
  have inputs : ∀ i : Fin P.length, ∃ a b : Fin 11, ∀ j : Fin (P ++ Q).length,
      (((P ++ Q).get j).testBit a.val && ((P ++ Q).get j).testBit b.val) =
        decide ((P ++ Q).get j = P.get i) := by decide +kernel
  have isolate (e : ℕ) (he : e ∈ P) : ∃ a b : Fin 11, ∀ r ∈ P ++ Q,
      (v r a.val && v r b.val) = decide (r = e) := by
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp he
    obtain ⟨a,b,good⟩ := inputs i
    refine ⟨a,b,?_⟩
    intro r hr
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hr
    simpa only [raw] using good j
  obtain ⟨R,cost,rawBounds,computes⟩ := completeRows P Q v 11 T isolate sound
  refine ⟨B,T ++ R,ao,?_,?_,ands,?_,dirty,?_,computes⟩
  · simp [nonempty]
  · change B.size + 2 * (T ++ R).length ≤ 22
    rw [List.length_append]
    change B.size + 2 * (T.length + (P.filter fun r => !(T.any fun e => v r e.1 && v r e.2)).length) ≤ 22 at budget
    change R.length ≤ (P.filter fun r => !(T.any fun e => v r e.1 && v r e.2)).length at cost
    omega
  · intro e he
    rcases List.mem_append.mp he with h | h
    · exact ⟨(bounds e h).1, (bounds e h).2.1⟩
    · obtain ⟨left,right⟩ := rawBounds e h
      exact ⟨by omega, by omega⟩
  · intro j hj hand
    obtain ⟨e,he,w,hw,path⟩ := cones j hj hand
    exact ⟨e,List.mem_append_left _ he,w,hw,path⟩
