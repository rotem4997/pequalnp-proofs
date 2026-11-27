import Mathlib.Data.List.ProdSigma
import Mathlib.Logic.Function.Iterate
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- After the initial gates are fixed, only pairs that reject every negative row can be used.
-- On an empty list of inputs, an AND returns true and an OR returns false.
-- At each choice take a pair that meets the first outstanding obligation and discard all
-- obligations that it meets. The depth limit is the remaining budget for terminal pairs.
theorem PEqualNP.Outside.R_meta_6796_73
    (extract : ∀ (E : List (ℕ × ℕ)) (D : List ((ℕ × ℕ) → Bool)) (k : ℕ),
      let next (prev : List ((ℕ × ℕ) → Bool) → Bool) (ds : List ((ℕ × ℕ) → Bool)) :=
        List.casesOn (motive := fun _ => Bool) ds true (fun d more =>
          E.any fun e => d e && prev (more.filter fun f => !(f e)))
      (next^[k] List.isEmpty) D = true →
        ∃ T : List (ℕ × ℕ), T.length ≤ k ∧ (∀ e ∈ T, e ∈ E) ∧ ∀ f ∈ D, T.any f = true)
    (searchB : ∃ B : Circuit,
      let P : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
      let Q : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
      let v (r w : ℕ) := BlindGate.wireValue B 11 (fun i => r.testBit i.val) w
      let fires (r : ℕ) (e : ℕ × ℕ) := v r e.1 && v r e.2
      let W := List.range (11 + B.size)
      let E := (W.product W).filter fun e => !(Q.any fun r => fires r e)
      let gate (j : ℕ) (e : ℕ × ℕ) := if (gateAt B j).op.eval [] then
        [e.1,e.2].any fun w => decide (w = 11 + j ∨ 11 ≤ w ∧ EdgeOwnership.InCone 11 B j (w-11)) else true
      let D := P.map fires ++ (List.range B.size).map gate
      let next (prev : List ((ℕ × ℕ) → Bool) → Bool) (ds : List ((ℕ × ℕ) → Bool)) :=
        List.casesOn (motive := fun _ => Bool) ds true (fun d more =>
          E.any fun e => d e && prev (more.filter fun f => !(f e)))
      TopForm.IsAO2 11 B ∧ B.size ≤ 20 ∧ 3 ≤ ReadTwo.nAnd B ∧
      (∀ j < B.size, (P.any fun r => v r (11+j)) = true ∧ (Q.any fun r => v r (11+j)) = true) ∧
      (next^[(22-B.size)/2] List.isEmpty) D = true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (ℕ × ℕ)),   have x3 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)];   have x4 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)];   have x5 : ℕ → ℕ → Bool := fun (x5 x6 : ℕ) => PEqualNP.BlindGate.wireValue x1 (11 : ℕ) (fun (x7 : Fin (11 : ℕ)) => x5.testBit ↑x7) x6;   PEqualNP.TopForm.IsAO2 (11 : ℕ) x1 ∧ x2 ≠ [] ∧ x1.size + (2 : ℕ) * x2.length ≤ (22 : ℕ) ∧ (3 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x1 ∧ (∀ x6 ∈ x2, x6.1 < (11 : ℕ) + x1.size ∧ x6.2 < (11 : ℕ) + x1.size) ∧ (∀ x6 < x1.size, (x3.any fun (x8 : ℕ) => x5 x8 ((11 : ℕ) + x6)) = Bool.true ∧ (x4.any fun (x8 : ℕ) => x5 x8 ((11 : ℕ) + x6)) = Bool.true) ∧ (∀ x6 < x1.size, PEqualNP.ReadTwo.isAnd x1 x6 → ∃ x9 ∈ x2, ∃ x10 ∈ [x9.1, x9.2], x10 = (11 : ℕ) + x6 ∨ (11 : ℕ) ≤ x10 ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x1 x6 (x10 - (11 : ℕ))) ∧ ∀ x6 ∈ x3 ++ x4, (x2.any fun (x8 : ℕ × ℕ) => x5 x6 x8.1 && x5 x6 x8.2) = Decidable.decide (x6 ∈ x3) := by
  obtain ⟨B,model,size,ands,live,solved⟩ := searchB
  let P : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
  let Q : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
  let v (r w : ℕ) := BlindGate.wireValue B 11 (fun i => r.testBit i.val) w
  let fires (r : ℕ) (e : ℕ × ℕ) := v r e.1 && v r e.2
  let W := List.range (11 + B.size)
  let E := (W.product W).filter fun e => !(Q.any fun r => fires r e)
  let gate (j : ℕ) (e : ℕ × ℕ) := if (gateAt B j).op.eval [] then
        [e.1,e.2].any fun w => decide (w = 11 + j ∨ 11 ≤ w ∧ EdgeOwnership.InCone 11 B j (w-11)) else true
  let D := P.map fires ++ (List.range B.size).map gate
  let k := (22-B.size)/2
  obtain ⟨T,budget,admiss,cover⟩ := extract E D k solved
  have pos (r : ℕ) (hr : r ∈ P) : T.any (fires r) = true :=
    cover (fires r) (List.mem_append_left _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
  have ne : T ≠ [] := by
    intro h
    have p := pos 513 (by decide)
    simp [h] at p
  have safe (e : ℕ × ℕ) (he : e ∈ T) :
      e.1 < 11 + B.size ∧ e.2 < 11 + B.size ∧ ∀ r ∈ Q, fires r e = false := by
    obtain ⟨hw,hq⟩ := List.mem_filter.mp (admiss e he)
    have hp : e.1 ∈ W ∧ e.2 ∈ W := List.mem_product.mp hw
    refine ⟨List.mem_range.mp hp.1,List.mem_range.mp hp.2,?_⟩
    intro r hr
    apply Bool.eq_false_of_not_eq_true
    intro hv
    have hits : (Q.any fun t => fires t e) = true := List.any_eq_true.mpr ⟨r,hr,hv⟩
    simp [hits] at hq
  have disjoint : ∀ r ∈ Q, r ∉ P := by decide
  refine ⟨B,T,model,ne,?_,ands,?_,live,?_,?_⟩
  · dsimp only [k] at budget
    omega
  · intro e he
    exact ⟨(safe e he).1,(safe e he).2.1⟩
  · intro j hj hand
    have h := cover (gate j) (List.mem_append_right _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩))
    obtain ⟨e,he,hv⟩ := List.any_eq_true.mp h
    have op := hand.2
    dsimp only [gate] at hv
    rw [op] at hv
    change ([e.1,e.2].any fun w => decide
      (w = 11 + j ∨ 11 ≤ w ∧ EdgeOwnership.InCone 11 B j (w-11))) = true at hv
    obtain ⟨w,hw,hreach⟩ := List.any_eq_true.mp hv
    exact ⟨e,he,w,hw,of_decide_eq_true hreach⟩
  · intro r hr
    rcases List.mem_append.mp hr with hp | hq
    · exact (pos r hp).trans (decide_eq_true hp).symm
    · have rejected : T.any (fires r) = false := by
        apply Bool.eq_false_of_not_eq_true
        intro h
        obtain ⟨e,he,hv⟩ := List.any_eq_true.mp h
        rw [(safe e he).2.2 r hq] at hv
        contradiction
      exact rejected.trans (decide_eq_false (disjoint r hq)).symm
