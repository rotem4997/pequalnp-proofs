import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_2210_811
    (block : ∀ (C : Circuit) (v j : ℕ) (x y : List Bool), x.length=y.length →
  C.output≠v → (∀ i, i≠v → x.getD i false=y.getD i false) →
  (C.gates.filter (fun g => decide (v∈g.inputs))).length=1 →
  j<C.gates.length → v∈(gateAt C j).inputs → C.eval x ≠ C.eval y →
  (⟨C.gates,x.length+j⟩ : Circuit).eval x ≠ (⟨C.gates,x.length+j⟩ : Circuit).eval y)
    (hard : ∀ C : Circuit, let readers := fun v : ℕ => C.gates.filter fun g => decide (v∈g.inputs)
  FanInTwo C → ReadsBack 10 C →
  (∀ g∈C.gates, (g.op=.not → g.inputs.length=1) ∧ (g.op≠.not → g.inputs.length=2 ∧ g.inputs.Nodup)) →
  C.size=14 → (∃ g, g.op=GateOp.or ∧ readers 9=[g]) →
  (∀ v∈([0,2] : List ℕ),(readers v).length=1) →
  (∀ v∈([4,6,7] : List ℕ),(readers v).length≤2) →
  (∀ v:Fin 9,(readers v.val).length≤3) →
  (∀ v∈([0,2] : List ℕ), ∀ j < C.gates.length, v∈(gateAt C j).inputs →
     ∀ m∈([2,104,400,50,138,208,258] : List ℕ),
     let D : Circuit := ⟨C.gates,10+j⟩
     D.eval ((List.range 10).map m.testBit) ≠ D.eval ((List.range 10).map (m+2^v).testBit)) →
  ¬ ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2]) = (([18440827511444797640,18441957826578283724,18446744073709222136,18446744073709485308,18446744073708175304,18446744073709551615,18446744073709223928,18446744073709551615] : List ℕ).getD (tableIndex x / 64) 0).testBit (tableIndex x % 64)) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x1 → (∀ x4 ∈ x1.gates, (x4.op = PEqualNP.CircuitLowerBounds.GateOp.not → x4.inputs.length = (1 : ℕ)) ∧ (x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x4.inputs.length = (2 : ℕ) ∧ x4.inputs.Nodup)) → x1.size = (14 : ℕ) → (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide ((9 : ℕ) ∈ x7.inputs)) x1.gates = [x6]) → (∀ x7 ∈ [(0 : ℕ), (2 : ℕ)], (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (x7 ∈ x9.inputs)) x1.gates).length = (1 : ℕ)) → (∀ x8 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)], (List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (x8 ∈ x10.inputs)) x1.gates).length ≤ (2 : ℕ)) → (∀ (x9 : Fin (9 : ℕ)), (List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x9 ∈ x10.inputs)) x1.gates).length ≤ (3 : ℕ)) → ¬∀ (x10 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ))]) = (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  intro C hao hback hclean hsize haux hsingle hm2 hm3 good
  have exactTable : ∀ x : Fin 9 → Bool, (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x = (([18440827511444797640,18441957826578283724,18446744073709222136,18446744073709485308,18446744073708175304,18446744073709551615,18446744073709223928,18446744073709551615] : List ℕ).getD (tableIndex x / 64) 0).testBit (tableIndex x % 64) := by decide
  apply hard C hao hback hclean hsize haux hsingle hm2 hm3 _ (fun x => (good x).trans (exactTable x))
  dsimp only
  let tape := fun (m : ℕ) => (List.range 10).map m.testBit
  let xrow := fun (m : ℕ) (i : Fin 9) => m.testBit i.val
  let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let valid := fun (v m : ℕ) =>
    ((List.ofFn (xrow m) ++ [xrow m 0 && xrow m 2]) == tape m) &&
    ((List.ofFn (xrow (m+2^v)) ++ [xrow (m+2^v) 0 && xrow (m+2^v) 2]) == tape (m+2^v)) &&
    (F (xrow m) != F (xrow (m+2^v))) &&
    (List.range 10).all (fun i => (i==v) || ((tape m).getD i false == (tape (m+2^v)).getD i false))
  have rows : ([0,2] : List ℕ).all (fun v => ([2,104,400,50,138,208,258] : List ℕ).all (valid v))=true := by decide
  have keep (gs : List Gate) (W : List Bool) (i : ℕ) (hi : i < W.length) :
      (Circuit.wires ⟨gs,0⟩ W).getD i false = W.getD i false := by
    induction gs generalizing W with
    | nil => rfl
    | cons g gs ih =>
      unfold Circuit.wires
      rw [List.foldl_cons]
      rw [show List.foldl _ _ gs = Circuit.wires ⟨gs,0⟩ (W++[g.op.eval (g.inputs.map fun k => W.getD k false)]) from rfl]
      rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hi]
  have noOut (v : ℕ) (hv : v∈([0,2] : List ℕ)) : C.output≠v := by
    intro he
    have aux : ∀ (m : ℕ), m=1 ∨ m=4 → C.eval (List.ofFn (xrow m) ++ [xrow m 0 && xrow m 2])=F (xrow m) := fun m _ => good _
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl
    · have hh := aux 1 (Or.inl rfl)
      change (Circuit.wires ⟨C.gates,0⟩ _).getD C.output false = _ at hh
      rw [he,keep _ _ _ (by decide)] at hh
      exact Bool.noConfusion hh
    · have hh := aux 4 (Or.inr rfl)
      change (Circuit.wires ⟨C.gates,0⟩ _).getD C.output false = _ at hh
      rw [he,keep _ _ _ (by decide)] at hh
      exact Bool.noConfusion hh
  intro v hv j hj hread m hm
  have test := List.all_eq_true.mp (List.all_eq_true.mp rows v hv) m hm
  simp only [valid,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,List.mem_range] at test
  obtain ⟨⟨⟨hx,hy⟩,hdiff⟩,hag⟩ := test
  have hlen (r : ℕ) : (tape r).length=10 := by simp [tape]
  have hin : ∀ i, i≠v → (tape m).getD i false=(tape (m+2^v)).getD i false := by
    intro i hi
    by_cases hh : i<10
    · exact (hag i hh).resolve_left hi
    · rw [List.getD_eq_default _ _ (by rw [hlen]; omega),List.getD_eq_default _ _ (by rw [hlen]; omega)]
  have hdiff' : C.eval (tape m) ≠ C.eval (tape (m+2^v)) := by
    rw [← hx,← hy,good,good]
    exact hdiff
  simpa only [hlen] using block C v j (tape m) (tape (m+2^v))
    ((hlen _).trans (hlen _).symm) (noOut v hv) hin (hsingle v hv) hj hread hdiff'
