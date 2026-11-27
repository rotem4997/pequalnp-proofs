import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.ReadK PEqualNP.HeptadCover

-- Trace the singleton-true collision to a later AND where that singleton stops.
-- The singleton-dead collision has an earlier AND combining opposite singleton
-- types. Both additional witnesses are on the same selected proof.
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_6068_461
    (polarity : let ok := (fun C : Circuit => 63 ≤ C.size ∧ C.size ≤ 64 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
    circuitFun 26 C = fpl 13 (fun p l => p ∈ singerLines3 l) ∧
    ∀ a ∈ ([0,13] : List ℕ), lineSingle C 26 (fun i => decide (i=a)) (13-a) a = false)
    let Q := (fun (C : Circuit) (a b : ℕ) => let V := fun (S : Finset ℕ) => wval C (indW 26 S); let P := Relation.ReflTransGen (fun u w : ℕ => ∃ j < C.size, w = 26+j ∧ (if (gateAt C j).op.eval [] then u ∈ (gateAt C j).inputs else u = if V {0,13} (in0 C j) then in0 C j else in1 C j)); let K := fun (z j : ℕ) => P (26+j) C.output ∧ isAnd C j ∧ ∀ t ∈ (gateAt C j).inputs, V {z} t = false; ∃ i j, K a i ∧ K b j ∧ V {b} (26+i)=true ∧ V {a} (26+j)=false)
    ∀ C, ok C → Q C 13 0 → ∃ D, ok D ∧ Q D 0 13)
    (trace : ∀ (C : Circuit), IsAO2 26 C →
    let V := fun (S : Finset ℕ) => wval C (indW 26 S)
    let P := Relation.ReflTransGen (fun u w : ℕ => ∃ j < C.size, w = 26+j ∧
     (if (gateAt C j).op.eval [] then u ∈ (gateAt C j).inputs
      else u = if V {0,13} (in0 C j) then in0 C j else in1 C j))
    let K := fun (z j : ℕ) => P (26+j) C.output ∧ isAnd C j ∧
       ∀ t ∈ (gateAt C j).inputs, V {z} t = false
    ∀ (a b j k : ℕ), (a=0 ∧ b=13 ∨ a=13 ∧ b=0) → K a j → K b k →
    V {b} (26+j) = true → V {a} (26+k) = false →
    V {0,13} C.output = true → V {b} C.output = false → ∃ s d : ℕ, s < k ∧ j < d ∧ isAnd C s ∧ isAnd C d ∧
      P (26+s) (26+k) ∧ P (26+j) (26+d) ∧ P (26+d) C.output ∧
      V {b} (in0 C d) ≠ V {b} (in1 C d) ∧
      V {a} (in0 C s) ≠ V {a} (in1 C s) ∧ V {b} (in0 C s) ≠ V {b} (in1 C s) ∧
      V {a} (in0 C s) ≠ V {b} (in0 C s))
    (bound : ∀ (C : Circuit), 63 ≤ C.size → C.size ≤ 64 → IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
    circuitFun 26 C = fpl 13 (fun p l => p ∈ singerLines3 l) →
    (∀ a ∈ ([0,13] : List ℕ), lineSingle C 26 (fun i => decide (i=a)) (13-a) a = false) →
    let V := fun (S : Finset ℕ) => wval C (indW 26 S)
    let P := Relation.ReflTransGen (fun u w : ℕ => ∃ j < C.size, w = 26+j ∧
     (if (gateAt C j).op.eval [] then u ∈ (gateAt C j).inputs
      else u = if V {0,13} (in0 C j) then in0 C j else in1 C j))
    let K := fun (z j : ℕ) => P (26+j) C.output ∧ isAnd C j ∧
       ∀ t ∈ (gateAt C j).inputs, V {z} t = false
    let pinL := in0 C
    let pinR := in1 C
    let pointVal := V {0}
    let lineVal := V {13}
    ∀ j k, K 0 j → K 13 k → lineVal (26+j) = true → pointVal (26+k) = false → (∃ s d : ℕ, s < k ∧ j < d ∧ isAnd C s ∧ isAnd C d ∧
      P (26+s) (26+k) ∧ P (26+j) (26+d) ∧ P (26+d) C.output ∧
      lineVal (pinL d) ≠ lineVal (pinR d) ∧
      pointVal (pinL s) ≠ pointVal (pinR s) ∧ lineVal (pinL s) ≠ lineVal (pinR s) ∧
      pointVal (pinL s) ≠ lineVal (pinL s)) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →               PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →                 have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);                 have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 : ℕ) (x15 : ℕ), x1.gates[x12]? = Option.some x13 ∧ x11 = (26 : ℕ) + x12 ∧ x13.inputs = [x14, x15] ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x10 = x14 ∨ x10 = x15) ∨ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x10 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x15) ∧ x9 {(0 : ℕ), (13 : ℕ)} x10 = Bool.true ∧ x9 {(0 : ℕ), (13 : ℕ)} x11 = Bool.true;                 have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) => Relation.ReflTransGen x10 ((26 : ℕ) + x12) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x12 ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs, x9 {(0 : ℕ), (13 : ℕ)} x13 = Bool.true ∧ x9 {x11} x13 = Bool.false;                 (∃ (x12 : ℕ) (x13 : ℕ), x12 ≠ x13 ∧ x11 (0 : ℕ) x12 ∧ x11 (13 : ℕ) x13 ∧ x9 {(13 : ℕ)} ((26 : ℕ) + x12) ≠ x9 {(0 : ℕ)} ((26 : ℕ) + x13)) → False := by
  intro C lo hi ao distinct ev noL noP
  dsimp only
  intro witness
  obtain ⟨i,j,_,wa,wb,mixed⟩ := witness
  let V := fun (S : Finset ℕ) => wval C (indW 26 S)
  let T := fun u w : ℕ => ∃ j < C.size, w = 26+j ∧
     (if (gateAt C j).op.eval [] then u ∈ (gateAt C j).inputs
      else u = if V {0,13} (in0 C j) then in0 C j else in1 C j)
  let P := Relation.ReflTransGen T
  let K := fun (z j : ℕ) => P (26+j) C.output ∧ isAnd C j ∧
       ∀ t ∈ (gateAt C j).inputs, V {z} t = false
  have rawStep {u w : ℕ} (h : ∃ (j : ℕ) (g : Gate) (l r : ℕ), C.gates[j]? = some g ∧
      w = 26+j ∧ g.inputs = [l,r] ∧
      (g.op = GateOp.and ∧ (u=l ∨ u=r) ∨ g.op = GateOp.or ∧ u=if V {0,13} l then l else r) ∧
      V {0,13} u = true ∧ V {0,13} w = true) : T u w := by
    obtain ⟨j,g,l,r,hj,rfl,ins,op,_⟩ := h
    obtain ⟨bound,eq⟩ := List.getElem?_eq_some_iff.mp hj
    have hit : gateAt C j = g := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ bound,eq]
    refine ⟨j,bound,rfl,?_⟩
    rcases op with ⟨hand,tmp⟩|⟨hor,tmp⟩
    · have h : (gateAt C j).op.eval [] = true := by rw [hit,hand]; rfl
      rw [h,if_pos rfl,hit,ins]; simpa using tmp
    · have h : (gateAt C j).op.eval [] = false := by rw [hit,hor]; rfl
      rw [h,if_neg Bool.false_ne_true]
      change u = if V {0,13} ((gateAt C j).inputs.getD 0 0) then (gateAt C j).inputs.getD 0 0 else (gateAt C j).inputs.getD 1 0
      rw [hit,ins]
      exact tmp
  have ci : K 0 i := ⟨Relation.ReflTransGen.mono (fun _ _ h => rawStep h) _ _ wa.1, wa.2.1, fun u hu => (wa.2.2 u hu).2⟩
  have cj : K 13 j := ⟨Relation.ReflTransGen.mono (fun _ _ h => rawStep h) _ _ wb.1, wb.2.1, fun u hu => (wb.2.2 u hu).2⟩
  let f := fpl 13 (fun p l => p ∈ singerLines3 l)
  have full : circuitFun 26 C = f := by
    funext x
    rw [Bool.eq_iff_iff]
    change C.eval _ = true ↔ decide (∃ p l : Fin 13, p ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) = true
    rw [decide_eq_true_iff,ev x]
    have plane (p l : Fin 13) : (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ↔ p ∈ singerLines3 l :=
      (by decide +kernel : ∀ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ↔ p ∈ singerLines3 l) p l
    simp only [plane]
  have val (S) : V S C.output = f (indW 26 S) := congrFun full _
  have pair : V {0,13} C.output = true := (val _).trans (by decide +kernel)
  have off0 : V {0} C.output = false := (val _).trans (by decide +kernel)
  have off13 : V {13} C.output = false := (val _).trans (by decide +kernel)
  have ns : ∀ a ∈ ([0,13] : List ℕ), lineSingle C 26 (fun u => decide (u=a)) (13-a) a = false := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl
    · exact noP
    · exact noL
  let ok := (fun C : Circuit => 63 ≤ C.size ∧ C.size ≤ 64 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
    circuitFun 26 C = fpl 13 (fun p l => p ∈ singerLines3 l) ∧
    ∀ a ∈ ([0,13] : List ℕ), lineSingle C 26 (fun i => decide (i=a)) (13-a) a = false)
  let Q := (fun (C : Circuit) (a b : ℕ) => let V := fun (S : Finset ℕ) => wval C (indW 26 S); let P := Relation.ReflTransGen (fun u w : ℕ => ∃ j < C.size, w = 26+j ∧ (if (gateAt C j).op.eval [] then u ∈ (gateAt C j).inputs else u = if V {0,13} (in0 C j) then in0 C j else in1 C j)); let K := fun (z j : ℕ) => P (26+j) C.output ∧ isAnd C j ∧ ∀ t ∈ (gateAt C j).inputs, V {z} t = false; ∃ i j, K a i ∧ K b j ∧ V {b} (26+i)=true ∧ V {a} (26+j)=false)
  have fits : ok C := ⟨lo,hi,ao,distinct,full,ns⟩
  have run (A : Circuit) (fitsA : ok A) (hit : Q A 0 13) : False := by
    obtain ⟨loA,hiA,aoA,distinctA,fullA,nsA⟩ := fitsA
    obtain ⟨j,k,cj,ck,hot,cold⟩ := hit
    have atPair : wval A (indW 26 {0,13}) A.output = true :=
      (congrFun fullA _).trans (by decide +kernel)
    have atLine : wval A (indW 26 {13}) A.output = false :=
      (congrFun fullA _).trans (by decide +kernel)
    exact bound A loA hiA aoA distinctA fullA nsA j k cj ck hot cold
      (trace A aoA 0 13 j k (Or.inl ⟨rfl,rfl⟩) cj ck hot cold atPair atLine)
  change V {13} (26+i) ≠ V {0} (26+j) at mixed
  by_cases h : V {13} (26+i) = true
  · have cold : V {0} (26+j) = false := Bool.eq_false_iff.mpr (fun e => mixed (h.trans e.symm))
    exact run C fits ⟨i,j,ci,cj,h,cold⟩
  · have h0 : V {13} (26+i) = false := Bool.eq_false_iff.mpr h
    have hot : V {0} (26+j) = true := by
      cases e : V {0} (26+j) <;> first | rfl | exact False.elim (mixed (h0.trans e.symm))
    obtain ⟨D,okD,marked⟩ := polarity C fits ⟨j,i,cj,ci,hot,h0⟩
    exact run D okD marked
