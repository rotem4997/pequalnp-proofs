import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_8225_87
    (sameSide : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (∃ g : PEqualNP.CircuitLowerBounds.Gate, x1.gates[0]?=some g ∧ (g.inputs=[0,1] ∨ g.inputs=[1,0])) → 64 ≤ x1.size)
    (incident : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (∃ g : PEqualNP.CircuitLowerBounds.Gate, x1.gates[0]?=some g ∧ (g.inputs=[0,13] ∨ g.inputs=[13,0])) → 64 ≤ x1.size)
    (nonincident : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (∃ g : PEqualNP.CircuitLowerBounds.Gate, x1.gates[0]?=some g ∧ (g.inputs=[0,14] ∨ g.inputs=[14,0])) → 64 ≤ x1.size)
    (star : ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) ∧ (∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) ∧ x4.size ≤ 64 ∧ ∃ (x5 : SimpleGraph (Fin (26 : ℕ))), x5 = PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x6 : Fin (13 : ℕ)) => List.map (fun (x7 : Fin (13 : ℕ)) => (↑x6, (13 : ℕ) + ↑x7)) (List.filter (fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ)))) (List.finRange (13 : ℕ)))) (List.finRange (13 : ℕ))) ∧ PEqualNP.EdgeOwnership.HasStarProfile (26 : ℕ) x5 x4 ∧ PEqualNP.EdgeOwnership.EveryEdgeOwned (26 : ℕ) x5 x4) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) ∧ (∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) ∧ x4.size ≤ x1.size ∧ ∃ (x5 : SimpleGraph (Fin (26 : ℕ))), x5 = PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x6 : Fin (13 : ℕ)) => List.map (fun (x7 : Fin (13 : ℕ)) => (↑x6, (13 : ℕ) + ↑x7)) (List.filter (fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ)))) (List.finRange (13 : ℕ)))) (List.finRange (13 : ℕ))) ∧ PEqualNP.EdgeOwnership.HasStarProfile (26 : ℕ) x5 x4 ∧ PEqualNP.EdgeOwnership.EveryEdgeOwned (26 : ℕ) x5 x4 := by
  let rn (ρ : (Fin 26) → (Fin 26)) (i : Nat) := if h : i<26 then (ρ ⟨i,h⟩).val else i
  have primary (ρ : (Fin 26) → (Fin 26)) (i : (Fin 26)) : rn ρ i.val = (ρ i).val := by simp [rn,i.isLt]
  have old (ρ : (Fin 26) → (Fin 26)) {i : Nat} (h : 26 ≤ i) : rn ρ i = i := by simp [rn,show ¬ i < 26 from by omega]
  have rn_inj {ρ : (Fin 26) → (Fin 26)} (h : Function.Injective ρ) : Function.Injective (rn ρ) := by
    intro i j e
    by_cases hi : i<26 <;> by_cases hj : j<26
    · have f := h (Fin.ext (by simpa [rn,hi,hj] using e) : ρ ⟨i,hi⟩ = ρ ⟨j,hj⟩)
      exact congrArg Fin.val f
    · simp [rn,hi,hj] at e;have := (ρ ⟨i,hi⟩).isLt;omega
    · simp [rn,hi,hj] at e;have := (ρ ⟨j,hj⟩).isLt;omega
    · simpa [rn,hi,hj] using e
  let rg (ρ : (Fin 26) → (Fin 26)) (g : Gate) : Gate := ⟨g.op,g.inputs.map (rn ρ)⟩
  let rename (ρ : (Fin 26) → (Fin 26)) (C : Circuit) : Circuit := ⟨C.gates.map (rg ρ),rn ρ C.output⟩
  let run {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate) (w : List α) :=
    gs.foldl (fun t g => t++[op g.op (g.inputs.map fun i => t.getD i d)]) w
  have equivRun {α : Type} (d : α) (op : GateOp → List α → α) (ρ : (Fin 26) → (Fin 26)) (gs : List Gate) (A B : List α)
      (eq : A.length=B.length) (lo : 26≤A.length) (start : ∀ i,A.getD i d=B.getD (rn ρ i) d) :
      ∀ i,(run d op gs A).getD i d = (run d op (gs.map (rg ρ)) B).getD (rn ρ i) d := by
    induction gs generalizing A B with
    | nil => exact start
    | cons g gs ih =>
      let v := op g.op (g.inputs.map fun i => A.getD i d)
      have same : op (rg ρ g).op ((rg ρ g).inputs.map fun i => B.getD i d) = v := by
        unfold rg v
        rw [List.map_map]
        congr 1
        exact List.map_congr_left (fun i _ => (start i).symm)
      change ∀ i,(run d op gs (A++[v])).getD i d = (run d op (gs.map (rg ρ)) (B++[_])).getD _ d
      rw [same]
      apply ih (A++[v]) (B++[v]) (by simp [eq]) (by simp;omega)
      intro i
      by_cases isEnd : i=A.length
      · subst i
        rw [old _ lo,List.getD_append_right A [v] d A.length (le_refl _),Nat.sub_self,eq,List.getD_append_right B [v] d B.length (le_refl _),Nat.sub_self]
      · have bn : rn ρ i ≠ B.length := by
          by_cases h : i<26
          · simp only [rn,dif_pos h];have := (ρ ⟨i,h⟩).isLt;omega
          · simp [rn,h];omega
        have skip (L : List α) (j : Nat) (ne : j≠L.length) : (L++[v]).getD j d=L.getD j d := by
          by_cases k : j<L.length
          · exact List.getD_append _ _ _ _ k
          · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
        rw [skip A i isEnd,skip B _ bn,start]
  have fetch {α : Type} (x : (Fin 26) → α) (i : (Fin 26)) (d : α) : (List.ofFn x).getD i.val d=x i := by
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt),List.getElem_ofFn]
  have start_match {α : Type} (ρ : (Fin 26) → (Fin 26)) (u v : (Fin 26) → α) (d : α) (h : ∀ i,u i = v (ρ i)) :
      ∀ j,(List.ofFn u).getD j d = (List.ofFn v).getD (rn ρ j) d := by
    intro j
    by_cases lt : j<26
    · exact (fetch u ⟨j,lt⟩ d).trans ((h _).trans ((fetch v (ρ ⟨j,lt⟩) d).symm.trans (by simp only [rn,dif_pos lt])))
    · rw [old _ (by omega),List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
  have eval (ρ : (Fin 26) → (Fin 26)) (C : Circuit) (x y : (Fin 26) → Bool) (e : ∀ i, x i=y (ρ i)) :
      C.eval (List.ofFn x) = (rename ρ C).eval (List.ofFn y) :=
    equivRun false GateOp.eval ρ C.gates (List.ofFn x) (List.ofFn y) (by simp) (by simp) (start_match _ _ _ _ e) C.output
  let edges : List ((Fin 26)×(Fin 26)) := [(0,13), (0,17), (0,23), (0,25), (1,13), (1,14), (1,18), (1,24), (2,14), (2,15), (2,19), (2,25), (3,13), (3,15), (3,16), (3,20), (4,14), (4,16), (4,17), (4,21), (5,15), (5,17), (5,18), (5,22), (6,16), (6,18), (6,19), (6,23), (7,17), (7,19), (7,20), (7,24), (8,18), (8,20), (8,21), (8,25), (9,13), (9,19), (9,21), (9,22), (10,14), (10,20), (10,22), (10,23), (11,15), (11,21), (11,23), (11,24), (12,16), (12,22), (12,24), (12,25)]
  let board (x : (Fin 26)→Bool) := ∃ e∈edges,x e.1=true ∧ x e.2=true
  let I (p l : (Fin 13)) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
  have listSpec : ∀ u v : (Fin 26),(u,v)∈edges ↔ ∃ p l,I p l ∧ u=Fin.castAdd 13 p ∧ v=Fin.natAdd 13 l := by dsimp only [I,edges];decide +kernel
  have meaning (x : (Fin 26)→Bool) : board x ↔ ∃ p l,I p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true := by
    constructor
    · rintro ⟨⟨u,v⟩,e,h,k⟩
      obtain ⟨p,l,edge,rfl,rfl⟩ := (listSpec u v).mp e
      exact ⟨p,l,edge,h,k⟩
    · rintro ⟨p,l,edge,h,k⟩
      exact ⟨_,(listSpec _ _).mpr ⟨p,l,edge,rfl,rfl⟩,h,k⟩
  let generators : List (List (Fin 26)) := [[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 13], [13, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 0, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1], [1, 0, 2, 3, 8, 5, 7, 6, 4, 9, 12, 11, 10, 13, 25, 15, 20, 18, 17, 19, 16, 21, 22, 24, 23, 14], [1, 9, 2, 0, 6, 8, 11, 5, 4, 3, 7, 12, 10, 13, 19, 25, 23, 18, 21, 15, 17, 16, 20, 24, 22, 14], [1, 3, 2, 9, 5, 6, 12, 8, 4, 0, 11, 7, 10, 13, 15, 19, 22, 18, 16, 25, 21, 17, 23, 24, 20, 14]]
  let act (g : Fin 5) (v : (Fin 26)) := (generators.getD g.val []).getD v.val 0
  let distance (u v : (Fin 26)) := (([[0, 0, 3, 1, 4, 4, 4, 3, 3, 1, 4, 3, 1, 0, 0, 2, 3, 2, 3, 2, 3, 3, 3, 2, 2, 2], [0, 0, 3, 2, 3, 4, 4, 4, 4, 2, 2, 3, 4, 1, 2, 2, 4, 2, 3, 2, 4, 4, 4, 2, 3, 1], [3, 3, 0, 4, 4, 4, 3, 4, 3, 4, 3, 3, 2, 3, 3, 3, 4, 4, 3, 3, 5, 5, 4, 3, 2, 2], [1, 2, 4, 0, 5, 3, 4, 4, 5, 2, 4, 2, 4, 1, 2, 3, 3, 4, 4, 2, 3, 4, 4, 3, 4, 1], [4, 3, 4, 5, 0, 4, 4, 4, 5, 5, 3, 5, 4, 3, 3, 5, 4, 4, 5, 4, 5, 5, 4, 3, 4, 4], [4, 4, 4, 3, 4, 0, 4, 4, 3, 4, 4, 3, 4, 3, 4, 3, 5, 4, 3, 5, 5, 5, 4, 3, 4, 3], [4, 4, 3, 4, 4, 4, 0, 3, 4, 2, 3, 3, 4, 2, 4, 3, 4, 4, 4, 2, 4, 4, 4, 3, 4, 4], [3, 4, 4, 4, 4, 4, 3, 0, 5, 3, 5, 3, 4, 3, 5, 4, 4, 4, 5, 3, 3, 5, 5, 3, 3, 3], [3, 4, 3, 5, 5, 3, 4, 5, 0, 5, 5, 5, 2, 3, 3, 5, 4, 5, 4, 5, 4, 4, 4, 5, 2, 2], [1, 2, 4, 2, 5, 4, 2, 3, 5, 0, 4, 4, 5, 1, 2, 2, 4, 4, 4, 3, 4, 3, 3, 3, 4, 1], [4, 2, 3, 4, 3, 4, 3, 5, 5, 4, 0, 3, 4, 2, 2, 4, 4, 4, 4, 3, 4, 4, 4, 3, 3, 3], [3, 3, 3, 2, 5, 3, 3, 3, 5, 4, 3, 0, 2, 2, 3, 2, 4, 3, 4, 4, 4, 4, 4, 3, 2, 2], [1, 4, 2, 4, 4, 4, 4, 4, 2, 5, 4, 2, 0, 1, 3, 4, 3, 3, 3, 4, 4, 4, 3, 3, 3, 1], [0, 1, 3, 1, 3, 3, 2, 3, 3, 1, 2, 2, 1, 0, 2, 2, 3, 2, 3, 2, 3, 3, 3, 2, 3, 1], [0, 2, 3, 2, 3, 4, 4, 5, 3, 2, 2, 3, 3, 2, 0, 3, 4, 4, 3, 5, 4, 5, 4, 3, 3, 3], [2, 2, 3, 3, 5, 3, 3, 4, 5, 2, 4, 2, 4, 2, 3, 0, 4, 4, 5, 4, 4, 4, 4, 3, 4, 4], [3, 4, 4, 3, 4, 5, 4, 4, 4, 4, 4, 4, 3, 3, 4, 4, 0, 5, 4, 4, 4, 5, 4, 4, 4, 3], [2, 2, 4, 4, 4, 4, 4, 4, 5, 4, 4, 3, 3, 2, 4, 4, 5, 0, 5, 4, 3, 5, 5, 3, 4, 3], [3, 3, 3, 4, 5, 3, 4, 5, 4, 4, 4, 4, 3, 3, 3, 5, 4, 5, 0, 4, 5, 4, 4, 5, 4, 3], [2, 2, 3, 2, 4, 5, 2, 3, 5, 3, 3, 4, 4, 2, 5, 4, 4, 4, 4, 0, 4, 4, 4, 3, 4, 4], [3, 4, 5, 3, 5, 5, 4, 3, 4, 4, 4, 4, 4, 3, 4, 4, 4, 3, 5, 4, 0, 5, 4, 5, 4, 4], [3, 4, 5, 4, 5, 5, 4, 5, 4, 3, 4, 4, 4, 3, 5, 4, 5, 5, 4, 4, 5, 0, 4, 4, 4, 4], [3, 4, 4, 4, 4, 4, 4, 5, 4, 3, 4, 4, 3, 3, 4, 4, 4, 5, 4, 4, 4, 4, 0, 4, 4, 3], [2, 2, 3, 3, 3, 3, 3, 3, 5, 3, 3, 3, 3, 2, 3, 3, 4, 3, 5, 3, 5, 4, 4, 0, 3, 3], [2, 3, 2, 4, 4, 4, 4, 3, 2, 4, 3, 2, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3, 0, 2], [2, 1, 2, 1, 4, 3, 4, 3, 2, 1, 3, 2, 1, 1, 3, 4, 3, 3, 3, 4, 4, 4, 3, 3, 2, 0]] : List (List Nat)).getD u.val []).getD v.val 0
  let rep (a b : (Fin 26)) (k : Nat) := (a.val=0 ∧ b.val=k) ∨ (b.val=0 ∧ a.val=k)
  let normal (a b : (Fin 26)) := rep a b 1 ∨ rep a b 13 ∨ rep a b 14
  have moves : ∀ a b : (Fin 26),a≠b → normal a b ∨ ∃g,distance (act g a) (act g b)<distance a b := by dsimp only [normal,rep,act,generators,distance];decide +kernel
  have bij : ∀ g,Function.Injective (act g) := by dsimp only [act,generators];decide +kernel
  have cycles : ∀ g,∀ e∈edges,((act g e.1,act g e.2)∈edges ∨ (act g e.2,act g e.1)∈edges) := by dsimp only [edges,act,generators];decide +kernel
  have ontoEdges : ∀ g,∀ e∈edges,∃ s∈edges, (act g s.1=e.1 ∧ act g s.2=e.2) ∨
      (act g s.1=e.2 ∧ act g s.2=e.1) := by dsimp only [edges,act,generators];decide +kernel
  have boardInvariant (g : Fin 5) (x : (Fin 26)→Bool) : board (x ∘ act g) ↔ board x := by
    constructor
    · rintro ⟨e,he,hu,hv⟩
      rcases cycles g e he with f|f
      · exact ⟨_,f,hu,hv⟩
      · exact ⟨_,f,hv,hu⟩
    · rintro ⟨e,he,hu,hv⟩
      obtain ⟨s,hs,h⟩:=ontoEdges g e he
      refine ⟨s,hs,?_⟩
      rcases h with ⟨p,l⟩|⟨p,l⟩ <;> simp [Function.comp_apply,p,l,hu,hv]
  let legalC (C : Circuit) := ∀ i g,C.gates[i]?=some g →
      (g.op=.and ∨ g.op=.or) ∧
        ∃ a b : Nat,g.inputs=[a,b] ∧ a≠b ∧ a<26+i ∧ b<26+i
  let computes (C : Circuit) := ∀ x : (Fin 26)→Bool,C.eval (List.ofFn x)=true ↔ board x
  let front (C : Circuit) (u v : Nat) := ∃ g,C.gates[0]?=some g ∧
      (g.inputs=[u,v] ∨ g.inputs=[v,u])
  let numeric (r : Nat) := ∀ C : Circuit,legalC C → computes C → front C 0 r → 64 ≤ C.size
  have renamedLegal {C : Circuit} (L : legalC C) (w : Fin 5) : legalC (rename (act w) C) := by
    intro i g h
    change (C.gates.map _)[i]?=some g at h
    rw [List.getElem?_map] at h
    cases old : C.gates[i]? with
    | none => simp [old] at h
    | some u =>
      have eq : rg (act w) u=g := by simpa [old] using h
      subst g
      obtain ⟨op,a,b,inputs,ne,la,lb⟩ := L i u old
      have bound (j : Nat) (le : j<26+i) : rn (act w) j<26+i := by
        by_cases h : j<26
        · simp only [rn,dif_pos h];have := (act w ⟨j,h⟩).isLt;omega
        · simpa [rn,h] using le
      exact ⟨op,_,_,by simp [rg,inputs],fun e => ne (rn_inj (bij w) e),bound a la,bound b lb⟩
  have renamedComputes {C : Circuit} (comp : computes C) (w : Fin 5) : computes (rename (act w) C) := by
    intro x
    rw [←eval (act w) C (x ∘ act w) x (fun _=>rfl),comp,boardInvariant]
  have renamedFront {C : Circuit} {u v : (Fin 26)} (h : front C u.val v.val) (w : Fin 5) :
      front (rename (act w) C) (act w u).val (act w v).val := by
    obtain ⟨g,hg,ins⟩ := h
    refine ⟨rg (act w) g,?_,?_⟩
    · simp [rename,List.getElem?_map,hg]
    · rcases ins with h|h
      · exact Or.inl (by simp [rg,h,primary])
      · exact Or.inr (by simp [rg,h,primary])
  have frontSwap {C : Circuit} {u v : Nat} : front C u v → front C v u := by
    rintro ⟨g,h,k⟩;exact ⟨g,h,k.symm⟩
  have finish (p : numeric 1) (q : numeric 13) (r : numeric 14) (C : Circuit)
      (ok : legalC C) (h : computes C) (u v : (Fin 26)) (ne : u≠v) (first : front C u.val v.val) : 64 ≤ C.size := by
    have go (k : Nat) : ∀ (D : Circuit) (a b : (Fin 26)),distance a b=k → legalC D → computes D →
        a≠b → front D a.val b.val → 64 ≤ D.size := by
      induction k using Nat.strong_induction_on with
      | ind k ih =>
       intro D a b kEq law correct diff gate
       rcases moves a b diff with ends|⟨w,win⟩
       · have close (j : Nat) (nj : numeric j) (repj : rep a b j) : 64 ≤ D.size := by
           rcases repj with ⟨ea,eb⟩|⟨eb,ea⟩
           · exact nj D law correct (by simpa only [ea,eb] using gate)
           · exact nj D law correct (by simpa only [ea,eb] using frontSwap gate)
         exact ends.elim (close 1 p) (fun m=>m.elim (close 13 q) (close 14 r))
       · have drop : distance (act w a) (act w b)<k := kEq ▸ win
         have step := ih _ drop (rename (act w) D) (act w a) (act w b) rfl (renamedLegal law w) (renamedComputes correct w)
           (fun eq=>diff (bij w eq)) (renamedFront gate w)
         change 64 ≤ (D.gates.map (rg (act w))).length at step;change 64 ≤ D.gates.length;simpa only [List.length_map] using step
    exact go _ C u v rfl ok h ne first
  have firstExists (C : Circuit) (ok : legalC C) (correct : computes C) :
      ∃ u v : (Fin 26), u≠v ∧ front C u.val v.val := by
    cases h : C.gates with
    | cons g tail =>
      have hg : C.gates[0]?=some g := by rw [h];rfl
      obtain ⟨_,a,b,ins,ne,la,lb⟩ := ok 0 g hg
      exact ⟨⟨a,by omega⟩,⟨b,by omega⟩,fun e=>ne (congrArg Fin.val e),g,hg,Or.inl ins⟩
    | nil =>
      exfalso
      let x (i : (Fin 26)) := decide (i=0 ∨ i=13)
      let y (i : (Fin 26)) := decide (i=1 ∨ i=14)
      have a : board x := ⟨(0,13),by dsimp only [edges];decide +kernel,by decide +kernel,by decide +kernel⟩
      have b : board y := ⟨(1,14),by dsimp only [edges];decide +kernel,by decide +kernel,by decide +kernel⟩
      have ex := (correct x).mpr a
      have ey := (correct y).mpr b
      dsimp only [Circuit.eval,Circuit.wires] at ex ey;rw [h] at ex ey
      by_cases inside : C.output<26
      · let i : (Fin 26) := ⟨C.output,inside⟩
        have xx := fetch x i false;have yy:=fetch y i false
        change (List.ofFn x).getD i.val false=true at ex
        change (List.ofFn y).getD i.val false=true at ey
        rw [xx] at ex;rw [yy] at ey
        have bad : ∀ i : (Fin 26), x i=true → y i=false := by dsimp only [x,y];decide +kernel
        rw [bad i ex] at ey;contradiction
      · rw [List.getD_eq_default _ _ (by simp;omega)] at ex;contradiction
  intro C law exactC
  have boardC : computes C := fun x => (exactC x).trans (meaning x).symm
  have normalize (k : Nat) (base : ∀ C : Circuit,legalC C →
      (∀ x : (Fin 26)→Bool,C.eval (List.ofFn x)=true ↔ ∃ a b,I a b ∧
        x (Fin.castAdd 13 a)=true ∧ x (Fin.natAdd 13 b)=true) →
      front C 0 k → 64 ≤ C.size) : numeric k :=
    fun D ok h pair => base D ok (fun x => (h x).trans (meaning x)) pair
  obtain ⟨u,v,ne,first⟩ := firstExists C law boardC
  have lower := finish (normalize 1 sameSide) (normalize 13 incident) (normalize 14 nonincident) C law boardC u v ne first
  obtain ⟨D,good,correct,price,profile⟩ := star
  exact ⟨D,good,correct,price.trans lower,profile⟩
