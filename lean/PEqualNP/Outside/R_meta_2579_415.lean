import PEqualNP.Defs

open Finset PEqualNP.TopForm PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_2579_415
    (hbank : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (∀ a, ∀ w : G.Walk a a, w.IsCycle → 5≤w.length) →
      ∀ C : Circuit, IsAO2 n C →
      let t := C.gates.foldl (fun (r : List (Finset (Fin n) × Finset (Fin n × Fin n))) g =>
        let a := r.getD (g.inputs.getD 0 0) (∅,∅)
        let b := r.getD (g.inputs.getD 1 0) (∅,∅)
        r ++ [ite (g.op.eval [true,false]=true) (a.1∪b.1,a.2∪b.2) (∅,a.1 ×ˢ b.1)])
        (List.ofFn fun i : Fin n => ({i},{(i,i)}))
      let K := fun j : ℕ => (t.getD (n+j) (∅,∅)).2
      ∃ E : Finset (Sym2 (Fin n)), E.card≤24*C.size ∧ ∀ j<C.size, ∀ c v : Fin n,
        (∀ x y, (x,y)∈K j → G.Adj c x ∨ G.Adj c y ∨ G.Adj x y) →
        3<((K j).filter fun p => p.1=p.2).card → (v,v)∈K j → s(c,v)∈E)
    (hcore : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a, ∀ w : G.Walk a a, w.IsCycle → 5≤w.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      let t := C.gates.foldl (fun (r : List (Finset (Fin n) × Finset (Fin n × Fin n))) g =>
        let a := r.getD (g.inputs.getD 0 0) (∅,∅)
        let b := r.getD (g.inputs.getD 1 0) (∅,∅)
        r ++ [ite (g.op.eval [true,false]=true) (a.1∪b.1,a.2∪b.2) (∅,a.1 ×ˢ b.1)])
        (List.ofFn fun i : Fin n => ({i},{(i,i)}))
      let K := fun j : ℕ => (t.getD (n+j) (∅,∅)).2
      ∀ T ⊆ Ustar G C,
        (∀ c v : Fin n, s(c,v)∈T → ∀ j<C.size, ∀ b : Fin 2, side (n:=n) C j b={v} →
          2≤(orIn n C (n+j)).card → ¬∀ u∈orIn n C (n+j),G.Adj c u) →
        (∀ j<C.size, ∀ c : Fin n, (∀ x y, (x,y)∈K j → G.Adj c x ∨ G.Adj c y ∨ G.Adj x y) →
          ((K j).filter fun p => p.1=p.2 ∧ s(c,p.1)∈T).card≤3) → T.card≤k*(C.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨k,core⟩ := hcore; refine ⟨k+24,?_⟩; intro n G dec gir nonempty C least top
  let R := (Ustar G C).filter fun e => ¬∃ c v : Fin n, e=s(c,v) ∧ ∃ j<C.gates.length, ∃ b : Fin 2,
    2≤(orIn n C (n+j)).card ∧ (∀ y∈orIn n C (n+j),G.Adj c y) ∧ orIn n C (opnd C j b)={v}
  obtain ⟨E,cost,cover⟩ := hbank n G gir C least.1
  let T := R \ E
  have sub : T⊆Ustar G C := fun e h => (mem_filter.mp (mem_sdiff.mp h).1).1
  have bound := core n G gir nonempty C least top T sub (by
    intro c v hit j hj b leaf big all; exact (mem_filter.mp (mem_sdiff.mp hit).1).2 ⟨c,v,rfl,j,hj,b,big,all,leaf⟩) (by
    intro j hj c guard; by_contra! big
    obtain ⟨⟨x,y⟩,hp⟩ := card_pos.mp (Nat.zero_lt_of_lt big)
    have entry := mem_filter.mp hp
    have xy : x=y := entry.2.1; subst y
    apply (mem_sdiff.mp entry.2.2).2 (cover j hj c x guard ?_ entry.1)
    exact big.trans_le (card_le_card fun u hu => mem_filter.mpr ⟨(mem_filter.mp hu).1,(mem_filter.mp hu).2.1⟩))
  have partition : R ⊆ T ∪ E := by intro e he; by_cases mem : e∈E; exact mem_union_right _ mem; exact mem_union_left _ (mem_sdiff.mpr ⟨he,mem⟩)
  change R.card≤_; have total := (card_le_card partition).trans (card_union_le T E)
  rw [Nat.add_mul]; omega
