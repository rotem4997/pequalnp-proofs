import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_4478_271
    (normalize : ∀ (P L : ℕ) (E : Finset (Fin P × Fin L)) (C : Circuit),
      let spec := fun (D : Circuit) => ∀ x : Fin (P+L) → Bool, circuitFun (P+L) D x =
        decide (∃ e ∈ E, x (Fin.castAdd L e.1) = true ∧ x (Fin.natAdd P e.2) = true)
      (∀ p q l m, p ≠ q → l ≠ m → ¬ ((p,l) ∈ E ∧ (p,m) ∈ E ∧ (q,l) ∈ E ∧ (q,m) ∈ E)) →
      IsAO2 (P+L) C → spec C →
      (∀ v : Fin (P+L), (E.filter fun e => Fin.castAdd L e.1 = v ∨ Fin.natAdd P e.2 = v).card ≠ 1) →
      ∃ D : Circuit, IsAO2 (P+L) D ∧ D.size ≤ C.size ∧ spec D ∧ IsReadK (P+L) D 1)
    (charge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → IsAO2 n C →
      (∀ x : Fin n → Bool, circuitFun n C x =
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      IsReadK n C 1 → ∃ T : Finset (Fin n),
        (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ C.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ ∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ x9 ∈ x6, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true);   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → x6 x3 x4 → (∀ (x9 : Fin (x1 + x2)), (Finset.filter (x5 x9) x3).card ≠ (1 : ℕ)) → ∃ (x10 : Finset (Fin (x1 + x2))), (∀ x11 ∈ x3, Fin.castAdd x2 x11.1 ∈ x10 ∨ Fin.natAdd x1 x11.2 ∈ x10) ∧ x3.card + x10.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro P L E C
  dsimp only
  intro noSquare spec noLeaf
  obtain ⟨D,model,budget,computes,readOne⟩ := normalize P L E C noSquare spec.1 spec.2 noLeaf
  let pt : Fin P → Fin (P+L) := Fin.castAdd L
  let ln : Fin L → Fin (P+L) := Fin.natAdd P
  have ptInj : Function.Injective pt := by
    intro a b eq
    exact Fin.ext (congrArg (fun i : Fin (P+L) => i.val) eq)
  have lnInj : Function.Injective ln := by
    intro a b eq
    apply Fin.ext
    have heq : P+a.val = P+b.val := congrArg (fun i : Fin (P+L) => i.val) eq
    omega
  have distinctSides (p : Fin P) (l : Fin L) : pt p ≠ ln l := by
    intro eq
    have impossible : p.val = P+l.val := congrArg (fun i : Fin (P+L) => i.val) eq
    have := p.isLt
    omega
  have casesSide (a : Fin (P+L)) : (∃ p, a = pt p) ∨ ∃ l, a = ln l := by
    by_cases isPoint : a.val < P
    · exact Or.inl ⟨⟨a.val,isPoint⟩, Fin.ext rfl⟩
    · have upper := a.isLt
      refine Or.inr ⟨⟨a.val-P,by omega⟩,Fin.ext ?_⟩
      change a.val = P+(a.val-P)
      omega
  let directed (a b : Fin (P+L)) : Prop := ∃ p l, (p,l) ∈ E ∧ a = pt p ∧ b = ln l
  let G := SimpleGraph.fromRel directed
  have adj (a b : Fin (P+L)) : G.Adj a b ↔ directed a b ∨ directed b a := by
    change (SimpleGraph.fromRel directed).Adj a b ↔ _
    rw [SimpleGraph.fromRel_adj]
    refine ⟨And.right,fun h => ⟨?_,h⟩⟩
    rcases h with ⟨p,l,_,hp,hl⟩ | ⟨p,l,_,hp,hl⟩
    · rw [hp,hl]
      exact distinctSides p l
    · rw [hl,hp]
      exact (distinctSides p l).symm
  have points_to_lines (p : Fin P) (v : Fin (P+L)) :
      G.Adj (pt p) v ↔ ∃ l, (p,l) ∈ E ∧ v = ln l := by
    rw [adj]
    constructor
    · rintro (⟨q,l,edge,pEq,eq⟩ | ⟨q,l,_,_,impossible⟩)
      · have same := ptInj pEq
        exact ⟨l,same.symm ▸ edge,eq⟩
      · exact (distinctSides p l impossible).elim
    · rintro ⟨l,edge,rfl⟩
      exact Or.inl ⟨p,l,edge,rfl,rfl⟩
  have lines_to_points (l : Fin L) (v : Fin (P+L)) :
      G.Adj (ln l) v ↔ ∃ p, (p,l) ∈ E ∧ v = pt p := by
    rw [adj]
    constructor
    · rintro (⟨p,q,_,impossible,_⟩ | ⟨p,q,edge,eq,lEq⟩)
      · exact (distinctSides p l impossible.symm).elim
      · have same := lnInj lEq
        exact ⟨p,same.symm ▸ edge,eq⟩
    · rintro ⟨p,edge,rfl⟩
      exact Or.inr ⟨p,l,edge,rfl,rfl⟩
  have listed (p : Fin P) (l : Fin L) : G.Adj (pt p) (ln l) ↔ (p,l) ∈ E := by
    rw [points_to_lines]
    constructor
    · rintro ⟨m,inE,eq⟩
      exact (lnInj eq).symm ▸ inE
    · exact fun inE => ⟨l,inE,rfl⟩
  have c4free : NoFourCycle G := by
    intro u v huv
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ua,va⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨ub,vb⟩ := (Finset.mem_filter.mp hb).2
    rcases casesSide u with ⟨p,rfl⟩ | ⟨l,rfl⟩ <;>
      rcases casesSide v with ⟨q,rfl⟩ | ⟨m,rfl⟩
    · obtain ⟨i,pi,rfl⟩ := (points_to_lines p a).mp ua
      obtain ⟨j,pj,rfl⟩ := (points_to_lines p b).mp ub
      by_contra no
      exact noSquare p q i j (fun same => huv (congrArg pt same))
        (fun same => no (congrArg ln same))
        ⟨pi,pj,(listed q i).mp va,(listed q j).mp vb⟩
    · obtain ⟨i,_,isLine⟩ := (points_to_lines p a).mp ua
      obtain ⟨j,_,isPoint⟩ := (lines_to_points m a).mp va
      exact (distinctSides j i (isPoint.symm.trans isLine)).elim
    · obtain ⟨i,_,isPoint⟩ := (lines_to_points l a).mp ua
      obtain ⟨j,_,isLine⟩ := (points_to_lines q a).mp va
      exact (distinctSides i j (isPoint.symm.trans isLine)).elim
    · obtain ⟨i,il,rfl⟩ := (lines_to_points l a).mp ua
      obtain ⟨j,jl,rfl⟩ := (lines_to_points l b).mp ub
      by_contra no
      exact noSquare i j l m (fun same => no (congrArg pt same))
        (fun same => huv (congrArg ln same))
        ⟨il,(listed i m).mp va.symm,jl,(listed j m).mp vb.symm⟩
  have correctGraph (x : Fin (P+L) → Bool) :
      circuitFun (P+L) D x = decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) := by
    rw [computes x]
    congr 1
    apply propext
    constructor
    · rintro ⟨⟨p,l⟩,mem,hp,hl⟩
      exact ⟨pt p,ln l,(listed p l).mpr mem,hp,hl⟩
    · rintro ⟨i,j,edge,hi,hj⟩
      rcases (adj i j).mp edge with ⟨p,l,hit,rfl,rfl⟩ | ⟨p,l,hit,rfl,rfl⟩
      · exact ⟨(p,l),hit,hi,hj⟩
      · exact ⟨(p,l),hit,hj,hi⟩
  let encode (e : Fin P × Fin L) : Sym2 (Fin (P+L)) := s(pt e.1,ln e.2)
  have encodeInj : Function.Injective encode := by
    rintro ⟨p,l⟩ ⟨q,m⟩ same
    change s(pt p,ln l) = s(pt q,ln m) at same
    rcases Sym2.eq_iff.mp same with ⟨hp,hl⟩ | ⟨hp,hl⟩
    · exact Prod.ext (ptInj hp) (lnInj hl)
    · exact (distinctSides p m hp).elim
  have edges : G.edgeFinset = E.image encode := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,adj]
      constructor
      · rintro (⟨p,l,hit,rfl,rfl⟩ | ⟨p,l,hit,rfl,rfl⟩)
        · exact Finset.mem_image.mpr ⟨(p,l),hit,rfl⟩
        · exact Finset.mem_image.mpr ⟨(p,l),hit,Sym2.eq_swap⟩
      · rintro mem
        obtain ⟨⟨p,l⟩,hit,eq⟩ := Finset.mem_image.mp mem
        change s(pt p,ln l) = s(a,b) at eq
        rcases Sym2.eq_iff.mp eq with ⟨hp,hl⟩ | ⟨hp,hl⟩
        · exact Or.inl ⟨p,l,hit,hp.symm,hl.symm⟩
        · exact Or.inr ⟨p,l,hit,hp.symm,hl.symm⟩
  obtain ⟨T,covered,size⟩ := charge (P+L) G D c4free model correctGraph readOne
  rw [edges,Finset.card_image_of_injective _ encodeInj] at size
  exact ⟨T,fun e mem => covered _ _ ((listed e.1 e.2).mpr mem),size.trans (Nat.add_le_add_right budget 1)⟩
