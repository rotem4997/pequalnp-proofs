import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_8225_681
    (surgery : let I (p l : Fin 13) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
      let ok (A : Circuit) :=
        (∀ k g, A.gates[k]?=some g → (g.op=.and ∨ g.op=.or) ∧
          ∃ a b : Fin (26+k), g.inputs=[a.val,b.val] ∧ a≠b) ∧
        (∀ x : Fin 26 → Bool, A.eval (List.ofFn x)=true ↔
          ∃ p l, I p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true)
      ∀ A, ok A → A.size ≤ 63 → ∀ k p l q m, p≠q → l≠m → I p l → I q m →
        Owns 26 A k (Fin.castAdd 13 p) (Fin.natAdd 13 l) →
        Owns 26 A k (Fin.castAdd 13 q) (Fin.natAdd 13 m) →
        ∃ B, ok B ∧ B.size<A.size)
    (cover : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (S : Finset (Fin 26)),
      (∀ u v, G.Adj u v → u∈S ∨ v∈S) → ∃ A : Circuit,
      (∀ k g, A.gates[k]?=some g → (g.op=.and ∨ g.op=.or) ∧
        ∃ a b : Fin (26+k), g.inputs=[a.val,b.val] ∧ a≠b) ∧
      circuitFun 26 A = graphFun G ∅ ∧ HasStarProfile 26 G A ∧
      A.size ≤ G.edgeFinset.card+S.card-1)
    (owners : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      AndOrOnly C → circuitFun n C=graphFun G ∅ → EveryEdgeOwned n G C) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) ∧ (∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) ∧ x4.size ≤ x1.size ∧ ∃ (x5 : SimpleGraph (Fin (26 : ℕ))), x5 = PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x6 : Fin (13 : ℕ)) => List.map (fun (x7 : Fin (13 : ℕ)) => (↑x6, (13 : ℕ) + ↑x7)) (List.filter (fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ)))) (List.finRange (13 : ℕ)))) (List.finRange (13 : ℕ))) ∧ PEqualNP.EdgeOwnership.HasStarProfile (26 : ℕ) x5 x4 ∧ PEqualNP.EdgeOwnership.EveryEdgeOwned (26 : ℕ) x5 x4 := by
  let I (p l : Fin 13) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
  let P : Fin 13 → Fin 26 := Fin.castAdd 13
  let L : Fin 13 → Fin 26 := Fin.natAdd 13
  let edges := (List.finRange 13).flatMap fun p : Fin 13 =>
    ((List.finRange 13).filter fun l : Fin 13 => decide (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9)).map
      fun l => (p.val,13+l.val)
  let G := edgeGraph 26 edges
  let shore := Finset.univ.filter fun a : Fin 26 => a.val<13
  have adj : ∀ u v : Fin 26, G.Adj u v ↔ ∃ p l, I p l ∧
      ((u=P p ∧ v=L l) ∨ (u=L l ∧ v=P p)) := by
    dsimp only [G,edges,I,P,L]
    decide +kernel
  have num : G.edgeFinset.card+shore.card-1 = 64 := by
    dsimp only [G,edges,shore]
    decide +kernel
  classical
  intro C shape fn
  let ok (A : Circuit) :=
    (∀ k g, A.gates[k]?=some g → (g.op=.and ∨ g.op=.or) ∧
      ∃ a b : Fin (26+k), g.inputs=[a.val,b.val] ∧ a≠b) ∧
    (∀ x : Fin 26 → Bool, A.eval (List.ofFn x)=true ↔
      ∃ p l, I p l ∧ x (P p)=true ∧ x (L l)=true)
  have hC : ok C := by
    refine ⟨?_,fn⟩
    intro k g hg
    obtain ⟨hop,a,b,ha,hn,h1,h2⟩ := shape k g hg
    exact ⟨hop,⟨a,h1⟩,⟨b,h2⟩,ha,fun e => hn (congrArg Fin.val e)⟩
  have sem (x : Fin 26 → Bool) : graphFun G ∅ x=true ↔ ∃ p l, I p l ∧ x (P p)=true ∧ x (L l)=true := by
    change (decide (∃ a ∈ (∅ : Finset (Fin 26)), x a=true) ||
      decide (∃ u v, G.Adj u v ∧ x u=true ∧ x v=true)) = true ↔ _
    simp only [Finset.notMem_empty, false_and, exists_const, decide_false, Bool.false_or,
      decide_eq_true_eq]
    constructor
    · rintro ⟨u,v,edge,hu,hv⟩
      obtain ⟨p,l,hi,h|h⟩ := (adj u v).mp edge
      · exact ⟨p,l,hi,h.1 ▸ hu,h.2 ▸ hv⟩
      · exact ⟨p,l,hi,h.2 ▸ hv,h.1 ▸ hu⟩
    · rintro ⟨p,l,hi,hp,hl⟩
      exact ⟨P p,L l,(adj _ _).mpr ⟨p,l,hi,Or.inl ⟨rfl,rfl⟩⟩,hp,hl⟩
  have found : ∃ A : Circuit, ok A ∧ A.size≤C.size ∧ HasStarProfile 26 G A := by
    by_cases low : C.size≤63
    · have ex : ∃ s : Nat, ∃ A : Circuit, ok A ∧ A.size=s := ⟨C.size,C,hC,rfl⟩
      obtain ⟨A,hA,hsize⟩ := Nat.find_spec ex
      have least (B : Circuit) (hb : ok B) : A.size ≤ B.size := by
        rw [hsize]; exact Nat.find_min' ex ⟨B,hb,rfl⟩
      refine ⟨A,hA,least C hC,?_⟩
      intro k _ _
      let K (p l : Fin 13) := I p l ∧ Owns 26 A k (P p) (L l)
      have meet {p l q m} (h : K p l) (h' : K q m) : p=q ∨ l=m := by
        by_cases hp : p=q
        · exact Or.inl hp
        by_cases hl : l=m
        · exact Or.inr hl
        obtain ⟨B,hb,smaller⟩ := surgery A hA ((least C hC).trans low) k p l q m hp hl h.1 h'.1 h.2 h'.2
        exact False.elim ((Nat.not_lt_of_ge (least B hb)) smaller)
      have c : ∃ z : Fin 26, ∀ p l, K p l → P p=z ∨ L l=z := by
        by_cases existsFlag : ∃ p l, K p l
        · obtain ⟨p,l,h⟩ := existsFlag
          by_cases other : ∃ q m, K q m ∧ q≠p
          · obtain ⟨q,m,hq,hn⟩ := other
            have hm : m=l := (meet hq h).resolve_left hn
            subst m
            refine ⟨L l,?_⟩
            intro s t hs
            by_cases ht : t=l
            · exact Or.inr (congrArg L ht)
            · exact False.elim (hn (((meet hs hq).resolve_right ht).symm.trans ((meet hs h).resolve_right ht)))
          · refine ⟨P p,?_⟩; intro s t hs; left
            apply congrArg P
            by_contra hne
            exact other ⟨s,t,hs,hne⟩
        · exact ⟨0,fun p l h => False.elim (existsFlag ⟨p,l,h⟩)⟩
      obtain ⟨z,hz⟩ := c
      right; refine ⟨z,?_⟩
      intro u v he ho
      obtain ⟨p,l,hi,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (adj u v).mp he
      · exact hz p l ⟨hi,ho⟩
      · have eq : pairInput (L l) (P p) = pairInput (P p) (L l) := by
          funext a
          change decide (a=L l ∨ a=P p) = decide (a=P p ∨ a=L l)
          simp only [or_comm]
        let pred (x : Fin 26 → Bool) := k<A.gates.length ∧ (gateAt A k).op=.and ∧
          gateVal 26 A k x=true ∧ ∀ i<k, InCone 26 A i k → (gateAt A i).op=.and → gateVal 26 A i x=false
        have old : pred (pairInput (L l) (P p)) := ho
        have ho' : pred (pairInput (P p) (L l)) := eq ▸ old
        exact (hz p l ⟨hi,ho'⟩).symm
    · have vert : ∀ u v, G.Adj u v → u∈shore ∨ v∈shore := by
        intro u v he
        obtain ⟨p,l,_,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (adj u v).mp he
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.isLt⟩)
        · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.isLt⟩)
      obtain ⟨A,ha,he,hs,hlen⟩ := cover G shore vert
      rw [num] at hlen
      refine ⟨A,⟨ha,?_⟩,hlen.trans (by omega),hs⟩
      intro x
      have h : A.eval (List.ofFn x)=graphFun G ∅ x := congrFun he x
      rw [h]; exact sem x
  obtain ⟨A,ha,hle,hstar⟩ := found
  refine ⟨A,?_,ha.2,hle,G,rfl,hstar,owners 26 G A ?_ ?_⟩
  · intro k g hg
    obtain ⟨hop,a,b,h,hn⟩ := ha.1 k g hg
    exact ⟨hop,a.val,b.val,h,fun e => hn (Fin.ext e),a.isLt,b.isLt⟩
  · intro g hg
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
    exact (ha.1 i g hi).1
  · funext x; apply Bool.eq_iff_iff.mpr; exact (ha.2 x).trans (sem x).symm
