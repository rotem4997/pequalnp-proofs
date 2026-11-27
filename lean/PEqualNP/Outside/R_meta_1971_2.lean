import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_1971_2
    (packing : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (B : Finset (Fin n)),
      (∀ x ∈ B, ∀ y, G.Adj x y → y ∈ B) → (∀ x ∈ B, (G.neighborSet x).ncard = 3) →
      (∀ x (w : G.Walk x x), w.IsCycle → 7 ≤ w.length) →
      ∃ I ⊆ B, (∀ x ∈ I, ∀ y ∈ I, ¬G.Adj x y) ∧ 5*B.card ≤ 14*I.card)
    (stars : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T : Finset (Fin n))
        (s : ℕ), (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) →
      (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) →
      s + 1 = A.card + G.edgeFinset.card + T.card →
      HasCircuitSize n (fun x : Fin n → Bool => decide
        ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s)
    (capacity : ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C →
      (∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j≠i → x j=y j) ∧ circuitFun n C x ≠ circuitFun n C y) →
      let front := fun g : Gate => g.inputs.take (bif g.op.eval [false] then 1 else 2)
      let cells := C.output :: C.gates.flatMap front
      let r := fun v : Fin n => (C.gates.filter fun g => (front g).contains v.val).length
      (∑ v, max 1 (r v)) + (∑ j ∈ Finset.range C.size, (cells.count (n+j)-1)) +
        (C.gates.filter fun g => g.op.eval [false]).length ≤ C.size+1)
    (sparse : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let front := fun g : Gate => g.inputs.take (bif g.op.eval [false] then 1 else 2)
      let cells := C.output :: C.gates.flatMap front
      let r := fun v : Fin n => C.gates.filter fun g => (front g).contains v.val
      (∀ x ∉ A, (G.neighborSet x).ncard = 3) → 7 ≤ G.egirth →
      (∀ i j, G.Adj i j → i ∉ A) → (∃ i j, G.Adj i j) →
      IsMinimalCircuit n C → circuitFun n C = f →
      (∀ v ∉ A, (r v).length ≤ 3 ∧ ((r v).length = 3 → ∀ g ∈ r v, g.op = .or)) →
      (∃ v ∉ A, (r v).length ≤ 1) →
      (∀ T : Finset (Fin n), T ⊆ Aᶜ → (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) →
        C.size+2 ≤ A.card + G.edgeFinset.card + T.card) →
      7*((∑ v, max 1 (r v).length) + (∑ j ∈ Finset.range C.size, (cells.count (n+j)-1)) +
        (C.gates.filter fun g => g.op.eval [false]).length + 1) ≤ 7*A.card + 15*Aᶜ.card →
      ∃ v ∉ A, ∃ s : ℕ, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length ≤ (1 : ℕ)) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  classical
  intro n G A f C hdeg hcycle hend hedge hspec hfan hfun hmin hread few
  let _ : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  have hgraph : f = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [hspec]
    change _ ↔ (decide (∃ a ∈ A, x a = true) ||
      decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) = true
    simp only [Bool.or_eq_true,decide_eq_true_eq]
  by_cases cheap : ∀ T : Finset (Fin n), T ⊆ Aᶜ → (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) →
      C.size+2 ≤ A.card + G.edgeFinset.card + T.card
  · obtain ⟨I,hI,ind,large⟩ := packing n G Aᶜ (fun _ _ y h => Finset.mem_compl.mpr (hend y _ h.symm))
      (fun x hx => hdeg x (Finset.mem_compl.mp hx)) hcycle
    let cover := Aᶜ \ I
    have hc (i j : Fin n) (h : G.Adj i j) : i ∈ cover ∨ j ∈ cover := by
      by_cases ii : i ∈ I
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (hend j i h.symm),fun jj => ind i ii j jj h⟩)
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (hend i j h),ii⟩)
    have cost := cheap cover Finset.sdiff_subset hc
    have tc : cover.card + I.card = Aᶜ.card := Finset.card_sdiff_add_card_eq_card hI
    have dA (a : Fin n) (ha : a ∈ A) : G.degree a = 0 :=
      (G.degree_eq_zero a).mpr (fun j hj => hend a j hj ha)
    have dB (a : Fin n) (ha : a ∈ Aᶜ) : G.degree a = 3 :=
      (G.ncard_neighborSet a).symm.trans (hdeg a (Finset.mem_compl.mp ha))
    have degreeSum := G.sum_degrees_eq_twice_card_edges
    rw [← A.sum_add_sum_compl,Finset.sum_congr rfl dA,Finset.sum_congr rfl dB] at degreeSum
    simp only [Finset.sum_const_zero,zero_add,Finset.sum_const,smul_eq_mul] at degreeSum
    have small : 7*(C.size+2) ≤ 7*A.card + 15*Aᶜ.card := by omega
    have least : IsMinimalCircuit n C := by
      refine ⟨hfan,fun D hD he => hmin D.size ⟨D,hD,le_rfl,?_⟩⟩
      exact fun x => congrFun (he.trans hfun) x
    have wide : 7 ≤ G.egirth := SimpleGraph.le_egirth.mpr fun v w hw => by exact_mod_cast hcycle v w hw
    have depends (v : Fin n) : ∃ x y : Fin n → Bool,
        (∀ j, j ≠ v → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y := by
      rw [hfun]
      by_cases hv : v ∈ A
      · let x : Fin n → Bool := fun _ => false
        let y : Fin n → Bool := fun i => decide (i = v)
        have no : f x ≠ true := by simp [hspec,x]
        have yes : f y = true := (hspec y).mpr (Or.inl ⟨v,hv,by simp [y]⟩)
        exact ⟨x,y,fun j hj => by simp [x,y,hj],fun eq => no (eq.trans yes)⟩
      · have deg : (G.neighborFinset v).card = 3 := (G.ncard_neighborSet v).symm.trans (hdeg v hv)
        obtain ⟨t,ht⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset v).card)
        have vt := (G.mem_neighborFinset v t).mp ht
        let x : Fin n → Bool := fun i => decide (i = t)
        let y : Fin n → Bool := fun i => decide (i = t ∨ i = v)
        have yes : f y = true := (hspec y).mpr (Or.inr ⟨v,t,vt,by simp [y],by simp [y]⟩)
        have no : f x ≠ true := by
          intro hx
          rcases (hspec x).mp hx with ⟨a,ha,ax⟩ | ⟨a,b,hab,ax,bx⟩
          · obtain rfl := of_decide_eq_true ax
            exact hend a v vt.symm ha
          · exact hab.ne ((of_decide_eq_true ax).trans (of_decide_eq_true bx).symm)
        exact ⟨x,y,fun j hj => by simp [x,y,hj],fun eq => no (eq.trans yes)⟩
    have cap := capacity n C least depends
    rw [hgraph]
    apply sparse n G A C hdeg wide hend hedge least (hfun.trans hgraph) hread few cheap
    dsimp only at cap ⊢
    omega
  · push_neg at cheap
    obtain ⟨T,inside,hcover,price⟩ := cheap
    have hbudget : A.card + G.edgeFinset.card + T.card ≤ C.size+1 := by omega
    have hdisjoint : Disjoint A T := by
      apply Finset.disjoint_left.mpr
      intro v ha ht
      exact (Finset.mem_compl.mp (inside ht)) ha
    obtain ⟨i,j,hij⟩ := hedge
    have marked_partner : ∃ v ∈ T, ∃ u, G.Adj u v := by
      rcases hcover i j hij with h | h
      · exact ⟨i,h,j,hij.symm⟩
      · exact ⟨j,h,i,hij⟩
    obtain ⟨v,hv,u,huv⟩ := marked_partner
    have hvA : v ∉ A := fun h => (Finset.disjoint_left.mp hdisjoint) h hv
    let H := G.deleteIncidenceSet v
    let T' := T.erase v
    have keep : ∃ j, G.Adj u j ∧ j ≠ v := by
      by_contra! h
      have sub : G.neighborSet u ⊆ {v} := fun j hj =>
        Set.mem_singleton_iff.mpr (h j hj)
      have small := Set.ncard_le_ncard sub
      have deg := hdeg u (hend u v huv)
      rw [deg, Set.ncard_singleton] at small
      omega
    obtain ⟨j,huj,hjv⟩ := keep
    have kept : H.Adj u j := SimpleGraph.deleteIncidenceSet_adj.mpr ⟨huj,huv.ne,hjv⟩
    have no_empty : 0 < H.edgeFinset.card :=
      Finset.card_pos.mpr ⟨s(u,j), SimpleGraph.mem_edgeFinset.mpr kept⟩
    have cover' : ∀ a b : Fin n, H.Adj a b → a ∈ T' ∨ b ∈ T' := by
      intro a b hab
      obtain ⟨old, ha, hb⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hab
      exact (hcover a b old).imp (fun h => Finset.mem_erase.mpr ⟨ha,h⟩)
        (fun h => Finset.mem_erase.mpr ⟨hb,h⟩)
    have he : H.edgeFinset.card = G.edgeFinset.card - 3 := by
      have hd : G.degree v = 3 := (G.ncard_neighborSet v).symm.trans (hdeg v hvA)
      exact (G.card_edgeFinset_deleteIncidenceSet v).trans (by rw [hd])
    have ht : T'.card = T.card - 1 := Finset.card_erase_of_mem hv
    let s := A.card + H.edgeFinset.card + T'.card - 1
    have hs : s + 1 = A.card + H.edgeFinset.card + T'.card := by
      dsimp [s]
      omega
    have size : s + 4 ≤ C.size := by
      have htp := Finset.card_pos.mpr ⟨v,hv⟩
      omega
    have cut := stars n H A T' s (Or.inr ⟨u,j,kept⟩) cover' hs
    have eval_cut :
        (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨
          ∃ i j : Fin n, H.Adj i j ∧ x i = true ∧ x j = true)) =
        (fun x : Fin n → Bool => f (Function.update x v false)) := by
      funext x
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, hspec]
      constructor
      · rintro (⟨a,ha,hxa⟩ | ⟨a,b,hab,hxa,hxb⟩)
        · have haz : a ≠ v := fun e => hvA (e ▸ ha)
          exact Or.inl ⟨a,ha, by simpa [Function.update_of_ne haz] using hxa⟩
        · obtain ⟨old,ha,hb⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hab
          exact Or.inr ⟨a,b,old,
            by simpa [Function.update_of_ne ha] using hxa,
            by simpa [Function.update_of_ne hb] using hxb⟩
      · rintro (⟨a,ha,hxa⟩ | ⟨a,b,hab,hxa,hxb⟩)
        · have haz : a ≠ v := fun e => hvA (e ▸ ha)
          exact Or.inl ⟨a,ha, by simpa [Function.update_of_ne haz] using hxa⟩
        · have ha : a ≠ v := by intro e; simp [e] at hxa
          have hb : b ≠ v := by intro e; simp [e] at hxb
          exact Or.inr ⟨a,b,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hab,ha,hb⟩,
            by simpa [Function.update_of_ne ha] using hxa,
            by simpa [Function.update_of_ne hb] using hxb⟩
    exact ⟨v,hvA,s,size,eval_cut ▸ cut⟩
