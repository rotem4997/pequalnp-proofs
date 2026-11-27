import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_8935_714
    (used : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → ∀ j < C.size, n + j ≠ C.output → n + j ∈ C.gates.flatMap Gate.inputs)
    (repeatCharge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.IsBipartite → ¬ G.IsAcyclic → NoFourCycle G → IsLeastAO G C → TopForm G C →
      (∃ j < C.size, (gateAt C j).op = .and ∧ ¬ BelowF G C j ∧
        ∃ e f : Fin n × Fin n, s(e.1,e.2) ≠ s(f.1,f.2) ∧
          ∀ q ∈ [e,f], G.Adj q.1 q.2 ∧ readsAtMost C n [q.1.val,q.2.val] 1 = false ∧
            gateVal n C j (pairInput q.1 q.2) = true) →
      ∀ (S : Finset (Fin n)) (f : S → Fin n), Function.Injective f →
        (∀ u : S, f u ∉ S ∧ G.Adj u.val (f u)) →
        let uses := C.gates.flatMap Gate.inputs
        let inputs := uses.toFinset.filter fun w => w < n
        G.edgeFinset.card + S.card - inputs.card ≤ uses.length - uses.toFinset.card)
    : (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∃ x10 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x10 ∧ ∃ (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1) (x14 : Fin x1), x2.Adj x11 x12 ∧ x2.Adj x13 x14 ∧ s(x11, x12) ≠ s(x13, x14) ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x11, ↑x12] (1 : ℕ) = Bool.false ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x13, ↑x14] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) → ∃ (x11 : Finset (Fin x1)), x2.IsVertexCover ↑x11 ∧ x2.edgeFinset.card + x11.card ≤ x4.size + (1 : ℕ)) := by
  classical
  intro n G _ C bip cyclic four least form witness
  obtain ⟨j,hj,op,dirty,a,b,c,d,ab,cd,different,rab,rcd,gab,gcd⟩ := witness
  have bad : ∃ j < C.size, (gateAt C j).op = .and ∧ ¬ BelowF G C j ∧
      ∃ e f : Fin n × Fin n, s(e.1,e.2) ≠ s(f.1,f.2) ∧
        ∀ q ∈ [e,f], G.Adj q.1 q.2 ∧ readsAtMost C n [q.1.val,q.2.val] 1 = false ∧
          gateVal n C j (pairInput q.1 q.2) = true := by
    refine ⟨j,hj,op,dirty,(a,b),(c,d),different,?_⟩
    intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl
    · exact ⟨ab,rab,gab⟩
    · exact ⟨cd,rcd,gcd⟩
  have matching : ∃ T : Finset (Fin n), G.IsVertexCover ↑T ∧
      ∃ f : T → Fin n, Function.Injective f ∧ ∀ u : T, f u ∉ T ∧ G.Adj u.val (f u) := by
    classical
    obtain ⟨color⟩ := bip
    let covers := (Finset.univ : Finset (Finset (Fin n))).filter fun (T : Finset (Fin n)) => G.IsVertexCover (T : Set (Fin n))
    have full : (Finset.univ : Finset (Fin n)) ∈ covers := by simp [covers]
    obtain ⟨T, member, minimal⟩ := covers.exists_min_image Finset.card ⟨_,full⟩
    have cover : G.IsVertexCover ↑T := (Finset.mem_filter.mp member).2
    let nbr (u : T) := Finset.univ.filter fun w : Fin n => w ∉ T ∧ G.Adj u.val w
    have sameSide (U : Finset T) (indep : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u.val v.val) :
        U.card ≤ (U.biUnion nbr).card := by
      let X := U.image (fun u : T => u.val)
      let K := (T \ X) ∪ U.biUnion nbr
      have chooseEnd {v w : Fin n} (edge : G.Adj v w) (hv : v ∈ T) : v ∈ K ∨ w ∈ K := by
        by_cases hx : v ∈ X
        · obtain ⟨u,hu,eu⟩ := Finset.mem_image.mp hx
          by_cases ht : w ∈ T
          · have nw : w ∉ X := by
              intro hw
              obtain ⟨z,hz,ez⟩ := Finset.mem_image.mp hw
              exact indep u hu z hz (eu ▸ ez ▸ edge)
            exact Or.inr (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ht,nw⟩))
          · exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
              ⟨u,hu,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht,eu ▸ edge⟩⟩))
        · exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv,hx⟩))
      have newCover : G.IsVertexCover ↑K := by
        intro v w edge
        rcases cover edge with hv | hw
        · exact chooseEnd edge hv
        · exact (chooseEnd edge.symm hw).symm
      have lower := minimal K (Finset.mem_filter.mpr ⟨Finset.mem_univ _,newCover⟩)
      have upper := Finset.card_union_le (T \ X) (U.biUnion nbr)
      have sub : X ⊆ T := by
        intro x h
        obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp h
        exact u.property
      have eqcard := Finset.card_sdiff_add_card_eq_card sub
      have xe : X.card = U.card := Finset.card_image_of_injective _ Subtype.val_injective
      change T.card ≤ ((T \ X) ∪ U.biUnion nbr).card at lower
      omega
    apply Exists.intro T
    refine ⟨cover,?_⟩
    have hall : ∀ U : Finset T, U.card ≤ (U.biUnion nbr).card := by
      intro U
      let A := U.filter fun u => color u.val = 0
      let B := U.filter fun u => ¬ color u.val = 0
      have cA {u : T} (h : u ∈ A) : color u.val = 0 := (Finset.mem_filter.mp h).2
      have cB {u : T} (h : u ∈ B) : color u.val ≠ 0 := (Finset.mem_filter.mp h).2
      have ca := sameSide A (by
        intro u hu v hv edge
        exact color.valid edge ((cA hu).trans (cA hv).symm))
      have cb := sameSide B (by
        intro u hu v hv edge
        have h := color.valid edge
        have h1 := cB hu
        have h2 := cB hv
        omega)
      have dis : Disjoint (A.biUnion nbr) (B.biUnion nbr) := by
        apply Finset.disjoint_left.mpr
        intro z ha hb
        obtain ⟨a,ham,haz⟩ := Finset.mem_biUnion.mp ha
        obtain ⟨b,hbm,hbz⟩ := Finset.mem_biUnion.mp hb
        have ea := color.valid ((Finset.mem_filter.mp haz).2.2)
        have eb := color.valid ((Finset.mem_filter.mp hbz).2.2)
        have va := cA ham
        have vb := cB hbm
        omega
      have sub : A.biUnion nbr ∪ B.biUnion nbr ⊆ U.biUnion nbr := by
        intro z h
        rcases Finset.mem_union.mp h with h | h
        all_goals
          obtain ⟨u,hu,hn⟩ := Finset.mem_biUnion.mp h
          exact Finset.mem_biUnion.mpr ⟨u,(Finset.mem_filter.mp hu).1,hn⟩
      have lower := Finset.card_le_card sub
      rw [Finset.card_union_of_disjoint dis] at lower
      have sum : A.card + B.card = U.card := Finset.card_filter_add_card_filter_not _
      omega
    obtain ⟨f,inj,valid⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' nbr).mp hall
    exact ⟨f,inj,fun u => (Finset.mem_filter.mp (valid u)).2⟩
  obtain ⟨T,cover,f,inj,hf⟩ := matching
  refine ⟨T,cover,?_⟩
  let uses := C.gates.flatMap Gate.inputs
  let inputs := uses.toFinset.filter fun w => w < n
  let internal := uses.toFinset.filter fun w => ¬ w < n
  have counts : inputs.card + internal.card = uses.toFinset.card :=
    Finset.card_filter_add_card_filter_not _
  have repeated := repeatCharge n G C bip cyclic four least form bad T f inj hf
  change G.edgeFinset.card + T.card - inputs.card ≤ uses.length - uses.toFinset.card at repeated
  have lengths (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length = 2) :
      (gs.flatMap Gate.inputs).length = 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [hg g (by simp), ih (fun g m => hg g (List.mem_cons_of_mem _ m))]
      omega
  have allSlots : uses.length = 2 * C.size := lengths _ least.1.2.2
  have coverGates : (Finset.range C.size).image (fun j => n+j) ⊆ insert C.output internal := by
    intro w hw
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hw
    by_cases out : n+k = C.output
    · exact Finset.mem_insert.mpr (Or.inl out)
    · have member := used n G C least k (Finset.mem_range.mp hk) out
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨List.mem_toFinset.mpr member,by omega⟩))
  have gatesBound := (Finset.card_le_card coverGates).trans (Finset.card_insert_le C.output internal)
  rw [Finset.card_image_of_injective _ (fun a b e => Nat.add_left_cancel e), Finset.card_range] at gatesBound
  have distinct : uses.toFinset.card ≤ uses.length := List.toFinset_card_le uses
  omega
