import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- A repair below the star budget only needs to reduce the number of unowned AND gates.
-- Edge pairs and maximal independent sets suffice to check that it preserves the function.
theorem PEqualNP.Outside.R_meta_4624_1
    (stars : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)),
      CoverPromise.IsVertexCover G T → ∃ C : Circuit, Monotone2 C ∧
        circuitFun n C = graphFun G ∅ ∧ C.size ≤ G.edgeSet.ncard + T.card - 1 ∧
        ∀ j < C.size, (gateAt C j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n C j u v)
    (lower : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
      (D : Circuit), (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      (∃ u v, G.Adj u v) → (∀ u, G.degree u ≠ 1) →
      IsMinCover G T → Monotone2 D → circuitFun n D = graphFun G ∅ →
      G.support.ncard + T.card ≤ D.size + 1 ∧ (D.size + 1 < G.edgeFinset.card + T.card →
        8 ≤ G.support.ncard ∧ ((∃ (u : Fin n) (w : G.Walk u u), w.IsCycle ∧ 5 ≤ w.length ∧ w.length ≤ 6) ∨
        ∃ u v, u ≠ v ∧ 3 ≤ G.degree u ∧ 3 ≤ G.degree v ∧ ∃ w : G.Walk u v, w.length ≤ 6)))
    (boundary : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      Monotone2 C → (∀ u v, G.Adj u v → circuitFun n C (pairInput u v) = true) →
      (∀ S : Finset (Fin n), Maximal (fun T : Finset (Fin n) => G.IsIndepSet T) S →
        circuitFun n C (fun i => decide (i ∈ S)) = false) → circuitFun n C = graphFun G ∅)
    (repair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      let bad := fun C : Circuit => {j : ℕ | j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        ∀ u v, G.Adj u v → ¬Owns n C j u v}.ncard
      ∀ (T : Finset (Fin n)) (D : Circuit), (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      (∀ u, G.degree u ≠ 1) → IsMinCover G T → IsMinimalMonoCircuit n D →
      circuitFun n D = graphFun G ∅ → G.support.ncard + T.card ≤ D.size + 1 →
      D.size + 1 < G.edgeFinset.card + T.card → 8 ≤ G.support.ncard →
      ((∃ (u : Fin n) (w : G.Walk u u), w.IsCycle ∧ 5 ≤ w.length ∧ w.length ≤ 6) ∨
        ∃ u v, u ≠ v ∧ 3 ≤ G.degree u ∧ 3 ≤ G.degree v ∧ ∃ w : G.Walk u v, w.length ≤ 6) →
      0 < bad D → ∃ E : Circuit, Monotone2 E ∧ E.size ≤ D.size ∧ bad E < bad D ∧
        (∀ u v, G.Adj u v → circuitFun n E (pairInput u v) = true) ∧
        ∀ S : Finset (Fin n), Maximal (fun T : Finset (Fin n) => G.IsIndepSet T) S →
          circuitFun n E (fun i => decide (i ∈ S)) = false) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 : Fin x1), x2.degree x7 ≠ (1 : ℕ)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 ∧ PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x9 < x8.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x8 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ PEqualNP.EdgeOwnership.Owns x1 x8 x9 x12 x13 := by
  intro n G _ tri sq edge leaf
  classical
  let cover (k : ℕ) := ∃ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) ∧ T.card = k
  have covers : ∃ k, cover k := ⟨_,Finset.univ,fun {_ _} _ => Or.inl (Finset.mem_univ _),rfl⟩
  obtain ⟨T,ct,card⟩ := Nat.find_spec covers
  have mt : IsMinCover G T := ⟨ct,fun S hs => card ▸ Nat.find_min' covers ⟨S,hs,rfl⟩⟩
  obtain ⟨C,mc,fc,cost,owned⟩ := stars n G T (fun _ _ e => ct e)
  rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset] at cost
  have nonempty : 0 < G.edgeFinset.card := by
    obtain ⟨u,v,e⟩ := edge
    exact Finset.card_pos.mpr ⟨s(u,v),by simpa using e⟩
  let feasible (s : ℕ) := ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = s
  have existsSize : ∃ s, feasible s := ⟨_,C,mc,fc,rfl⟩
  obtain ⟨D,md,fd,sd⟩ := Nat.find_spec existsSize
  have least (E : Circuit) (me : Monotone2 E) (fe : circuitFun n E = graphFun G ∅) : D.size ≤ E.size :=
    sd ▸ Nat.find_min' existsSize ⟨E,me,fe,rfl⟩
  have finish (E : Circuit) (me : Monotone2 E) (fe : circuitFun n E = graphFun G ∅)
      (bound : E.size ≤ D.size) : IsMinimalMonoCircuit n E :=
    ⟨me,fun F mf eq => bound.trans (least F mf (eq.trans fe))⟩
  by_cases cheap : D.size + 1 < G.edgeFinset.card + T.card
  · let unowned (E : Circuit) := {j : ℕ | j < E.gates.length ∧ (gateAt E j).op = GateOp.and ∧
        ∀ u v, G.Adj u v → ¬Owns n E j u v}
    let admissible (k : ℕ) := ∃ F : Circuit, Monotone2 F ∧ circuitFun n F = graphFun G ∅ ∧
      F.size = D.size ∧ (unowned F).ncard = k
    have candidates : ∃ k, admissible k := ⟨_,D,md,fd,rfl,rfl⟩
    obtain ⟨F,mf,ff,sf,count⟩ := Nat.find_spec candidates
    have opt := finish F mf ff sf.le
    refine ⟨F,opt,ff,?_⟩
    intro j hj hand
    by_contra missing
    have member : j ∈ unowned F := ⟨hj,hand,fun u v adj owns => missing ⟨u,v,adj,owns⟩⟩
    have finite : (unowned F).Finite :=
      (Finset.range F.gates.length).finite_toSet.subset (fun _ h => Finset.mem_range.mpr h.1)
    have positive := (Set.ncard_pos finite).mpr ⟨j,member⟩
    obtain ⟨floor,near⟩ := lower n G T F tri sq edge leaf mt mf ff
    have below : F.size + 1 < G.edgeFinset.card + T.card := by simpa [sf] using cheap
    obtain ⟨order,obstruction⟩ := near below
    obtain ⟨E,me,sz,drop,pos,neg⟩ := repair n G T F tri sq leaf mt opt ff floor below order obstruction positive
    have fe := boundary n G E me pos neg
    have eqSize := le_antisymm (sz.trans sf.le) (least E me fe)
    have best := Nat.find_min' candidates (show admissible (unowned E).ncard from ⟨E,me,fe,eqSize,rfl⟩)
    change (unowned E).ncard < (unowned F).ncard at drop
    omega
  · exact ⟨C,finish C mc fc (by omega),fc,owned⟩
