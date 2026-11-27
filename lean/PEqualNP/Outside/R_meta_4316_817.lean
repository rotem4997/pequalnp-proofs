import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_4316_817
    (essential : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      ∀ j < C.size, ∀ v : Fin n, gateVal n C j (pairInput v v) = true →
        ∃ a b : Fin n, G.Adj a b ∧ a ≠ v ∧ b ≠ v ∧
          circuitFun n ⟨C.gates.set j ⟨GateOp.or, [(v : ℕ)]⟩, C.output⟩ (pairInput a b) = false)
    (repair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      let clean := fun (D : Circuit) (i : ℕ) =>
        (gateAt D i).op = GateOp.and → ∀ w : Fin n, gateVal n D i (pairInput w w) = false
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      ∀ j < C.size, (∀ i < j, clean C i) → (gateAt C j).op = GateOp.and →
      ∀ v a b : Fin n, gateVal n C j (pairInput v v) = true → G.Adj a b → a ≠ v → b ≠ v →
        circuitFun n ⟨C.gates.set j ⟨GateOp.or, [(v : ℕ)]⟩, C.output⟩ (pairInput a b) = false →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
          D.size ≤ C.size ∧ ∀ i ≤ j, clean D i) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → x2.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x10.size ≤ x7.size ∧ ∀ x11 < x10.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x10 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x14 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x10 x11 (PEqualNP.EdgeOwnership.pairInput x14 x14) = Bool.false := by
  classical
  intro n G inst htri hsquare _ C hC hG
  let fits (D : Circuit) := Monotone2 D ∧ circuitFun n D = graphFun G ∅
  let clean (D : Circuit) (j : ℕ) := (gateAt D j).op = GateOp.and →
    ∀ v : Fin n, gateVal n D j (pairInput v v) = false
  have existsSize : ∃ k : ℕ, ∃ D : Circuit, fits D ∧ D.size = k := ⟨C.size, C, ⟨hC,hG⟩, rfl⟩
  let k := Nat.find existsSize
  have lower (D : Circuit) (hD : fits D) : k ≤ D.size :=
    Nat.find_min' existsSize ⟨D, hD, rfl⟩
  have grow : ∀ i ≤ k, ∃ D : Circuit, fits D ∧ D.size = k ∧ ∀ q < i, clean D q := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨D,hD,hs⟩ := Nat.find_spec existsSize
      exact ⟨D,hD,hs,by simp⟩
    | succ i ih =>
      intro hik
      obtain ⟨D,hD,hs,hprefix⟩ := ih (by omega)
      by_cases hc : clean D i
      · refine ⟨D,hD,hs,?_⟩
        intro q hq
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hq) with h | rfl
        · exact hprefix q h
        · exact hc
      · have hmin : IsMinimalMonoCircuit n D := by
          refine ⟨hD.1,?_⟩
          intro T hT he
          rw [hs]
          exact lower T ⟨hT,he.trans hD.2⟩
        have hop : (gateAt D i).op = GateOp.and := by
          by_contra h
          exact hc fun he => False.elim (h he)
        obtain ⟨v,hv⟩ : ∃ v : Fin n, gateVal n D i (pairInput v v) = true := by
          by_contra! h
          exact hc fun _ v => by simpa using h v
        have hi : i < D.size := by omega
        obtain ⟨a,b,hab,ha,hb,hlost⟩ := essential n G D hmin hD.2 i hi v hv
        obtain ⟨T,hm,he,hlen,hnew⟩ :=
          repair n G htri hsquare D hmin hD.2 i hi hprefix hop v a b hv hab ha hb hlost
        exact ⟨T,⟨hm,he⟩,le_antisymm (hlen.trans_eq hs) (lower T ⟨hm,he⟩),
          fun q hq => hnew q (Nat.le_of_lt_succ hq)⟩
  obtain ⟨D,hD,hs,hprefix⟩ := grow k (le_refl k)
  refine ⟨D,hD.1,hD.2,hs.le.trans (lower C ⟨hC,hG⟩),?_⟩
  intro j hj
  exact hprefix j (hj.trans_le hs.le)
