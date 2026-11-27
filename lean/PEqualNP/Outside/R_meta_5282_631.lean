import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_5282_631
    (existence : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅)
    (shape : ∀ (n : ℕ) (C : Circuit), IsMinimalMonoCircuit n C →
      C.eval (List.ofFn fun _ : Fin n => false) = false →
      (∀ j < C.size, gateVal n C j (fun _ => false) = false) ∧
      ∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ v : Fin n,
        gateVal n C j (pairInput v v) = true →
        (∀ k < j, (gateAt C k).op = GateOp.and →
          gateVal n C k (pairInput v v) = false) →
        ∃ a < j, ∃ b < j, a ≠ b ∧ (gateAt C j).inputs = [n+a,n+b] ∧
          (gateAt C a).op = GateOp.or ∧ (gateAt C b).op = GateOp.or)
    (repair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d) →
      ∀ (C : Circuit), IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
        ∀ (j a b : ℕ) (v : Fin n), j < C.size → a < j → b < j → a ≠ b →
          (gateAt C j).op = GateOp.and → (gateAt C j).inputs = [n+a,n+b] →
          (gateAt C a).op = GateOp.or → (gateAt C b).op = GateOp.or →
          gateVal n C j (pairInput v v) = true →
          (∀ k < j, (gateAt C k).op = GateOp.and → gateVal n C k (pairInput v v) = false) →
          ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
            ∀ k < D.size, (gateAt D k).op = GateOp.and → ∀ u : Fin n,
              gateVal n D k (pairInput u u) = false) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ (∀ (x10 : Fin x1 → Bool), x9.eval (List.ofFn x10) = x4 x10) ∧ (∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → (∀ (x12 : Fin x1 → Bool), x10.eval (List.ofFn x12) = x4 x12) → x9.size ≤ x10.size) ∧ x6 x9 := by
  classical
  intro n G decI
  dsimp only
  intro htri hsquare
  obtain ⟨C,hmin,hC⟩ := existence n G
  have zero (D : Circuit) (hD : circuitFun n D = graphFun G ∅) :
      D.eval (List.ofFn fun _ : Fin n => false) = false := by
    change circuitFun n D (fun _=>false) = false
    rw [hD]
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), (fun _ : Fin n => false) a = true) ||
      decide (∃ u v : Fin n, G.Adj u v ∧ false = true ∧ false = true)) = false
    simp
  have existsClean : ∃ D : Circuit, IsMinimalMonoCircuit n D ∧
      circuitFun n D = graphFun G ∅ ∧ ∀ k<D.size,
        (gateAt D k).op = GateOp.and → ∀ u : Fin n,
          gateVal n D k (pairInput u u) = false := by
    by_cases good : ∀ k<C.size, (gateAt C k).op = GateOp.and → ∀ u : Fin n,
        gateVal n C k (pairInput u u) = false
    · exact ⟨C,hmin,hC,good⟩
    · push Not at good
      obtain ⟨j,hj,hA,v,ht⟩ := good
      let bad (k : ℕ) := k < C.size ∧ (gateAt C k).op = GateOp.and ∧
        gateVal n C k (pairInput v v) = true
      have hb : ∃ k, bad k := ⟨j,hj,hA,by simpa using ht⟩
      obtain ⟨hk,hop,hbad⟩ := Nat.find_spec hb
      have prev : ∀ k < Nat.find hb, (gateAt C k).op = GateOp.and →
          gateVal n C k (pairInput v v) = false := by
        intro k hlt ha
        cases hv : gateVal n C k (pairInput v v)
        · rfl
        · exact False.elim (Nat.find_min hb hlt ⟨hlt.trans hk,ha,hv⟩)
      obtain ⟨a,ha,b,hb',hne,hins,ho1,ho2⟩ :=
        (shape n C hmin (zero C hC)).2 _ hk hop v hbad prev
      exact repair n G htri hsquare C hmin hC _ a b v hk ha hb' hne hop hins ho1 ho2 hbad prev
  obtain ⟨D,hD,hfun,hgood⟩ := existsClean
  have ev (x : Fin n→Bool) : D.eval (List.ofFn x) =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
    change circuitFun n D x = _
    rw [hfun]
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) = _
    simp
  refine ⟨D,hD.1,ev,?_,?_⟩
  · intro E hm he
    apply hD.2 E hm
    funext x
    exact (he x).trans (ev x).symm
  · intro j g hg hop S hs
    have hj : j<D.size := (List.getElem?_eq_some_iff.mp hg).choose
    have hAt : gateAt D j = g := by
      change D.gates.getD j ⟨GateOp.or,[]⟩ = g
      simp [List.getD_eq_getElem?_getD,hg]
    have hAnd : (gateAt D j).op = GateOp.and := hAt ▸ hop
    cases hcard : S.card with
    | zero =>
      have hS := Finset.card_eq_zero.mp hcard
      subst S
      have hInputs : (fun w : Fin n => decide (w∈(∅ : Finset (Fin n)))) = fun _ => false := by
        funext w; simp
      rw [hInputs]
      exact (shape n D hD (zero D hfun)).1 j hj
    | succ k =>
      have hon : S.card = 1 := by omega
      obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hon
      have hInputs : (fun w : Fin n => decide (w∈({v} : Finset (Fin n)))) = pairInput v v := by
        funext w
        change decide (w ∈ ({v} : Finset (Fin n))) = decide (w=v ∨ w=v)
        simp
      rw [hInputs]
      exact hgood j hj hAnd v
