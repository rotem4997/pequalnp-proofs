import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_1780_78
    (priced : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ → ℕ),   (∀ (x6 x7 : Fin x1), x6 ≠ x7 → ∃! x9 : Fin x1, x6 ∈ x3 x9 ∧ x7 ∈ x3 x9) →     PEqualNP.MetaComplexity.Monotone2 x4 →       have x8 : Finset (Fin x1) → Finset (Fin x1) → ℕ → Bool := fun (x8 x9 : Finset (Fin x1)) (x10 : ℕ) => (x4.wires (PEqualNP.GenericRejection.incidenceInput x8 x9)).getD x10 Bool.false;       have x9 : Finset (Fin x1) → Finset (Fin x1) → Prop := fun (x9 x10 : Finset (Fin x1)) => ∃ x11 < x2, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x11).inputs.length = (2 : ℕ) ∧ ∃ (x12 : Fin (2 : ℕ)), (x8 x9 ∅ (PEqualNP.TopForm.opnd x4 x11 x12) && x8 ∅ x10 (PEqualNP.TopForm.opnd x4 x11 ((1 : Fin (2 : ℕ)) - x12)) && (x8 x9 ∅ (x5 x11) || x8 ∅ x10 (x5 x11))) = Bool.true;       (∀ (x10 x11 : Finset (Fin x1)), x9 x10 x11 → PEqualNP.GenericRejection.incidenceFun x3 x10 x11 = Bool.true) → ∀ (x11 : Finset (Fin x1 × Fin x1)), (∀ x12 ∈ x11, x9 {x12.1} {x12.2}) → x11.card ≤ (2 : ℕ) * x4.size + (4 : ℕ) * x2)
    (residual : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
    199 ≤ q → n=q^2+q+1 → (∀ l, (S l).card=q+1) →
    (∀ p r, p≠r → ∃! l, p∈S l ∧ r∈S l) → Monotone2 C → RightOnIncidentPairs S C →
    (∀ X Y, C.eval (incidenceInput X Y)=true → incidenceFun S X Y=true) →
    ∃ (D : Circuit) (k : ℕ → ℕ), Monotone2 D ∧ D.gates.take C.size=C.gates ∧ D.size ≤ 5*C.size+2 ∧
    have W := fun (X Y : Finset (Fin n)) (i : ℕ) => (D.wires (incidenceInput X Y)).getD i false
    have h : Finset (Fin n) → Finset (Fin n) → Prop := fun (X Y : Finset (Fin n)) => ∃ j<C.size, (gateAt D j).op=.and ∧ (gateAt D j).inputs.length=2 ∧ ∃ b : Fin 2,
      (W X ∅ (opnd D j b) && W ∅ Y (opnd D j (1-b)) && (W X ∅ (k j) || W ∅ Y (k j))) = true
    (∀ X Y, h X Y → incidenceFun S X Y=true) ∧
    ∀ E : Finset (Fin n × Fin n), (∀ e∈E, e.1∈S e.2 ∧ ¬h {e.1} {e.2}) → E.card ≤ 86*C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q n I dec C hq hn degree join mon pos neg
  let S (l : Fin n) := Finset.univ.filter (fun p => I p l)
  have memS (p l : Fin n) : p∈S l ↔ I p l := by simp [S]
  have deg (l : Fin n) : (S l).card=q+1 := by
    have h := degree l
    simpa [S,Fintype.card_subtype] using h
  have unique (p r : Fin n) (ne : p≠r) : ∃! l, p∈S l ∧ r∈S l := by
    simpa only [memS] using join p r ne
  have right : RightOnIncidentPairs S C := by
    intro l p hp
    let x : Fin (n+n) → Bool := Fin.addCases (fun i => decide (i∈({p}:Finset (Fin n))))
      (fun i => decide (i∈({l}:Finset (Fin n))))
    have row : List.ofFn x = incidenceInput {p} {l} := List.ofFn_fin_append _ _
    have apart (a b : Fin n) : Fin.castAdd n a ≠ Fin.natAdd n b := by
      intro e
      have v := congrArg Fin.val e
      simp only [Fin.val_castAdd,Fin.val_natAdd] at v
      omega
    have fn : x = (fun i => decide (i=Fin.castAdd n p ∨ i=Fin.natAdd n l)) := by
      funext i
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · change x (Fin.castAdd n a) = decide (Fin.castAdd n a = Fin.castAdd n p ∨ Fin.castAdd n a = Fin.natAdd n l)
        rw [show x (Fin.castAdd n a) = decide (a∈({p}:Finset (Fin n))) from Fin.addCases_left ..]
        simp only [Finset.mem_singleton,Fin.castAdd_inj,apart a l,or_false]
      · change x (Fin.natAdd n b) = decide (Fin.natAdd n b = Fin.castAdd n p ∨ Fin.natAdd n b = Fin.natAdd n l)
        rw [show x (Fin.natAdd n b) = decide (b∈({l}:Finset (Fin n))) from Fin.addCases_right ..]
        simp only [Finset.mem_singleton,Fin.natAdd_inj,Ne.symm (apart p b),false_or]
    rw [← row]
    change circuitFun (n+n) C x=true
    rw [fn]
    exact pos p l ((memS p l).mp hp)
  have sound (X Y : Finset (Fin n)) (hit : C.eval (incidenceInput X Y)=true) :
      incidenceFun S X Y=true := by
    let z : Fin (n+n) → Bool := Fin.addCases (fun p => decide (p∈X)) (fun l => decide (l∈Y))
    have row : List.ofFn z = incidenceInput X Y := List.ofFn_fin_append _ _
    change decide _ = true
    apply decide_eq_true
    by_contra miss
    have off := neg z (by
      rintro ⟨p,l,inc,hp,hl⟩
      have vp : z (Fin.castAdd n p)=decide (p∈X) := Fin.addCases_left ..
      have vl : z (Fin.natAdd n l)=decide (l∈Y) := Fin.addCases_right ..
      rw [vp] at hp
      rw [vl] at hl
      exact miss ⟨p,of_decide_eq_true hp,l,of_decide_eq_true hl,(memS p l).mpr inc⟩)
    change C.eval (List.ofFn z)=false at off
    rw [row,hit] at off
    contradiction
  obtain ⟨D,k,model,pre,size,conditions⟩ := residual q n S C hq hn deg unique mon right sound
  let W := fun (X Y : Finset (Fin n)) (i : ℕ) => (D.wires (incidenceInput X Y)).getD i false
  let h := fun (X Y : Finset (Fin n)) => ∃ j<C.size, (gateAt D j).op=.and ∧ (gateAt D j).inputs.length=2 ∧ ∃ b : Fin 2,
      W X ∅ (opnd D j b) && W ∅ Y (opnd D j (1-b)) && (W X ∅ (k j) || W ∅ Y (k j))
  have safe : ∀ X Y, h X Y → incidenceFun S X Y=true := conditions.1
  let flags := Finset.univ.filter (fun e : Fin n × Fin n => e.1∈S e.2)
  let good := flags.filter (fun e => h {e.1} {e.2})
  let bad := flags.filter (fun e => ¬h {e.1} {e.2})
  have A : good.card ≤ 2*D.size+4*C.size :=
    priced n C.size S D k unique model safe good (fun _ he => (Finset.mem_filter.mp he).2)
  have B : bad.card ≤ 86*C.size := conditions.2 bad (by
    intro e he
    have h' := Finset.mem_filter.mp he
    exact ⟨(Finset.mem_filter.mp h'.1).2,h'.2⟩)
  have part : good.card + bad.card = flags.card := Finset.card_filter_add_card_filter_not _
  have total : flags.card=n*(q+1) := by
    let swap : {e : Fin n × Fin n // e.1∈S e.2} ≃ (Σ l : Fin n, {p // p∈S l}) :=
      { toFun := fun e => ⟨e.1.2,e.1.1,e.2⟩
        invFun := fun d => ⟨(d.2.1,d.1),d.2.2⟩
        left_inv := fun e => by rcases e with ⟨⟨a,b⟩,h⟩; rfl
        right_inv := fun d => by rcases d with ⟨l,p,h⟩; rfl }
    calc
      flags.card = Fintype.card {e : Fin n × Fin n // e.1∈S e.2} := by simp [flags,Fintype.card_subtype]
      _ = _ := Fintype.card_congr swap
      _ = _ := by simp [Fintype.card_sigma,deg]
  rw [Nat.mul_add,Nat.mul_one] at total
  omega
