import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.SharedBlockCost

-- The compiler gets one product slot per gate, with a second orientation and
-- 94 extra side-OR gates per syntactic cross AND. Guard reuse is priced below.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2664_317
    (extract : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      199 ≤ q → N=q^2+q+1 → (∀ l, (S l).card = q+1) → (∀ l m, l ≠ m → ((S l) ∩ (S m)).card ≤ 1) →
      Monotone2 C → ComputesIncidence S C →
      let c := PEqualNP.CrossAnd.crossCount (N+N) (Finset.univ.map (Fin.natAddEmb N)) C
      ∃ (k r t : ℕ) (A B : Fin k → Finset (Fin N)), k ≤ C.size+c ∧ r+t ≤ 2*C.size+94*c ∧
      HasOrCost N (Finset.univ.image A) r ∧ HasOrCost N (Finset.univ.image B) t ∧
      ∀ l, ∀ p ∈ S l, ∃ i, p ∈ A i ∧ l ∈ B i ∧
        (((2 ≤ (B i).card ∨ (A i).card ≤ 1) ∧ (∀ v ∈ B i, p ∈ S v)) ∨ ((2 ≤ (A i).card ∨ (B i).card ≤ 1) ∧ (∀ u ∈ A i, u ∈ S l))))
    (stars : ∀ (N k r t : ℕ) (S : Fin N → Finset (Fin N)) (A B P L : Fin k → Finset (Fin N)),
      (∀ l m, l ≠ m → ((S l) ∩ (S m)).card ≤ 1) → HasOrCost N (Finset.univ.image A) r → HasOrCost N (Finset.univ.image B) t →
      (∀ i, (P i).card ≤ 1 ∧ (L i).card ≤ 1) →
      (∀ i, ∀ p ∈ P i, ∀ l ∈ B i, p ∈ S l) → (∀ i, ∀ l ∈ L i, A i ⊆ S l) →
      (∀ l, ∀ p ∈ S l, ∃ i, (p ∈ P i ∧ l ∈ B i) ∨ (p ∈ A i ∧ l ∈ L i)) →
      (∑ l, (S l).card) ≤ r+t+2*k) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x14 (Fin.castAdd x2 x15) = Bool.true ∧ x14 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ (x15 : Finset ℕ), (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x16]? = Option.some x17 → x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x16 ∉ x15 → ¬((∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.false)).getD x21 Bool.false ≠ (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.true)).getD x21 Bool.false) ∨ ∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x23)).getD x21 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x23)).getD x21 Bool.false)) → (100 : ℕ) * x15.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq hN degrees joins mono _out _wires positives negatives _marks _covers _few
  let S (l : Fin N) := Finset.univ.filter (fun p => I p l)
  have mem (p l : Fin N) : p ∈ S l ↔ I p l := by simp [S]
  have degree (l : Fin N) : (S l).card=q+1 := by
    simpa only [S,Fintype.card_subtype] using degrees l
  have thin (l m : Fin N) (ne : l≠m) : (S l ∩ S m).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra h
    obtain ⟨t,_,unique⟩ := joins a b h
    have la := Finset.mem_inter.mp ha
    have lb := Finset.mem_inter.mp hb
    exact ne ((unique _ ⟨(mem a l).mp la.1,(mem b l).mp lb.1⟩).trans
      (unique _ ⟨(mem a m).mp la.2,(mem b m).mp lb.2⟩).symm)
  -- A monotone circuit correct on the incidence pairs and all independent sets computes incidence.
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let rel (a b : List Bool) := a.length=b.length ∧ ∀ i, a.getD i false=true → b.getD i false=true
  have push (w : List Bool) (v : Bool) (i : ℕ) :
      (w++[v]).getD i false = if i=w.length then v else w.getD i false := by
    by_cases hl : i<w.length
    · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hl,Nat.ne_of_lt hl]
    · rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
      by_cases he : i=w.length
      · simp [he]
      · simp [he,List.getElem?_eq_none (by omega : w.length ≤ i),List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp;omega : [v].length ≤ i-w.length)]
  have andLaw (z : List Bool) : GateOp.and.eval z = z.all id := rfl
  have orLaw (z : List Bool) : GateOp.or.eval z = z.any id := rfl
  have grows (gs : List Gate) (good : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) (a b : List Bool)
      (le : rel a b) : rel (gs.foldl step a) (gs.foldl step b) := by
    induction gs generalizing a b with
    | nil => exact le
    | cons g gs ih =>
      apply ih (fun k hk => good k (List.mem_cons_of_mem g hk))
      refine ⟨by simp [step,le.1],?_⟩
      intro i
      simp only [step,push,le.1]
      split
      · have hh := le.2
        rcases good g List.mem_cons_self with op | op
        · simpa only [op,andLaw,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] using
            (fun (ha : ∀ j ∈ g.inputs, a.getD j false = true) j hj => hh j (ha j hj))
        · simp only [op,orLaw,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
          rintro ⟨j,hj,hv⟩
          exact ⟨j,hj,hh j hv⟩
      · exact le.2 i
  have funMono (x y : Fin (N+N) → Bool) (h : ∀ i, x i=true → y i=true) :
      circuitFun (N+N) C x=true → circuitFun (N+N) C y=true := by
    apply (grows C.gates (fun g hg => (mono g hg).1) (List.ofFn x) (List.ofFn y) _).2 C.output
    refine ⟨by simp,?_⟩
    intro i
    by_cases hi : i<N+N
    · simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,dite_true,Option.getD_some] using h ⟨i,hi⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp
  have computes : ComputesIncidence S C := by
    intro X Y
    let z := Fin.append (fun p : Fin N => decide (p ∈ X)) (fun l : Fin N => decide (l ∈ Y))
    have bridge : List.ofFn z = incidenceInput X Y := List.ofFn_fin_append _ _
    change C.eval (incidenceInput X Y) = _
    rw [← bridge]
    change circuitFun (N+N) C z = _
    have point (p : Fin N) : z (Fin.castAdd N p) = true ↔ p ∈ X := by simp [z]
    have line (l : Fin N) : z (Fin.natAdd N l) = true ↔ l ∈ Y := by simp only [z,Fin.append_right,decide_eq_true_eq]
    by_cases hit : ∃ p ∈ X, ∃ l ∈ Y, p ∈ S l
    · rw [show incidenceFun S X Y = true from decide_eq_true hit]
      obtain ⟨p,hp,l,hl,inc⟩ := hit
      apply funMono _ z _ (positives p l ((mem p l).mp inc))
      intro i hi
      rcases of_decide_eq_true hi with rfl | rfl
      · exact (point p).mpr hp
      · exact (line l).mpr hl
    · rw [show incidenceFun S X Y = false from decide_eq_false hit]
      apply negatives z
      rintro ⟨p,l,inc,hp,hl⟩
      exact hit ⟨p,(point p).mp hp,l,(line l).mp hl,(mem p l).mpr inc⟩
  obtain ⟨k,r,t,A,B,hk,hrt,ha,hb,cover⟩ := extract q N S C hq hN degree thin mono computes
  let P (i : Fin k) := (A i).filter (fun p => (2 ≤ (B i).card ∨ (A i).card ≤ 1) ∧ (∀ v ∈ B i, p ∈ S v))
  let L (i : Fin k) := (B i).filter (fun l => (2 ≤ (A i).card ∨ (B i).card ≤ 1) ∧ (∀ u ∈ A i, u ∈ S l))
  have cap (i : Fin k) : (P i).card ≤ 1 ∧ (L i).card ≤ 1 := by
    constructor
    · apply Finset.card_le_one.mpr
      intro p hp p' hp'
      obtain ⟨hp,hsize,hguard⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp',_,hguard'⟩ := Finset.mem_filter.mp hp'
      rcases hsize with wide | narrow
      · obtain ⟨l,hl,m,hm,ne⟩ := Finset.one_lt_card.mp (by omega : 1 < (B i).card)
        exact Finset.card_le_one.mp (thin l m ne) _ (Finset.mem_inter.mpr ⟨hguard _ hl,hguard _ hm⟩)
          _ (Finset.mem_inter.mpr ⟨hguard' _ hl,hguard' _ hm⟩)
      · exact Finset.card_le_one.mp narrow _ hp _ hp'
    · apply Finset.card_le_one.mpr
      intro l hl m hm
      obtain ⟨hl,hsize,hguard⟩ := Finset.mem_filter.mp hl
      obtain ⟨hm,_,hguard'⟩ := Finset.mem_filter.mp hm
      rcases hsize with wide | narrow
      · by_contra ne
        have sub : A i ⊆ S l ∩ S m := fun p hp => Finset.mem_inter.mpr ⟨hguard p hp,hguard' p hp⟩
        have small := (Finset.card_le_card sub).trans (thin l m ne)
        omega
      · exact Finset.card_le_one.mp narrow _ hl _ hm
  have total := stars N k r t S A B P L thin ha hb cap
    (fun i _ hp => (Finset.mem_filter.mp hp).2.2)
    (fun i _ hl _ hp => (Finset.mem_filter.mp hl).2.2 _ hp)
    (by
      intro l p hpl
      obtain ⟨i,hp,hl,h⟩ := cover l p hpl
      exact ⟨i,h.elim (fun h => Or.inl ⟨Finset.mem_filter.mpr ⟨hp,h⟩,hl⟩)
        (fun h => Or.inr ⟨hp,Finset.mem_filter.mpr ⟨hl,h⟩⟩)⟩)
  simp only [degree, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at total
  rw [Nat.mul_add, Nat.mul_one] at total
  have bounded : PEqualNP.CrossAnd.crossCount (N+N) (Finset.univ.map (Fin.natAddEmb N)) C ≤ C.size :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  omega
