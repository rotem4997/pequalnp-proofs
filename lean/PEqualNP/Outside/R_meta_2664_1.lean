import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CrossAnd PEqualNP.GenericRejection

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2664_1
    (clean : ∀ (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      0 < N → Monotone2 C → ComputesIncidence S C →
      crossCount (N+N) (Finset.univ.map (Fin.natAddEmb N)) C = 0 →
      ∃ a b : Fin C.size → Fin N, ∃ t : Fin C.size → Fin 3,
        ∀ p l, p ∈ S l → ∃ g,
          (t g=0 ∧ p=a g ∧ l=b g) ∨
          (t g=1 ∧ a g≠b g ∧ (p=a g ∨ p=b g) ∧ a g ∈ S l ∧ b g ∈ S l) ∨
          (t g=2 ∧ a g≠b g ∧ (l=a g ∨ l=b g) ∧ p ∈ S (a g) ∧ p ∈ S (b g)))
    (peel : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      199 ≤ q → N = q^2+q+1 → (∀ l, (S l).card=q+1) →
      (∀ l m, l ≠ m → ((S l) ∩ (S m)).card ≤ 1) →
      Monotone2 C → ComputesIncidence S C →
      let cost := crossCount (N+N) (Finset.univ.map (Fin.natAddEmb N))
      2*C.size < N*q → 0 < cost C → ∃ D : Circuit, Monotone2 D ∧ ComputesIncidence S D ∧
        cost D < cost C ∧ D.size ≤ C.size + 49)
    :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x14 (Fin.castAdd x2 x15) = Bool.true ∧ x14 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ (x15 : Finset ℕ), (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x16]? = Option.some x17 → x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x16 ∉ x15 → ¬((∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.false)).getD x21 Bool.false ≠ (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.true)).getD x21 Bool.false) ∨ ∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x23)).getD x21 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x23)).getD x21 Bool.false)) → (100 : ℕ) * x15.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq hN degrees joins mono _out _wires positives negatives _marks _covers _few
  let S (l : Fin N) := Finset.univ.filter (fun p => I p l)
  let cost := crossCount (N+N) (Finset.univ.map (Fin.natAddEmb N))
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
  -- Two named points determine at most one line, and two named lines meet in at most one point.
  let lineOf (a b : Fin N) :=
    if e : ∃ l, a ∈ S l ∧ b ∈ S l then e.choose else a
  let pointOf (a b : Fin N) :=
    if e : ∃ p, p ∈ S a ∧ p ∈ S b then e.choose else a
  have joinHit {a b l : Fin N} (ab : a≠b) (ha : a ∈ S l) (hb : b ∈ S l) : lineOf a b = l := by
    have e : ∃ l, a ∈ S l ∧ b ∈ S l := ⟨l,ha,hb⟩
    rw [show lineOf a b = e.choose from dif_pos e]
    exact (joins a b ab).unique ⟨(mem _ _).mp e.choose_spec.1,(mem _ _).mp e.choose_spec.2⟩
      ⟨(mem _ _).mp ha,(mem _ _).mp hb⟩
  have meetHit {a b p : Fin N} (ab : a≠b) (ha : p ∈ S a) (hb : p ∈ S b) : pointOf a b = p := by
    have e : ∃ p, p ∈ S a ∧ p ∈ S b := ⟨p,ha,hb⟩
    rw [show pointOf a b = e.choose from dif_pos e]
    exact Finset.card_le_one.mp (thin a b ab) _ (Finset.mem_inter.mpr e.choose_spec)
      _ (Finset.mem_inter.mpr ⟨ha,hb⟩)
  have base (D : Circuit) (md : Monotone2 D) (correct : ComputesIncidence S D) (hc : cost D=0) :
      N*(q+1) ≤ 2*D.size := by
    obtain ⟨a,b,t,cover⟩ := clean N S D (by omega) md correct hc
    let charge (g : Fin D.size) : Finset (Fin N × Fin N) :=
      if t g=0 then {(a g,b g)} else if t g=1 then
        {(a g,lineOf (a g) (b g)), (b g,lineOf (a g) (b g))}
      else {(pointOf (a g) (b g),a g), (pointOf (a g) (b g),b g)}
    have cap (g : Fin D.size) : (charge g).card ≤ 2 := by
      dsimp only [charge]
      split
      · simp
      · split <;> exact Finset.card_le_two
    have locate (p l : Fin N) (hit : p ∈ S l) : ∃ g, (p,l) ∈ charge g := by
      obtain ⟨g,h | h | h⟩ := cover p l hit
      · obtain ⟨code,rfl,rfl⟩ := h
        exact ⟨g,by simp [charge,code]⟩
      · obtain ⟨code,ab,which,h1,h2⟩ := h
        have line := joinHit ab h1 h2
        rcases which with rfl | rfl <;> exact ⟨g,by simp [charge,code,line]⟩
      · obtain ⟨code,ab,which,h1,h2⟩ := h
        have point := meetHit ab h1 h2
        rcases which with rfl | rfl <;> exact ⟨g,by simp [charge,code,point]⟩
    let fiber (l : Fin N) := (S l) ×ˢ ({l} : Finset (Fin N))
    have disj : ((Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint fiber := by
      intro l _ m _ ne
      apply Finset.disjoint_left.mpr
      rintro ⟨p,k⟩ h1 h2
      have a : k=l := Finset.mem_singleton.mp (Finset.mem_product.mp h1).2
      have b : k=m := Finset.mem_singleton.mp (Finset.mem_product.mp h2).2
      exact ne (a.symm.trans b)
    have coversAll : Finset.univ.biUnion fiber ⊆ Finset.univ.biUnion charge := by
      rintro ⟨p,l⟩ h
      obtain ⟨m,_,hm⟩ := Finset.mem_biUnion.mp h
      obtain ⟨hpt,hs⟩ := Finset.mem_product.mp hm
      obtain rfl := Finset.mem_singleton.mp hs
      obtain ⟨g,hg⟩ := locate p l hpt
      exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,hg⟩
    calc
      N*(q+1) = (Finset.univ.biUnion fiber).card := by
        rw [Finset.card_biUnion disj]
        simp only [fiber,Finset.card_product,Finset.card_singleton,Nat.mul_one,degree,Finset.sum_const,
          Finset.card_univ,Fintype.card_fin,smul_eq_mul]
      _ ≤ _ := Finset.card_le_card coversAll
      _ ≤ ∑ g : Fin D.size, (charge g).card := Finset.card_biUnion_le
      _ ≤ ∑ _g : Fin D.size, 2 := Finset.sum_le_sum (fun g _ => cap g)
      _ = 2*D.size := by simp [Nat.mul_comm]
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
        · simp [op,andLaw]; aesop
        · simp [op,orLaw]; aesop
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
  -- Each eliminated cross AND costs at most 49 additional gates, including all rewiring.
  have priced (k : ℕ) : ∀ D : Circuit, Monotone2 D → ComputesIncidence S D →
      cost D=k → N*q ≤ 2*(D.size+49*k) := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro D md exactD eq
      by_cases zero : k=0
      · have edges := base D md exactD (eq.trans zero)
        rw [Nat.mul_add,Nat.mul_one] at edges
        omega
      · by_cases paid : N*q ≤ 2*D.size
        · omega
        · obtain ⟨D',md',exactD',less,price⟩ := peel q N S D hq hN degree thin md exactD
            (by omega) (show 0 < cost D by omega)
          change cost D' < cost D at less
          have h := ih (cost D') (by omega) D' md' exactD' rfl
          omega
  have result := priced (cost C) C mono computes rfl
  have bounded : cost C ≤ C.size := Finset.card_filter_le _ _ |>.trans_eq (Finset.card_range _)
  omega
