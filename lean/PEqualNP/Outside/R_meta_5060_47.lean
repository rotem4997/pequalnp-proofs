import PEqualNP.Defs

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- The low-clash child concentrates the 105 incidences in one large gate.
-- Every vertex must then occur outside that gate. A sole outside occurrence
-- must be a singleton operand, which the 38 operands cannot supply for all 42 vertices.
-- Four gates consequently accept a pair of points or a pair of lines.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_5060_47
    (concentrate : let G := SimpleGraph.fromRel fun a b : Fin 42 => a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val)%21 ∈ ([0,5,7,17,20] : List Nat)
      ∀ C : AndCountCircuit 42, C.Computes G → C.outVars=∅ →
      (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) → C.size=19 → (∀ v : Fin 42, {i : Fin C.size | v∈C.leftVars i ∨ v∈C.rightVars i}.ncard≤3) →
      {j : Fin C.size | ∃ a∈C.leftVars j, ∃ b∈C.rightVars j, (a.val<21 ↔ b.val<21)}.ncard≤3 →
      ∃ k : Fin C.size, 7≤(C.leftVars k).card ∧ 7≤(C.rightVars k).card ∧
        (∑ j∈Finset.univ.erase k,((C.leftVars j).card+(C.rightVars j).card))≤42)
    (geometry : let G := SimpleGraph.fromRel fun a b : Fin 42 => a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val)%21 ∈ ([0,5,7,17,20] : List Nat)
      ∀ C : AndCountCircuit 42, C.Computes G → C.outVars=∅ →
      (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) →
      C.size=19 → (∀ v : Fin 42, {i : Fin C.size | v∈C.leftVars i ∨ v∈C.rightVars i}.ncard≤3) →
      (∀ p l : Fin 42, p.val<21 → 21≤l.val → ¬G.Adj p l →
        {i : Fin C.size | p∈C.leftVars i ∨ p∈C.rightVars i ∨ l∈C.leftVars i ∨ l∈C.rightVars i}.ncard≤5) →
      4≤{j : Fin C.size | ∃ a∈C.leftVars j, ∃ b∈C.rightVars j, (a.val<21 ↔ b.val<21)}.ncard →
      5≤{j : Fin C.size | ∃ a∈C.leftVars j, ∃ b∈C.rightVars j, ¬G.Adj a b}.ncard ∧ (∃ j : Fin C.size, let a := (C.leftVars j).card; let b := (C.rightVars j).card; (5≤ min a b ∧ 6≤ max a b) ∨ (4≤ min a b ∧ 14≤ max a b)))
    (readProfile : let G := SimpleGraph.fromRel fun a b : Fin 42 => a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val)%21 ∈ ([0,5,7,17,20] : List Nat)
  ∀ C : PEqualNP.AndCount.AndCountCircuit 42, C.Computes G → C.outVars=∅ →
    (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) → C.size=19 →
    (∀ v : Fin 42, {j : Fin C.size | v∈C.leftVars j ∨ v∈C.rightVars j}.ncard≤3) →
    let degree (v : Fin 42) := {j : Fin C.size | v∈C.leftVars j ∨ v∈C.rightVars j}.ncard
    let p := {v : Fin 42 | v.val<21 ∧ degree v≤1}.ncard
    let l := {v : Fin 42 | 21≤v.val ∧ degree v≤1}.ncard
    p.choose 2+l≤8 ∧ l.choose 2+p≤8 ∧ p+l≤6 ∧ ∃ v : Fin 42, degree v=3)
    (remaining : let G := SimpleGraph.fromRel fun a b : Fin 42 => a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val)%21 ∈ ([0,5,7,17,20] : List Nat)
      ∀ C : AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars=∅ →
      (∀ i v,C.gateVal {v} i=false) → (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) →
      C.size=19 → (∀ v : Fin 42, {i : Fin C.size | v∈C.leftVars i ∨ v∈C.rightVars i}.ncard≤3) →
      (∀ p l : Fin 42, p.val<21 → 21≤l.val → ¬G.Adj p l →
        {i : Fin C.size | p∈C.leftVars i ∨ p∈C.rightVars i ∨ l∈C.leftVars i ∨ l∈C.rightVars i}.ncard≤5) →
      4≤{j : Fin C.size | ∃ a∈C.leftVars j, ∃ b∈C.rightVars j, (a.val<21 ↔ b.val<21)}.ncard → C.outGates.card≤14 →
      (∃ j : Fin C.size, let a := (C.leftVars j).card; let b := (C.rightVars j).card; (5≤ min a b ∧ 6≤ max a b) ∨ (4≤ min a b ∧ 14≤ max a b)) →
      (let degree (v : Fin 42) := {j : Fin C.size | v∈C.leftVars j ∨ v∈C.rightVars j}.ncard
    let p := {v : Fin 42 | v.val<21 ∧ degree v≤1}.ncard
    let l := {v : Fin 42 | 21≤v.val ∧ degree v≤1}.ncard
    p.choose 2+l≤8 ∧ l.choose 2+p≤8 ∧ p+l≤6 ∧ ∃ v : Fin 42, degree v=3) → False) :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → x2.size = (19 : ℕ) → (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard ≤ (3 : ℕ)) → (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → {x15 : Fin x2.size | x10 ∈ x2.leftVars x15 ∨ x10 ∈ x2.rightVars x15 ∨ x11 ∈ x2.leftVars x15 ∨ x11 ∈ x2.rightVars x15}.ncard ≤ (5 : ℕ)) → False := by
  let plane := SimpleGraph.fromRel fun a b : Fin 42 => a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val)%21 ∈ ([0,5,7,17,20] : List Nat)
  let vars {n} (C : AndCountCircuit n) (i : (Fin C.size × Bool)) := if i.2 then C.leftVars i.1 else C.rightVars i.1

  have side_eq {n m : Nat} (U B : Finset (Fin n)) (F : Finset (Fin m)) (i : Fin m) (v : Fin m → Bool) :
      sideTrue U B F i v = decide ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := rfl
  have eval_eq {n : Nat} (E : AndCountCircuit n) (U : Finset (Fin n)) :
      E.eval U = decide ((∃ v ∈ E.outVars, v ∈ U) ∨ ∃ j ∈ E.outGates, E.gateVal U j = true) := rfl
  have side_mono {n m : Nat} (U Y B : Finset (Fin n)) (F : Finset (Fin m)) (i : Fin m)
      (a b : Fin m→Bool) (bare : ∀ u ∈ B, u∈U → ∃ y∈B, y∈Y) (earlier : ∀ j, a j=true → b j=true) :
      sideTrue U B F i a=true → sideTrue Y B F i b=true := by
    simp only [side_eq,decide_eq_true_eq]
    rintro (⟨u,hu,inp⟩|⟨j,hj,lt,on⟩)
    · exact Or.inl (bare u hu inp)
    · exact Or.inr ⟨j,hj,lt,earlier j on⟩

  have dominated {n} (C : AndCountCircuit n) (out : C.outVars=∅) (U Y : Finset (Fin n))
      (dom : ∀ i : (Fin C.size × Bool), ∀ u∈vars C i,u∈U → ∃ y∈vars C i,y∈Y) : C.eval U=true → C.eval Y=true := by
    have vals (d : Nat) (j : Fin C.size) : C.gateValFuel U d j=true → C.gateValFuel Y d j=true := by
      induction d generalizing j with
      | zero => exact fun h => h
      | succ d ih =>
        intro h
        rcases Bool.and_eq_true_iff.mp h with ⟨hl,hr⟩
        apply Bool.and_eq_true_iff.mpr
        exact ⟨side_mono _ _ _ _ _ _ _ (dom (j,true)) ih hl,side_mono _ _ _ _ _ _ _ (dom (j,false)) ih hr⟩
    simp only [eval_eq,out,Finset.notMem_empty,false_and,exists_false,false_or,decide_eq_true_eq]
    rintro ⟨j,hj,v⟩
    exact ⟨j,hj,vals _ _ v⟩

  let same (v w : (Fin 42)) := decide (v.val<21) == decide (w.val<21)
  have same_nonedge : ∀ u v : (Fin 42),same u v=true → ¬plane.Adj u v := by decide +kernel
  have neighbors : ∀ v : (Fin 42),(Finset.univ.filter (plane.Adj v)).card=5 := by decide +kernel
  have one_common : ∀ v w : (Fin 42), v≠w →
      ((Finset.univ.filter (plane.Adj v)).filter (plane.Adj w)).card ≤ 1 := by decide +kernel
  have avoid_pair (C : AndCountCircuit 42) (comp : C.Computes plane) (out : C.outVars=∅)
      (v x y : (Fin 42)) (xv : x≠v) (yv : y≠v) (ind : ¬plane.Adj x y) :
      ∃ i : (Fin C.size × Bool), v∈vars C i ∧ x∉vars C i ∧ y∉vars C i := by
    classical
    let N := Finset.univ.filter (plane.Adj v)
    let X := N.filter (plane.Adj x)
    let Y := N.filter (plane.Adj y)
    have xc : X.card≤1 := one_common v x xv.symm
    have yc : Y.card≤1 := one_common v y yv.symm
    obtain ⟨l,hl,free⟩ : ∃ l∈N,l∉X∪Y := by
      by_contra! sub
      have := Finset.card_le_card sub
      have := Finset.card_union_le X Y
      have five : N.card=5 := neighbors v
      omega
    have xl : ¬plane.Adj x l := fun h => free (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hl,h⟩))
    have yl : ¬plane.Adj y l := fun h => free (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hl,h⟩))
    have adj := (Finset.mem_filter.mp hl).2
    by_contra! missing
    have ev : C.eval {x,y,l}=true := by
      apply dominated C out {v,l} {x,y,l}
      · intro i u inp hu
        rcases Finset.mem_insert.mp hu with rfl|h
        · by_cases hx : x∈vars C i
          · exact ⟨x,hx,by simp⟩
          · exact ⟨y,missing i inp hx,by simp⟩
        · obtain rfl := Finset.mem_singleton.mp h
          exact ⟨u,inp,by simp⟩
      · exact (comp {v,l}).mpr ⟨v,by simp,l,by simp,adj⟩
    obtain ⟨a,ha,b,hb,ab⟩ := (comp _).mp ev
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;>
      first | exact plane.irrefl ab | exact ind ab | exact ind ab.symm | exact xl ab | exact xl ab.symm | exact yl ab | exact yl ab.symm

  have outside_degree (C : AndCountCircuit 42) (comp : C.Computes plane) (out : C.outVars=∅)
      (dj : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (k : Fin C.size)
      (huge : ∀ b : Bool, 7≤(vars C (k,b)).card) (v : (Fin 42)) :
      let O := Finset.univ.filter fun i : (Fin C.size × Bool) => i.1≠k ∧ v∈vars C i
      0<O.card ∧ (O.card≤1 → ∃ i : (Fin C.size × Bool), vars C i={v}) := by
    classical
    intro O
    obtain ⟨w,ne⟩ : ∃ w : (Fin 42),w≠v := exists_ne v
    have chooseLarge (y : (Fin 42)) (yv : y≠v) : ∃ x : (Fin 42),x≠v ∧ ¬plane.Adj x y ∧
        ∀ b : Bool,v∈vars C (k,b) → x∈vars C (k,b) := by
      by_cases inp : ∃ b : Bool, v∈vars C (k,b)
      · obtain ⟨b,hb⟩ := inp
        let forbid := insert v (Finset.univ.filter (plane.Adj y))
        have card : forbid.card≤6 := (Finset.card_insert_le ..).trans (by rw [neighbors])
        obtain ⟨x,hx,hy⟩ : ∃ x∈vars C (k,b),x∉forbid := by
          by_contra! sub
          have := Finset.card_le_card sub
          have := huge b
          omega
        have neq : x≠v := fun eq => hy (eq ▸ Finset.mem_insert_self ..)
        have na : ¬plane.Adj x y := fun e => hy (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.symm⟩))
        refine ⟨x,neq,na,?_⟩
        intro c hc
        have eq : b=c := by
          cases b <;> cases c <;> first | rfl | exact (Finset.disjoint_left.mp (dj k) hb hc).elim | exact (Finset.disjoint_left.mp (dj k) hc hb).elim
        exact eq ▸ hx
      · exact ⟨y,yv,plane.loopless.irrefl _,fun b hv => (inp ⟨b,hv⟩).elim⟩
    have witness (y : (Fin 42)) (yv : y≠v) : ∃ i∈O,y∉vars C i := by
      obtain ⟨x,ne,ind,hx⟩ := chooseLarge y yv
      obtain ⟨i,hi,miss,other⟩ := avoid_pair C comp out v x y ne yv ind
      have notK : i.1≠k := by
        rintro eq
        rcases i with ⟨j,b⟩
        change j=k at eq
        subst j
        exact miss (hx b hi)
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,notK,hi⟩,other⟩
    have nonempty := witness w ne
    obtain ⟨i,hi,_⟩ := nonempty
    refine ⟨Finset.card_pos.mpr ⟨i,hi⟩,?_⟩
    intro one
    refine ⟨i,Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hi).2.2)⟩
    intro y hy
    apply Finset.mem_singleton.mpr
    by_contra neq
    obtain ⟨j,hj,miss⟩ := witness y neq
    exact miss ((Finset.card_le_one.mp one i hi j hj) ▸ hy)
  intro G C wf comp out unit dj size read overlap
  let B := Finset.univ.filter fun j : Fin C.size => ∃ a∈C.leftVars j, ∃ b∈C.rightVars j, (a.val<21 ↔ b.val<21)
  have count_eq : {j : Fin C.size | ∃ a∈C.leftVars j, ∃ b∈C.rightVars j, (a.val<21 ↔ b.val<21)}.ncard = B.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext j
    simp [B]
  have four : 4≤B.card := by
    by_contra! few
    obtain ⟨k,hl,hr,budget⟩ := concentrate C comp out dj size read (by omega)
    have huge (b : Bool) : 7≤(vars C (k,b)).card := by cases b <;> first | exact hl | exact hr
    let O (v : (Fin 42)) := Finset.univ.filter fun i : (Fin C.size × Bool) => i.1≠k ∧ v∈vars C i
    obtain ⟨v,missing⟩ : ∃ v : (Fin 42), ∀ i : (Fin C.size × Bool),vars C i≠{v} := by
      by_contra! witnesses
      choose index eq using witnesses
      have inj : Function.Injective index := by
        intro a b h
        have ha := eq a
        rw [h,eq b] at ha
        simpa using ha.symm
      have le := Fintype.card_le_of_injective _ inj
      simp [size] at le
    have above : 42 < ∑ u : (Fin 42),(O u).card := calc
      42 = ∑ _u : (Fin 42),1 := by simp
      _ < _ := by
        apply Finset.sum_lt_sum
        · intro u _
          exact (outside_degree C comp out dj k huge u).1
        · refine ⟨v,Finset.mem_univ _,?_⟩
          by_contra! low
          obtain ⟨i,single⟩ := (outside_degree C comp out dj k huge v).2 low
          exact missing i single
    let T : Finset (Fin C.size) := Finset.univ.erase k
    have degreeSum (u : (Fin 42)) : (O u).card = ∑ j∈T,
        ((if u∈C.leftVars j then 1 else 0)+(if u∈C.rightVars j then 1 else 0)) := by
      have form : O u = ((T ×ˢ (Finset.univ : Finset Bool)).filter fun i => u∈vars C i) := by
        ext i
        simp only [O,T,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_product,Finset.mem_erase,
          and_true]
      rw [form]
      trans ∑ i∈T ×ˢ (Finset.univ : Finset Bool), if u∈vars C i then 1 else 0
      · rw [← Finset.sum_filter]; simp
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_bool]
      rfl
    have eq : (∑ u : (Fin 42),(O u).card) = ∑ j∈T,((C.leftVars j).card+(C.rightVars j).card) := by
      simp_rw [degreeSum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp [Finset.sum_add_distrib]
    rw [eq] at above
    exact (Nat.not_lt_of_ge budget) above
  obtain ⟨many,wide⟩ := geometry C comp out dj size read overlap (by omega)
  let U := Finset.univ.filter fun j : Fin C.size => ∃ a∈C.leftVars j, ∃ b∈C.rightVars j, ¬plane.Adj a b
  have eqU : {j : Fin C.size | ∃ a∈C.leftVars j, ∃ b∈C.rightVars j, ¬plane.Adj a b}.ncard = U.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext j
    simp [U]
  have five : 5≤U.card := eqU ▸ many
  have free : Disjoint U C.outGates := by
    apply Finset.disjoint_left.mpr
    intro j hj jout
    obtain ⟨a,ha,b,hb,notAdj⟩ := (Finset.mem_filter.mp hj).2
    have positive : C.gateVal {a,b} j=true := by
      unfold gateVal
      rw [size]
      apply Bool.and_eq_true_iff.mpr
      exact ⟨decide_eq_true (Or.inl ⟨a,ha,by simp⟩), decide_eq_true (Or.inl ⟨b,hb,by simp⟩)⟩
    have cev : C.eval {a,b}=true := decide_eq_true (Or.inr ⟨j,jout,positive⟩)
    obtain ⟨u,hu,v,hv,adj⟩ := (comp _).mp cev
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
      first | exact plane.irrefl adj | exact notAdj adj | exact notAdj adj.symm
  have plus := Finset.card_union_of_disjoint free
  have max := Finset.card_le_univ (U∪C.outGates)
  simp only [Fintype.card_fin,size] at max
  exact remaining C wf comp out unit dj size read overlap (by omega) (by omega) wide (readProfile C comp out dj size read)
