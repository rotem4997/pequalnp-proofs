import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

-- Put the joint strict ancestors of the two distinguished gates first.
-- The terminal-AND condition forces all of these ancestors to be OR gates.
-- In this order the two bad ANDs are consecutive, and every later AND is clean.
theorem PEqualNP.Outside.R_meta_4065_734
    (transport : ∀ (n : ℕ) (C : Circuit) (σ : Equiv.Perm (Fin C.size)),
      IsAO2 n C → (∀ i j, InCone n C i.val j.val → σ i < σ j) →
      ∃ D : Circuit, D.size = C.size ∧ IsAO2 n D ∧
        (∀ x, circuitFun n D x = circuitFun n C x) ∧
        (∀ i, (gateAt D (σ i).val).op = (gateAt C i.val).op) ∧
        (∀ i x, gateVal n D (σ i).val x = gateVal n C i.val x) ∧
        ∀ i j, InCone n D (σ i).val (σ j).val ↔ InCone n C i.val j.val)
    (ordered :
      let N : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]; let P : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768];
      ∀ (D : Circuit) (k : ℕ), let a := fun j => (gateAt D j).op = GateOp.and;
        let c := InCone 11 D; let clean := fun j => ∀ r ∈ N, gateVal 11 D j (fun i => r.testBit i.val) = false;
        IsAO2 11 D → D.size ≤ 21 → k+1 < D.size →
        (∀ j < k, (gateAt D j).op = GateOp.or ∧ (c j k ∨ c j (k+1))) →
        a k → a (k+1) → ¬clean k → ¬clean (k+1) → ¬c k (k+1) →
        (∀ j < D.size, k+1 < j → a j → clean j ∧ ∀ t < D.size, a t → ¬c j t) →
        (∃ j < D.size, a j ∧ c k j ∧ c (k+1) j) →
        (∀ r ∈ P, circuitFun 11 D (fun i => r.testBit i.val) = true) →
        (∀ r ∈ N, circuitFun 11 D (fun i => r.testBit i.val) = false) → False) :
  (have x1 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)]; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => ∀ x6 ∈ x1, (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x4 x5 fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false; have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 → x6.size ≤ (21 : ℕ) → x7 < x8 → x8 < x6.size → x3 x6 x7 → x3 x6 x8 → (∀ x15 < x6.size, x3 x6 x15 → (x4 x6 x15 ↔ x15 ≠ x7 ∧ x15 ≠ x8)) → (∀ x16 < x6.size, x3 x6 x16 → x4 x6 x16 → ∀ x20 < x6.size, x3 x6 x20 → ¬x5 x6 x16 x20) → ¬x5 x6 x7 x8 → ¬x5 x6 x8 x7 → (∃ x19 < x6.size, x3 x6 x19 ∧ x4 x6 x19 ∧ x5 x6 x7 x19 ∧ x5 x6 x8 x19) → (∀ x20 ∈ x2, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x22 : Fin (11 : ℕ)) => x20.testBit ↑x22) = Bool.true) → (∀ x21 ∈ x1, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x23 : Fin (11 : ℕ)) => x21.testBit ↑x23) = Bool.false) → False) := by
  classical
  dsimp only
  intro C u v ao size uv vsize au av which terminal incomparable reverse common yes no
  let x : Fin C.size := ⟨u,by omega⟩
  let y : Fin C.size := ⟨v,vsize⟩
  have different : x ≠ y := by
    intro e
    have eq : u=v := congrArg Fin.val e
    omega
  have finiteOrder (m : ℕ) (R : Fin m → Fin m → Prop) (a b : Fin m)
      (forward : ∀ i j, R i j → i<j) (trans : ∀ i j k, R i j → R j k → R i k)
      (ne : a≠b) (ab : ¬R a b) (ba : ¬R b a) :
      ∃ t : Equiv.Perm (Fin m), (∀ i j, R i j → t i < t j) ∧ (t b).val=(t a).val+1 ∧
        ∀ i, t i<t a → R i a ∨ R i b := by
    classical
    let pred (i : Fin m) := R i a ∨ R i b
    let key (i : Fin m) := if pred i then i.val else if i=a then m else if i=b then m+1 else m+2+i.val
    have ka : key a=m := by
      have h : ¬pred a := fun x => x.elim (fun z => (lt_irrefl _ (forward _ _ z))) ab
      simp [key,h]
    have kb : key b=m+1 := by
      have h : ¬pred b := fun x => x.elim ba (fun z => (lt_irrefl _ (forward _ _ z)))
      simp [key,h,ne.symm]
    have uniqueKey : Function.Injective key := by
      intro i j h
      apply Fin.ext
      have hi:=i.isLt; have hj:=j.isLt
      dsimp only [key] at h
      split_ifs at h <;> subst_vars <;> omega
    have preserves (i j) (h : R i j) : key i<key j := by
      by_cases q : pred j
      · have z : pred i := q.imp (trans i j a h) (trans i j b h)
        have valLess : i.val<j.val := forward i j h
        simpa only [key,z,q,ite_true] using valLess
      · by_cases z : pred i
        · have hi:=i.isLt
          simp only [key,z,q,ite_true,ite_false];split_ifs <;> omega
        · have ja : j≠a := fun e => z (Or.inl (e ▸ h))
          have jb : j≠b := fun e => z (Or.inr (e ▸ h))
          have ij : i.val<j.val := forward i j h
          simp only [key,z,q,ja,jb,ite_false];split_ifs <;> omega
    let lower (i : Fin m) := Finset.univ.filter (fun j : Fin m => key j<key i)
    have absent (i) : i∉lower i := by simp [lower]
    have rankLt (i j) (h : key i<key j) : (lower i).card < (lower j).card := by
      apply Finset.card_lt_card
      apply lt_of_le_of_ne
      · intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_trans (Finset.mem_filter.mp hx).2 h⟩
      · intro e
        apply absent i
        rw [e]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
    have rankBound (i) : (lower i).card<m := by
      have sub : lower i ⊂ Finset.univ := by
        apply lt_of_le_of_ne (Finset.subset_univ _)
        intro e
        exact absent i (e ▸ Finset.mem_univ i)
      simpa using Finset.card_lt_card sub
    let rank (i : Fin m) : Fin m := ⟨(lower i).card,rankBound i⟩
    have injective : Function.Injective rank := by
      intro i j eq
      have same : (lower i).card=(lower j).card := congrArg Fin.val eq
      rcases lt_trichotomy (key i) (key j) with l | e | r
      · exact (False.elim (Nat.ne_of_lt (rankLt i j l) same))
      · exact uniqueKey e
      · exact (False.elim (Nat.ne_of_lt (rankLt j i r) same.symm))
    let σ : Equiv.Perm (Fin m) := Equiv.ofBijective rank (Finite.injective_iff_bijective.mp injective)
    have jump : lower b=insert a (lower a) := by
      ext i
      simp only [lower,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,ka,kb]
      constructor
      · intro hi
        by_cases eq : key i=m
        · exact Or.inl (uniqueKey (eq.trans ka.symm))
        · exact Or.inr (by omega)
      · rintro (rfl|lt)
        · omega
        · omega
    refine ⟨σ,(fun i j h => rankLt i j (preserves i j h)),?_,?_⟩
    · change (lower b).card=(lower a).card+1
      rw [jump,Finset.card_insert_of_notMem (absent a)]
    · intro i hi
      change (lower i).card < (lower a).card at hi
      have klt : key i<m := by
        rcases lt_trichotomy (key i) (key a) with l | e | r
        · rwa [ka] at l
        · have eq := uniqueKey e
          subst i; omega
        · have opp := rankLt a i r
          omega
      change pred i
      by_contra nop
      simp only [key,nop,ite_false] at klt
      split_ifs at klt <;> omega
  have coneOrder (n : ℕ) (C : Circuit) :
      (∀ i j : Fin C.size, InCone n C i.val j.val → i<j) ∧
      (∀ i j k : Fin C.size, InCone n C i.val j.val → InCone n C j.val k.val → InCone n C i.val k.val) := by
    let ok (cs : List (List ℕ)) := ∀ j, j<cs.length → ∀ i∈cs.getD j [], i<j ∧ ∀ z∈cs.getD i [], z∈cs.getD j []
    have advance (cs : List (List ℕ)) (g : Gate) (prior : ok cs) : ok (PEqualNP.EdgeOwnership.coneStep n cs g) := by
      let links := g.inputs.filter (fun w => decide (n ≤ w ∧ w<n+cs.length))
      let new := links.flatMap fun w => (w-n)::cs.getD (w-n) []
      change ok (cs++[new])
      have kept (i : ℕ) (hi : i<cs.length) : (cs++[new]).getD i []=cs.getD i [] := List.getD_append _ _ _ _ hi
      have last : (cs++[new]).getD cs.length []=new := by simp
      intro j hj i hi
      by_cases old : j<cs.length
      · rw [kept j old] at hi
        obtain ⟨less,below⟩ := prior j old i hi
        refine ⟨less,?_⟩
        rw [kept i (lt_trans less old),kept j old]
        exact below
      · have je : j=cs.length := by simp at hj;omega
        subst j
        rw [last] at hi
        obtain ⟨w,hw,inside⟩ := List.mem_flatMap.mp hi
        have bounds : n≤w ∧ w<n+cs.length := of_decide_eq_true (List.mem_filter.mp hw).2
        have hparent : w-n<cs.length := by omega
        rcases List.mem_cons.mp inside with eq | deep
        · subst i
          refine ⟨hparent,?_⟩
          rw [kept _ hparent,last]
          exact fun z hz => List.mem_flatMap.mpr ⟨w,hw,List.mem_cons.mpr (Or.inr hz)⟩
        · obtain ⟨small,desc⟩ := prior (w-n) hparent i deep
          refine ⟨lt_trans small hparent,?_⟩
          rw [kept i (lt_trans small hparent),last]
          exact fun z hz => List.mem_flatMap.mpr ⟨w,hw,List.mem_cons.mpr (Or.inr (desc z hz))⟩
    have full (gs : List Gate) (cs : List (List ℕ)) (h : ok cs) :
        ok (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs) ∧
        (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length=cs.length+gs.length := by
      induction gs generalizing cs with
      | nil => exact ⟨h,by simp⟩
      | cons g gs ih =>
        obtain ⟨holds,len⟩ := ih _ (advance cs g h)
        refine ⟨holds,?_⟩
        rw [List.foldl_cons,len]
        change (_++[_]).length+gs.length = _
        simp; omega
    obtain ⟨valid,len⟩ := full C.gates [] (by intro j h; simp at h)
    change ok (PEqualNP.EdgeOwnership.cones n C) at valid
    have length : (PEqualNP.EdgeOwnership.cones n C).length=C.size := by
      change (C.gates.foldl (PEqualNP.EdgeOwnership.coneStep n) []).length=C.gates.length
      simpa only [List.length_nil,Nat.zero_add] using len
    refine ⟨?_,?_⟩
    · intro i j edge
      exact (valid j.val (by rw [length];exact j.isLt) i.val edge).1
    · intro i j k ij jk
      exact (valid k.val (by rw [length];exact k.isLt) j.val jk).2 i.val ij
  obtain ⟨prior,closed⟩ := coneOrder 11 C
  obtain ⟨σ,order,pos,ancestors⟩ := finiteOrder C.size (fun i j => InCone 11 C i.val j.val) x y prior closed different incomparable reverse
  obtain ⟨D,sz,dao,out,op,value,reach⟩ := transport 11 C σ ao order
  let k := (σ x).val
  have next : (σ y).val=k+1 := pos
  have ksize : k+1<D.size := by rw [← next,sz];exact (σ y).isLt
  let back (i : Fin D.size) : Fin C.size := σ.symm ⟨i.val,by rw [← sz];exact i.isLt⟩
  have backVal (i : Fin D.size) : (σ (back i)).val=i.val := by simp [back]
  have allOps (i : Fin C.size) : (gateAt C i.val).op=.and ∨ (gateAt C i.val).op=.or := by
    apply ao.1
    change C.gates.getD i.val _∈C.gates
    rw [List.getD_eq_getElem _ _ i.isLt]
    exact List.getElem_mem _
  have firstAnd : (gateAt D k).op=.and := (op x).trans au
  have secondAnd : (gateAt D (k+1)).op=.and := by rw [← next];exact (op y).trans av
  have separated (i : Fin C.size) (left : (σ i).val≠k) (right : (σ i).val≠k+1) :
      i.val≠u ∧ i.val≠v := by
    constructor
    · intro e
      have same : i=x := Fin.ext e
      exact left (congrArg (fun z => (σ z).val) same)
    · intro e
      have same : i=y := Fin.ext e
      exact right ((congrArg (fun z => (σ z).val) same).trans next)
  apply ordered D k dao (by omega) ksize
  · intro j hj
    let z : Fin D.size := ⟨j,by omega⟩
    let i := back z
    have eq : (σ i).val=j := backVal z
    have before : σ i < σ x := by change (σ i).val < k;omega
    have occurs := ancestors i before
    have either : InCone 11 D j k ∨ InCone 11 D j (k+1) := by
      rw [← eq,← next]
      exact occurs.imp (reach i x).mpr (reach i y).mpr
    refine ⟨?_,either⟩
    rw [← eq,op i]
    rcases allOps i with a | o
    · have good := (which i.val i.isLt a).mpr (separated i (by omega) (by omega))
      rcases occurs with h | h
      · exact (terminal i.val i.isLt a good u x.isLt au h).elim
      · exact (terminal i.val i.isLt a good v y.isLt av h).elim
    · exact o
  · exact firstAnd
  · exact secondAnd
  · intro clean
    have transfer := (which u x.isLt au).mp (by intro r hr; exact (value x _).symm.trans (clean r hr))
    exact transfer.1 rfl
  · intro clean
    have transfer := (which v y.isLt av).mp (by
      intro r hr
      have h := clean r hr
      rw [← next] at h
      exact (value y _).symm.trans h)
    exact transfer.2 rfl
  · rw [← next]
    exact fun h => incomparable ((reach x y).mp h)
  · intro j js after andGate
    let z : Fin D.size := ⟨j,js⟩
    let i := back z
    have eq : (σ i).val=j := backVal z
    have a : (gateAt C i.val).op=.and := (op i).symm.trans (eq ▸ andGate)
    have good := (which i.val i.isLt a).mpr (separated i (by omega) (by omega))
    constructor
    · intro r hr
      rw [← eq,value i]
      exact good r hr
    · intro t ts andT dep
      let w : Fin D.size := ⟨t,ts⟩
      let m := back w
      have et : (σ m).val=t := backVal w
      have aT : (gateAt C m.val).op=.and := (op m).symm.trans (et ▸ andT)
      rw [← eq,← et] at dep
      exact terminal i.val i.isLt a good m.val m.isLt aT ((reach i m).mp dep)
  · obtain ⟨j,js,andJ,_,left,right⟩ := common
    let z : Fin C.size := ⟨j,js⟩
    refine ⟨(σ z).val,by rw [sz];exact (σ z).isLt,(op z).trans andJ,(reach x z).mpr left,?_⟩
    rw [← next]
    exact (reach y z).mpr right
  · intro r hr
    exact (out _).trans (yes r hr)
  · intro r hr
    exact (out _).trans (no r hr)
