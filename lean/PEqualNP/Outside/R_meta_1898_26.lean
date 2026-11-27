import Mathlib.Combinatorics.Pigeonhole
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.AndCount

-- Compress the free disjunctions. If twelve conjunctions suffice, at least five
-- of the fifty-two flags must use one output gate. Two cyclic orbits of
-- generic negative rows show that this gate must read another conjunction.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_1898_26
    (compress : ∀ C : Circuit, Monotone2 C →
      (∃ U : Finset (Fin 26), circuitFun 26 C (fun j => decide (j ∈ U)) = false) →
      ∃ A : AndCountCircuit 26, A.WellFormed ∧
        A.size ≤ Nat.card {j : Fin C.gates.length // (C.gates.get j).op = GateOp.and} ∧
        ∀ U, A.eval U = circuitFun 26 C (fun j => decide (j ∈ U)))
    (nested : ∀ A : AndCountCircuit 26, A.WellFormed → A.outVars = ∅ →
      let I := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let miss := fun X : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ X, ¬ I p l
      let row := fun X Y : Finset (Fin 13) => X.map (Fin.castAddEmb 13) ∪ Y.map (Fin.natAddEmb 13)
      let pair := fun p l : Fin 13 => ({Fin.castAdd 13 p, Fin.natAdd 13 l} : Finset (Fin 26))
      (∀ p l, I p l → A.eval (pair p l) = true) →
      (∀ X, (∀ p ∉ X, ∃ l ∈ miss X, I p l) →
        (¬ ∃ l, ∀ p ∈ X, I p l) → (¬ ∃ p, ∀ l ∈ miss X, I p l) →
        A.eval (row X (miss X)) = false) →
      (∃ i ∈ A.outGates, 4 < Nat.card {e : Fin 13 × Fin 13 // I e.1 e.2 ∧ A.gateVal (pair e.1 e.2) i = true} ∧
        ((A.leftGates i).Nonempty ∨ (A.rightGates i).Nonempty)) →
      13 ≤ A.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (13 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  classical
  intro C mono pos neg
  let I := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  let miss := fun X : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ X, ¬ I p l
  let row := fun X Y : Finset (Fin 13) => X.map (Fin.castAddEmb 13) ∪ Y.map (Fin.natAddEmb 13)
  let pair := fun p l : Fin 13 => ({Fin.castAdd 13 p, Fin.natAdd 13 l} : Finset (Fin 26))
  let generic := fun X : Finset (Fin 13) =>
    (∀ p ∉ X, ∃ l ∈ miss X, I p l) ∧ (¬ ∃ l, ∀ p ∈ X, I p l) ∧ (¬ ∃ p, ∀ l ∈ miss X, I p l)
  have reject (X) (h : generic X) :
      circuitFun 26 C (fun j => decide (j ∈ row X (miss X))) = false := by
    obtain ⟨hc,hl,hp⟩ := h
    have H := neg X (by simpa [miss,I] using hc) ⟨hl,by simpa [miss,I] using hp⟩
    convert H using 2
    funext j
    apply decide_eq_decide.mpr
    constructor
    · intro hj
      rcases Finset.mem_union.mp hj with hx | hy
      · obtain ⟨p,hp,e⟩ := Finset.mem_map.mp hx
        exact Or.inl ⟨p,hp,e.symm⟩
      · obtain ⟨l,hl,e⟩ := Finset.mem_map.mp hy
        exact Or.inr ⟨l,e.symm,(Finset.mem_filter.mp hl).2⟩
    · rintro (⟨p,hp,e⟩ | ⟨l,e,hl⟩)
      · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨p,hp,e.symm⟩)
      · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩,e.symm⟩)
  let dataX : Fin 26 → Nat := ![19,38,76,152,304,608,1216,2432,4864,1537,3074,6148,4105,71,142,284,568,1136,2272,4544,897,1794,3588,7176,6161,4131]
  let dataY : Fin 26 → Nat := ![5799955,11599910,23199820,46399640,25698608,51397216,35693760,4286848,8573696,17139201,34278402,1456132,2904073,7340103,14680206,29360412,58720824,50340976,33581280,61888,115585,231170,462340,924680,1841169,3674147]
  let xs := fun t => Finset.univ.filter fun p : Fin 13 => (dataX t).testBit p.val = true
  let ys := fun t => Finset.univ.filter fun j : Fin 26 => (dataY t).testBit j.val = true
  have geometry : ∀ t, generic (xs t) ∧ row (xs t) (miss (xs t)) = ys t := by decide +kernel
  have rejects (t) : circuitFun 26 C (fun j => decide (j ∈ ys t)) = false := by
    rw [← (geometry t).2]
    exact reject _ (geometry t).1
  obtain ⟨A,wf,cost,spec⟩ := compress C mono ⟨ys 0,rejects 0⟩
  have negA (t) : A.eval (ys t) = false := (spec _).trans (rejects t)
  have every : ∀ v : Fin 26, ∃ t, v ∈ ys t := by
    simp only [ys,Finset.mem_filter,Finset.mem_univ,true_and]
    decide +kernel
  have empty : A.outVars = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨t,ht⟩ := every v
    have yes : A.eval (ys t) = true := decide_eq_true (Or.inl ⟨v,hv,ht⟩)
    exact Bool.noConfusion (yes.symm.trans (negA t))
  have posA (p l) (h : I p l) : A.eval (pair p l) = true := by
    rw [spec]
    convert pos p l h using 2
    funext j
    simp [pair]
  suffices bound : 13 ≤ A.size by exact bound.trans cost
  by_contra! small
  apply (Nat.not_le.mpr small)
  apply nested A wf empty posA (fun X hc hl hp => (spec _).trans (reject X ⟨hc,hl,hp⟩))
  let off : Fin 4 → Fin 13 := ![0,1,3,9]
  let E := fun f : Fin 13 × Fin 4 => pair (f.1 + off f.2) f.1
  have inc : ∀ (l : Fin 13) (b : Fin 4), I (l + off b) l := by decide +kernel
  have pick (f : Fin 13 × Fin 4) : ∃ i ∈ A.outGates, A.gateVal (E f) i = true := by
    have h := posA _ _ (inc f.1 f.2)
    change decide ((∃ v ∈ A.outVars, v ∈ E f) ∨ ∃ i ∈ A.outGates, A.gateVal (E f) i = true) = true at h
    simpa [empty] using h
  choose g gm gv using pick
  obtain ⟨i,hot⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card g
    (n := 4) (by simp only [Fintype.card_fin,Fintype.card_prod]; omega)
  let G := Finset.univ.filter (fun f : Fin 13 × Fin 4 => g f = i)
  change 4 < G.card at hot
  obtain ⟨u,v,ne,tag⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun f : {f // f ∈ G} => f.val.2) (by simpa using hot)
  change u.val.2 = v.val.2 at tag
  let z := u.val.2
  let p := u.val.1
  let q := v.val.1
  have pq : p ≠ q := fun h => ne (Subtype.ext (Prod.ext h tag))
  have inG (f) (h : f ∈ G) : g f = i := (Finset.mem_filter.mp h).2
  have hi : i ∈ A.outGates := inG u.val u.property ▸ gm u.val
  have ep : A.gateVal (pair (p+off z) p) i = true := inG u.val u.property ▸ gv u.val
  have eq : A.gateVal (pair (q+off z) q) i = true := by
    change A.gateVal (pair (v.val.1 + off u.val.2) v.val.1) i = true
    rw [tag,← inG v.val v.property]
    exact gv v.val
  let flag := fun f : Fin 13 × Fin 4 => (f.1 + off f.2, f.1)
  have flag_inj : Function.Injective flag := by
    change ∀ a b : Fin 13 × Fin 4, flag a = flag b → a = b
    decide +kernel
  let dest := {e : Fin 13 × Fin 13 // I e.1 e.2 ∧ A.gateVal (pair e.1 e.2) i = true}
  let embed : {f // f ∈ G} → dest := fun f =>
    ⟨flag f.val,inc f.val.1 f.val.2,inG f.val f.property ▸ gv f.val⟩
  have inj : Function.Injective embed := fun a b e => Subtype.ext (flag_inj (congrArg Subtype.val e))
  have card : 4 < Nat.card dest := by
    have le := Fintype.card_le_of_injective embed inj
    exact lt_of_lt_of_le hot (by simpa [Nat.card_eq_fintype_card] using le)
  refine ⟨i,hi,card,?_⟩
  by_contra missing
  push Not at missing
  obtain ⟨nl,nr⟩ := missing
  have l0 : A.leftGates i = ∅ := by simpa using nl
  have r0 : A.rightGates i = ∅ := by simpa using nr
  let endpt := fun (t : Fin 4) (p : Fin 13) (b : Bool) => if b then Fin.castAdd 13 (p + off t) else Fin.natAdd 13 p
  have flat (U) : A.gateVal U i = true ↔
      (∃ v ∈ A.leftVars i, v ∈ U) ∧ (∃ v ∈ A.rightVars i, v ∈ U) := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (show A.size ≠ 0 by have := i.isLt; omega)
    change A.gateValFuel U A.size i = true ↔ _
    conv_lhs => rw [show A.gateValFuel U A.size i = A.gateValFuel U (d+1) i from congrArg (fun k => A.gateValFuel U k i) hd]
    change (decide ((∃ v ∈ A.leftVars i, v ∈ U) ∨ ∃ j ∈ A.leftGates i, j < i ∧ A.gateValFuel U d j = true) &&
      decide ((∃ v ∈ A.rightVars i, v ∈ U) ∨ ∃ j ∈ A.rightGates i, j < i ∧ A.gateValFuel U d j = true)) = true ↔ _
    simp [l0,r0]
  have endpoint (v t) (mem : v ∈ pair (t + off z) t) : ∃ b, endpt z t b = v := by
    rcases Finset.mem_insert.mp mem with h | h
    · exact ⟨true,h.symm⟩
    · exact ⟨false,(Finset.mem_singleton.mp h).symm⟩
  obtain ⟨⟨a,al,ap⟩,⟨b,br,bp⟩⟩ := (flat _).1 ep
  obtain ⟨⟨c,cl,cq⟩,⟨d,dr,dq⟩⟩ := (flat _).1 eq
  obtain ⟨ba,rfl⟩ := endpoint a p ap
  obtain ⟨bb,rfl⟩ := endpoint b p bp
  obtain ⟨bc,rfl⟩ := endpoint c q cq
  obtain ⟨bd,rfl⟩ := endpoint d q dq
  have cover : ∀ (z : Fin 4) (p q : Fin 13), p ≠ q → ∀ a b c d : Bool, ∃ t,
      (endpt z p a ∈ ys t ∨ endpt z q c ∈ ys t) ∧
      (endpt z p b ∈ ys t ∨ endpt z q d ∈ ys t) := by
    simp only [ys,Finset.mem_filter,Finset.mem_univ,true_and]
    decide +kernel
  obtain ⟨t,left,right⟩ := cover z p q pq ba bb bc bd
  have on : A.gateVal (ys t) i = true := (flat _).2 ⟨
    left.elim (fun h => ⟨_,al,h⟩) (fun h => ⟨_,cl,h⟩),
    right.elim (fun h => ⟨_,br,h⟩) (fun h => ⟨_,dr,h⟩)⟩
  have yes : A.eval (ys t) = true := decide_eq_true (Or.inr ⟨i,hi,on⟩)
  exact Bool.noConfusion (yes.symm.trans (negA t))
