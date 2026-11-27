import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership PEqualNP.PairShadow

theorem PEqualNP.Outside.R_meta_1780_3
    (price : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
    (∀ p p', p≠p' → ∃! l, I p l ∧ I p' l) → Monotone2 C →
    let V := fun (x : Fin (N+N) → Bool) (w : ℕ) => (C.wires (List.ofFn x)).getD w false
    let L := fun l => Fin.append (fun p => decide (¬I p l)) (unitInput l)
    let P := fun p => Fin.append (unitInput p) (fun l => decide (¬I p l))
    ∀ E : Finset (Fin N × Fin N), (∀ e∈E, ∃ (g : Gate), g∈C.gates ∧
      ∃ a∈g.inputs, ∃ b∈g.inputs, V (unitInput (Fin.castAdd N e.1)) a=true ∧
      V (unitInput (Fin.natAdd N e.2)) b=true ∧ V (L e.2) a=false ∧ V (P e.1) b=false) →
      E.card≤8*C.size)
    (locate : ∀ (n : ℕ) (C : Circuit) (x y z : Fin n → Bool), Monotone2 C →
    (∀ u, x u=true → y u=true ∨ z u=true) →
    circuitFun n C x=true → circuitFun n C y=false → circuitFun n C z=false →
    let V := fun (r : Fin n → Bool) (w : ℕ) => (C.wires (List.ofFn r)).getD w false
    ∃ g∈C.gates, g.op=GateOp.and ∧ ∃ a∈g.inputs, ∃ b∈g.inputs,
       V x a=true ∧ V x b=true ∧ V y a=false ∧ V z a=true ∧ V y b=true ∧ V z b=false)
    (hard : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
    199≤q → N=q^2+q+1 → (∀ l, Fintype.card {p // I p l}=q+1) →
    (∀ p p', p≠p' → ∃! l, I p l ∧ I p' l) → Monotone2 C → (∀ x : Fin (N+N) → Bool, (¬∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) →
      circuitFun (N+N) C x=false) → let V := fun (x : Fin (N+N) → Bool) (w : ℕ) => (C.wires (List.ofFn x)).getD w false
    let L := fun l => Fin.append (fun p => decide (¬I p l)) (unitInput l)
    let P := fun p => Fin.append (unitInput p) (fun l => decide (¬I p l))
    let K := fun (p l : Fin N) (a b : ℕ) =>
      let active := V (pairInput (Fin.castAdd N p) (Fin.natAdd N l))
      (∃ g∈C.gates, g.op=GateOp.and ∧ a∈g.inputs ∧ b∈g.inputs) ∧
      active C.output=true ∧ active a=true ∧ active b=true ∧ V (L l) a < V (L l) b ∧ V (P p) b < V (P p) a
    ∀ E : Finset (Fin N × Fin N),
    (∀ e∈E, I e.1 e.2 ∧ (∃ a b, K e.1 e.2 a b) ∧ ∀ a b, K e.1 e.2 a b →
      V (unitInput (Fin.castAdd N e.1)) a=false ∨ V (unitInput (Fin.natAdd N e.2)) b=false) →
    E.card≤92*C.size)
    : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I inst C hq order lines unique mono accept sound
  classical
  let V := fun (x : Fin (N+N) → Bool) (w : ℕ) => (C.wires (List.ofFn x)).getD w false
  let L := fun (l : Fin N) => Fin.append (fun p => decide (¬I p l)) (fun m => decide (m=l))
  let P := fun (p : Fin N) => Fin.append (fun a => decide (a=p)) (fun l => decide (¬I p l))
  let bill := fun (e : Fin N × Fin N) => ∃ g∈C.gates, ∃ a∈g.inputs, ∃ b∈g.inputs,
    V (unitInput (Fin.castAdd N e.1)) a=true ∧ V (unitInput (Fin.natAdd N e.2)) b=true ∧
    V (L e.2) a=false ∧ V (P e.1) b=false
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  let A := E.filter bill
  let B := E.filter (fun e => ¬bill e)
  have costA : A.card ≤ 8*C.size :=
    price N I C unique mono A (fun _ h => (Finset.mem_filter.mp h).2)
  have costB : B.card ≤ 92*C.size := by
    apply hard q N I C hq order lines unique mono sound B
    intro e he
    obtain ⟨edge,unpaid⟩ := Finset.mem_filter.mp he
    have i := (Finset.mem_filter.mp edge).2
    refine ⟨i,?_,?_⟩
    · let x := pairInput (Fin.castAdd N e.1) (Fin.natAdd N e.2)
      have yes : circuitFun (N+N) C x=true := accept e.1 e.2 i
      have ny : circuitFun (N+N) C (L e.2)=false := by
        apply sound
        rintro ⟨u,v,uv,hu,hv⟩
        have miss : ¬I u e.2 := by simpa only [L,Fin.append_left,decide_eq_true_eq] using hu
        have eq : v=e.2 := by simpa only [L,Fin.append_right,decide_eq_true_eq] using hv
        exact miss (eq ▸ uv)
      have nz : circuitFun (N+N) C (P e.1)=false := by
        apply sound
        rintro ⟨u,v,uv,hu,hv⟩
        have miss : ¬I e.1 v := by simpa only [P,Fin.append_right,decide_eq_true_eq] using hv
        have eq : u=e.1 := by simpa only [P,Fin.append_left,decide_eq_true_eq] using hu
        exact miss (eq ▸ uv)
      have cv : ∀ u, x u=true → L e.2 u=true ∨ P e.1 u=true := by
        intro u h
        rcases of_decide_eq_true h with rfl|rfl
        · exact Or.inr (by simp only [P,Fin.append_left,decide_eq_true_eq])
        · exact Or.inl (by simp only [L,Fin.append_right,decide_eq_true_eq])
      obtain ⟨g,hg,op,a,ha,b,hb,ax,bx,ay,az,by',bz⟩ := locate (N+N) C x (L e.2) (P e.1) mono cv yes ny nz
      exact ⟨a,b,⟨g,hg,op,ha,hb⟩,yes,ax,bx,Bool.lt_iff.mpr ⟨ay,by'⟩,Bool.lt_iff.mpr ⟨bz,az⟩⟩
    · rintro a b ⟨⟨g,hg,_,ga,gb⟩,_,_,_,yl,zp⟩
      by_contra! h
      exact unpaid ⟨g,hg,a,ga,b,gb,Bool.eq_true_of_ne_false h.1,Bool.eq_true_of_ne_false h.2,
        (Bool.lt_iff.mp yl).1,(Bool.lt_iff.mp zp).1⟩
  have part : A.card+B.card=E.card := Finset.card_filter_add_card_filter_not (s:=E) bill
  have lineCard (l : Fin N) : (Finset.univ.filter (fun p => I p l)).card=q+1 := by
    simpa only [Fintype.card_subtype] using lines l
  let fibers (l : Fin N) : Finset (Fin N × Fin N) :=
    (Finset.univ.filter fun p => I p l).map ⟨fun p => (p,l),fun _ _ h => congrArg Prod.fst h⟩
  have fiber (l : Fin N) (e : Fin N × Fin N) : e∈fibers l ↔ I e.1 l ∧ e.2=l := by
    constructor
    · intro h
      obtain ⟨p,hp,eq⟩ := Finset.mem_map.mp h
      change (p,l)=e at eq
      rw [←eq]
      exact ⟨(Finset.mem_filter.mp hp).2,rfl⟩
    · rintro ⟨h,eq⟩
      exact Finset.mem_map.mpr ⟨e.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,Prod.ext rfl eq.symm⟩
  have pieces : E=Finset.univ.biUnion fibers := by
    ext e
    simp only [E,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion,fiber]
    constructor
    · exact fun h => ⟨e.2,h,rfl⟩
    · rintro ⟨_,h,eq⟩
      exact eq ▸ h
  have size : E.card=N*(q+1) := by
    rw [pieces,Finset.card_biUnion]
    · simp [fibers,lineCard]
    · intro l _ m _ ne
      exact Finset.disjoint_left.mpr (fun e hl hm => ne (((fiber _ _).mp hl).2.symm.trans ((fiber _ _).mp hm).2))
  have le : N*q≤N*(q+1) := Nat.mul_le_mul_left N (Nat.le_succ q)
  omega
