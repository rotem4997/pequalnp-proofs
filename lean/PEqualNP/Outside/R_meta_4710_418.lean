import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4710_418
    (single : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ) (T : Finset (Fin N × Fin N)), (∀ p r,p≠r → ∃! l,I p l ∧ I r l) → PEqualNP.TopForm.IsAO2 (N+N) C → (∀ j∈A,j<C.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op=.and) →
      (∀ p l,¬I p l → ∀ j∈A,PEqualNP.EdgeOwnership.gateVal (N+N) C j (fun i : Fin (N+N) => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l))=false) →
      (∀ e∈T,∃ j∈A,[1,1]∈(PEqualNP.ReadK.readVectors C (N+N) [e.1.val,N+e.2.val] 1).getD (N+N+j) []) → T.card≤4*C.size)
    (repeated : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ) (T : Finset (Fin N × Fin N)), 300≤q → N=q^2+q+1 → (∀ l,Fintype.card {p : Fin N // I p l}=q+1) → (∀ p r,p≠r → ∃! l,I p l ∧ I r l) → PEqualNP.TopForm.IsAO2 (N+N) C → (∀ j∈A,j<C.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op=.and) → (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q → (¬∃ p l,I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → ∀ j∈A,PEqualNP.EdgeOwnership.gateVal (N+N) C j x=false) →
      (∀ e∈T,I e.1 e.2 ∧ (∃ j∈A,PEqualNP.EdgeOwnership.gateVal (N+N) C j (fun i : Fin (N+N) => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true) ∧ ¬∃ j∈A,[1,1]∈(PEqualNP.ReadK.readVectors C (N+N) [e.1.val,N+e.2.val] 1).getD (N+N+j) []) →
      96*C.size<T.card → N*q≤100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset ℕ), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x14 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x14 ∧ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x15]? = Option.some x16 → ∃ (x18 : ℕ) (x19 : ℕ), x16.inputs = [x18, x19] ∧ x18 < x19 ∧ x19 < x2 + x2 + x15) → (∀ x16 ∈ x6, x16 < x5.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x16).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x17 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x17 = Bool.true ↔ ∃ x18 ∈ x6, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 x18 x17 = Bool.true) → (∀ (x18 x19 : Fin x2), x3 x18 x19 → ∃ x21 ∈ x6, (PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 x21 fun (x22 : Fin (x2 + x2)) => Decidable.decide (x22 = Fin.castAdd x2 x18 ∨ x22 = Fin.natAdd x2 x19)) = Bool.true) → (∀ (x19 : Fin (x2 + x2) → Bool), Fintype.card { x20 : Fin x2 // x19 (Fin.natAdd x2 x20) = Bool.true } ≤ x1 → (¬∃ (x21 : Fin x2) (x22 : Fin x2), x3 x21 x22 ∧ x19 (Fin.castAdd x2 x21) = Bool.true ∧ x19 (Fin.natAdd x2 x22) = Bool.true) → ∀ x22 ∈ x6, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 x22 x19 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I inst C A hq hn degree unique mono _ _ _ rows valid _ coverage sound
  have rowAt (j) (hj : j<C.gates.length) :
      ∃ a b,(PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs=[a,b] ∧ a<b ∧ b<N+N+j := by
    obtain ⟨a,b,hs,lt,up⟩ := rows j C.gates[j] (List.getElem?_eq_getElem hj)
    change ∃ a b,(C.gates.getD j ⟨.or,[]⟩).inputs=[a,b] ∧ a<b ∧ b<N+N+j
    rw [List.getD_eq_getElem _ _ hj]
    exact ⟨a,b,hs,lt,up⟩
  have ao : PEqualNP.TopForm.IsAO2 (N+N) C := by
    refine ⟨fun g hg => (mono g hg).1,?_,?_⟩
    · intro j hj i hi
      obtain ⟨a,b,hs,lt,up⟩ := rowAt j hj
      rw [hs] at hi
      rcases (by simpa using hi : i=a ∨ i=b) with rfl|rfl <;> omega
    · intro g hg
      obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨a,b,h,_,_⟩ := rows j g (by rw [List.getElem?_eq_getElem hj,eq])
      simp [h]
  have pairSafe (p l : Fin N) (no : ¬I p l) : ∀ j∈A,PEqualNP.EdgeOwnership.gateVal (N+N) C j (fun i : Fin (N+N) => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l))=false := by
    have dis (a b : Fin N) : Fin.castAdd N a ≠ Fin.natAdd N b := by intro eq;have h := congrArg Fin.val eq;change a.val=N+b.val at h;omega
    apply sound
    · have s : Fintype.card {t : Fin N // ((fun i : Fin (N+N) => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)) (Fin.natAdd N t))=true}≤1 := by
        apply Fintype.card_le_one_iff_subsingleton.mpr
        constructor
        intro a b
        apply Subtype.ext
        have ha := of_decide_eq_true a.property
        have hb := of_decide_eq_true b.property
        have ea := congrArg Fin.val (ha.resolve_left (dis _ _).symm)
        have eb := congrArg Fin.val (hb.resolve_left (dis _ _).symm)
        apply Fin.ext
        change N+a.val.val=N+l.val at ea
        change N+b.val.val=N+l.val at eb
        omega
      exact s.trans (by omega)
    · rintro ⟨a,b,adj,x,y⟩
      have ha := of_decide_eq_true x
      have hb := of_decide_eq_true y
      have ea : a=p := Fin.ext (congrArg (fun v : Fin (N+N) => v.val) (ha.resolve_right (dis _ _)))
      have eq := congrArg Fin.val (hb.resolve_left (dis _ _).symm)
      have eb : b=l := Fin.ext (by change N+b.val=N+l.val at eq;omega)
      exact no (ea ▸ eb ▸ adj)
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  let has := fun e : Fin N × Fin N => ∃ j∈A,[1,1]∈(PEqualNP.ReadK.readVectors C (N+N) [e.1.val,N+e.2.val] 1).getD (N+N+j) []
  let L := E.filter has
  let H := E.filter (fun e => ¬has e)
  have upper := single N I C A L unique ao valid pairSafe (fun e h => (Finset.mem_filter.mp h).2)
  have residual (e) (he : e∈H) : I e.1 e.2 ∧ (∃ j∈A,PEqualNP.EdgeOwnership.gateVal (N+N) C j (fun i : Fin (N+N) => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true) ∧ ¬has e := by
    have h := Finset.mem_filter.mp he
    have inc := (Finset.mem_filter.mp h.1).2
    exact ⟨inc,coverage _ _ inc,h.2⟩
  by_contra! small
  apply Nat.not_le_of_lt small
  apply repeated q N I C A H hq hn degree unique ao valid sound residual
  have equiv : {e : Fin N × Fin N // I e.1 e.2} ≃ (Σ l : Fin N,{p : Fin N // I p l}) :=
    {toFun := fun e => ⟨e.1.2,e.1.1,e.2⟩
     invFun := fun e => ⟨⟨e.2.1,e.1⟩,e.2.2⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}
  have count : E.card=N*(q+1) := by
    calc
      _ = Fintype.card {e : Fin N × Fin N // I e.1 e.2} := (Fintype.card_subtype _).symm
      _ = _ := Fintype.card_congr equiv
      _ = _ := by rw [Fintype.card_sigma];simp [degree]
  have both : L.card+H.card=E.card := Finset.card_filter_add_card_filter_not _
  rw [count,Nat.mul_add,Nat.mul_one] at both
  omega
