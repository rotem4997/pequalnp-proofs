import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2008_873
    (small : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit), 100<q → q<200 → N=q^2+q+1 →
      (∀ l,Fintype.card {p : Fin N // I p l}=q+1) →
      (∀ p r : Fin N,p≠r → ∃! l,I p l ∧ I r l) → Monotone2 C →
      (∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l))=true) →
      (∀ x : Fin (N+N)→Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q →
        (¬∃ p l,I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) →
        circuitFun (N+N) C x=false) → N*q≤100*C.size)
    (rectify : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit), 0<q →
      (∀ p r : Fin N,p≠r → ∃! l,I p l ∧ I r l) → Monotone2 C →
      (∀ x : Fin (N+N)→Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q →
        (¬∃ p l,I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) →
        circuitFun (N+N) C x=false) →
      ∀ a b : ℕ, ¬((∀ i∈[a,b],∃ p : Fin N→Bool,
        (C.wires (List.ofFn p ++ List.replicate N false)).getD i false ≠
        (C.wires (List.ofFn p ++ List.replicate N true)).getD i false) ∨
      ∀ i∈[a,b],∃ l : Fin N→Bool,
        (C.wires (List.replicate N false ++ List.ofFn l)).getD i false ≠
        (C.wires (List.replicate N true ++ List.ofFn l)).getD i false) →
      let wire := fun (i : ℕ) (p l : Fin N→Bool) =>
        (C.wires (List.ofFn p ++ List.ofFn l)).getD i false
      let atom := fun p t : Fin N => decide (t=p)
      (∃ i∈[a,b],∀ p l,(wire a p l && wire b p l)=wire i p l) ∨
       ∃ f g : (Fin N→Bool)→Bool,(∀ p l,(wire a p l && wire b p l)=(f p && g l)) ∧
       ((∀ p w : Fin N, (f (atom p) && g (atom w))=true →
           circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N w))=true) →
         ∀ p r u v : Fin N, (f (atom p) && g (atom u))=true →
           (f (atom r) && g (atom v))=true → p=r ∨ u=v))
    (pricing : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit), 200≤q → N=q^2+q+1 →
      (∀ l,Fintype.card {p : Fin N // I p l}=q+1) →
      (∀ p r : Fin N,p≠r → ∃! l,I p l ∧ I r l) → Monotone2 C →
      (∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l))=true) →
      (∀ x : Fin (N+N)→Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q →
        (¬∃ p l,I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) →
        circuitFun (N+N) C x=false) →
      let atm := fun i j : Fin N => decide (j=i)
      let read := fun (t : ℕ) (p w : Fin N) => (C.wires (List.ofFn (atm p) ++ List.ofFn (atm w))).getD t false
      let hit := fun (a b : ℕ) (p w : Fin N) => read a p w && read b p w
      ∀ E : Finset ℕ, (∀ j (g : Gate) (a b : ℕ),C.gates[j]?=some g → g.op=.and →
        g.inputs=[a,b] → j∉E →
        (∃ i∈[a,b],∀ p w,hit a b p w=read i p w) ∨
          ((∀ p w,hit a b p w=true → I p w) →
          ∀ p r u v,hit a b p u=true → hit a b r v=true → p=r ∨ u=v)) →
      100*E.card<N*q → N*q≤100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ (x15 : Finset ℕ), (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x16]? = Option.some x17 → x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x16 ∉ x15 → ¬((∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.false)).getD x21 Bool.false ≠ (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.true)).getD x21 Bool.false) ∨ ∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x23)).getD x21 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x23)).getD x21 Bool.false)) → (100 : ℕ) * x15.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I inst C hq order lines joins mono output inputs pos sound E outside budget
  by_cases low : q<200
  · exact small q N I C hq low order lines joins mono pos sound
  apply pricing q N I C (by omega) order lines joins mono pos sound E _ budget
  intro j g a b hj op pins fresh
  have h := rectify q N I C (by omega) joins mono sound a b (by simpa only [pins] using outside j g hj op fresh)
  rcases h with ⟨i,hi,copy⟩|⟨f,z,fac,stars⟩
  · exact Or.inl ⟨i,hi,fun p w => copy _ _⟩
  · right
    intro safe p r u v first second
    apply stars (fun x y hr => pos x y (safe x y ((fac _ _).trans hr))) p r u v
    · exact (fac _ _).symm.trans first
    · exact (fac _ _).symm.trans second
