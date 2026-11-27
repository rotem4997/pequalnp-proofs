import Mathlib
import PEqualNP.Defs

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

set_option maxRecDepth 6000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_909_418
    (compile : ∀ (n k : ℕ),
    let A := Finset (Finset (Fin n))
    let U := (Finset.univ : Finset (Fin k))
    ∀ (T : A) (B : Fin k → Finset (Fin n)) (L R : Fin k → A) (Z : A),
    let V := fun v : Fin n => T.filter (v∈·)
    let H := fun i => L i ∩ R i
    let ok := fun i (S : A) => ∀ t∈S,
      (∃ v∈B i,t∈V v ∧ V v⊆S) ∨ ∃ j < i,t∈H j ∧ H j⊆S
    (∀ i,ok i (L i) ∧ ok i (R i)) → (∀ t∈Z,∃ i,t∈H i ∧ H i⊆Z) →
    ∃ C : AndCountCircuit n,C.WellFormed ∧ C.size=k ∧
      (let W := (Finset.univ : Finset (Fin C.size)); ∀ v,(W.filter (fun i : Fin C.size => v∈C.leftVars i ∨ v∈C.rightVars i)).card≤
       (U.filter (fun i => v∈B i)).card) ∧ ∀ t∈T,(C.eval t=true ↔ t∈Z))
    (search : let A := Finset (Finset (Fin 10))
    let E := fun (a b : Fin 10) => decide (
      (a.val < 5 ∧ (b.val=(a.val+1)%5 ∨ b.val=a.val+5)) ∨ (5 ≤ a.val ∧ b.val=5+(a.val+2)%5))
    ∃ (T Z : A) (k : ℕ) (B : Fin k → Finset (Fin 10)) (L R : Fin k → A),
    k≤6 ∧ (let U := (Finset.univ : Finset (Fin k)); ∀ v,(U.filter (fun i => v∈B i)).card≤2) ∧
    (∀ I : Finset (Fin 10),
      (∀ a∈I,∀ b∈I,E a b=false) →
      (∀ w : Fin 10,w∉I → ∃ a∈I,E a w=true ∨ E w a=true) →
      I∈T ∧ I∉Z ∧ ∀ w : Fin 10,w∉I → ∃ z∈T,z∈Z ∧ z⊆insert w I) ∧
    let V := fun v : Fin 10 => T.filter (v∈·)
    let H := fun i => L i ∩ R i
    let ok := fun i (S : A) => ∀ t∈S,
      (∃ v∈B i,t∈V v ∧ V v⊆S) ∨ ∃ j < i,t∈H j ∧ H j⊆S
    (∀ i,ok i (L i) ∧ ok i (R i)) ∧ (∀ t∈Z,∃ i,t∈H i ∧ H i⊆Z)) :
    ∀ G : SimpleGraph (Fin 10), G = SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))) →
  ∃ C : PEqualNP.AndCount.AndCountCircuit 10, C.WellFormed ∧ C.size ≤ 6 ∧
    (∀ v : Fin 10, (Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2) ∧
    (∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 10, w ∉ I → C.eval (insert w I) = true) := by
  intro G eqG
  let E := fun (a b : Fin 10) => decide (
    (a.val < 5 ∧ (b.val=(a.val+1)%5 ∨ b.val=a.val+5)) ∨ (5 ≤ a.val ∧ b.val=5+(a.val+2)%5))
  obtain ⟨T,Z,k,B,L,R,sz,budget,cover,side,out⟩ := search
  obtain ⟨C,wf,count,reads,values⟩ := compile 10 k T B L R Z side out
  refine ⟨C,wf,count.trans_le sz,fun v => (reads v).trans (budget v),?_⟩
  let G0 : SimpleGraph (Fin 10) := SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ)))
  have adjacency : ∀ a b : Fin 10,G0.Adj a b ↔ E a b=true ∨ E b a=true := by decide +kernel
  have sideMono (U W : Finset (Fin 10)) (sub : U⊆W) (B : Finset (Fin 10)) (A : Finset (Fin C.size))
      (i : Fin C.size) (v v' : Fin C.size → Bool) (up : ∀ j,v j=true → v' j=true) :
      sideTrue U B A i v=true → sideTrue W B A i v'=true := by
    intro old
    rcases of_decide_eq_true old with ⟨x,h,on⟩|⟨j,h,e,on⟩
    · exact decide_eq_true (Or.inl ⟨x,h,sub on⟩)
    · exact decide_eq_true (Or.inr ⟨j,h,e,up j on⟩)
  have mono (U W : Finset (Fin 10)) (sub : U⊆W) : C.eval U=true → C.eval W=true := by
    have fuel (d : ℕ) : ∀ i,C.gateValFuel U d i=true → C.gateValFuel W d i=true := by
      induction d with
      | zero => intro i h;exact (Bool.false_ne_true h).elim
      | succ d ih =>
        intro i
        change (_ && _)=true → (_ && _)=true
        rw [Bool.and_eq_true_iff,Bool.and_eq_true_iff]
        exact fun h => ⟨sideMono U W sub _ _ _ _ _ ih h.1,sideMono U W sub _ _ _ _ _ ih h.2⟩
    intro old
    rcases of_decide_eq_true old with ⟨v,m,h⟩|⟨i,m,h⟩
    · exact decide_eq_true (Or.inl ⟨v,m,sub h⟩)
    · exact decide_eq_true (Or.inr ⟨i,m,fuel C.size i h⟩)
  subst G
  intro I independent maximal
  have indep : ∀ a∈I,∀ b∈I,E a b=false := by
    intro a ha b hb
    cases e : E a b
    · rfl
    · exact False.elim (independent a ha b hb ((adjacency a b).mpr (Or.inl e)))
  have maxI (w : Fin 10) (hw : w∉I) : ∃ a∈I,E a w=true ∨ E w a=true := by
    obtain ⟨a,ha,on⟩ := maximal w hw
    exact ⟨a,ha,(adjacency a w).mp on⟩
  obtain ⟨inT,nz,extensions⟩ := cover I indep maxI
  constructor
  · cases e : C.eval I
    · rfl
    · exact False.elim (nz ((values I inT).mp e))
  · intro w hw
    obtain ⟨z,zt,zp,sub⟩ := extensions w hw
    exact mono z _ sub ((values z zt).mpr zp)
