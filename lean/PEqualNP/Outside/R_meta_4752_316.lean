import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.GenericRejection

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_4752_316
    (tests : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.Monotone2 C →
  ((∀ P L, C.eval (PEqualNP.GenericRejection.incidenceInput P L) = PEqualNP.GenericRejection.incidenceFun S P L) ↔
    PEqualNP.GenericRejection.RightOnIncidentPairs S C ∧ ∀ P L,
      PEqualNP.GenericRejection.IsMaximalFalse S P L → C.eval (PEqualNP.GenericRejection.incidenceInput P L)=false))
    (triple : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
    2 ≤ q → N = q^2+q+1 →
    (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
    (∀ p r : Fin N, p≠r → ∃! l : Fin N, I p l ∧ I r l) →
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N+N) C
      (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)) = true) →
    (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q →
      (¬∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C x = false) → 3*N ≤ C.size)
    (structureCost : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 14 C → ∀ g : ℕ, g<C.gates.length →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op=PEqualNP.CircuitLowerBounds.GateOp.and →
  PEqualNP.TopForm.opnd C g 0≠PEqualNP.TopForm.opnd C g 1 →
  let V := fun (w : ℕ) (a b : Fin 14) => PEqualNP.CleanedNonEdge.wireVal 14 C w (PEqualNP.EdgeOwnership.pairInput a b)
  let marked := fun w => V w 0 7=true ∧ V w 0 0=false ∧ V w 7 7=false
  let nodes := (Finset.range (g+1)).filter (fun j => marked (14+j))
  let reads := fun (a b : ℕ) => 14+a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C b).inputs
  V (14+g) 0 7=true → (∀ k : Fin 2, V (PEqualNP.TopForm.opnd C g k) 0 0=false ∧ V (PEqualNP.TopForm.opnd C g k) 7 7=false) →
  (∀ k : Fin 2,marked (PEqualNP.TopForm.opnd C g k)) ∧ (2 ≤ (nodes.filter (fun b => (PEqualNP.MetaComplexity.NestedCover.gateAt C b).op.eval []=true ∧ ∀ a∈nodes, ¬reads a b)).card ∨
    ∃ a∈nodes, 2 ≤ (nodes.filter (reads a)).card))
    (lastCase :
    let S := fun l : Fin 7 => ({l,l+1,l+3} : Finset (Fin 7))
    ∀ C : Circuit, IsAO2 14 C → (∀ h∈C.gates,h.inputs.Nodup) → 21 ≤ C.size → C.size ≤ 27 →
      RightOnIncidentPairs S C → (∀ P L, IsMaximalFalse S P L → C.eval (incidenceInput P L)=false) →
      ∀ g : ℕ, (gateAt C g).op=.and → InCone 14 C g (C.output-14) →
      let V := fun (w : ℕ) (a b : Fin 14) => PEqualNP.CleanedNonEdge.wireVal 14 C w (PEqualNP.EdgeOwnership.pairInput a b)
      let marked := fun w => V w 0 7=true ∧ V w 0 0=false ∧ V w 7 7=false
      let nodes := (Finset.range (g+1)).filter (fun j => marked (14+j))
      let reads := fun (a b : ℕ) => 14+a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C b).inputs
      (∀ k : Fin 2, marked (opnd C g k)) → (2 ≤ (nodes.filter (fun b => (PEqualNP.MetaComplexity.NestedCover.gateAt C b).op.eval []=true ∧ ∀ a∈nodes, ¬reads a b)).card ∨
    ∃ a∈nodes, 2 ≤ (nodes.filter (reads a)).card) → False) :
  ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ)) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x3 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false ∧ PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by

  rintro ⟨C,small,well,correct,g,op,cone,hit,miss⟩
  classical
  let S (l : Fin 7) := ({l,l+1,l+3} : Finset (Fin 7))
  let I (p l : Fin 7) := p=l ∨ p=l+1 ∨ p=l+3
  have mem (l p : Fin 7) : p∈S l ↔ I p l := by simp only [S,I,Finset.mem_insert,Finset.mem_singleton]
  have member (j : ℕ) (hj : j<C.gates.length) : C.gates[j]?=some (gateAt C j) := by
    rw [List.getElem?_eq_getElem hj]
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
  have ao : IsAO2 14 C := by
    refine ⟨?_,?_,?_⟩
    · intro h present
      obtain ⟨j,atj⟩ := List.mem_iff_getElem?.mp present
      exact (well j h atj).1
    · intro j hj w hw
      obtain ⟨a,b,args,_,ha,hb⟩ := (well j _ (member j hj)).2
      rw [args] at hw
      rcases List.mem_cons.mp hw with rfl|h
      · exact ha
      · exact (List.mem_singleton.mp h) ▸ hb
    · intro h present
      obtain ⟨j,atj⟩ := List.mem_iff_getElem?.mp present
      obtain ⟨a,b,args,_,_,_⟩ := (well j _ atj).2
      simp [args]
  have uniquePins : ∀ h∈C.gates,h.inputs.Nodup := by
    intro h present
    obtain ⟨j,atj⟩ := List.mem_iff_getElem?.mp present
    obtain ⟨a,b,args,ne,_,_⟩ := (well j _ atj).2
    simp [args,ne]
  have mono : Monotone2 C := fun h hh => ⟨by simpa using ao.1 h hh,(ao.2.2 h hh).le⟩
  have table (P L : Finset (Fin 7)) : C.eval (incidenceInput P L)=incidenceFun S P L := by
    let x := Fin.append (fun p : Fin 7 => decide (p∈P)) (fun l : Fin 7 => decide (l∈L))
    have row : List.ofFn x=incidenceInput P L := List.ofFn_fin_append _ _
    apply Bool.eq_iff_iff.mpr
    rw [←row,correct]
    change _ ↔ decide (∃ p∈P,∃ l∈L,p∈S l)=true
    simp only [decide_eq_true_eq,x,Fin.append_left,Fin.append_right,mem]
    constructor
    · rintro ⟨p,l,on,hp,hl⟩
      exact ⟨p,hp,l,hl,on⟩
    · rintro ⟨p,hp,l,hl,on⟩
      exact ⟨p,l,on,hp,hl⟩
  obtain ⟨positive,negative⟩ := (tests 7 7 S C mono).mp table
  have incidence : ∀ p r : Fin 7,p≠r → ∃ l : Fin 7, (I p l ∧ I r l) ∧ ∀ m : Fin 7,(I p m ∧ I r m) → m=l := by
    dsimp only [I]
    decide +kernel
  have lower : 21 ≤ C.size := triple 2 7 I C (by decide) (by decide)
    (by dsimp only [I];decide +kernel) incidence mono (by
      intro p l edge
      apply (correct _).mpr
      exact ⟨p,l,edge,by simp,by simp⟩) (by
      intro x _ no
      exact Bool.eq_false_iff.mpr fun h => no ((correct x).mp h))
  have valid : g<C.gates.length := by
    by_contra! out
    have bad : gateAt C g=⟨GateOp.or,[]⟩ := List.getD_eq_default _ _ out
    rw [bad] at op
    contradiction
  obtain ⟨a,b,ins,ne,_,_⟩ := (well g _ (member g valid)).2
  have different : opnd C g 0≠opnd C g 1 := by
    change (gateAt C g).inputs.getD 0 0 ≠ (gateAt C g).inputs.getD 1 0
    rw [ins]
    exact ne
  obtain ⟨operands,split⟩ := structureCost C ao g valid op different hit miss
  exact lastCase C ao uniquePins lower small positive negative g op cone operands split
