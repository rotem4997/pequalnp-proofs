import PEqualNP.Defs
open PEqualNP.AndCount
-- A 19-gate minimum needs at least two excess gate memberships, and a
-- 20-gate minimum at least one. Distinguish a triple from pair-only overlap.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_9053_417
    (prepare : let G := SimpleGraph.fromRel (fun p l : Fin 42 => p.val<21 ∧ 21≤l.val ∧
      (l.val+21-p.val)%21 ∈ ([0,5,7,17,20] : List ℕ))
    let sparse := fun (D : AndCountCircuit 42) => ∀ v : Fin 42,
      {i : Fin D.size | v ∈ D.leftVars i ∨ v ∈ D.rightVars i}.ncard + 16 ≤ D.size
    ∀ C : AndCountCircuit 42, C.WellFormed → C.Computes G → C.size≤20 →
      ∃ D : AndCountCircuit 42, D.WellFormed ∧ D.Computes G ∧ D.size≤C.size ∧ 19≤D.size ∧ sparse D)
    (triple : let G := SimpleGraph.fromRel (fun p l : Fin 42 => p.val<21 ∧ 21≤l.val ∧
      (l.val+21-p.val)%21 ∈ ([0,5,7,17,20] : List ℕ))
    let block := fun (r : Fin 3) => Finset.univ.image (fun j : Fin 14 =>
      Fin.ofNat 42 (if j.val<7 then (9*j.val+r.val)%21 else 21+(9*(j.val-7)+r.val+5)%21))
    let sparse := fun (D : AndCountCircuit 42) => ∀ v : Fin 42,
      {i : Fin D.size | v ∈ D.leftVars i ∨ v ∈ D.rightVars i}.ncard + 16 ≤ D.size
    ∀ D : AndCountCircuit 42, D.WellFormed → D.Computes G → 19≤D.size → D.size≤20 → sparse D →
      (∃ i : Fin D.size, ∀ r : Fin 3, D.gateVal (block r) i=true) →
      ∃ E : AndCountCircuit 42, E.WellFormed ∧ E.Computes G ∧ E.size<D.size)
    (pairs : let G := SimpleGraph.fromRel (fun p l : Fin 42 => p.val<21 ∧ 21≤l.val ∧
      (l.val+21-p.val)%21 ∈ ([0,5,7,17,20] : List ℕ))
    let block := fun (r : Fin 3) => Finset.univ.image (fun j : Fin 14 =>
      Fin.ofNat 42 (if j.val<7 then (9*j.val+r.val)%21 else 21+(9*(j.val-7)+r.val+5)%21))
    let sparse := fun (D : AndCountCircuit 42) => ∀ v : Fin 42,
      {i : Fin D.size | v ∈ D.leftVars i ∨ v ∈ D.rightVars i}.ncard + 16 ≤ D.size
    let live := fun (D : AndCountCircuit 42) (r : Fin 3) =>
      Finset.univ.filter (fun i : Fin D.size => D.gateVal (block r) i=true)
    ∀ D : AndCountCircuit 42, D.WellFormed → D.Computes G → 19≤D.size → D.size≤20 → sparse D →
      (∀ i : Fin D.size, ∃ r : Fin 3, D.gateVal (block r) i=false) →
      21 ≤ D.size + ((live D 0) ∩ (live D 1)).card + (((live D 0) ∪ (live D 1)) ∩ (live D 2)).card →
      ∃ E : AndCountCircuit 42, E.WellFormed ∧ E.Computes G ∧ E.size<D.size) :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : Fin (3 : ℕ) → Fin (14 : ℕ) → Fin (42 : ℕ) := fun (x2 : Fin (3 : ℕ)) (x3 : Fin (14 : ℕ)) => Fin.ofNat (42 : ℕ) (if ↑x3 < (7 : ℕ) then ((9 : ℕ) * ↑x3 + ↑x2) % (21 : ℕ) else (21 : ℕ) + ((9 : ℕ) * (↑x3 - (7 : ℕ)) + ↑x2 + (5 : ℕ)) % (21 : ℕ)); ∀ (x3 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x3.WellFormed → x3.Computes x1 → ∃ (x6 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x7 : Fin (3 : ℕ)), x6.WellFormed ∧ x6.Computes x1 ∧ x6.size ≤ x3.size ∧ (3 : ℕ) * {x8 : Fin x6.size | x6.gateVal (Finset.image (x2 x7) Finset.univ) x8 = Bool.true}.ncard ≤ x6.size := by
  classical
  let R := fun p l : Fin 42 => p.val<21 ∧ 21≤l.val ∧ (l.val+21-p.val)%21 ∈ ([0,5,7,17,20] : List ℕ)
  let G := SimpleGraph.fromRel R
  let block := fun (r : Fin 3) => Finset.univ.image (fun j : Fin 14 =>
      Fin.ofNat 42 (if j.val<7 then (9*j.val+r.val)%21 else 21+(9*(j.val-7)+r.val+5)%21))
  let sparse := fun (D : AndCountCircuit 42) => ∀ v : Fin 42,
      {i : Fin D.size | v ∈ D.leftVars i ∨ v ∈ D.rightVars i}.ncard + 16 ≤ D.size
  let live := fun (D : AndCountCircuit 42) (r : Fin 3) =>
      Finset.univ.filter (fun i : Fin D.size => D.gateVal (block r) i=true)
  let A := AndCountCircuit 42
  let S : A := {
    size := 21
    leftVars := fun i => {Fin.castAdd 21 i}
    leftGates := fun _ => ∅
    rightVars := fun i => Finset.univ.filter (R (Fin.castAdd 21 i))
    rightGates := fun _ => ∅
    outVars := ∅
    outGates := Finset.univ }
  have val (U : Finset (Fin 42)) (i : Fin 21) : S.gateVal U i=true ↔
      Fin.castAdd 21 i ∈ U ∧ ∃ v ∈ U, R (Fin.castAdd 21 i) v := by
    change ((_ && _)=true) ↔ _
    delta AndCountCircuit.sideTrue
    simp [S,and_comm]
  have starWF : S.WellFormed := by intro i; exact ⟨fun j h => (Finset.notMem_empty j h).elim, fun j h => (Finset.notMem_empty j h).elim⟩
  have starOK : S.Computes G := by
    intro U
    change decide ((∃ v ∈ (∅ : Finset (Fin 42)), v ∈ U) ∨ ∃ i ∈ (Finset.univ : Finset (Fin 21)), S.gateVal U i=true)=true ↔ _
    simp only [decide_eq_true_eq,Finset.notMem_empty,false_and,exists_const,false_or,Finset.mem_univ,true_and,val]
    constructor
    · rintro ⟨i,hi,l,hl,edge⟩
      exact ⟨_,hi,_,hl,(show G.Adj _ _ from ⟨fun eq => by have := edge.2.1; rw [← eq] at this; have := i.isLt; simp at * <;> omega,Or.inl edge⟩)⟩
    · rintro ⟨p,hp,l,hl,_,h|h⟩
      · let i : Fin 21 := ⟨p.val,h.1⟩
        have eq : Fin.castAdd 21 i=p := Fin.ext rfl
        exact ⟨i,eq ▸ hp,l,hl,eq ▸ h⟩
      · let i : Fin 21 := ⟨l.val,h.1⟩
        have eq : Fin.castAdd 21 i=l := Fin.ext rfl
        exact ⟨i,eq ▸ hl,p,hp,eq ▸ h⟩
  have starCount : (live S 0).card≤7 := by
    let pts := Finset.univ.filter (fun i : Fin 21 => Fin.castAdd 21 i ∈ block 0)
    have sub : live S 0 ⊆ pts := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((val _ _).mp (Finset.mem_filter.mp hi).2).1⟩
    have count : pts.card=7 := by decide +kernel
    exact (Finset.card_le_card sub).trans count.le
  change ∀ C : A, C.WellFormed → C.Computes G → ∃ (D : A) (r : Fin 3), D.WellFormed ∧ D.Computes G ∧ D.size≤C.size ∧ 3*{i : Fin D.size | D.gateVal (block r) i=true}.ncard≤D.size
  intro C wf correct
  let minPred := fun k : ℕ => ∃ D : A, D.WellFormed ∧ D.Computes G ∧ D.size=k
  have existsMin : ∃ k, minPred k := ⟨C.size,C,wf,correct,rfl⟩
  obtain ⟨B,bwf,bok,bcost⟩ := Nat.find_spec existsMin
  have least (E : A) (ew : E.WellFormed) (eh : E.Computes G) : B.size≤E.size := by
    rw [bcost]
    exact Nat.find_min' existsMin ⟨E,ew,eh,rfl⟩
  have bc := least C wf correct
  have ncard (D : A) (r : Fin 3) :
      {i : Fin D.size | D.gateVal (block r) i=true}.ncard = (live D r).card := by
    change _ = (Finset.univ.filter _).card
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  by_cases big : 21≤B.size
  · refine ⟨S,0,starWF,starOK,le_trans big bc,?_⟩
    change 3*{i : Fin S.size | S.gateVal (block 0) i=true}.ncard≤S.size
    rw [ncard]; change 3*(live S 0).card≤21; omega
  have tiny : B.size≤20 := by omega
  obtain ⟨D,dw,dh,leB,lo,raw⟩ := prepare B bwf bok tiny
  have eq := le_antisymm leB (least D dw dh)
  have cap : D.size≤20 := leB.trans tiny
  by_cases good : ∃ r : Fin 3, 3*(live D r).card≤D.size
  · obtain ⟨r,hr⟩ := good
    refine ⟨D,r,dw,dh,leB.trans bc,?_⟩
    change 3*{i : Fin D.size | D.gateVal (block r) i=true}.ncard≤D.size
    rwa [ncard]
  have sev (r : Fin 3) : 7≤(live D r).card := by
    have h : ¬3*(live D r).card≤D.size := fun h => good ⟨r,h⟩
    omega
  have smaller : ∃ E : A, E.WellFormed ∧ E.Computes G ∧ E.size<D.size := by
    by_cases shared : ∃ i : Fin D.size, ∀ r : Fin 3, D.gateVal (block r) i=true
    · exact triple D dw dh lo cap raw shared
    · push Not at shared
      apply pairs D dw dh lo cap raw (fun i => by change ∃ r : Fin 3, D.gateVal (block r) i=false; simpa using shared i)
      change 21 ≤ D.size + (live D 0 ∩ live D 1).card + ((live D 0 ∪ live D 1) ∩ live D 2).card
      have ab := Finset.card_union_add_card_inter (live D 0) (live D 1)
      have abc := Finset.card_union_add_card_inter ((live D 0) ∪ (live D 1)) (live D 2)
      have ub := Finset.card_le_univ ((live D 0) ∪ (live D 1) ∪ (live D 2))
      simp only [Fintype.card_fin] at ub
      have h0 := sev 0; have h1 := sev 1; have h2 := sev 2
      omega
  obtain ⟨E,ew,eh,es⟩ := smaller
  have := least E ew eh
  omega

