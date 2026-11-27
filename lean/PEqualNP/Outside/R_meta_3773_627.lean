import Mathlib
import PEqualNP.Defs

-- Supply the first gate as one extra input to a circuit with 62 remaining slots.
-- The labels are tested on incident pairs and on the independent boundary inputs.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.Defs.LratEncoding in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3773_627
    (search : let D : Finset (Fin 13) := {0,1,3,9}
      let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun l : Fin 13 => ∀ p∈s, p+l∉D
      let P := (List.finRange 13).flatMap fun p => D.toList.map fun d => incidenceInput {p} {d-p}
      let small := (List.range 4).flatMap fun k => ((Finset.univ : Finset (Fin 13)).powersetCard k).toList
      let M := small.flatMap fun s => [incidenceInput s (off s),incidenceInput (off s) s]
      ∃ h : Gate, (h.op=.and ∧ h.inputs=[0,13] ∨ h.op=.or ∧ h.inputs∈[[0,1],[0,13],[2,13]]) ∧
        let key := fun (x : List Bool) => (x ++ [h.op.eval (h.inputs.map fun i => x.getD i false)]).foldr Nat.bit 0
        let on := P.map key
        FormulaSat (enc 27 62 (fun r => on.contains r) (on ++ M.map key).eraseDups))
    (reconstruct : ∀ (n s : ℕ) (h : Gate) (P M : List (List Bool)),
      (h.op=.and ∨ h.op=.or) → h.inputs.length ≤ 2 →
      (∀ x ∈ P ++ M, x.length=n) → (∀ x ∈ M, x∉P) →
      (let key := fun (x : List Bool) => (x ++ [h.op.eval (h.inputs.map fun i => x.getD i false)]).foldr Nat.bit 0
       let on := P.map key
       FormulaSat (enc (n+1) s (fun r => on.contains r) (on ++ M.map key).eraseDups)) →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s+1 ∧ C.gates.head?=some h ∧
        (∀x∈P,C.eval x=true) ∧ ∀x∈M,C.eval x=false) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∃ (x3 : PEqualNP.CircuitLowerBounds.Gate), x2.gates.head? = Option.some x3 ∧ (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3.inputs = [(0 : ℕ), (13 : ℕ)] ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs ∈ [[(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(2 : ℕ), (13 : ℕ)]])) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 + x4 ∈ x1 → x2.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) x3) (Fin.natAdd (13 : ℕ) x4))) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card ≤ (3 : ℕ) → x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 + x6 ∉ x1)) x5) = Bool.false ∧ x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x6 + x7 ∉ x1)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) x5) = Bool.false := by
  let D : Finset (Fin 13) := {0,1,3,9}
  let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun l : Fin 13 => ∀ p∈s, p+l∉D
  let P := (List.finRange 13).flatMap fun p => D.toList.map fun d => incidenceInput {p} {d-p}
  let small := (List.range 4).flatMap fun k => ((Finset.univ : Finset (Fin 13)).powersetCard k).toList
  let M := small.flatMap fun s => [incidenceInput s (off s),incidenceInput (off s) s]
  obtain ⟨h,head,sat⟩ := search
  have expandInput (s t : Finset (Fin 13)) : incidenceInput s t =
      List.ofFn (fun p : Fin 13 => decide (p ∈ s)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ t)) := rfl
  have inSmall {s : Finset (Fin 13)} (bound : s.card ≤ 3) : s∈small := by
    apply List.mem_flatMap.mpr
    exact ⟨s.card,List.mem_range.mpr (by omega),Finset.mem_toList.mpr
      (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,rfl⟩)⟩
  have positive (x : List Bool) (mem : x∈P) :
      ∃ p l : Fin 13, p+l∈D ∧ x=incidenceInput {p} {l} := by
    obtain ⟨p,_,found⟩ := List.mem_flatMap.mp mem
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp found
    exact ⟨p,d-p,by rw [show p+(d-p)=d by abel];exact Finset.mem_toList.mp hd,rfl⟩
  have negative (x : List Bool) (mem : x∈M) :
      ∃ s t : Finset (Fin 13), x=incidenceInput s t ∧ ∀p∈s, ∀l∈t, p+l∉D := by
    obtain ⟨u,_,found⟩ := List.mem_flatMap.mp mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl | rfl
    · exact ⟨u,off u,rfl,fun p hp l hl => (Finset.mem_filter.mp hl).2 p hp⟩
    · refine ⟨off u,u,rfl,?_⟩
      intro p hp l hl
      simpa only [add_comm l p] using (Finset.mem_filter.mp hp).2 l hl
  have readPoint (s t : Finset (Fin 13)) (p : Fin 13) :
      (incidenceInput s t).getD p.val false=decide (p∈s) := by
    rw [expandInput,List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using p.isLt),
      List.getD_eq_getElem _ false (by simpa only [List.length_ofFn] using p.isLt),List.getElem_ofFn]
  have readLine (s t : Finset (Fin 13)) (l : Fin 13) :
      (incidenceInput s t).getD (13+l.val) false=decide (l∈t) := by
    rw [expandInput,List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn];omega),
      List.length_ofFn,show 13+l.val-13=l.val by omega,
      List.getD_eq_getElem _ false (by simpa only [List.length_ofFn] using l.isLt),List.getElem_ofFn]
  have len (x : List Bool) (mem : x∈P++M) : x.length=26 := by
    rcases List.mem_append.mp mem with on | offRow
    · obtain ⟨p,l,_,rfl⟩ := positive x on; simp only [expandInput,List.length_append,List.length_ofFn] <;> decide
    · obtain ⟨s,t,rfl,_⟩ := negative x offRow; simp only [expandInput,List.length_append,List.length_ofFn] <;> decide
  have separate : ∀ x∈M, x∉P := by
    intro x no yes
    obtain ⟨p,l,inc,pos⟩ := positive x yes
    obtain ⟨s,t,neg,apart⟩ := negative x no
    have same := neg.symm.trans pos
    have pa := congrArg (fun row : List Bool => row.getD p.val false) same
    have la := congrArg (fun row : List Bool => row.getD (13+l.val) false) same
    change (incidenceInput s t).getD p.val false = (incidenceInput {p} {l}).getD p.val false at pa
    change (incidenceInput s t).getD (13+l.val) false = (incidenceInput {p} {l}).getD (13+l.val) false at la
    rw [readPoint,readPoint] at pa;rw [readLine,readLine] at la
    exact apart p (by simpa using pa) l (by simpa using la) inc
  have proper : (h.op=.and ∨ h.op=.or) ∧ h.inputs.length ≤ 2 := by
    rcases head with ⟨op,inp⟩ | ⟨op,inp⟩
    · exact ⟨Or.inl op,by simp [inp]⟩
    · refine ⟨Or.inr op,?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at inp
      rcases inp with i | i | i <;> simp [i]
  obtain ⟨C,mono,budget,first,yes,no⟩ := reconstruct 26 62 h P M proper.1 proper.2 len separate sat
  refine ⟨C,mono,budget,⟨h,first,head⟩,?_,?_⟩
  · intro p l inc
    have pointList : ∀ p l : Fin 13, List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l)) =
        incidenceInput {p} {l} := by decide +kernel
    rw [pointList]
    apply yes
    apply List.mem_flatMap.mpr
    refine ⟨p,List.mem_finRange _,List.mem_map.mpr ⟨p+l,Finset.mem_toList.mpr inc,?_⟩⟩
    rw [show p+l-p=l by abel]
  · intro s short
    have fst : incidenceInput s (off s) ∈ M :=
      List.mem_flatMap.mpr ⟨s,inSmall short,by simp⟩
    have snd : incidenceInput (off s) s ∈ M :=
      List.mem_flatMap.mpr ⟨s,inSmall short,by simp⟩
    have split (a b : Fin 13 → Bool) : List.ofFn (fun i : Fin (13+13) => Fin.addCases a b i) = List.ofFn a ++ List.ofFn b := by
      rw [List.ofFn_add]
      congr 1 <;> congr 1 <;> funext i <;> first | exact Fin.addCases_left i | exact Fin.addCases_right i
    rw [split,split]
    constructor
    · simpa only [expandInput,off,Finset.mem_filter,Finset.mem_univ,true_and] using no _ fst
    · simpa only [expandInput,off,Finset.mem_filter,Finset.mem_univ,true_and,add_comm] using no _ snd
