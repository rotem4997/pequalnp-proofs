import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover

-- A free input that is false or repeats an existing coordinate carries no new information.
-- Replace its readers without adding a gate, including ANDs that must become constant false.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_3803_418
  (within : ∀ (C : Circuit) (J : List Nat), J ∈ [[0,1],[13,14]] → Monotone2 C → ReadsBack 27 C →
    let test := fun (P L : Finset (Fin 13)) =>
      let w := List.ofFn (fun p : Fin 13 => decide (p∈P)) ++ List.ofFn (fun l : Fin 13 => decide (l∈L))
      C.eval (w ++ [J.any (fun j => w.getD j false)])
    (∀ p l, p∈singerLines3 l → test {p} {l}=true) →
    (∀ Q, IsQuadrangle singerLines3 Q → test Q (missLines singerLines3 Q)=false) → 63≤C.size)
  (across : ∀ (C : Circuit) (J : List Nat), J ∈ [[0,13],[0,14]] → Monotone2 C → ReadsBack 27 C →
    let test := fun (P L : Finset (Fin 13)) =>
      let w := List.ofFn (fun p : Fin 13 => decide (p∈P)) ++ List.ofFn (fun l : Fin 13 => decide (l∈L))
      C.eval (w ++ [J.any (fun j => w.getD j false)])
    (∀ p l, p∈singerLines3 l → test {p} {l}=true) →
    (∀ Q, IsQuadrangle singerLines3 Q → test Q (missLines singerLines3 Q)=false) → 63≤C.size) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); have x5 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : List ℕ) =>   have x7 : List Bool → List Bool := fun (x7 : List Bool) => x7 ++ [x6.any fun (x8 : ℕ) => x7.getD x8 Bool.false];   (∀ (x8 x9 : Fin (13 : ℕ)), x8 - x9 ∈ x1 → x5.eval (x7 (x2 x8 x9)) = Bool.true) ∧ ∀ (x8 : Finset (Fin (13 : ℕ))), x4 x8 → x5.eval (x7 (x3 x8)) = Bool.false; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]], PEqualNP.MetaComplexity.Monotone2 x6 → (∀ (x10 : Fin x6.gates.length), ∀ x11 ∈ (x6.gates.get x10).inputs, x11 < (27 : ℕ) + ↑x10) → x5 x6 x7 → (63 : ℕ) ≤ x6.size := by
  classical
  let d : Finset (Fin 13) := {0,1,3,9}
  let pos (p l : Fin 13) := (List.ofFn (fun i : Fin 13 => decide (i=p))) ++
    List.ofFn (fun i : Fin 13 => decide (i=l))
  let neg (Q : Finset (Fin 13)) := (List.ofFn (fun i : Fin 13 => decide (i∈Q))) ++
    List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p-l∉d))
  let arc (Q : Finset (Fin 13)) := Q.card=4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p-l∈d)).card≤2
  let add (J : List Nat) (w : List Bool) := w ++ [J.any (fun j => w.getD j false)]
  let accepts (C : Circuit) (J : List Nat) :=
    (∀ p l : Fin 13, p-l∈d → C.eval (add J (pos p l))=true) ∧
    ∀ Q, arc Q → C.eval (add J (neg Q))=false
  let binary (J : List Nat) := J ∈ [[0,1],[13,14]] ∨ J ∈ [[0,13],[0,14]]
  have incidence : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p-l∈d := by decide
  have quad {Q} (hq : IsQuadrangle singerLines3 Q) : arc Q := by
    refine ⟨hq.1,fun l => ?_⟩
    have eq : Q.filter (fun p => p-l∈d)=Q ∩ singerLines3 l := by
      ext p;simp [incidence]
    rw [eq];exact hq.2 l
  have binaryBound (C : Circuit) (J : List Nat) (b : binary J) (mono : Monotone2 C)
      (legal : ReadsBack 27 C) (fit : accepts C J) : 63≤C.size := by
    let bits (P L : Finset (Fin 13)) := (List.ofFn (fun i : Fin 13 => decide (i∈P))) ++
      List.ofFn (fun i : Fin 13 => decide (i∈L))
    have pOK (p l : Fin 13) (on : p∈singerLines3 l) :
        C.eval (add J (bits {p} {l}))=true := by simpa [bits,pos] using fit.1 p l ((incidence p l).mp on)
    have nOK (Q : Finset (Fin 13)) (arcQ : IsQuadrangle singerLines3 Q) :
        C.eval (add J (bits Q (missLines singerLines3 Q)))=false := by
      have miss (l : Fin 13) : l∈missLines singerLines3 Q ↔ ∀ p∈Q, p-l∉d := by
        change l∈Finset.univ.filter (fun a => Disjoint (singerLines3 a) Q) ↔ _
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left,incidence]
        exact ⟨fun h p hp hit => h hit hp,fun h p hit hp => h p hp hit⟩
      simpa only [bits,neg,miss] using fit.2 Q (quad arcQ)
    rcases b with b|b
    · exact within C J b mono legal pOK nOK
    · exact across C J b mono legal pOK nOK
  let evalGate (g : Gate) (w : List Bool) :=
    g.op.eval (g.inputs.map fun i => w.getD i false)

  let run (gates : List Gate) (w : List Bool) :=
    gates.foldl (fun s g => s ++ [evalGate g s]) w

  have push (l : List Gate) (g : Gate) (w : List Bool) :
      run (l ++ [g]) w = run l w ++ [evalGate g (run l w)] := by
    simp [run, List.foldl_append]

  have width (l : List Gate) (w : List Bool) :
      (run l w).length = w.length + l.length := by
    induction l using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton l g ih => simp [push, ih, Nat.add_assoc]

  have read_push (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    rcases lt_trichotomy i w.length with h | h | h
    · rw [List.getD_append _ _ _ _ h, ite_eq_right (ne_of_lt h)]
    · subst i
      simp
    · rw [ite_eq_right (ne_of_gt h), List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]
  change ∀ C : Circuit, ∀ J ∈ ([[],[0],[13],[0,1],[13,14],[0,13],[0,14]] : List (List Nat)),
    Monotone2 C → (∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a<27+i.val) →
    accepts C J → 63≤C.size
  intro C J member mono back fits
  change accepts C J at fits
  have atGate (E : Circuit) (i : Nat) : gateAt E i=E.gates.getD i ⟨.or,[]⟩ := rfl
  have backC : ReadsBack 27 C := by
    intro j hj
    simpa [atGate,List.getD_eq_getElem?_getD,hj] using back (⟨j,hj⟩ : Fin C.gates.length)
  have trivialPort (t : Nat) (port : t=27+C.gates.length ∨ t<26)
      (input : ∀ w : List Bool, w.length=26 →
        (add J w).getD 26 false = (add [0,1] w).getD t false) : 63≤C.size := by
    let fence := 27+C.gates.length
    let r (j : Nat) := if j=26 then t else j
    let fix (g : Gate) : Gate :=
      let args := g.inputs.map r
      if fence∈args then
        if g.op.eval [] then ⟨.or,[]⟩ else ⟨.or,args.filter (fun j => j≠fence)⟩
      else ⟨g.op,args⟩
    let D : Circuit := ⟨C.gates.map fix,r C.output⟩
    have gateOK (g : Gate) (op : g.op ∈ ({GateOp.and,.or} : Set GateOp)) (size : g.inputs.length≤2) :
        (fix g).op∈({GateOp.and,.or} : Set GateOp) ∧ (fix g).inputs.length≤2 := by
      dsimp [fix];split
      · split
        · exact ⟨Or.inr rfl,by decide⟩
        · refine ⟨Or.inr rfl,?_⟩
          exact (List.length_filter_le _ _).trans (by simpa using size)
      · exact ⟨op,by simpa using size⟩
    have monoD : Monotone2 D := by
      intro g hg
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
      exact gateOK a (mono a ha).1 (mono a ha).2
    have backD : ReadsBack 27 D := by
      intro j hj u hu
      have orig : j<C.gates.length := by simpa [D] using hj
      let g := C.gates[j]
      have active : u∈(fix g).inputs := by
        simpa [atGate,D,List.getD_eq_getElem?_getD,orig,g] using hu
      have inArgs : u∈g.inputs.map r ∧ u≠fence := by
        dsimp only [fix] at active
        split at active
        · split at active
          · contradiction
          · simpa using List.mem_filter.mp active
        · rename_i no; exact ⟨active,fun eq => no (eq ▸ active)⟩
      obtain ⟨a,ha,eq⟩ := List.mem_map.mp inArgs.1
      have earlier := back (⟨j,orig⟩ : Fin C.gates.length) a ha
      by_cases atPort : a=26
      · have isT : u=t := by simpa [r,atPort] using eq.symm
        have ne := inArgs.2
        dsimp [fence] at ne
        omega
      · simpa [← eq,r,atPort] using earlier
    have val (g : Gate) (op : g.op∈({GateOp.and,.or} : Set GateOp)) (o w : List Bool)
        (zero : w.getD fence false=false) (agree : ∀ j, o.getD j false=w.getD (r j) false) :
        evalGate (fix g) w = evalGate g o := by
      let args := g.inputs.map r
      let v := fun j => w.getD j false
      have eq : g.inputs.map (fun i => o.getD i false)=args.map v := by
        simp only [args,List.map_map];apply List.map_congr_left;intro a _;exact agree a
      change (fix g).op.eval _=g.op.eval _
      rw [eq]
      by_cases seen : fence∈args
      · rcases op with op|op
        · have b : g.op.eval []=true := by rw [op];rfl
          have fixed : fix g=⟨.or,[]⟩ := by change (if fence∈args then _ else _)=_;rw [if_pos seen];simp [b]
          rw [fixed,op];symm
          change (args.map v).all id=false
          apply Bool.eq_false_iff.mpr;intro all
          have on := List.all_eq_true.mp all _ (List.mem_map.mpr ⟨fence,seen,rfl⟩)
          exact Bool.noConfusion (zero.symm.trans on)
        · have b : g.op.eval []=false := by rw [op];rfl
          have fixed : fix g=⟨.or,args.filter (fun j => j≠fence)⟩ := by
            change (if fence∈args then _ else _)=_;rw [if_pos seen];simp [b,args]
          rw [fixed,op]
          change ((args.filter (fun j => j≠fence)).map v).any id=(args.map v).any id
          simp only [List.any_map,List.any_filter]
          apply List.any_congr rfl;intro a
          have vf : v fence=false := zero
          by_cases h : a=fence <;> simp [h,vf]
      · have fixed : fix g=⟨g.op,args⟩ := by change (if fence∈args then _ else _)=_;rw [if_neg seen]
        rw [fixed]
    have simulate (w : List Bool) (hw : w.length=26) (gs : List Gate)
        (ops : ∀ g∈gs, g.op∈({GateOp.and,.or} : Set GateOp)) (limit : gs.length≤C.gates.length) :
        ∀ j, (run gs (add J w)).getD j false=(run (gs.map fix) (add [0,1] w)).getD (r j) false := by
      induction gs using List.reverseRecOn with
      | nil =>
        intro j
        by_cases h : j=26
        · simpa [r,h,run] using input w hw
        · change (w++[_]).getD j false=(w++[_]).getD (r j) false
          simp only [r,if_neg h,read_push,hw,if_neg h]
      | append_singleton pre g ih =>
        have sz : pre.length<C.gates.length := by simp at limit;omega
        have prior := ih (fun a ha => ops a (by simp [ha])) sz.le
        have wO : (run pre (add J w)).length=27+pre.length := by simp [width,add,hw]
        have wN : (run (pre.map fix) (add [0,1] w)).length=27+pre.length := by simp [width,add,hw]
        have far : (run (pre.map fix) (add [0,1] w)).getD fence false=false :=
          List.getD_eq_default _ _ (by rw [wN];dsimp [fence];omega)
        intro j
        rw [List.map_append,List.map_singleton,push,push,read_push,read_push,wO,wN]
        have hit : r j=27+pre.length ↔ j=27+pre.length := by dsimp [r];split_ifs <;> omega
        by_cases isNew : j=27+pre.length
        · rw [if_pos isNew,if_pos (hit.mpr isNew)]
          exact (val g (ops g (by simp)) _ _ far prior).symm
        · rw [if_neg isNew,if_neg (fun e => isNew (hit.mp e)),prior]
    have transfer (w : List Bool) (hw : w.length=26) : D.eval (add [0,1] w)=C.eval (add J w) :=
      (simulate w hw C.gates (fun g hg => (mono g hg).1) (by rfl) C.output).symm
    have newFits : accepts D [0,1] := by
      constructor
      · intro p l hit;rw [transfer _ (by simp [pos])];exact fits.1 p l hit
      · intro Q hQ;rw [transfer _ (by simp [neg])];exact fits.2 Q hQ
    have got := binaryBound D [0,1] (Or.inl (by simp)) monoD backD newFits
    change 63≤(C.gates.map fix).length at got
    change 63≤C.gates.length
    simpa only [List.length_map] using got
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with empty|point|line|pp|ll|pl|off
  · apply trivialPort (27+C.gates.length) (Or.inl rfl)
    intro w hw;rw [empty]
    change (w++[false]).getD 26 false=(w++[_]).getD _ false
    rw [read_push,read_push,hw,if_pos rfl,if_neg (show 27+C.gates.length≠26 by omega),
      List.getD_eq_default _ _ (by omega)]
  · apply trivialPort 0 (Or.inr (by decide))
    intro w hw;rw [point];change (w++[_]).getD 26 false=(w++[_]).getD 0 false
    simp only [read_push,hw,ite_true];simp [add,List.any_cons,List.any_nil]
  · apply trivialPort 13 (Or.inr (by decide))
    intro w hw;rw [line];change (w++[_]).getD 26 false=(w++[_]).getD 13 false
    simp only [read_push,hw,ite_true];simp [add,List.any_cons,List.any_nil]
  · exact binaryBound C J (Or.inl (by simp [pp])) mono backC fits
  · exact binaryBound C J (Or.inl (by simp [ll])) mono backC fits
  · exact binaryBound C J (Or.inr (by simp [pl])) mono backC fits
  · exact binaryBound C J (Or.inr (by simp [off])) mono backC fits
