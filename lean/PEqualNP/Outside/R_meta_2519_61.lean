import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2519_61
 (h1 : ∀ (n : ℕ) (D : Circuit), FanInTwo D →
  ∃ S : Finset ℕ, S.card ≤ (D.gates.countP fun g => !(g.op.eval [false]))+1 ∧
    ∀ X Y : List Bool, X.length=n → Y.length=n →
      (∀ i ∈ S, X.getD i false=Y.getD i false) → D.eval X=D.eval Y)
 (h2 :
  let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  ∀ P : Circuit, Monotone2 P → P.size=8 →
  (∀ x : Fin 9 → Bool, (P.wires (List.ofFn x)).getD 9 false=(x 0 || x 2)) →
  ∀ S : Finset ℕ, S.card ≤ 6 → ∃ x y : Fin 9 → Bool,
    (∀ j ∈ S, (P.wires (List.ofFn x)).getD j false=(P.wires (List.ofFn y)).getD j false) ∧ F x ≠ F y) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ (8 : ℕ) ≤ ↑x3 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C hC hex first target
  obtain ⟨i,j,hij,h8,hi,hj,only⟩ := hex
  have hil := i.isLt
  have hjl := j.isLt
  change i.val < j.val at hij
  have hge : 8 ≤ C.gates.length := by omega
  let P : Circuit := ⟨C.gates.take 8,0⟩
  let D : Circuit := ⟨C.gates.drop 8,C.output⟩
  have plen : P.size=8 := by
    change (C.gates.take 8).length=8
    simp [Nat.min_eq_left hge]
  have mono : Monotone2 P := by
    intro g hg
    obtain ⟨k,hk,he⟩ := List.getElem_of_mem hg
    change k < (C.gates.take 8).length at hk
    have hk8 : k<8 := by simp [Nat.min_eq_left hge] at hk; exact hk
    let t : Fin C.gates.length := ⟨k,by omega⟩
    have ht : C.gates.get t=g := by simpa [P,t,List.get_eq_getElem] using he
    have hgate := hC g (ht ▸ C.gates.get_mem t)
    refine ⟨?_,hgate.2⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hgate ⊢
    rcases hgate.1 with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · rcases only t ((congrArg Gate.op ht).trans h) with hi'|hj'
      · have := congrArg Fin.val hi'
        change k=i.val at this
        omega
      · have := congrArg Fin.val hj'
        change k=j.val at this
        omega
  let run (gs : List Gate) (w : List Bool) := (Circuit.mk gs 0).wires w
  have runlen (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (w++[_])).length=_
      rw [ih]
      simp; omega
  have preserves (gs : List Gate) (w : List Bool) (q : ℕ) (hq : q<w.length) :
      (run gs w).getD q false=w.getD q false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (w++[_])).getD q false=_
      rw [ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hq
  have full (w : List Bool) : C.wires w=D.wires (P.wires w) := by
    let step := fun (v : List Bool) (g : Gate) => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]
    change C.gates.foldl step w=(C.gates.drop 8).foldl step ((C.gates.take 8).foldl step w)
    rw [← List.foldl_append,List.take_append_drop]
  have prefLen (x : Fin 9 → Bool) : (P.wires (List.ofFn x)).length=17 := by
    change (run P.gates _).length=17
    rw [runlen,List.length_ofFn]
    change 9+P.size=17
    omega
  have hpfirst (x : Fin 9 → Bool) : (P.wires (List.ofFn x)).getD 9 false=(x 0 || x 2) := by
    rw [← first x,full]
    exact (preserves D.gates _ 9 (by rw [prefLen]; decide)).symm
  have two (L : List Gate) (p : Gate→Bool) (a b : ℕ) (hab : a<b) (hb : b<L.length)
      (ha' : p L[a]=false) (hb' : p L[b]=false) : L.countP p+2≤L.length := by
    induction L generalizing a b with
    | nil => simp at hb
    | cons g l ih =>
      cases b with
      | zero => omega
      | succ b =>
        have hbl : b<l.length := by simpa using hb
        simp only [List.getElem_cons_succ] at hb'
        cases a with
        | zero =>
          simp only [List.getElem_cons_zero] at ha'
          have hh : l.countP p ≠ l.length := by
            intro eq
            have := List.countP_eq_length.mp eq l[b] (List.getElem_mem ..)
            simp [hb'] at this
          have hle := List.countP_le_length (p:=p) (l:=l)
          simp only [List.countP_cons,ha',Bool.false_eq_true,ite_false,Nat.add_zero,List.length_cons]
          omega
        | succ a =>
          have haa : a<b := by omega
          have hh := ih a b haa hbl (by simpa using ha') hb'
          simp only [List.countP_cons,List.length_cons]
          split <;> omega
  have hD : FanInTwo D := fun g hg => hC g (List.mem_of_mem_drop hg)
  let p := fun g : Gate => !(g.op.eval [false])
  have il : i.val-8 < D.gates.length := by simp [D]; omega
  have jl : j.val-8 < D.gates.length := by simp [D]; omega
  have pi : p D.gates[i.val-8]=false := by
    have ee : 8+(i.val-8)=i.val := by omega
    have hh : D.gates[i.val-8]=C.gates.get i := by simp [D,List.get_eq_getElem,List.getElem_drop,ee]
    simp only [p,hh,hi]; rfl
  have pj : p D.gates[j.val-8]=false := by
    have ee : 8+(j.val-8)=j.val := by omega
    have hh : D.gates[j.val-8]=C.gates.get j := by simp [D,List.get_eq_getElem,List.getElem_drop,ee]
    simp only [p,hh,hj]; rfl
  have small := two D.gates p (i.val-8) (j.val-8) (by omega) jl pi pj
  by_contra! short
  change C.gates.length<16 at short
  obtain ⟨S,hS,hdep⟩ := h1 17 D hD
  change S.card ≤ D.gates.countP p+1 at hS
  have dl : D.gates.length=C.gates.length-8 := List.length_drop
  obtain ⟨x,y,ha,hne⟩ := h2 P mono plen hpfirst S (by omega)
  have same := hdep _ _ (prefLen x) (prefLen y) ha
  have out : circuitFun 9 C x=circuitFun 9 C y := by
    change (C.wires _).getD C.output false=(C.wires _).getD C.output false
    simpa only [full] using (show (D.wires (P.wires (List.ofFn x))).getD C.output false=
      (D.wires (P.wires (List.ofFn y))).getD C.output false from same)
  apply hne
  rw [target] at out
  simp only [List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] at out ⊢
  convert out using 1
